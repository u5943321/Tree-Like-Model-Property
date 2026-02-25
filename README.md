# Supplementary material accompanying ITP 2025 submission #68: "Finite Tree-Like Property for Multi-Modal Logic"

## Content

This archive contains the following files (ordered by dependency):

- Modal_Syntax: basic facts about the syntax of modal logic, including signatures
- Modal_Model: basic definition and lemmas about structures for modal logic
- Modal_Semantics: basic definition and lemmas about structures for modal logic
- Bool_Comb: lemmas about boolean combination (to prove Theorem 6)
- Disjoint_Union: definition of disjoint union of structures, and application of it to prove the congruence theorem (Theorem 5 in our paper).
- deg_wffs: the proof that we have only finitely many modal formulas of degree no more than n up to equivalence (Theorem 6)
- Bounded_Morphism: the definition of bounded morphism and the proof that a world and its image under a bounded morphism satisfy the same modal formulas (required by the tree-like property)
- Generated_Submodel: about generated substructures
- Tree_Like_Model: definition of a tree, and the proof of the tree-like property
- n-Bisimulation: the definition of n-bisimulation and the proof that worlds that are linked by an n-bisimulation satisfy the same modal formulas up to degree n
- Finite_Model: intermediate lemmas and definitions required for constructing the world set of the finite tree-like structure
- Upgraded_TLP_and_FMP: The proofs of the strengthened version of tree-like property and finite-tree-like property, where the strengthen happens in the sense described in the paragraph between Theorem 18 and its proof
- FMP_in_HOLZF: the proof of the main theorem (Theorem 18)


## Instructions to verify the results

This work was formalized using Isabelle/HOL on Isabelle2025-2. To verify it, you must follow these steps:

1. Download Isabelle2025-2 here: https://www.isabelle.in.tum.de/index.html 
(or, if a later version of isabelle is available from the main page, go to: https://www.isabelle.in.tum.de/download_past.html)

2. Install Isabelle2025-2 on your system following the instructions here: https://www.isabelle.in.tum.de/installation.html

3. Open the file FMP_in_HOLZF and go to the end of the file. This will ensure Isabelle runs through all the theories in this work


## Detailed connections with the paper

### Section 2 (Syntax and Semantics)

| Notion in paper                    | Theory          | Notion in Theory               |
|------------------------------------|-----------------|--------------------------------|
| constructors of modal formulas     | Modal_Syntax    | datatype ('m,'p) cform         |
| signature                          | Modal_Syntax    | type_synonym ('m,'p) sig       |
| structure                          | Modal_Model     | type_synonym ('m,'p,'a) struct |
| struct_on (\tau-structure)         | Modal_Model     | is_struct                      |
| Definition 1 (\Vdash_\tau)         | Modal_Semantics | csatis                         |
| Extension of Definition 1 (\Vdash) | Modal_Semantics | asatis                         |
| Lemma 2                            | Modal_Semantics | csatis_asatis                  |

### Section 3 (Formula equivalence)

| Notion in paper                       | Theory          | Notion in Theory |
|---------------------------------------|-----------------|------------------|
| Definition 3 (semantical equivalence) | Modal_Semantics | cequiv           |

#### Section 3.1 (Congruence condition for triangle formulas)

| Notion in paper                          | Theory         | Notion in Theory             |
|------------------------------------------|----------------|------------------------------|
| disjoint union (in the proof of Lemma 4) | Disjoint_Union | Du                           |
| Lemma 4                                  | Disjoint_Union | infinite_cDIAM_cequiv_ops_eq |
| Theorem 5                                | Disjoint_Union | infinite_cDIAM_cong_iff      |

#### Section 3.2 (Finiteness of equivalence classes of degree-bounded formulas)

| Notion in paper | Theory          | Notion in Theory               |
|-----------------|-----------------|--------------------------------|
| degree          | Modal_Syntax    | deg                            |
| degwffs         | Modal_Semantics | deg_wffs                       |
| Theorem 6       | deg_wffs        | prop_2_29                      |
| peval           | Bool_Comb       | peval                          |
| Equation (1)    | Bool_Comb       | a special case of peval_asatis |
| boolcomb        | Bool_Comb       | bool_comb                      |
| prop            | Modal_Syntax    | prop_cform                     |
| Lemma 7         | Bool_Comb       | bool_comb_prop_cform_EXISTS    |
| Theorem 8       | Bool_Comb       | subst_equiv                    |

| Proof of  | Arguments in paper        | Theory    | Argument in theory              |
|---------------------------------------|-----------|---------------------------------|  
| Theorem 6 | base case injection       | Bool_Comb | bool_comb_INJ_prop_cform_cequiv |
| Theorem 8 | first horizontal equality | Bool_Comb | subst_prop_cform_asatis         |
| Theorem 8 | third horizontal equality | Bool_Comb | peval_asatis                    |


### Section 4 (Tree-Like frames)

| Notion in paper     | Theory             | Notion in Theory      |
|---------------------|--------------------|-----------------------|
| \widehat{R}_O       | Generated_Submodel | gen_birel             |
| Definition 9 (tree) | Tree_Like_Model    | tree                  |
| Lemma 10            | Tree_Like_Model    | tree_like_property'   |
| height_\le          | Finite_Model       | height_le             |
| height              | Finite_Model       | height                |
| Theorem 11          | Finite_Model       | tree_height_rel_lemma |

Comment: tree_like_property' has a short proof because it simply replaces "csatis"(||-_\tau in the paper) with "asatis" (||- in the paper) in tree_like_property.

### Section 5 (Construction of the finite tree-like structure)

| Notion in paper     | Theory               | Notion in Theory           |
|---------------------|----------------------|----------------------------|
| Theorem 12          | Upgraded_TLP_and_FMP | Finite_Tree_Model_Property |

Comment: The Finite_Tree_Model_Property in Isabelle has an extra conjunct "world fM ⊆ {l. set l ⊆ world M00}" on its conclusion. 
This is due to the refinement required for transferring to the ZF version (as discussed between Theorem 18 and its proof in our paper) 
and is not required for the standard HOL logic version of finite tree-like property.

#### Section 5.1 (Structure construction)

| Notion in paper     | Theory               | Notion in Theory                                           |
|---------------------|----------------------|------------------------------------------------------------|
| reps                | deg_wffs             | cDIAM_deg_wff_reps                                         |
| Eps                 | deg_wffs             | in Choice, the first cast sets to characteristic functions |
| Lemma 13            | deg_wffs             | cDIAM_deg_wff_reps_properties'                             |
| Property 14         | Upgraded_TLP_and_FMP | in proof of Finite_Tree_Model_Property (~line 330)         |

Comment: cDIAM_deg_wff_reps_properties' has a short proof because it simply replaces "not equivalent to FALSE" with "satisfiable".

#### Section 5.2 (Satisfaction via n-bisimulation)

| Notion in paper                | Theory                 | Notion in Theory                              |
|--------------------------------|------------------------|-----------------------------------------------|
| Definition 15 (n-bisimulation) | n_Bisimulation         | n_bisim                                       |
| Z (middle of page 12)          | Upgraded_TLP_and_FMP   | Z (~line 360, in proof)                       |  
| Property 16                    | deg_wffs               | in definition of deg_thy                      | 
| The 4 formulas on page 13      | Upgraded_TLP_and_FMP   | lines 552,471,507 (ul'fl'sat),492 (philfl'eq) | 

### Section 6 (Using HOLZF to avoid the type issue)

| Notion in paper | Theory       | Notion in Theory             |
|-----------------|--------------|------------------------------|
| Theorem 17      | FMP_in_HOLZF | small_alt                    |
| Vstruct_on      | FMP_in_HOLZF | is_Vstruct                   |
| Theorem 18      | FMP_in_HOLZF | Finite_Tree_Model_Property_V |
| \equiv^V        | FMP_in_HOLZF | Vequiv                       |
| Theorem 19      | FMP_in_HOLZF | Vequiv_small_type            |



