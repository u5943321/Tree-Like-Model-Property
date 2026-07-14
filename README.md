# Supplementary material accompanying the paper "Finite Tree-Like Property for Multi-Modal Logic"

## Content

This archive contains the following files (ordered by dependency):

- Modal_Syntax: basic facts about the syntax of modal logic, including signatures

- Modal_Model: basic definition and lemmas about structures for modal logic

- Modal_Semantics: basic definition and lemmas about structures for modal logic

- Bool_Comb: lemmas about boolean combination (to prove Theorem 2.4)

- Disjoint_Union: definition of disjoint union of structures, and application of it to prove the congruence theorem (Theorem 2.3 in our paper)

- deg_wffs: the proof that we have only finitely many modal formulas of degree no more than n up to equivalence (Theorem 2.4)

- Bounded_Morphism: the definition of bounded morphism and the proof that a world and its image under a bounded morphism satisfy the same modal formulas (required by the tree-like property)

- Generated_Submodel: about generated substructures

- Tree_Like_Model: definition of a tree, and the proof of the tree-like property

- n-Bisimulation: the definition of n-bisimulation and the proof that worlds that are linked by an n-bisimulation satisfy the same modal formulas up to degree n

- Finite_Model: intermediate lemmas and definitions required for constructing the world set of the finite tree-like structure

- Upgraded_TLP_and_FMP: the proofs of the strengthened version of tree-like property and finite-tree-like property, where the strengthen happens in the sense described in the paragraph between Theorem 5.4 and its proof

- FMP_in_HOLZF: the proof of the main theorem (Theorem 5.4)

- Partition_Alt: minor extension to make the partition lemmas easier to use  (since the lemmas provided by the existing library does not allow quotienting a set A by a relation that relates elements beyond A)


## Instructions to verify the results

This work was formalized using Isabelle/HOL version Isabelle2025-2. To verify it, follow these steps:

1. Download Isabelle2025-2 from https://www.isabelle.in.tum.de/index.html (or, if a later version of isabelle is available from the main page, go to https://www.isabelle.in.tum.de/download_past.html)

2. Install Isabelle2025-2 on your system following the instructions here: https://www.isabelle.in.tum.de/installation.html

3. Install the Isabelle2025-2 edition of the Archive of Formal Proof. See https://isa-afp.org/download/ for downloading instructions and https://isa-afp.org/help/ for further help.

4. Open the file FMP_in_HOLZF and go to the end of the file. This will ensure Isabelle runs through all the theories in this work


## Detailed connections with the paper

### Section 1 (Syntax and Semantics)

| Notion in paper                      | Theory          | Notion in Theory               |
|--------------------------------------|-----------------|--------------------------------|
| constructors of modal formulas       | Modal_Syntax    | datatype ('m,'p) cform         |
| signature                            | Modal_Syntax    | type_synonym ('m,'p) sig       |
| structure                            | Modal_Model     | type_synonym ('m,'p,'a) struct |
| struct_on (\tau-structure)           | Modal_Model     | is_struct                      |
| Definition 1.2 (\Vdash_\tau)         | Modal_Semantics | csatis                         |
| Extension of Definition 1.2 (\Vdash) | Modal_Semantics | asatis                         |
| Lemma 1.3                            | Modal_Semantics | csatis_asatis                  |

### Section 2 (Formula equivalence)

| Notion in paper                         | Theory          | Notion in Theory |
|-----------------------------------------|-----------------|------------------|
| Definition 2.1 (semantical equivalence) | Modal_Semantics | cequiv           |

#### Section 3.1 (Congruence condition for triangle formulas)

| Notion in paper                            | Theory         | Notion in Theory             |
|--------------------------------------------|----------------|------------------------------|
| disjoint union (in the proof of Lemma 2.2) | Disjoint_Union | Du                           |
| Lemma 2.2                                  | Disjoint_Union | infinite_cDIAM_cequiv_ops_eq |
| Theorem 2.3                                | Disjoint_Union | infinite_cDIAM_cong_iff      |


#### Section 3.2 (Finiteness of equivalence classes of degree-bounded formulas)

| Notion in paper | Theory          | Notion in Theory               |
|-----------------|-----------------|--------------------------------|
| degree          | Modal_Syntax    | deg                            |
| degwffs         | Modal_Semantics | deg_wffs                       |
| Theorem 2.4     | deg_wffs        | prop_2_29                      |
| peval           | Bool_Comb       | peval                          |
| Equation (1)    | Bool_Comb       | a special case of peval_asatis |
| boolcomb        | Bool_Comb       | bool_comb                      |
| prop            | Modal_Syntax    | prop_cform                     |
| Lemma 2.5       | Bool_Comb       | bool_comb_prop_cform_EXISTS    |
| Theorem 2.6     | Bool_Comb       | subst_equiv                    |

| Proof of  | Arguments in paper        | Theory    | Argument in theory              |
|-----------|---------------------------|-----------|---------------------------------|  
| Theorem 2.4 | base case injection     | Bool_Comb | bool_comb_INJ_prop_cform_cequiv |
| Theorem 2.6 | first vertical equality | Bool_Comb | subst_prop_cform_asatis         |
| Theorem 2.6 | third vertical equality | Bool_Comb | peval_asatis                    |


### Section 3 (Tree-Like frames)

| Notion in paper       | Theory             | Notion in Theory      |
|-----------------------|--------------------|-----------------------|
| \widehat{R}_O         | Generated_Submodel | gen_birel             |
| Definition 3.1 (tree) | Tree_Like_Model    | tree                  |
| Lemma 3.2             | Tree_Like_Model    | tree_like_property'   |
| height_\le            | Finite_Model       | height_le             |
| height                | Finite_Model       | height                |
| Theorem 3.3           | Finite_Model       | tree_height_rel_lemma |

Comment: tree_like_property' has a short proof because it simply replaces "csatis"(||-_\tau in the paper) with "asatis" (||- in the paper) in tree_like_property.


### Section 4 (Construction of the finite tree-like structure)

| Notion in paper     | Theory               | Notion in Theory           |
|---------------------|----------------------|----------------------------|
| Theorem 4.1         | Upgraded_TLP_and_FMP | Finite_Tree_Model_Property |

Comment: The Finite_Tree_Model_Property in Isabelle has an extra conjunct "world fM ⊆ {l. set l ⊆ world M00}" on its conclusion. 
This is due to the refinement required for transferring to the ZF version (as discussed between Theorem 5.4 and its proof in our paper) 
and is not required for the standard HOL logic version of finite tree-like property.


#### Section 4.1 (Structure construction)

| Notion in paper     | Theory               | Notion in Theory                                           |
|---------------------|----------------------|------------------------------------------------------------|
| reps                | deg_wffs             | cDIAM_deg_wff_reps                                         |
| Eps                 | deg_wffs             | in Choice, the first cast sets to characteristic functions |
| Lemma 4.2           | deg_wffs             | cDIAM_deg_wff_reps_properties'                             |
| Property 1          | Upgraded_TLP_and_FMP | in proof of Finite_Tree_Model_Property (~line 330)         |

Comment: cDIAM_deg_wff_reps_properties' has a short proof because it simply replaces "not equivalent to FALSE" with "satisfiable".


#### Section 4.2 (Satisfaction via n-bisimulation)

| Notion in paper                 | Theory                 | Notion in Theory                              |
|---------------------------------|------------------------|-----------------------------------------------|
| Definition 4.3 (n-bisimulation) | n_Bisimulation         | n_bisim                                       |
| Z (page 13)                     | Upgraded_TLP_and_FMP   | Z (~line 360, in proof)                       |  
| Property 2                      | deg_wffs               | in definition of deg_thy                      | 
| The 4 formulas on page 14       | Upgraded_TLP_and_FMP   | lines 552,471,507 (ul'fl'sat),492 (philfl'eq) | 


### Section 5 (Using HOLZF to avoid the type issue)

| Notion in paper | Theory       | Notion in Theory             |
|-----------------|--------------|------------------------------|
| Theorem 5.2     | FMP_in_HOLZF | small_alt                    |
| Vstruct_on      | FMP_in_HOLZF | is_Vstruct                   |
| Theorem 5.4     | FMP_in_HOLZF | Finite_Tree_Model_Property_V |
| \equiv^V        | FMP_in_HOLZF | Vequiv                       |
| Theorem 5.5     | FMP_in_HOLZF | Vequiv_small_type            |
