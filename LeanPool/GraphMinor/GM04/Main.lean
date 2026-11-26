/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM04.Patchwork.Main
public import LeanPool.GraphMinor.GM04.Decomposition.TreeWidth
public import LeanPool.GraphMinor.GM04.TreeLemma.Lemma22
public import LeanPool.GraphMinor.GM04.HigmanProof
public import LeanPool.GraphMinor.Thomas.Translate
public import LeanPool.GraphMinor.Menger.Basic
public import LeanPool.GraphMinor.Minor.Basic

/-!
# Graph Minors IV, (1.5), with every hypothesis proved

`GM04.theorem_1_5_proved` derives (1.5) from (5.3), Menger's theorem, the labelled finite-set
generalization of Higman's theorem (8.3) and the description of minors by models. This file
supplies each of them:
- (5.3) is `theorem_5_3`, which uses the tree lemma (2.2) (`lemma_2_2`) and Thomas's lemma (5.1)
  (`thomas_5_1`, which uses Menger's theorem);
- Menger's theorem is `menger`;
- `higman_8_3` is the generalization of (8.3) allowing repeated labels;
- the statement about models of minors is `isIsoMinor_of_isMinorModel`.
-/

@[expose] public section

namespace GraphMinor.GM04

open Graph

universe u v

/-- Graph Minors IV, (1.5) (page 229): "For any integer $k$ the class of all graphs with tree-width
$\le k$ is well-quasi-ordered by
minors." In the form of `theorem_1_5_of_cited`: every sequence
of finite graphs of tree-width `≤ k` has `i < j` with `G i` isomorphic to a minor of `G j`. -/
theorem theorem_1_5_proved {α : Type u} {β : Type v} (k : ℕ) (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (htw : ∀ n, TreeWidthLE (Hypergraph.ofGraph (G n) (hV n) (hE n)).toRooted k) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) :=
  theorem_1_5_of_cited.{u, v, 0, 0} (theorem_5_3_proof lemma_2_2 (thomas_5_1)) menger higman_8_3
    isIsoMinor_of_isMinorModel k G hV hE htw

end GraphMinor.GM04
