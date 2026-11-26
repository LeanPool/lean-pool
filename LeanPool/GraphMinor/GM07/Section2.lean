/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2Base
public import LeanPool.GraphMinor.GM07.Section2Euler
public import LeanPool.GraphMinor.GM07.Section2MinVal
public import LeanPool.GraphMinor.GM07.Section26
public import LeanPool.GraphMinor.GM07.Section2Seam

/-!
# Graph Minors VII, Section 2: Main Theorems (2.1)–(2.6)

This file states and proves the numbered results `(2.1)`–`(2.6)` of Section 2 (pages 213–218) of
N. Robertson and P. D. Seymour, *Graph Minors. VII. Disjoint paths on a surface*,
J. Combin. Theory Ser. B 45 (1988) 212–254:
- `(2.1)` (`theorem_2_1_forward`): the forward direction of the characterization of seam graphs, as
  printed. The printed converse fails (`not_theorem_2_1_proof` in
  `GraphMinor/GM07/Section2Seam.lean`);
  the converse for `U(J)` connected and the equivalence `theorem_2_1_proof` are in
  `GraphMinor/GM07/Section2Converse.lean`;
- `(2.2)` (`theorem_2_2`): vertex and edge bounds for seam graphs of minimum valency at least `3`,
  proved from `seamGraph_euler_formula` (`GraphMinor/GM07/Section2Euler.lean`) and the handshaking
  lemma (`three_mul_ncard_V_le_two_mul_ncard_E`);
- `(2.3)` (`theorem_2_3`): every vertex of the seam graph of a minimal net has valency at least `3`;
- `(2.4)` (`theorem_2_4`): vertex and edge bounds for the seam graph of a minimal net, deduced from
  `(2.2)`, `(2.3)`, and `Surface.modelCriterion`;
- `(2.5)` (`theorem_2_5`): existence of a path in `J'` between `φ(s)` and `φ(t)` with no edges of
  type (iii) or (iv);
- `(2.6)` (`theorem_2_6`): shortcutting a `φ⁻¹(G)`-normal proper `I`-arc `F` in `Δ` by a `G`-normal
  `O`-arc `A` in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Graph Minors VII, (2.1) (pages 215–216), forward direction as printed:
"Let $J$ be a graph in $\Sigma$. Then $J$ is a seam graph for some net if and only if
(i) $bd(\Sigma) \subseteq U(J)$, and for every edge $e$ of $J$, either $e \subseteq bd(\Sigma)$ or
$e \cap bd(\Sigma) = \emptyset$, (ii) $J - bd(\Sigma)$ has no isolated vertices, (iii) $J$ has a
unique region, and (iv) every $O$-arc included in that region is null-homotopic."
Here `deleteBd J` is the paper's `J - bd(Σ)` (page 214). The printed converse is false
(`not_theorem_2_1_proof`, `GraphMinor/GM07/Section2Seam.lean`). See the correction to (2.1) in
`corrections/GM07.md`. -/
theorem theorem_2_1_forward [T1Space S] (hS : IsSurface S) (J : Drawing S) (hJ : IsSeamGraph J) :
    (bd S ⊆ J.U ∧ ∀ e ∈ J.E, e ⊆ bd S ∨ e ∩ bd S = ∅) ∧
    HasNoIsolatedVertices (deleteBd J) ∧
    J.R.ncard = 1 ∧
    (∀ r ∈ J.R, ∀ F : Set S, F ⊆ r → IsOArc F → IsNullHomotopicOArc F) := by
  have : T2Space S := hS.2.1
  obtain ⟨N, hNJ⟩ := hJ
  exact ⟨N.bd_subset_and_edges_seamGraph hS hNJ, N.hasNoIsolatedVertices_deleteBd_seamGraph hS hNJ,
    (N.seamGraph_unique_region hNJ).2, N.seamGraph_region_nullHomotopic hS hNJ⟩

/-- Graph Minors VII, (2.2) (page 216):
"(2.2) *Let $\Sigma \cong \Sigma(a, b, c)$ and let $J$ be a seam graph in $\Sigma$ for some net.
Suppose that every vertex of $J$ has valency at least $3$. Then $|V(J)| \le 2(2a + b + c - 1)$, and
$|E(J)| \le 3(2a + b + c - 1)$.*" -/
theorem theorem_2_2_proof (hS : IsSurface S) {a b c : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (J : Drawing S)
    (hSeam : IsSeamGraph J) (hval : ∀ v ∈ J.V, 3 ≤ vertexValency J v) :
    J.V.ncard ≤ 2 * (2 * a + b + c - 1) ∧ J.E.ncard ≤ 3 * (2 * a + b + c - 1) := by
  have heuler : J.E.ncard + 1 = J.V.ncard + 2 * a + b + c :=
    seamGraph_euler_formula S hS a b c he J hSeam
  have hdeg : 3 * J.V.ncard ≤ 2 * J.E.ncard :=
    three_mul_ncard_V_le_two_mul_ncard_E J hval
  omega

/-- Graph Minors VII, (2.3) (pages 216–217):
"(2.3) *Let $\Sigma$ be a connected surface with $\Sigma \not\cong \Sigma(0, 0, 0)$, $\Sigma(0, 0,
1)$,
... $\Sigma(0, 1, 0)$. Let $J$ be the seam graph for some minimal net with respect to some proper
graph
$G$ in $\Sigma$. Then no vertex of $J$ has valency $\le 2$.*" -/
theorem theorem_2_3_proof (hS : IsSurface S) [hConn : ConnectedSpace S]
    (h000 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 0))
    (h001 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 1))
    (h010 : ¬ Nonempty (S ≃ₜ SurfaceModel 0 1 0))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J) :
    ∀ v ∈ J.V, 3 ≤ vertexValency J v :=
  minimalNet_minValency S hS hConn h000 h001 h010 G J N hG hMin hSeam

/-- Graph Minors VII, (2.4) (page 217):
"(2.4) *If $\Sigma \cong \Sigma(a, b, c)$ where $2a + b + c > 1$, and $J$ is the seam graph for
some minimal net for $\Sigma$ (with respect to some $G$), then $|V(J)| \le 2(2a + b + c - 1)$ and
$|E(J)| \le 3(2a + b + c - 1)$.*" -/
theorem theorem_2_4_proof (hS : IsSurface S) {a b c : ℕ} (habc : 2 * a + b + c > 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J) :
    J.V.ncard ≤ 2 * (2 * a + b + c - 1) ∧ J.E.ncard ≤ 3 * (2 * a + b + c - 1) := by
  obtain ⟨hconn, h000, h001, h010⟩ := not_homeo_small_models_of_gt_one habc he
  have : ConnectedSpace S := hconn
  have hval : ∀ v ∈ J.V, 3 ≤ vertexValency J v :=
    theorem_2_3_proof hS h000 h001 h010 hG hMin hSeam
  exact theorem_2_2_proof hS he J ⟨N, hSeam⟩ hval

/-- Graph Minors VII, (2.5) (page 217):
"(2.5) *There is a path of $J'$ between $\phi(s)$ and $\phi(t)$ with no edges of type (iii) or
(iv).*" -/
theorem theorem_2_5_proof [T1Space S] (hS : IsSurface S) (N : Net S) (J J' : Drawing S)
    (hSeam : N.IsSeamGraphFor J) {s t : N.D} (hs : s ∈ bd N.D) (ht : t ∈ bd N.D) (hst : s ≠ t)
    {C₁ C₂ : Set N.D} (hcomp : componentsIn (bd N.D \ {s, t}) = {C₁, C₂}) (hC12 : C₁ ≠ C₂)
    (hJ'U : J'.U = J.U) (hJ'V : J'.V = J.V ∪ {N.φ s, N.φ t}) :
    ∃ P : Drawing S, P.IsSubdrawing J' ∧ P.IsPathBetween (N.φ s) (N.φ t) ∧
      ∀ e ∈ P.E, ¬ IsNetEdgeType3 N C₁ e ∧ ¬ IsNetEdgeType4 N C₂ e :=
  exists_path_no_type3_type4 hS N J J' hSeam hs ht hst hcomp hC12 hJ'U hJ'V

/-- Graph Minors VII, (2.6) (page 218):
"(2.6) *Let $(\Delta, \Pi)$ be a minimal net with respect to a proper graph $G$ in $\Sigma$, where
$\Sigma \cong \Sigma(a, b, c)$ and $2a + b + c > 1$. Let $J$ be the associated seam graph and let
$\phi$ be the associated surjection. Let $F$ be a $\phi^{-1}(G)$-normal proper $I$-arc in $\Delta$
with ends $s, t$, and let $F^* = F - \{s, t\}$. Then there is a $G$-normal $O$-arc $A$ in $\Sigma$
with*
$$|A \cap V(G)| \le 2(2a + b + c)(|\phi(F^*) \cap V(G)| + 1) + |bd(\Sigma) \cap V(G)|$$
*and with $\phi(F) \subseteq A \subseteq \phi(F) \cup U(J)$.*" -/
theorem theorem_2_6_proof [T1Space S] (hS : IsSurface S) {a b c : ℕ} (habc : 2 * a + b + c > 1)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {G J : Drawing S} {N : Net S}
    (hG : G.IsProper) (hMin : N.IsMinimalFor G) (hSeam : N.IsSeamGraphFor J)
    {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    {F : Set N.D} {s t : N.D}
    (hNorm : G_D.IsNormal F) (hProperF : IsProperIArc F) (hEnds : IsLineWithEnds F s t) :
    ∃ A : Set S, G.IsNormal A ∧ IsOArc A ∧
      (A ∩ G.V).ncard ≤
        2 * (2 * a + b + c) * ((N.φ '' (F \ {s, t}) ∩ G.V).ncard + 1) +
          (bd S ∩ G.V).ncard ∧
      N.φ '' F ⊆ A ∧ A ⊆ N.φ '' F ∪ J.U := by
  obtain ⟨hV, hE⟩ := theorem_2_4_proof hS habc he hG hMin hSeam
  exact minimalNetShortcutOArc S hS a b c habc he G J N hG hMin hSeam hV hE G_D hPull F s t hNorm
    hProperF hEnds

end GraphMinor.GM07
