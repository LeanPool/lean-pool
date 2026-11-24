/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section9CoreProved
import LeanPool.GraphMinor.GM07.Section9CylinderProved

/-!
# Graph Minors VII, (9.3) to (9.6)

The cylinder case uses the proved (9.1) on the punctured surface. The disc,
sphere, and grid consequences follow in the order of Section 9, pages 244–246.
The proofs of (9.1) and (9.2) are exposed by `Section9CoreProved`.
-/

@[expose] public section
namespace GraphMinor.GM07
open Set Topology GraphMinor.Surface
universe u
variable {S : Type u} [TopologicalSpace S]

/-! ## Proofs of (9.3), (9.4), (9.5), and (9.6) -/

/-- Graph Minors VII, (9.3) (pages 244–245):
"(9.3) *Let $\Sigma$ be a cylinder with cuffs $C_1$ and $C_2$. Let $(H, H^+, H^-)$ be a proper
digraph in $\Sigma$. Let $t = |V(H)| + |E(H)|$, and let $r = 84(t+2) 5^t v(\Sigma(0, 0, t+4),
2t+4)$.
Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$ such that
$V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Suppose that there are disjoint
$G$-normal $O$-arcs $F_1, F_2$ with the following properties:*
(i) *$F_1, F_2$ are not null-homotopic, and $C_1, F_2, F_1, C_2$ occur on $\Sigma$ in that order
(in the natural sense),*
(ii) *$|V(G) \cap F| \ge 2r$ for every $G$-normal $[0, 1]$-arc $F$ with
$F \cap F_1 \ne \emptyset \ne F \cap F_2$,*
(iii) *$k(F_1, F_2) \ge r$, and*
(iv) *$k(F_i, C_i) \ge |V(G) \cap C_i| \ (i = 1, 2)$.*
*Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_3_proof
    (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C₁ C₂ : Set S} (hcuffs : cuffs S = {C₁, C₂}) (hne : C₁ ≠ C₂)
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hOrder : CylinderOArcsInOrder C₁ F₂ F₁ C₂)
    (hInC₁ : ∀ x ∈ F₂, IsPointInsideSurroundingOArc C₁ F₁ x)
    (hbd₁ : Disjoint F₁ (bd S)) (hbd₂ : Disjoint F₂ (bd S))
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂)
    (hkC₁ : (G.G.V ∩ C₁).ncard ≤ maxDisjointPaths G.G F₁ C₁)
    (hkC₂ : (G.G.V ∩ C₂).ncard ≤ maxDisjointPaths G.G F₂ C₂) :
    IsBoundaryRootedMinor H G :=
  cylinderPunctureReduction
    S hS he C₁ C₂ hcuffs hne H G hH hG hbd_eq F₁ F₂ hF₁ hF₂
    hOrder hInC₁ hbd₁ hbd₂ hLine hk12 hkC₁ hkC₂

/-- Graph Minors VII, (9.4) (page 246):
"(9.4) *Let $\Sigma$ be a closed disc with cuff $C$ and let $(H, H^+, H^-)$ be a proper digraph in
$\Sigma$. Let $r$ be defined as in (9.3). Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$, such
that $V(G) \cap \mathrm{bd}(\Sigma) = V(H) \cap \mathrm{bd}(\Sigma)$. Suppose that there are
disjoint $G$-normal $O$-arcs $F_1, F_2$ of $\Sigma$, with $F_1$ inside $F_2$, such that*
(i) *$|V(G) \cap F| \ge 2r$ for every $G$-normal $[0, 1]$-arc $F$ with
$F \cap F_1 \ne \emptyset \ne F \cap F_2$,*
(ii) *$k(F_1, F_2) \ge r$, and*
(iii) *$k(F_1, C) \ge |V(G) \cap C|$.*
*Then $(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_4_proof
    (hS : IsSurface S) (hD : IsClosedDisc (univ : Set S))
    {C : Set S} (hcuffs : cuffs S = {C})
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    (hbd_eq : G.G.V ∩ bd S = H.G.V ∩ bd S)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    (hInside : IsInsideOArc F₁ F₂) (hbd₂ : Disjoint F₂ (bd S))
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂)
    (hkC : (G.G.V ∩ C).ncard ≤ maxDisjointPaths G.G F₁ C) :
    IsBoundaryRootedMinor H G := by
  obtain ⟨S', tS', -, C₁, C₂, H', G', F₁', F₂', hS', he', hcuffs', hne', hH', hG', hbd_eq',
      hF₁', hF₂', hOrder', hInC₁', hbd₁', hbd₂', hLine', hk12', hkC₁', hkC₂', himp⟩ :=
    discToCylinderReduction S hS hD C hcuffs H G hH hG hbd_eq F₁ F₂ hF₁ hF₂ hO₁ hO₂ hDisj hInside
      hbd₂ hLine hk12 hkC
  exact himp (@theorem_9_3_proof S' tS' hS' he' C₁ C₂ hcuffs' hne' H' G' hH' hG'
    hbd_eq' F₁' F₂' hF₁' hF₂' hOrder' hInC₁' hbd₁' hbd₂' hLine' hk12' hkC₁' hkC₂')

/-- Graph Minors VII, (9.5) (page 246):
"(9.5) *Let $\Sigma$ be a sphere, and let $(H, H^+, H^-)$ be a proper digraph in $\Sigma$. Let $r$
be defined as in (9.3). Let $(G, G^+, G^-)$ be a proper digraph in $\Sigma$. Suppose that there are
disjoint $G$-normal $O$-arcs $F_1, F_2$ of $\Sigma$ satisfying (i) and (ii) of (9.4). Then
$(H, H^+, H^-)$ is a boundary-rooted minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_5_proof
    [T1Space S] (hS : IsSurface S) (hSph : IsSphere S)
    (H G : SurfaceDigraph S) (hH : H.IsProper) (hG : G.IsProper)
    {F₁ F₂ : Set S} (hF₁ : G.G.IsNormal F₁) (hF₂ : G.G.IsNormal F₂)
    (hO₁ : IsOArc F₁) (hO₂ : IsOArc F₂) (hDisj : Disjoint F₁ F₂)
    (hLine : ∀ F : Set S, G.G.IsNormal F → IsLine F →
      (F ∩ F₁).Nonempty → (F ∩ F₂).Nonempty →
      2 * (rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard)) ≤ (G.G.V ∩ F).ncard)
    (hk12 : rCylinderBound H.G * 5 ^ (H.G.V.ncard + H.G.E.ncard) ≤ maxDisjointPaths G.G F₁ F₂) :
    IsBoundaryRootedMinor H G := by
  obtain ⟨S', tS', -, C, H', G', F₁', F₂', hS', hD', hcuffs', hH', hG', hbd_eq', hF₁', hF₂',
      hO₁', hO₂', hDisj', hInside', hbd₂', hLine', hk12', hkC', himp⟩ :=
    sphereToDiscReduction S hS hSph H G hH hG F₁ F₂ hF₁ hF₂ hO₁ hO₂ hDisj hLine hk12
  exact himp (@theorem_9_4_proof S' tS' hS' hD' C hcuffs' H' G' hH' hG'
    hbd_eq' F₁' F₂' hF₁' hF₂' hO₁' hO₂' hDisj' hInside' hbd₂' hLine' hk12' hkC')

/-- Graph Minors VII, (9.6) (page 246):
"(9.6) *Let $(G, G^+, G^-)$, $(H, H^+, H^-)$ be directed graphs in a sphere $\Sigma$, where $G$ is
isomorphic to an $N \times N$-grid. If $N$ is sufficiently large (bounded below by a function of
$H$) then $(H, H^+, H^-)$ is a minor of $(G, G^+, G^-)$.*" -/
theorem theorem_9_6_proof
    [T1Space S] (hS : IsSurface S) (hSph : IsSphere S)
    (H : SurfaceDigraph S) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (G : SurfaceDigraph S),
      N₀ ≤ N → IsGridDrawing G.G N → IsDigraphMinor H G := by
  have hbd : bd S = ∅ := by
    by_contra hbd_ne
    exact not_isSphere_of_bd_ne_empty hbd_ne hSph
  have hH : H.IsProper := isProper_of_bd_eq_empty hbd H.G
  obtain ⟨N₀, hN₀⟩ := sphereGridMinorReduction S hS H
  refine ⟨N₀, fun N G hN hG_grid => ⟨hbd, ?_⟩⟩
  have hG : G.IsProper := isProper_of_bd_eq_empty hbd G.G
  obtain ⟨F₁, F₂, hF₁, hF₂, hO₁, hO₂, hDisj, hLine, hk12⟩ := hN₀ N G hN hG_grid
  exact theorem_9_5_proof hS hSph H G hH hG hF₁ hF₂ hO₁ hO₂ hDisj hLine hk12

end GraphMinor.GM07
