/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46Universe
public import LeanPool.GraphMinor.GM07.Section46Deficient
import LeanPool.GraphMinor.GM07.Section41
import LeanPool.GraphMinor.GM19.Section4c
import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# VII (4.6)

The proof of VII (4.6), pages 224 to 230. `exists_disc_reduction` gives the
disc and the set `Λ`, `Net.deficient_test_arc` gives the inequality of (4.1)
for each test arc, and `isGFeasible_of_arcs` closes the proof.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

/-- VII (4.6) for a surface in `Type`. -/
theorem theorem_4_6_type {S : Type} [TopologicalSpace S] [T1Space S] (hS : IsSurface S)
    [ConnectedSpace S] (hcuffs : 2 ≤ (cuffs S).ncard) (k : ℕ) (G H : Drawing S)
    (hG : G.IsProper) (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbdeq : G.V ∩ bd S = H.V ∩ bd S) : IsGFeasible G H := by
  obtain ⟨N, J, K, a, b, c, Gd, Hd, γ, sK, tK, l, hmin, hJ, hc, hmodel, hv, hPull, hγ, hcut, hKU,
    hl,
    hGdp, hFd, hbdD, hfe, hΛ⟩ := exists_disc_reduction hS hcuffs k G H hG hbd hi hii hiii hH hbdeq
  apply hfe
  refine isGFeasible_of_arcs N.isSurface_D N.isClosedDisc_D hGdp hFd hbdD ?_
  intro F s t C₁ C₂ hFn hF hEnds hC hne
  obtain ⟨hΛc, hΛd, hΛm, hΛv⟩ := hΛ s t C₁ C₂ hC hne _ rfl
  exact N.deficient_test_arc hS hcuffs hc hmodel hv hG hmin hJ hPull hbd hi hii hiii hγ sK tK hcut
    hKU l hl hFn hF hEnds hC hne hΛc hΛd hΛm hΛv

/-- Graph Minors VII, (4.6) (pages 224–230):
"(4.6) *Let $\Sigma$ be a connected surface with at least two cuffs and let $k \ge 0$ be an
integer. Let $G$ be a proper graph in $\Sigma$, with $|V(G) \cap bd(\Sigma)| \le 2k$, such that*
*(i) for every $G$-normal $I$-arc $B$ with $|V(G) \cap B| \le v(\Sigma, k)$ the ends of $B$ are in
the same cuff of $\Sigma$,*
*(ii) for every $G$-normal $O$-arc $B$ with $|V(G) \cap B| \le v(\Sigma, k)$ either $B$ is
null-homotopic, or for some cuff $C$, $B$ is null-homotopic in $\Sigma + \hat{C}$ and
$V(G) \cap C \subseteq B$, and*
*(iii) for every cuff $C$, $|V(G) \cap C| \ge 2$.*
*Let $H$ be a forest in $\Sigma$ with $V(G) \cap bd(\Sigma) = V(H) \cap bd(\Sigma)$. Then $H$ is
$G$-feasible.*" -/
theorem theorem_4_6_proof {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) [hConn : ConnectedSpace S]
    (hcuffs : 2 ≤ (cuffs S).ncard) (k : ℕ) (G H : Drawing S)
    (hG : G.IsProper) (hbd_card : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    (hH : IsSurfaceForest H) (hbd_eq : G.V ∩ bd S = H.V ∩ bd S) :
    IsGFeasible G H := by
  obtain ⟨a, b, c, -, ⟨e⟩, -⟩ := exists_model_vSurface_two_cuffs hS hcuffs k
  have hT : IsSurface (SurfaceModel a b c) := isSurface_of_homeo e hS
  have : T2Space (SurfaceModel a b c) := hT.2.1
  have : ConnectedSpace (SurfaceModel a b c) := e.surjective.connectedSpace e.continuous
  have hbdimg : ∀ X : Set S, (e '' X ∩ bd (SurfaceModel a b c)) = e '' (X ∩ bd S) := fun X => by
    rw [← GM19.image_bd e, image_inter e.injective]
  have hk := vSurface_eq_of_homeo e k
  refine isGFeasible_of_map e (theorem_4_6_type hT ?_ k _ _ ?_ ?_ ?_ ?_ (hiii_map e hiii)
    (IsSurfaceForest.map_homeo e hH) ?_)
  · rw [cuffs_image_homeo e, ncard_image_of_injective _ (image_injective.mpr e.injective)]
    exact hcuffs
  · rintro x ⟨hb, y, hy, rfl⟩
    rw [← GM19.image_bd e] at hb
    obtain ⟨z, hz, hzy⟩ := hb
    obtain rfl := e.injective hzy
    exact mem_image_of_mem e (hG ⟨hz, hy⟩)
  · change (e '' G.V ∩ _).ncard ≤ _
    rw [hbdimg, ncard_image_of_injective _ e.injective]
    exact hbd_card
  · rw [← hk]
    exact hi_map e hi
  · rw [← hk]
    exact hii_map e hii
  · change e '' G.V ∩ _ = e '' H.V ∩ _
    rw [hbdimg, hbdimg, hbd_eq]

end GraphMinor.GM07
