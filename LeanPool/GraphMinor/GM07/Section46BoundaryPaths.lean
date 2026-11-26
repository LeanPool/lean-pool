/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section43
import LeanPool.GraphMinor.GM07.Section46ChooseLift
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.Surface.Classification

/-!
# The paths and the choice of `l(z)` in VII (4.6)

We use the first path step already proved in `Section43`, with `v - 2k`
paths, then apply the boundary fibre count to their lifted first edges.
The resulting family retains its disjoint interiors for claim (3).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

/-- The first two paragraphs of the proof of VII (4.6), pages 224–225:
the paths from `z` to the other cuffs, and a common lifted first incidence
`l(z)` for at least `μ` of them. -/
theorem Net.exists_boundary_paths_and_lift_4_6 {S : Type} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S) (N : Net S)
    {a b c k : ℕ} (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hv : vSurface S k = vModel a b c k) {G J : Drawing S}
    (hG : G.IsProper) (hmin : N.IsMinimalFor G)
    (hJ : N.IsSeamGraphFor J) (hnorm : G.IsNormal J.U)
    (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ vSurface S k →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {C C' : Set S} (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C')
    {z : S} (hzV : z ∈ G.V) (hzC : z ∈ C) :
    ∃ (P : Fin (vModel a b c k - 2 * k) → Drawing S)
      (t : Fin (vModel a b c k - 2 * k) → S) (l : N.D),
      N.φ l = z ∧
      (∀ i, (P i).IsSubdrawing G ∧ t i ∈ G.V ∩ (bd S \ C) ∧
        (P i).IsPathBetween z (t i)) ∧
      (∀ i j, i ≠ j → Disjoint ((P i).V \ {z, t i}) ((P j).V \ {z, t j})) ∧
      ∃ I : Finset (Fin (vModel a b c k - 2 * k)), muModel a b c k ≤ I.card ∧
        ∀ i ∈ I, ∃ e ∈ (P i).E, l ∈ closure (N.φ ⁻¹' e) ∧
          ∀ x ∈ closure (N.φ ⁻¹' e), N.φ x = z → x = l := by
  have hzbd : z ∈ bd S := sUnion_cuffs (S := S) ▸ ⟨C, hC, hzC⟩
  let n := vModel a b c k - 2 * k
  have hn : 0 < n := by
    dsimp [n]
    unfold vModel
    rw [Nat.add_sub_cancel]
    exact Nat.mul_pos (by omega) (by omega)
  have hCV : (G.V ∩ C).ncard ≤ 2 * k := by
    have hsub : G.V ∩ C ⊆ G.V ∩ bd S := fun x hx =>
      ⟨hx.1, sUnion_cuffs (S := S) ▸ ⟨C, hC, hx.2⟩⟩
    exact (Set.ncard_le_ncard hsub
      (G.finite_V.subset inter_subset_left)).trans hbd
  have hm : n - 1 + (G.V ∩ C).ncard ≤ vSurface S k := by
    have h2k : 2 * k ≤ vModel a b c k := by
      unfold vModel
      exact Nat.le_add_left _ _
    dsimp [n]
    rw [hv]
    omega
  have hthree : ∀ C ∈ cuffs S, (G.V ∩ C).Nonempty := by
    intro D hD
    exact Set.nonempty_of_ncard_ne_zero (by have h := hiii D hD; omega)
  have hpaths := exists_paths_from_vertex hS hG hii hthree hC hC' hne hzV hzC hm
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at hpaths
  obtain ⟨P, s, t, hP, hd⟩ := hpaths
  have hP' : ∀ i, (P i).IsSubdrawing G ∧ t i ∈ G.V ∩ (bd S \ C) ∧
      (P i).IsPathBetween z (t i) := by
    intro i
    have hs := (hP i).2.1
    exact ⟨(hP i).1, (hP i).2.2.1, hs ▸ (hP i).2.2.2⟩
  obtain ⟨l, hl, I, hI, hIe⟩ := N.exists_common_lifted_first_edge hS hc hmodel
    hG hmin hJ hnorm hzbd P t (fun i =>
      ⟨(hP' i).1, (fun he => (hP' i).2.1.2.2 (he ▸ hzC)), (hP' i).2.2⟩)
  refine ⟨P, t, l, hl, hP', ?_, I, hI, hIe⟩
  intro i j hij
  simpa only [(hP i).2.1, (hP j).2.1] using hd i j hij

end GraphMinor.GM07
