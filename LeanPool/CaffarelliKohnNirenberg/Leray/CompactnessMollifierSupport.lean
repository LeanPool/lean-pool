/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMollifierTest
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceDistributionKernel

/-!
# Compactness Mollifier Support

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Set Topology
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- On a compact subset of an open spatial neighborhood, all sufficiently
small reflected mollifiers are supported inside that neighborhood. -/
theorem eventually_reflected_mollifier_supported_in_open
    {K W : Set Vec3} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ K, ∀ y : Vec3,
      CKN.mollifier (d := 3) (CKN.sliceRadius m)
        (CKN.sliceRadius_pos m) (x - y) ≠ 0 → y ∈ W := by
  obtain ⟨W', δ, hδ, hW', hKW', hW'c, hW'cW, hballs⟩ :=
    CKN.exists_open_between_of_isCompact hK hW hKW
  have hsmall : ∀ᶠ m : ℕ in atTop, CKN.sliceRadius m ≤ δ := by
    have hlt : ∀ᶠ m : ℕ in atTop, CKN.sliceRadius m < δ :=
      CKN.tendsto_sliceRadius_atTop.eventually
        (isOpen_Iio.mem_nhds hδ)
    exact hlt.mono (fun m hm => hm.le)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨m₀, fun m hmm x hx y hκ => ?_⟩
  have hyBall : y ∈ Metric.closedBall x (CKN.sliceRadius m) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra hnot
    rw [norm_sub_rev] at hnot
    have hlt : CKN.sliceRadius m < ‖x - y‖ := lt_of_not_ge hnot
    exact hκ (CKN.mollifier_eq_zero_of_lt_norm
      (CKN.sliceRadius_pos m) hlt)
  exact hW'cW (subset_closure
    (hballs x hx (CKN.sliceRadius m) (CKN.sliceRadius_pos m)
      (hm₀ m hmm) hyBall))

end CKN.Leray
