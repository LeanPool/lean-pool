/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedRealTrace
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortFixedCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics

/-!
# Trace cylinder containing the compact cutoff

The spatial support of the cutoff lies strictly inside the ball used in
the initial-time trace estimate.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The compact cutoff support lies in the open trace ball and shifted
time interval. -/
theorem buShortCutSupport_subset_traceCylinder
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    buCutSupportSet (buShortFullCutoff scale R hR ε) ⊆
      spaceTimeSet (buShortTraceBall R) (Ioo (1 / 2 : ℝ) 1) := by
  let χ := ucSpatialCutoff (2 * R) (by positivity)
  let κ := buShortFullCutoff scale R hR ε
  have hχclosed : IsClosed
      {q : Vec3 × ℝ | q.1 ∈ tsupport χ} :=
    (isClosed_tsupport χ).preimage continuous_fst
  have hsp : tsupport κ ⊆ {q : Vec3 × ℝ | q.1 ∈ tsupport χ} := by
    apply closure_minimal _ hχclosed
    intro q hq
    have hχne : χ q.1 ≠ 0 := by
      intro hzero
      exact hq (by simp [κ, buShortFullCutoff, χ, hzero])
    exact subset_tsupport χ (Function.mem_support.mpr hχne)
  intro z hz
  have hzχ := hsp hz
  have hball := ucSpatialCutoff_tsupport
    (show 0 < 2 * R by positivity) hzχ
  have htime := (buShortFullCutoff_compact_support
    hscale hscale1 hR hε).2 hz
  have hball' : z.1 ∈ euclideanBall 0 (2 * R) := by
    rwa [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
      (show 0 < 2 * R by positivity)]
  have hheight : (0 : ℝ) < z.1 2 :=
    lt_trans (by norm_num : (0 : ℝ) < 1) htime.1
  exact ⟨⟨hball', hheight⟩, htime.2⟩

end ESS
