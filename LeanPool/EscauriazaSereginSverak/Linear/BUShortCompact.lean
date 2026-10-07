/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTopSupport
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffFull

/-!
# Compact support of the short-time cutoff

For fixed spatial radius and lower-time parameter, the smooth cutoff stays
inside a compact subset of the shifted half-space Carleman domain.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The scalar cutoff is supported in a compact spatial ball, above the
normal transition height, and below a time level strictly smaller than one. -/
theorem buShortFullCutoff_compact_support
    {scale R ε : ℝ} (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε) :
    HasCompactSupport (buShortFullCutoff scale R hR ε) ∧
      tsupport (buShortFullCutoff scale R hR ε) ⊆
        {y : Vec3 | 1 < y 2} ×ˢ Ioo (1 / 2 : ℝ) 1 := by
  obtain ⟨σ, hσ, hσ1, hηzero⟩ :=
    buShortEtaExt_zero_near_one (R := R) hscale hscale1
  let H : Set Vec3 := {y | buShortYMinus scale ≤ y 2}
  let Kx : Set Vec3 :=
    euclideanClosedBall 0 (3 * (2 * R) / 4) ∩ H
  let K : Set (Vec3 × ℝ) := Kx ×ˢ Icc (1 / 2 + ε) σ
  have hHclosed : IsClosed H :=
    isClosed_le continuous_const (continuous_apply 2)
  have hKxcompact : IsCompact Kx :=
    (isCompact_euclideanClosedBall (0 : Vec3) (by positivity)).inter_right hHclosed
  have hKcompact : IsCompact K := hKxcompact.prod isCompact_Icc
  have hsupport : Function.support (buShortFullCutoff scale R hR ε) ⊆ K := by
    intro q hq
    have hspne : ucSpatialCutoff (2 * R) (by positivity) q.1 ≠ 0 := by
      intro hzero
      exact hq (by simp [buShortFullCutoff, hzero])
    have hηne : buShortEtaExt scale q ≠ 0 := by
      intro hzero
      exact hq (by simp [buShortFullCutoff, hzero])
    have htne : buShortTimeCutoff ε q.2 ≠ 0 := by
      intro hzero
      exact hq (by simp [buShortFullCutoff, hzero])
    have hspSupp : q.1 ∈ tsupport (ucSpatialCutoff (2 * R) (by positivity)) :=
      subset_tsupport _ (Function.mem_support.mpr hspne)
    have hspBall : q.1 ∈ vec3Ball 0 (2 * R) :=
      ucSpatialCutoff_tsupport (show 0 < 2 * R by positivity) hspSupp
    have hspOuter : q.1 ∈ euclideanBall 0 (3 * (2 * R) / 4) :=
      mollifiedBallCutoff_tsupport_subset_outer 0
        (show 0 < 2 * R by positivity) hspSupp
    have hspClosed : q.1 ∈ euclideanClosedBall 0 (3 * (2 * R) / 4) := by
      change euclideanSqDist q.1 0 ≤ (3 * (2 * R) / 4) ^ 2
      exact hspOuter.le
    have hheight : buShortYMinus scale ≤ q.1 2 := by
      by_contra hnot
      have hlow : q.1 2 ≤ buShortYMinus scale := le_of_not_ge hnot
      exact hηne (by
        unfold buShortEtaExt
        rw [buShortNormalCutoff_eq_zero hlow]
        ring)
    have htimeLower : 1 / 2 + ε ≤ q.2 := by
      by_contra hnot
      have hs : q.2 ≤ 1 / 2 + ε := le_of_not_ge hnot
      exact htne (by
        unfold buShortTimeCutoff
        apply ucInitialTimeCutoff_eq_zero hε
        linarith only [hs])
    have htimeUpper : q.2 ≤ σ := by
      by_contra hnot
      have hs : σ ≤ q.2 := le_of_not_ge hnot
      by_cases hs1 : q.2 < 1
      · exact hηne (hηzero q.1 hspBall q.2 hs hs1)
      · exact hηne (buShortEtaExt_zero_after_one hscale hscale1 q.1
          (le_of_not_gt hs1))
    exact ⟨⟨hspClosed, hheight⟩, ⟨htimeLower, htimeUpper⟩⟩
  have hcompact : HasCompactSupport (buShortFullCutoff scale R hR ε) :=
    HasCompactSupport.of_support_subset_isCompact hKcompact hsupport
  have hts : tsupport (buShortFullCutoff scale R hR ε) ⊆ K :=
    closure_minimal hsupport hKcompact.isClosed
  refine ⟨hcompact, ?_⟩
  intro q hq
  have hqK := hts hq
  have hheight : 1 < q.1 2 := by
    have hminus : 1 < buShortYMinus scale := by
      dsimp [buShortYMinus]
      have h : 0 < 3 / scale := by positivity
      linarith only [h]
    exact lt_of_lt_of_le hminus hqK.1.2
  have htime0 : (1 / 2 : ℝ) < q.2 := by
    linarith only [hqK.2.1, hε]
  exact ⟨hheight, htime0, lt_of_le_of_lt hqK.2.2 hσ1⟩

end ESS
