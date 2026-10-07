/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortTraceStrip
public import LeanPool.EscauriazaSereginSverak.Linear.BUWeakSpatialRestriction
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineL2
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.BallTopology

/-!
# Rescaled data for the initial-time trace estimate

The unshifted parabolic rescaling has zero trace at time zero and retains
the specified weak time derivative and local quadratic bounds on every
bounded spatial ball in the half-space.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Bounded positive-half-space ball used to control the early cutoff
error. -/
@[expose] def buShortTraceBall (R : ℝ) : Set Vec3 :=
  euclideanBall 0 (2 * R) ∩ {y : Vec3 | 0 < y 2}

/-- The trace ball is open, has finite volume, and lies in the positive
half-space. -/
theorem buShortTraceBall_geometry
    {R : ℝ} (hR : 0 < R) :
    IsOpen (buShortTraceBall R) ∧
      volume (buShortTraceBall R) < ⊤ ∧
      buShortTraceBall R ⊆ {y : Vec3 | 0 < y 2} := by
  have hopen : IsOpen (buShortTraceBall R) :=
    (isOpen_euclideanBall 0 (2 * R)).inter
      (isOpen_lt continuous_const (continuous_apply 2))
  have hclosed : IsCompact (euclideanClosedBall 0 (2 * R)) :=
    isCompact_euclideanClosedBall (0 : Vec3) (by positivity)
  have hsub : buShortTraceBall R ⊆ euclideanClosedBall 0 (2 * R) := by
    intro y hy
    change euclideanSqDist y 0 ≤ (2 * R) ^ 2
    exact (show euclideanSqDist y 0 < (2 * R) ^ 2 from hy.1).le
  have hfinite : volume (buShortTraceBall R) < ⊤ :=
    (measure_mono hsub).trans_lt hclosed.isBounded.measure_lt_top
  exact ⟨hopen, hfinite, fun y hy => hy.2⟩

/-- The full trace cylinder over a bounded ball is bounded in the
parabolic metric. -/
theorem buShortTraceBall_cylinder_bounded
    {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded
      (spaceTimeSet (buShortTraceBall R) (Ioo (0 : ℝ) 1)) := by
  let C : Set ParabolicPoint := parabolicHomeomorph ⁻¹'
    (euclideanClosedBall 0 (2 * R) ×ˢ Icc (0 : ℝ) 1)
  have hC : IsCompact C := by
    dsimp [C]
    apply parabolicHomeomorph.isCompact_preimage.mpr
    exact (isCompact_euclideanClosedBall (0 : Vec3)
      (by positivity)).prod isCompact_Icc
  apply hC.isBounded.subset
  intro z hz
  rcases hz with ⟨hy, ht⟩
  have hclosed : z.1 ∈ euclideanClosedBall 0 (2 * R) := by
    change euclideanSqDist z.1 0 ≤ (2 * R) ^ 2
    exact (show euclideanSqDist z.1 0 < (2 * R) ^ 2 from hy.1).le
  exact ⟨hclosed, ⟨ht.1.le, ht.2.le⟩⟩

/-- The unshifted rescaling satisfies all data required by the
small-time trace estimate on the bounded half-space ball. -/
theorem bu_short_trace_rescaled_data
    (scale R : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1))
    (hinit : ∀ x : Vec3, 0 < x 2 → w (x, 0) = 0)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let B := buShortTraceBall R
    let v := buAffineField 0 scale w
    let Dv := buAffineDw 0 scale Dw
    let D2v := buAffineD2w 0 scale D2w
    let Dtv := buAffineDtw 0 scale Dtw
    ContinuousOn v (spaceTimeSet B (Ico 0 1)) ∧
      (∀ x ∈ B, v (x, 0) = 0) ∧
      HasSpaceTimeWeakDerivs B (Ioo 0 1) v Dv D2v Dtv ∧
      MemLp Dtv 2
        ((volume.restrict B).prod (volume.restrict (Ioo 0 1))) := by
  let B := buShortTraceBall R
  let v := buAffineField 0 scale w
  let Dv := buAffineDw 0 scale Dw
  let D2v := buAffineD2w 0 scale D2w
  let Dtv := buAffineDtw 0 scale Dtw
  let K := spaceTimeSet B (Ioo (0 : ℝ) 1)
  have hupper : (0 : ℝ) + scale ^ 2 ≤ 1 := by
    have hs : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
    linarith only [hs]
  have hBsub := (buShortTraceBall_geometry hR).2.2
  have hKsub : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
    intro z hz
    exact ⟨hBsub hz.1, hz.2⟩
  have hKb : Bornology.IsBounded K := buShortTraceBall_cylinder_bounded hR
  have hweakv := bu_affine_weak_derivatives 0 scale (by norm_num)
    hscale hupper w Dw D2w Dtw hweak
  have hcontv := buAffineField_continuousOn 0 scale (by norm_num)
    hscale hupper w hcont
  have hcontB : ContinuousOn v (spaceTimeSet B (Ico 0 1)) := by
    apply hcontv.mono
    intro z hz
    exact ⟨hBsub hz.1, hz.2⟩
  have hzero : ∀ x ∈ B, v (x, 0) = 0 := by
    intro x hx
    exact buAffineField_initial_zero 0 scale w hinit hscale x (hBsub hx)
  have hweakB : HasSpaceTimeWeakDerivs B (Ioo 0 1)
      v Dv D2v Dtv :=
    bu_weak_restrict_space hBsub v Dv D2v Dtv hweakv
  have hsum := bu_affine_derivative_l2 0 scale (by norm_num)
    hscale hupper w Dw D2w Dtw hweak hL2 K hKsub hKb
  have hDtfin : (∫⁻ z in K, ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt hsum
    exact le_add_of_nonneg_left (by positivity)
  have hDtmeas : AEStronglyMeasurable Dtv (volume.restrict K) :=
    (hweakv.2.2.2.1.mono_set hKsub).aestronglyMeasurable
  have hDtLp : MemLp Dtv 2 (volume.restrict K) := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hDtmeas).2
    simpa using hDtfin
  have hmeasure : (volume : Measure ParabolicPoint).restrict K =
      ((volume.restrict B).prod (volume.restrict (Ioo 0 1))) := by
    dsimp [K, spaceTimeSet]
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    exact (Measure.prod_restrict B (Ioo (0 : ℝ) 1)).symm
  rw [hmeasure] at hDtLp
  exact ⟨hcontB, hzero, hweakB, hDtLp⟩

end ESS
