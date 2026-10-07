/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCompact
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeakProductBasis
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffOperator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Quadratic data for smooth compact cutoffs

On the compact support of a smooth scalar cutoff, bounded multipliers
preserve square integrability of the field and its specified derivatives.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The parabolic preimage of a scalar cutoff's product-space support. -/
@[expose] def buCutSupportSet (κ : Vec3 × ℝ → ℝ) : Set ParabolicPoint :=
  parabolicHomeomorph ⁻¹' tsupport κ

private theorem bu_memLp_mul_bounded_support
    {K : Set ParabolicPoint} (hKmeas : MeasurableSet K)
    {f g : ParabolicPoint → ℝ}
    (hf : MemLp f 2 (volume.restrict K))
    (hg : Continuous g)
    (C : ℝ) (hbound : ∀ z, |g z| ≤ C)
    (hzero : ∀ z ∉ K, g z = 0) :
    MemLp (fun z => g z * f z) 2 volume := by
  have hExt : MemLp (K.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hKmeas).2 hf
  have hprod : MemLp (fun z => g z * K.indicator f z) 2 volume := by
    apply MemLp.of_le_mul (c := C) hExt
      (hg.aestronglyMeasurable.mul hExt.aestronglyMeasurable)
    filter_upwards [] with z
    change |g z * K.indicator f z| ≤ C * |K.indicator f z|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound z) (abs_nonneg _)
  convert hprod using 1
  funext z
  by_cases hz : z ∈ K
  · simp only [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz, hzero z hz]

/-- Smooth compact scalar factors preserve quadratic data in all specified
weak derivative fields. -/
theorem buCut_memLp_data
    (κ : Vec3 × ℝ → ℝ)
    (hκsmooth : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκcompact : HasCompactSupport κ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (hv : MemLp v 2 (volume.restrict (buCutSupportSet κ)))
    (hDv : MemLp Dv 2 (volume.restrict (buCutSupportSet κ)))
    (hD2v : MemLp D2v 2 (volume.restrict (buCutSupportSet κ)))
    (hDtv : MemLp Dtv 2 (volume.restrict (buCutSupportSet κ))) :
    MemLp (buCutField κ v) 2 volume ∧
      MemLp (buCutDw κ v Dv) 2 volume ∧
      MemLp (buCutD2 κ v Dv D2v) 2 volume ∧
      MemLp (buCutDt κ v Dtv) 2 volume := by
  let K := buCutSupportSet κ
  have hKmeas : MeasurableSet K := by
    dsimp [K, buCutSupportSet]
    exact hκcompact.isCompact.isClosed.measurableSet.preimage
      parabolicHomeomorph.measurable
  have hκc : Continuous (buCutScalar κ) :=
    hκsmooth.continuous.comp parabolicHomeomorph.continuous
  obtain ⟨C₀, hC₀⟩ := hκsmooth.continuous.bounded_above_of_compact_support hκcompact
  have hb₀ (z : ParabolicPoint) : |buCutScalar κ z| ≤ C₀ := by
    simpa only [Real.norm_eq_abs, buCutScalar] using hC₀ (parabolicHomeomorph z)
  have hz₀ (z : ParabolicPoint) (hz : z ∉ K) : buCutScalar κ z = 0 := by
    exact image_eq_zero_of_notMem_tsupport
      (f := κ) (show parabolicHomeomorph z ∉ tsupport κ from hz)
  have hspc (j : Fin 3) : Continuous
      (fun z : ParabolicPoint => spatialPartial (buCutScalar κ) j z) := by
    have h := (spatialPartial_contDiff hκsmooth j).continuous.comp
      parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  have hspb (j : Fin 3) : ∃ C : ℝ,
      ∀ z : ParabolicPoint,
        |spatialPartial (buCutScalar κ) j z| ≤ C := by
    obtain ⟨C, hC⟩ :=
      (spatialPartial_contDiff hκsmooth j).continuous.bounded_above_of_compact_support
        (hasCompactSupport_spatialPartial hκcompact j)
    refine ⟨C, ?_⟩
    intro z
    convert hC (parabolicHomeomorph z) using 1
    · rcases z with ⟨y, s⟩
      rfl
  have hspz (j : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      spatialPartial (buCutScalar κ) j z = 0 := by
    have hnot : parabolicHomeomorph z ∉ tsupport κ := hz
    have h := CKN.spatialPartial_eq_zero_off_tsupport hnot j
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  have hsecondc (j k : Fin 3) : Continuous
      (fun z : ParabolicPoint => spatialSecondPartial (buCutScalar κ) j k z) := by
    have h := (spatialPartial_contDiff
      (spatialPartial_contDiff hκsmooth j) k).continuous.comp
        parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  have hsecondb (j k : Fin 3) : ∃ C : ℝ,
      ∀ z : ParabolicPoint,
        |spatialSecondPartial (buCutScalar κ) j k z| ≤ C := by
    obtain ⟨C, hC⟩ :=
      (spatialPartial_contDiff
        (spatialPartial_contDiff hκsmooth j) k).continuous.bounded_above_of_compact_support
        (hasCompactSupport_spatialPartial
          (hasCompactSupport_spatialPartial hκcompact j) k)
    refine ⟨C, ?_⟩
    intro z
    convert hC (parabolicHomeomorph z) using 1
    · rcases z with ⟨y, s⟩
      rfl
  have hsecondz (j k : Fin 3) (z : ParabolicPoint) (hz : z ∉ K) :
      spatialSecondPartial (buCutScalar κ) j k z = 0 := by
    have hnot : parabolicHomeomorph z ∉ tsupport κ := hz
    have h := CKN.spatialSecondPartial_eq_zero_off_tsupport hnot j k
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  have htimec : Continuous (fun z : ParabolicPoint =>
      timePartial (buCutScalar κ) z) := by
    have h := (contDiff_timePartial hκsmooth).continuous.comp
      parabolicHomeomorph.continuous
    convert h using 1
    funext z
    rcases z with ⟨y, s⟩
    rfl
  have htimeb : ∃ C : ℝ, ∀ z : ParabolicPoint,
      |timePartial (buCutScalar κ) z| ≤ C := by
    obtain ⟨C, hC⟩ :=
      (contDiff_timePartial hκsmooth).continuous.bounded_above_of_compact_support
        (hasCompactSupport_timePartial hκcompact)
    refine ⟨C, ?_⟩
    intro z
    convert hC (parabolicHomeomorph z) using 1
    · rcases z with ⟨y, s⟩
      rfl
  have htimez (z : ParabolicPoint) (hz : z ∉ K) :
      timePartial (buCutScalar κ) z = 0 := by
    have hnot : parabolicHomeomorph z ∉ tsupport κ := hz
    have h := CKN.timePartial_eq_zero_off_tsupport hnot
    convert h using 1
    rcases z with ⟨y, s⟩
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply MemLp.of_eval
    intro i
    have hmul := bu_memLp_mul_bounded_support hKmeas
      (hv.eval i) hκc C₀ hb₀ hz₀
    convert hmul using 1
    funext z
    rfl
  · apply MemLp.of_eval
    intro i
    apply MemLp.of_eval
    intro j
    obtain ⟨Cj, hCj⟩ := hspb j
    have hA := bu_memLp_mul_bounded_support hKmeas
      ((hDv.eval i).eval j) hκc C₀ hb₀ hz₀
    have hB := bu_memLp_mul_bounded_support hKmeas
      (hv.eval i) (hspc j) Cj hCj (hspz j)
    convert hA.add hB using 1
    funext z
    dsimp [buCutDw]
    ring
  · apply MemLp.of_eval
    intro i
    apply MemLp.of_eval
    intro j
    apply MemLp.of_eval
    intro k
    obtain ⟨Ck, hCk⟩ := hspb k
    obtain ⟨Cj, hCj⟩ := hspb j
    obtain ⟨Cjk, hCjk⟩ := hsecondb j k
    have hA := bu_memLp_mul_bounded_support hKmeas
      (((hD2v.eval i).eval j).eval k) hκc C₀ hb₀ hz₀
    have hB := bu_memLp_mul_bounded_support hKmeas
      ((hDv.eval i).eval j) (hspc k) Ck hCk (hspz k)
    have hC := bu_memLp_mul_bounded_support hKmeas
      ((hDv.eval i).eval k) (hspc j) Cj hCj (hspz j)
    have hD := bu_memLp_mul_bounded_support hKmeas
      (hv.eval i) (hsecondc j k) Cjk hCjk (hsecondz j k)
    convert ((hA.add hB).add hC).add hD using 1
    funext z
    dsimp [buCutD2]
    ring
  · apply MemLp.of_eval
    intro i
    obtain ⟨Ct, hCt⟩ := htimeb
    have hA := bu_memLp_mul_bounded_support hKmeas
      (hDtv.eval i) hκc C₀ hb₀ hz₀
    have hB := bu_memLp_mul_bounded_support hKmeas
      (hv.eval i) htimec Ct hCt htimez
    convert hA.add hB using 1
    funext z
    dsimp [buCutDt]
    ring

end ESS
