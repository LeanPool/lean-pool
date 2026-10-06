/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupCutoffProduct
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Blowup Cutoff Spatial Bound

Cutoff bounds used to localize the rescaled endpoint sequence.
-/

public section

open CKN CKN.Foundation.Parabolic Set
noncomputable section
namespace ESS

/-- The fixed spatial cutoff has bounded first and second coordinate
derivatives. The bound depends on the chosen ball but not on the time cutoff. -/
theorem blowupBallCutoff_derivative_bounds (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3,
      (∀ i : Fin 3,
        |(fderiv ℝ (canonicalBallCutoff 0 R (R + 1)) x) (basisVec i)| ≤ C) ∧
      (∀ i : Fin 3,
        |(fderiv ℝ
          (fun y : Vec3 => (fderiv ℝ (canonicalBallCutoff 0 R (R + 1)) y)
            (basisVec i)) x) (basisVec i)| ≤ C) := by
  let ζ : Vec3 → ℝ := canonicalBallCutoff 0 R (R + 1)
  have hr : 0 ≤ R := hR.le
  have hrR : R < R + 1 := by linarith only []
  have hs : ContDiff ℝ (⊤ : ℕ∞) ζ := canonicalBallCutoff_smooth 0 hr hrR
  have hc : HasCompactSupport ζ := canonicalBallCutoff_hasCompactSupport hr hrR
  have hfirst (i : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Vec3, |(fderiv ℝ ζ x) (basisVec i)| ≤ C := by
    have hcont : Continuous (fun x : Vec3 => (fderiv ℝ ζ x) (basisVec i)) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcompact : HasCompactSupport
        (fun x : Vec3 => (fderiv ℝ ζ x) (basisVec i)) :=
      hc.fderiv_apply ℝ (basisVec i)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hx : |(fderiv ℝ ζ x) (basisVec i)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x
    exact hx.trans (le_max_left _ _)
  have hsecond (i : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Vec3,
        |(fderiv ℝ (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) x)
          (basisVec i)| ≤ C := by
    have hdiff : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) := by
      have h := hs.contDiff_fderiv_apply (m := (⊤ : ℕ∞))
        (n := (⊤ : ℕ∞)) (by simp)
      have hc : ContDiff ℝ (⊤ : ℕ∞)
          (fun y : Vec3 => (y, basisVec i)) := by fun_prop
      simpa only [Function.comp_def] using h.comp hc
    have hcont : Continuous
        (fun x : Vec3 =>
          (fderiv ℝ (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) x)
            (basisVec i)) :=
      (hdiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcompact : HasCompactSupport
        (fun x : Vec3 =>
          (fderiv ℝ (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) x)
            (basisVec i)) :=
      (hc.fderiv_apply ℝ (basisVec i)).fderiv_apply ℝ (basisVec i)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hx : |(fderiv ℝ (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) x)
        (basisVec i)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x
    exact hx.trans (le_max_left _ _)
  choose A hA hAbound using hfirst
  choose B hB hBbound using hsecond
  let C : ℝ := (∑ i : Fin 3, A i) + ∑ i : Fin 3, B i
  have hAnonneg : 0 ≤ ∑ i : Fin 3, A i := Finset.sum_nonneg fun i _ => hA i
  have hBnonneg : 0 ≤ ∑ i : Fin 3, B i := Finset.sum_nonneg fun i _ => hB i
  refine ⟨C, add_nonneg hAnonneg hBnonneg, fun x => ⟨fun i => ?_, fun i => ?_⟩⟩
  · exact (hAbound i x).trans ((Finset.single_le_sum
      (fun j _ => hA j) (Finset.mem_univ i)).trans (le_add_of_nonneg_right hBnonneg))
  · exact (hBbound i x).trans ((Finset.single_le_sum
      (fun j _ => hB j) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hAnonneg))

/-- Spatial coefficients of the energy test have one bound independent of
the upper time cutoff. Its time derivative has a uniform upper bound. -/
theorem blowupEnergyCutoff_coefficient_bounds (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a b : ℝ), b < 0 → ∀ z : Vec3 × ℝ,
      timePartialProd (blowupEnergyCutoff R a b) z ≤ 8 ∧
      (∀ i : Fin 3,
        |spatialPartialProd (blowupEnergyCutoff R a b) i z| ≤ C) ∧
      (∀ i : Fin 3,
        |spatialSecondPartialProd (blowupEnergyCutoff R a b) i i z| ≤ C) := by
  obtain ⟨C, hC, hbound⟩ := blowupBallCutoff_derivative_bounds R hR
  refine ⟨C, hC, fun a b hb z => ?_⟩
  let ζ : Vec3 → ℝ := canonicalBallCutoff 0 R (R + 1)
  let ψ₀ : Vec3 × ℝ → ℝ := fun w => ζ w.1
  let η : ℝ → ℝ := blowupTimeCutoff a b
  have hr : 0 ≤ R := hR.le
  have hrR : R < R + 1 := by linarith only []
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ₀ := by
    exact (canonicalBallCutoff_smooth 0 hr hrR).comp contDiff_fst
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η := blowupTimeCutoff_smooth a b
  have hηbound := blowupTimeCutoff_bounds a b z.2
  have hζbound : 0 ≤ ζ z.1 ∧ ζ z.1 ≤ 1 :=
    ⟨canonicalBallCutoff_nonneg 0 R (R + 1) z.1,
      canonicalBallCutoff_le_one 0 R (R + 1) z.1⟩
  have htime₀ : timePartialProd ψ₀ z = 0 := by
    unfold timePartialProd timePartial
    change (fderiv ℝ (fun _ : ℝ => ζ z.1) z.2) 1 = 0
    simp
  have htime : timePartialProd (blowupEnergyCutoff R a b) z =
      ζ z.1 * deriv η z.2 := by
    change timePartial (fun w => ψ₀ w * η w.2) z = _
    rw [timePartial_mul_time hs hηs z]
    simp only [timePartialProd] at htime₀
    rw [htime₀]
    ring
  have hfirst (i : Fin 3) :
      spatialPartialProd (blowupEnergyCutoff R a b) i z =
        (fderiv ℝ ζ z.1) (basisVec i) * η z.2 := by
    change spatialPartial (fun w => ψ₀ w * η w.2) i z = _
    rw [spatialPartial_mul_time hs i z]
    rfl
  have hsecond (i : Fin 3) :
      spatialSecondPartialProd (blowupEnergyCutoff R a b) i i z =
        (fderiv ℝ
          (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) z.1)
          (basisVec i) * η z.2 := by
    change spatialSecondPartial (fun w => ψ₀ w * η w.2) i i z = _
    rw [spatialSecondPartial_mul_time hs i i z]
    rfl
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · rw [htime]
    have hd := blowupTimeCutoff_deriv_le_eight a b z.2 hb
    calc
      ζ z.1 * deriv η z.2 ≤ ζ z.1 * 8 :=
        mul_le_mul_of_nonneg_left hd hζbound.1
      _ ≤ 8 := by nlinarith only [hζbound.2]
  · rw [hfirst i, abs_mul, abs_of_nonneg hηbound.1]
    calc
      |(fderiv ℝ ζ z.1) (basisVec i)| * η z.2 ≤ C * η z.2 :=
        mul_le_mul_of_nonneg_right ((hbound z.1).1 i) hηbound.1
      _ ≤ C := by nlinarith only [hηbound.2, hC]
  · rw [hsecond i, abs_mul, abs_of_nonneg hηbound.1]
    calc
      |(fderiv ℝ (fun y : Vec3 => (fderiv ℝ ζ y) (basisVec i)) z.1)
          (basisVec i)| * η z.2 ≤ C * η z.2 :=
        mul_le_mul_of_nonneg_right ((hbound z.1).2 i) hηbound.1
      _ ≤ C := by nlinarith only [hηbound.2, hC]

end ESS
