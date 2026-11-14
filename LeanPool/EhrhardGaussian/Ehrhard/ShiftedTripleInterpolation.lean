/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.ShiftedMatrixCondition
public import LeanPool.EhrhardGaussian.Ehrhard.TripleOUPullback
public import LeanPool.EhrhardGaussian.Ehrhard.RestrictedTimeInterpolation
public import LeanPool.EhrhardGaussian.Ehrhard.CompactQuantileBounds

/-! # Applying restricted interpolation to the correlated triple -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped Matrix BigOperators ContDiff

namespace EhrhardGaussian.Ehrhard

/-- A strict quantile gap gives a uniform upper bound along the shifted triple interpolation. -/
theorem shifted_triple_interpolation {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Measurable (f i))
    {lo hi p q ρ σ ε η G H M : ℝ} (hlo : 0 < lo) (hhi : hi < 1)
    (hbound : ∀ i z, f i z ∈ Icc lo hi) (hp : 0 < p) (hq : 0 < q) (hsum : p + q = 1)
    (hρ : |ρ| < 1) (hσ : 0 < σ) (hvar : σ ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q * ρ)
    (hε : 0 < ε) (hη : 0 < η)
    (hregular : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (tripleLift f p q ρ i))
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hgrad : ∀ i y, ‖fderiv ℝ (tripleLift f p q ρ i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (tripleLift f p q ρ i) j) l y|
      ≤ H)
    (hgen : ∀ i y, |ouGenerator (tripleLift f p q ρ i) y| ≤ M)
    (hgap : ∀ y, quantileLinear (tripleTheta p q σ) (ouFamily (tripleLift f p q ρ) (ε, y)) ≤ -η) :
    ∃ R : ℝ, 0 < R ∧ ∀ T : ℝ, ε ≤ T → ∀ x : Fin 2 → ℝ,
      interpolationFunctional (tripleTheta p q σ) R ε (T, ouFamily (tripleLift f p q ρ) (T, x)) ≤
        gaussianCDF (-(R * Real.sqrt (1 - Real.exp (-ε))) * η) := by
  let θ := tripleTheta p q σ
  let F := tripleLift f p q ρ
  let d := Real.sqrt (1 - Real.exp (-ε))
  let κ := d * η / 2
  have hd : 0 < d := Real.sqrt_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only
    [hε])))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hρsq : ρ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one ρ).mpr hρ.le
  obtain ⟨L, _, hL⟩ := exists_quantile_bound (k := 3) hlo hhi
  obtain ⟨R, hR, hconditions⟩ := exists_shifted_interpolation_conditions hp hq hsum hρ hσ hvar hκ hε
    L
  let a := gaussianCDF (-R * κ)
  let b := gaussianCDF (-(R * d) * η)
  have hba : b < a := by
    apply strictMono_gaussianCDF
    dsimp only [κ]
    nlinarith only [mul_pos (mul_pos hR hd) hη]
  have hf₁ := fun i => hasPolynomiallyBoundedCoordinateDerivatives_of_second
    (hasPolynomiallyBoundedSecond_of_third (hregular i))
  have hinput (i) (y) : F i y ∈ Icc lo hi := hbound i _
  have hrange (t) (y) := ouFamily_mem_Icc hf₁ hinput y t
  have hprob (t) (y) : ouFamily F (t, y) ∈ probabilityBox :=
    fun i => ⟨hlo.trans_le (hrange t y i).1, (hrange t y i).2.trans_lt hhi⟩
  have hbound₀ (i z) : f i z ∈ Icc (0 : ℝ) 1 :=
    ⟨hlo.le.trans (hbound i z).1, (hbound i z).2.trans hhi.le⟩
  have hstart (y) : interpolationFunctional θ R ε (ε, ouFamily F (ε, y)) ≤ b := by
    apply strictMono_gaussianCDF.monotone
    change interpolationScale R ε (ε - ε) * quantileLinear θ (ouFamily F (ε, y)) ≤ -(R * d) * η
    rw [sub_self]
    have hs : interpolationScale R ε 0 = R * d := by simp [interpolationScale, d]
    rw [hs]
    have h := mul_le_mul_of_nonneg_left (hgap y) (mul_nonneg hR.le hd.le)
    nlinarith only [h]
  refine ⟨R, hR, ?_⟩
  intro T hT x
  have hJ (s) (hs : s ∈ Icc (3 * ε / 4) T) (z : Fin 3 → ℝ) (hz : ∀ i, z i ∈ Icc lo hi) :
      ContDiffAt ℝ 2 (interpolationFunctional θ R ε) (s, z) := by
    apply (contDiffAt_interpolationFunctional θ R ε (by linarith only [hs.1, hε])
      (fun i => ⟨hlo.trans_le (hz i).1, (hz i).2.trans_lt hhi⟩)).of_le
    simp
  have hresult := restricted_time_interpolation hregular hG hH hM hinput hgrad hsecond hgen
    (l := 3 * ε / 4) (c := ε) (T := T)
    (by linarith only [hε]) (by linarith only [hε]) hT hJ
    (tripleGaussianFactor p q ρ) (tripleScalarGradient f p q ρ σ)
    (fun _ z => interpolationWeightMatrix (tripleInterpolationWeights p q σ) (tripleVariances σ)
      (fun i => gaussianPDFReal 0 1 (gaussianCDFChart.symm (z i))))
    (fun s => Real.exp (2 * s) - 1)
    (fun s hs => sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith only [hs.1, hε])))
    (fun s hs y i j => tripleLift_ou_gradient_shape hf hbound₀ hρsq hσ hvar (hε.trans_le hs.1) y i
      j)
    (fun s hs y => triple_ou_gradient_condition hf hlo hhi hbound hp.le hq.le hsum hρsq hσ hvar
      (hε.trans_le hs.1) y) hba
    (fun s hs y hsub => by
      rw [tripleFactor_gram p q hρsq]
      exact hconditions s hs.1 _ (hprob s y) (hL _ (hrange s y)) hsub) hstart
  exact hresult.1 T ⟨hT, le_rfl⟩ x

end EhrhardGaussian.Ehrhard

end
