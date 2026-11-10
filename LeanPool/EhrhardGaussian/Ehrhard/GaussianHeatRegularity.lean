/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott N. Armstrong
-/

/-
Ported from ASDExplicitGamma-dev/Gaussian/ConcentrationSemigroup.lean,
commit 2c9673f0bcca8062b441989bdc56f87b38715bb8.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianHeatCenter
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Second derivatives and polynomial closure for Gaussian heat flow -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- A `C³` function whose coordinate derivatives through order three have polynomial growth. -/
def HasPolynomiallyBoundedThirdCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 3 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d) ∧
    (∀ i j x, |coordinateDerivative (coordinateDerivative F i) j x| ≤
      C * (1 + ‖x‖) ^ d) ∧
    ∀ i j k x,
      |coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x| ≤
        C * (1 + ‖x‖) ^ d

/-- Polynomial bounds through third coordinate derivatives imply the corresponding bounds through
second derivatives. -/
theorem hasPolynomiallyBoundedSecond_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

/-- A coordinate derivative of a three-times continuously differentiable function is twice
continuously differentiable. -/
theorem contDiff_coordinateDerivative_of_three {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (i : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hpair : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

/-- A coordinate derivative of a twice continuously differentiable function is continuously
differentiable. -/
theorem contDiff_coordinateDerivative_of_two {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (i : Fin n) :
    ContDiff ℝ 1 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

/-- Polynomial bounds through second coordinate derivatives imply the corresponding first-derivative
bounds. -/
theorem hasPolynomiallyBoundedCoordinateDerivatives_of_second {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) :
    HasPolynomiallyBoundedCoordinateDerivatives F := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  refine ⟨hF.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2), 2 * C, by positivity, d,
    ?_, ?_⟩
  · intro x
    calc
      |F x| ≤ C * (1 + ‖x‖) ^ d := hzero x
      _ ≤ 2 * C * (1 + ‖x‖) ^ d := by
        have hn : 0 ≤ C * (1 + ‖x‖) ^ d := by positivity
        nlinarith
  · intro i x
    calc
      |F x| + |coordinateDerivative F i x| ≤
          C * (1 + ‖x‖) ^ d + C * (1 + ‖x‖) ^ d := add_le_add (hzero x) (hone i x)
      _ = 2 * C * (1 + ‖x‖) ^ d := by ring

/-- Translating the argument translates the point at which the Fréchet derivative is evaluated. -/
theorem fderiv_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) :
    fderiv ℝ (fun y => F (x + y)) z = fderiv ℝ F (x + z) := by
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := by
    exact (hasFDerivAt_const_add_iff x).2 (hasFDerivAt_id z)
  have hcomp := (hF.differentiable_one (x + z)).hasFDerivAt.comp z hinner
  simpa [Function.comp_def] using hcomp.fderiv

/-- Coordinate differentiation commutes with translation of the argument. -/
theorem coordinateDerivative_translate {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x z : Fin n → ℝ) (i : Fin n) :
    coordinateDerivative (fun y => F (x + y)) i z =
      coordinateDerivative F i (x + z) := by
  rw [coordinateDerivative, fderiv_translate hF x z, coordinateDerivative]

/-- Translation preserves polynomial bounds through second coordinate derivatives. -/
theorem hasPolynomiallyBoundedSecond_of_translate {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F)
    (x : Fin n → ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun z => F (x + z)) := by
  rcases hF.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  let B : ℝ := 1 + ‖x‖
  let C' : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hnorm (z : Fin n → ℝ) : 1 + ‖x + z‖ ≤ B * (1 + ‖z‖) := by
    have htriangle := norm_add_le x z
    have hprod : 1 + ‖x‖ + ‖z‖ ≤ (1 + ‖x‖) * (1 + ‖z‖) := by
      nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg z)]
    dsimp [B]
    linarith
  have hcont : ContDiff ℝ 2 (fun z : Fin n → ℝ => F (x + z)) := by
    exact hF.1.comp (contDiff_const.add contDiff_id)
  have hfirst (i : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (fun y => F (x + y)) i z =
        coordinateDerivative F i (x + z) :=
    coordinateDerivative_translate (hF.1.of_le (by norm_num)) x z i
  have hsecond (i j : Fin n) (z : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative (fun y => F (x + y)) i) j z =
        coordinateDerivative (coordinateDerivative F i) j (x + z) := by
    have heq : coordinateDerivative (fun y => F (x + y)) i =
        fun y => coordinateDerivative F i (x + y) := by
      funext y
      exact hfirst i y
    rw [heq]
    exact coordinateDerivative_translate
      (contDiff_coordinateDerivative_of_two hF.1 i) x z j
  refine ⟨hcont, C', hC', d, ?_, ?_, ?_⟩
  · intro z
    calc
      |F (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hzero _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i z
    rw [hfirst]
    calc
      |coordinateDerivative F i (x + z)| ≤ C * (1 + ‖x + z‖) ^ d := hone i _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring
  · intro i j z
    rw [hsecond]
    calc
      |coordinateDerivative (coordinateDerivative F i) j (x + z)| ≤
          C * (1 + ‖x + z‖) ^ d := htwo i j _
      _ ≤ C * (B * (1 + ‖z‖)) ^ d := by gcongr; exact hnorm z
      _ = C' * (1 + ‖z‖) ^ d := by dsimp [C']; rw [mul_pow]; ring


/-- Polynomially bounded second coordinate derivatives give continuously differentiable heat
averages. -/
theorem contDiff_one_heatAverage_of_second {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F) (t : ℝ) :
    ContDiff ℝ 1 (fun x : Fin n → ℝ => heatAverage F x t) := by
  let c : ℝ := Real.sqrt t
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x t
  let D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ := fun x =>
    ∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianMeasure n)
  have hF₁ : HasPolynomiallyBoundedCoordinateDerivatives F :=
    hasPolynomiallyBoundedCoordinateDerivatives_of_second hF₂
  have hcenter (x : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hF₁ x c
  have hDderiv (x : Fin n → ℝ) : HasFDerivAt U (D x) x := by
    have h := hcenter x
    simpa [U, D, heatAverage, c] using h.2.1
  have hDcont : Continuous D :=
    continuous_iff_continuousAt.mpr fun x => (hcenter x).2.2
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨D, hDcont, hDderiv⟩

/-- A directional derivative inherits polynomially bounded second derivatives from third derivative
bounds. -/
theorem hasPolynomiallyBoundedSecond_of_directionalDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    (v : Fin n → ℝ) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (fun x => fderiv ℝ F x v) := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let D : (Fin n → ℝ) → ℝ := fun x => fderiv ℝ F x v
  let C' : ℝ := (Fintype.card (Fin n) : ℝ) * ‖v‖ * C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hDcont : ContDiff ℝ 2 D := by
    have h := hcont.contDiff_fderiv_apply (m := 2)
      (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have hpair : ContDiff ℝ 2 (fun x : Fin n → ℝ => (x, v)) :=
      contDiff_id.prodMk contDiff_const
    convert h.comp hpair using 1
    · ext x
      rfl
  have hDrepr : D = fun x => ∑ i, v i * coordinateDerivative F i x := by
    funext x
    exact concentration_fderiv_apply_eq_sum x v
  have hfirst (j : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative D j x =
        ∑ i, v i * coordinateDerivative (coordinateDerivative F i) j x := by
    rw [coordinateDerivative, hDrepr]
    rw [fderiv_fun_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hdiffi : DifferentiableAt ℝ (coordinateDerivative F i) x :=
        (contDiff_coordinateDerivative_of_two
          (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) i).differentiable_one x
      have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single j (1 : ℝ)))
        (fderiv_const_mul hdiffi (v i))
      simpa [coordinateDerivative, smul_eq_mul] using h
    · intro i hi
      exact ((contDiff_coordinateDerivative_of_three hcont i).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x |>.const_mul (v i)
  have hsecond (j k : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative (coordinateDerivative D j) k x =
        ∑ i, v i *
          coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x := by
    have hfun : coordinateDerivative D j = fun y =>
        ∑ i, v i * coordinateDerivative (coordinateDerivative F i) j y := by
      funext y
      exact hfirst j y
    rw [hfun, coordinateDerivative, fderiv_fun_sum]
    · simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hdiffi : DifferentiableAt ℝ
          (coordinateDerivative (coordinateDerivative F i) j) x :=
        (contDiff_coordinateDerivative_of_two
          (contDiff_coordinateDerivative_of_three hcont i) j).differentiable_one x
      have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single k (1 : ℝ)))
        (fderiv_const_mul hdiffi (v i))
      simpa [coordinateDerivative, smul_eq_mul] using h
    · intro i hi
      exact ((contDiff_coordinateDerivative_of_two
        (contDiff_coordinateDerivative_of_three hcont i) j).differentiable_one x).const_mul
          (v i)
  have habsSum (x : Fin n → ℝ) {A : Fin n → ℝ}
      (hA : ∀ i, |A i| ≤ C * (1 + ‖x‖) ^ d) :
      |∑ i, v i * A i| ≤ C' * (1 + ‖x‖) ^ d := by
    calc
      |∑ i, v i * A i| ≤ ∑ i, |v i * A i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ * (C * (1 + ‖x‖) ^ d) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        have hvi : |v i| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
        calc
          |v i| * |A i| ≤ |v i| * (C * (1 + ‖x‖) ^ d) :=
            mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _)
          _ ≤ ‖v‖ * (C * (1 + ‖x‖) ^ d) := by gcongr
      _ = C' * (1 + ‖x‖) ^ d := by
        simp [C', Finset.sum_const, mul_assoc]
  refine ⟨hDcont, ?_⟩
  refine ⟨C', hC', d, ?_, ?_, ?_⟩
  · intro x
    change |D x| ≤ C' * (1 + ‖x‖) ^ d
    rw [hDrepr]
    apply habsSum x
    intro i
    exact hone i x
  · intro i x
    rw [hfirst]
    apply habsSum x
    intro j
    exact htwo j i x
  · intro i j x
    rw [hsecond]
    apply habsSum x
    intro k
    exact hthree k i j x

/-- Polynomially bounded third coordinate derivatives give twice continuously differentiable heat
averages. -/
theorem contDiff_two_heatAverage_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (t : ℝ) :
    ContDiff ℝ 2 (fun x : Fin n → ℝ => heatAverage F x t) := by
  have hF₂ := hasPolynomiallyBoundedSecond_of_third hF₃
  have hF₁ := hasPolynomiallyBoundedCoordinateDerivatives_of_second hF₂
  let c : ℝ := Real.sqrt t
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x t
  have hcenter (x : Fin n → ℝ) := hasFDerivAt_shiftAverage_center hF₁ x c
  have hUderiv (x : Fin n → ℝ) :
      HasFDerivAt U (∫ ξ, fderiv ℝ F (x + c • ξ) ∂(standardGaussianMeasure n)) x := by
    simpa [U, heatAverage, c] using (hcenter x).2.1
  have hUdifferentiable : Differentiable ℝ U := fun x => (hUderiv x).differentiableAt
  have hEval (x v : Fin n → ℝ) :
      fderiv ℝ U x v = shiftAverage (fun z => fderiv ℝ F z v) x c := by
    calc
      fderiv ℝ U x v = (∫ ξ, fderiv ℝ F (x + c • ξ)
          ∂(standardGaussianMeasure n)) v := by rw [(hUderiv x).fderiv]
      _ = ∫ ξ, fderiv ℝ F (x + c • ξ) v ∂(standardGaussianMeasure n) :=
        ContinuousLinearMap.integral_apply (hcenter x).1 v
      _ = shiftAverage (fun z => fderiv ℝ F z v) x c := by rfl
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num,
    contDiff_succ_iff_fderiv_apply]
  refine ⟨hUdifferentiable, ?_, ?_⟩
  · intro hn
    norm_num at hn
  · intro v
    let G : (Fin n → ℝ) → ℝ := fun z => fderiv ℝ F z v
    have hG₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives G :=
      hasPolynomiallyBoundedSecond_of_directionalDerivative hF₃ v
    have hGcont : ContDiff ℝ 1 (fun x : Fin n → ℝ => heatAverage G x t) :=
      contDiff_one_heatAverage_of_second hG₂ t
    have hEq : (fun x => fderiv ℝ U x v) = fun x => heatAverage G x t := by
      funext x
      calc
        fderiv ℝ U x v = shiftAverage G x c := hEval x v
        _ = heatAverage G x t := by rfl
    rw [hEq]
    exact hGcont


end EhrhardGaussian.Ehrhard
