/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.OperatorEigenEqualityCutoffs

/-! # Equality-case distributional rigidity without a classical representative -/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem abs_coordinateDerivative_le_norm_gradient (f : E → ℝ) (i : Fin d) (x : E) :
    |coordinateDerivative i f x| ≤ ‖gradient f x‖ := by
  rw [coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  exact PiLp.norm_apply_le (gradient f x) i

/-- The genuine equality-case weak derivative pairing is controlled by
the inverse-radius cutoff bound. The Hessian pairing uses the actual
Gibbs density to compare the ordinary-volume distribution with L²(μ). -/
theorem gibbsOperatorEigen_equalRate_cutoff_distribution_bound {V χ η ψ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hη : ContDiff ℝ 3 η) (hηc : HasCompactSupport η)
    (hlocal : ∀ x ∈ tsupport η, χ x = 1 ∧ ∀ k, coordinateDerivative k χ x = 0)
    (M : ℝ) (hM : 0 ≤ M) (hgrad : ∀ x, ‖gradient η x‖ ≤ M)
    (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    |∫ x, η x *
      (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u) x) i *
      coordinateDerivative j ψ x| ≤
    2 * M * ‖gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)‖ *
      ‖((hψ.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport
        (by simpa only [Pi.mul_def, Function.comp_def] using hψc.mul_right (f'
          := fun x => Real.exp (V x))) :
          MemLp (fun x => ψ x * Real.exp (V x)) 2 (gibbsMeasure volume V)).toLp
            (fun x => ψ x * Real.exp (V x))‖ +
    M * (∫ x, |(gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u) x) i * ψ x|)
      := by
  let := hp
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)
  let H := gibbsOperatorLocalizedHessian hV hp ρ u hχ hχc i j
  have hψexpCont : Continuous (fun x => ψ x * Real.exp (V x)) := by fun_prop
  have hψexpSupp : HasCompactSupport (fun x => ψ x * Real.exp (V x)) := by
    simpa only [Pi.mul_def] using hψc.mul_right (f' := fun x => Real.exp (V x))
  have hψexp : MemLp (fun x => ψ x * Real.exp (V x)) 2 (gibbsMeasure volume V) :=
    hψexpCont.memLp_of_hasCompactSupport hψexpSupp
  have hηH := operatorEigen_cutoff_hessian_memLp hV hp ρ hρ hHess ρ u hχ hχc hη.continuous hηc i j
  have hHnorm := gibbsOperatorEigen_equalRate_local_hessian_norm_bound hV hp ρ hρ hHess u
    hχ hχc hη hηc hlocal M hM hgrad i j
  have hchange : (∫ x, (η x * H x) * (ψ x * Real.exp (V x)) ∂gibbsMeasure volume V) =
      ∫ x, (η x * H x) * ψ x := by
    rw [integral_gibbsMeasure volume hV.continuous.measurable]
    apply integral_congr_ae
    filter_upwards with x
    have he : Real.exp (-V x) * Real.exp (V x) = 1 := by rw [← Real.exp_add]; simp
    change Real.exp (-V x) * (η x * H x * (ψ x * Real.exp (V x))) = _
    calc
      _ = (Real.exp (-V x) * Real.exp (V x)) * (η x * H x * ψ x) := by ring
      _ = _ := by rw [he, one_mul]
  have hHpair : |∫ x, (η x * H x) * ψ x| ≤
      2 * M * ‖G‖ * ‖hψexp.toLp (fun x => ψ x * Real.exp (V x))‖ := by
    rw [← hchange, ← real_inner_toLp hηH hψexp]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hHnorm (norm_nonneg _))
  have hGiψ : Integrable (fun x => (G x) i * ψ x) volume := by
    simpa only [mul_comm] using integrable_compact_test_gibbsVector_coordinate_volume
      hV.continuous hp hψ.continuous hψc G i
  have hDη := (c1_coordinateDerivative_of_c2 (hη.of_le (by norm_num)) j).continuous
  have hboundary : Integrable (fun x => coordinateDerivative j η x * (G x) i * ψ x) volume := by
    have hc : Continuous (fun x => coordinateDerivative j η x * ψ x) := hDη.mul hψ.continuous
    have hs : HasCompactSupport (fun x => coordinateDerivative j η x * ψ x) := by
      simpa only [Pi.mul_def] using hψc.mul_left (f := coordinateDerivative j η)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hp hc hs G i
  have hboundaryBound : |∫ x, coordinateDerivative j η x * (G x) i * ψ x| ≤
      M * (∫ x, |(G x) i * ψ x|) := by
    have hpnt (x : E) : ‖coordinateDerivative j η x * (G x) i * ψ x‖ ≤ M * |(G x) i * ψ x| := by
      have hD : |coordinateDerivative j η x| ≤ M :=
        (abs_coordinateDerivative_le_norm_gradient η j x).trans (hgrad x)
      rw [mul_assoc, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hD (abs_nonneg _)
    have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall
      (fun x => norm_nonneg _)) (hGiψ.abs.const_mul M)
      (Filter.Eventually.of_forall hpnt)
    rw [integral_const_mul] at hi
    exact (norm_integral_le_integral_norm _).trans hi
  have hDψ := (c1_coordinateDerivative_of_c2 (hψ.of_le (by norm_num)) j).continuous
  have hleft : Integrable (fun x => η x * (G x) i * coordinateDerivative j ψ x) volume := by
    have hc : Continuous (fun x => η x * coordinateDerivative j ψ x) := hη.continuous.mul hDψ
    have hs : HasCompactSupport (fun x => η x * coordinateDerivative j ψ x) := by
      simpa only [Pi.mul_def] using hηc.mul_right (f' := coordinateDerivative j ψ)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hp hc hs G i
  have he := gibbsOperatorLocalizedHessian_weak_derivative hV hp ρ u hχ hχc i j
    (fun x => η x * ψ x) (hη.mul hψ) (by simpa only [Pi.mul_def] using hηc.mul_right (f' := ψ))
  have hpoint (x : E) : localizedOperatorEigenGradient hV hp ρ u χ i x *
      coordinateDerivative j (fun y => η y * ψ y) x =
      η x * (G x) i * coordinateDerivative j ψ x + coordinateDerivative j η x * (G x) i * ψ x := by
    rw [coordinateDerivative_mul_actual (hη.differentiable (by norm_num)) (hψ.differentiable
      (by norm_num))]
    by_cases hx : x ∈ tsupport η
    · rw [localizedOperatorEigenGradient_eq_of_cutoff_jet hV hp ρ u i x
        (hlocal x hx).1 ((hlocal x hx).2 i)]
      dsimp only [G]
      ring
    · have hz := image_eq_zero_of_notMem_tsupport hx
      have hdz := coordinateDerivative_eq_zero_of_notMem_tsupport j hx
      simp [hz, hdz]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_add hleft hboundary] at he
  have hHp : (∫ x, H x * (η x * ψ x)) = ∫ x, (η x * H x) * ψ x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  change (∫ x, η x * (G x) i * coordinateDerivative j ψ x) +
    (∫ x, coordinateDerivative j η x * (G x) i * ψ x) = -(∫ x, H x * (η x * ψ x)) at he
  rw [hHp] at he
  have htri : |∫ x, η x * (G x) i * coordinateDerivative j ψ x| ≤
      |∫ x, (η x * H x) * ψ x| + |∫ x, coordinateDerivative j η x * (G x) i * ψ x| := by
    have ha := abs_add_le (-(∫ x, (η x * H x) * ψ x))
      (-(∫ x, coordinateDerivative j η x * (G x) i * ψ x))
    have heq : (∫ x, η x * (G x) i * coordinateDerivative j ψ x) =
        -(∫ x, (η x * H x) * ψ x) - (∫ x, coordinateDerivative j η x * (G x) i * ψ x) := by linarith
    rw [heq]
    simpa only [sub_eq_add_neg, abs_neg] using ha
  exact htri.trans (add_le_add hHpair hboundaryBound)

/-- Equality of the actual operator eigenvalue and curvature forces all
ordinary-volume distributional derivatives of the genuine weak gradient
to vanish. No classical representative is assumed or bootstrapped. -/
theorem gibbsOperatorEigen_equalRate_gradient_distribution_zero {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (u : gibbsOperatorEigenspace hV hp ρ) (i j : Fin d)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, (gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u) x) i *
      coordinateDerivative j ψ x) = 0 := by
  let := hp
  let G := gibbsSobolevDerivative hV hp (gibbsOperatorEigenSobolevLift hV hp ρ u)
  obtain ⟨C, hC, η, hη, hηc, hb, hone, hgrad⟩ := exists_smooth_C3_cutoff_exhaustion (d := d)
  have hψexpCont : Continuous (fun x => ψ x * Real.exp (V x)) := by fun_prop
  have hψexpSupp : HasCompactSupport (fun x => ψ x * Real.exp (V x)) := by
    simpa only [Pi.mul_def] using hψc.mul_right (f' := fun x => Real.exp (V x))
  have hψexp : MemLp (fun x => ψ x * Real.exp (V x)) 2 (gibbsMeasure volume V) :=
    hψexpCont.memLp_of_hasCompactSupport hψexpSupp
  let P := ‖hψexp.toLp (fun x => ψ x * Real.exp (V x))‖
  let Q := ∫ x, |(G x) i * ψ x|
  have hbound (n : ℕ) :
      |∫ x, η n x * (G x) i * coordinateDerivative j ψ x| ≤
        2 * (C / ((n : ℝ) + 1)) * ‖G‖ * P + (C / ((n : ℝ) + 1)) * Q := by
    obtain ⟨χ, hχ, hχc, hlocal⟩ := exists_compact_C3_cutoff_one_jet (tsupport (η n)) (hηc n)
    exact gibbsOperatorEigen_equalRate_cutoff_distribution_bound hV hp ρ hρ hHess u
      hχ hχc (hη n) (hηc n) hlocal (C / ((n : ℝ) + 1))
      (div_nonneg hC (by positivity)) (hgrad n) hψ hψc i j
  have hDψ := (c1_coordinateDerivative_of_c2 (hψ.of_le (by norm_num)) j).continuous
  have hDψc : HasCompactSupport (coordinateDerivative j ψ) :=
    hψc.fderiv_apply ℝ (EuclideanSpace.single j 1)
  have hf : Integrable (fun x => (G x) i * coordinateDerivative j ψ x) volume := by
    simpa only [mul_comm] using integrable_compact_test_gibbsVector_coordinate_volume
      hV.continuous hp hDψ hDψc G i
  have hleft : Tendsto (fun n => |∫ x, η n x * (G x) i * coordinateDerivative j ψ x|)
      atTop (𝓝 |∫ x, (G x) i * coordinateDerivative j ψ x|) := by
    simpa only [mul_assoc] using
      (cutoff_integral_tendsto hf η (fun n => (hη n).continuous.measurable) hb hone).abs
  have hM := cutoff_inverse_radius_tendsto_zero C
  have hright : Tendsto (fun n : ℕ => 2 * (C / ((n : ℝ) + 1)) * ‖G‖ * P +
      (C / ((n : ℝ) + 1)) * Q) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      (((hM.const_mul 2).mul_const ‖G‖).mul_const P).add (hM.mul_const Q)
  have hz : |∫ x, (G x) i * coordinateDerivative j ψ x| ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hbound)
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

end CutoffRigidity
