/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsOperatorLocalElliptic
public import LeanPool.CutoffRigidity.GibbsLocalizedTranslations
public import LeanPool.CutoffRigidity.EuclideanWeakHessianEstimates

/-! # Actual localization of weak operator eigenfunctions

Compact scalar products preserve the genuine weak derivative identity.
The resulting distributional Laplacian has an actual compactly supported
L² right-hand side, allowing the checked mollified Hessian estimate.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual coordinate product rule, expressed using the actual gradients. -/
theorem coordinateDerivative_mul_actual {a b : E → ℝ}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) (i : Fin d) (x : E) :
    coordinateDerivative i (fun y => a y * b y) x =
      a x * coordinateDerivative i b x + b x * coordinateDerivative i a x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul (ha x) (hb x)]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- Localization of the actual distributional Laplacian using only the
actual closed first gradient, before any second weak derivative is constructed. -/
theorem gibbsSobolev_cutoff_laplacian_test {V χ φ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (u : gibbsSobolevGraph hV hprob)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, χ x * gibbsSobolevInclusion hV hprob u x * euclideanLaplacian φ x) =
      -(∫ x, χ x * inner ℝ (gibbsSobolevDerivative hV hprob u x) (gradient φ x)) +
      (∫ x, φ x * inner ℝ (gibbsSobolevDerivative hV hprob u x) (gradient χ x)) +
      (∫ x, gibbsSobolevInclusion hV hprob u x * φ x * euclideanLaplacian χ x) := by
  let U := gibbsSobolevInclusion hV hprob u
  let G := gibbsSobolevDerivative hV hprob u
  have hdχ (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i χ) := by
    apply contDiff_coordinateDerivative
    convert hχ using 1
    norm_num
  have hdφ (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i φ) := by
    apply contDiff_coordinateDerivative
    convert hφ using 1
    norm_num
  have hddχ (i : Fin d) := (c1_coordinateDerivative_of_c2 (hdχ i) i).continuous
  have hddφ (i : Fin d) := (c1_coordinateDerivative_of_c2 (hdφ i) i).continuous
  have hdcχ (i : Fin d) : HasCompactSupport (coordinateDerivative i χ)
    := hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hdcφ (i : Fin d) : HasCompactSupport (coordinateDerivative i φ)
    := hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  let A (i : Fin d) (x : E) := (χ x * coordinateDerivative i φ x) * (G x) i
  let B (i : Fin d) (x : E) := (φ x * coordinateDerivative i χ x) * (G x) i
  let C (i : Fin d) (x : E) := (coordinateDerivative i χ x * coordinateDerivative i φ x) * U x
  let D (i : Fin d) (x : E) := (χ x * coordinateDerivative i (coordinateDerivative i φ) x) * U x
  let F (i : Fin d) (x : E) := (φ x * coordinateDerivative i (coordinateDerivative i χ) x) * U x
  have hA (i : Fin d) : Integrable (A i) volume := by
    apply integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
      (hχ.continuous.mul (hdφ i).continuous) _ G i
    simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i φ)
  have hB (i : Fin d) : Integrable (B i) volume := by
    apply integrable_compact_test_gibbsVector_coordinate_volume hV.continuous hprob
      (hφ.continuous.mul (hdχ i).continuous) _ G i
    simpa only [Pi.mul_def] using hφc.mul_right (f' := coordinateDerivative i χ)
  have hC (i : Fin d) : Integrable (C i) volume := by
    apply integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      ((hdχ i).continuous.mul (hdφ i).continuous) _ U
    simpa only [Pi.mul_def] using (hdcχ i).mul_right (f' := coordinateDerivative i φ)
  have hD (i : Fin d) : Integrable (D i) volume := by
    apply integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hχ.continuous.mul (hddφ i)) _ U
    simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i (coordinateDerivative
      i φ))
  have hF (i : Fin d) : Integrable (F i) volume := by
    apply integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hφ.continuous.mul (hddχ i)) _ U
    simpa only [Pi.mul_def] using hφc.mul_right (f' := coordinateDerivative i (coordinateDerivative
      i χ))
  have hrow (i : Fin d) : (∫ x, D i x) = -(∫ x, A i x) + (∫ x, B i x) + (∫ x, F i x) := by
    have ht1 : ContDiff ℝ 2 (fun x => χ x * coordinateDerivative i φ x) :=
      (hχ.of_le (by norm_num)).mul (hdφ i)
    have ht1c : HasCompactSupport (fun x => χ x * coordinateDerivative i φ x) := by
      simpa only [Pi.mul_def] using hχc.mul_right (f' := coordinateDerivative i φ)
    have ht2 : ContDiff ℝ 2 (fun x => φ x * coordinateDerivative i χ x) :=
      (hφ.of_le (by norm_num)).mul (hdχ i)
    have ht2c : HasCompactSupport (fun x => φ x * coordinateDerivative i χ x) := by
      simpa only [Pi.mul_def] using hφc.mul_right (f' := coordinateDerivative i χ)
    have h1 := gibbsSobolev_coordinate_weak_derivative_volume hV hprob ht1 ht1c i u
    have h2 := gibbsSobolev_coordinate_weak_derivative_volume hV hprob ht2 ht2c i u
    have hp1 (x : E) : coordinateDerivative i (fun y => χ y * coordinateDerivative i φ y) x * U x =
      D i x + C i x := by
      rw [coordinateDerivative_mul_actual (hχ.differentiable (by norm_num)) ((hdφ i).differentiable
        (by norm_num))]
      dsimp [C, D]
      ring
    have hp2 (x : E) : coordinateDerivative i (fun y => φ y * coordinateDerivative i χ y) x * U x =
      F i x + C i x := by
      rw [coordinateDerivative_mul_actual (hφ.differentiable (by norm_num)) ((hdχ i).differentiable
        (by norm_num))]
      dsimp [C, F]
      ring
    change (∫ x, A i x) = -(∫ x, coordinateDerivative i (fun y => χ y * coordinateDerivative i φ y)
      x * U x) at h1
    change (∫ x, B i x) = -(∫ x, coordinateDerivative i (fun y => φ y * coordinateDerivative i χ y)
      x * U x) at h2
    simp_rw [hp1] at h1
    simp_rw [hp2] at h2
    rw [integral_add (hD i) (hC i)] at h1
    rw [integral_add (hF i) (hC i)] at h2
    linarith
  have hInner (p : E → ℝ) (x : E) : inner ℝ (G x) (gradient p x) =
      ∑ i : Fin d, coordinateDerivative i p x * (G x) i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
    ring
  have hpD (x : E) : χ x * U x * euclideanLaplacian φ x = ∑ i : Fin d, D i x := by
    change χ x * U x * (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i φ) x) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [D]
    ring
  have hpF (x : E) : U x * φ x * euclideanLaplacian χ x = ∑ i : Fin d, F i x := by
    change U x * φ x * (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i χ) x) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F]
    ring
  change (∫ x, χ x * U x * euclideanLaplacian φ x) =
    -(∫ x, χ x * inner ℝ (G x) (gradient φ x)) +
      (∫ x, φ x * inner ℝ (G x) (gradient χ x)) +
      (∫ x, U x * φ x * euclideanLaplacian χ x)
  simp_rw [hpD, hpF, hInner, Finset.mul_sum]
  simp only [← mul_assoc]
  change (∫ x, ∑ i : Fin d, D i x) = -(∫ x, ∑ i : Fin d, A i x) +
    (∫ x, ∑ i : Fin d, B i x) + (∫ x, ∑ i : Fin d, F i x)
  rw [integral_finsetSum _ (fun i _ => hD i), integral_finsetSum _ (fun i _ => hA i),
    integral_finsetSum _ (fun i _ => hB i), integral_finsetSum _ (fun i _ => hF i)]
  simp_rw [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Compact continuous coefficients localize actual Gibbs L² vector pairings
into ordinary Lebesgue integrals. -/
theorem integrable_compact_coeff_inner_gibbsVector_volume {V a : E → ℝ}
    (hV : Continuous V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (ha : Continuous a) (hac : HasCompactSupport a) {H : E → E} (hH : Continuous H)
    (G : E →₂[gibbsMeasure volume V] E) :
    Integrable (fun x => a x * inner ℝ (G x) (H x)) volume := by
  have hi (i : Fin d) : Integrable (fun x => (a x * (H x) i) * (G x) i) volume := by
    have hc : Continuous (fun x => a x * (H x) i) :=
      ha.mul ((EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous.comp hH)
    have hs : HasCompactSupport (fun x => a x * (H x) i) := by
      simpa only [Pi.mul_def] using hac.mul_right (f' := fun x => (H x) i)
    exact integrable_compact_test_gibbsVector_coordinate_volume hV hprob hc hs G i
  have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
  convert hh using 1
  funext x
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.inner_apply]
  ring

/-- The actual lower-order source after compactly localizing an operator eigenvector. -/
@[expose] noncomputable def localizedOperatorEigenLaplacian {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (χ : E → ℝ) (x : E) : ℝ :=
  χ x * (inner ℝ (gradient V x)
    (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) -
      rate * (u : E →₂[gibbsMeasure volume V] ℝ) x) +
    2 * inner ℝ (gradient χ x)
      (gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u) x) +
        (u : E →₂[gibbsMeasure volume V] ℝ) x * euclideanLaplacian χ x

/-- The actual localized weak Laplace equation for every operator eigenvector.
The input has no classical differentiability assumption. -/
theorem gibbsOperatorEigen_localized_distributional_laplacian {V χ φ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate)
    (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hφ : ContDiff ℝ 3 φ) (hφc : HasCompactSupport φ) :
    (∫ x, (χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) * euclideanLaplacian φ x) =
      ∫ x, localizedOperatorEigenLaplacian hV hprob rate u χ x * φ x := by
  let v := gibbsOperatorEigenSobolevLift hV hprob rate u
  let U : E → ℝ := fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x
  let G := gibbsSobolevDerivative hV hprob v
  have hGχ : Continuous (gradient χ) := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
  have hGφ : Continuous (gradient φ) := continuous_gradient_of_c1 (hφ.of_le (by norm_num))
  have hGV : Continuous (gradient V) := continuous_gradient_of_c1 (hV.of_le (by norm_num))
  have hχφ : ContDiff ℝ 2 (fun x => χ x * φ x) := (hχ.mul hφ).of_le (by norm_num)
  have hχφc : HasCompactSupport (fun x => χ x * φ x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := φ)
  let A (x : E) := χ x * inner ℝ (G x) (gradient φ x)
  let B (x : E) := φ x * inner ℝ (G x) (gradient χ x)
  let D (x : E) := (χ x * φ x) * inner ℝ (G x) (gradient V x)
  let N (x : E) := U x * χ x * φ x
  let Eterm (x : E) := U x * φ x * euclideanLaplacian χ x
  have hA : Integrable A volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob hχ.continuous hχc hGφ G
  have hB : Integrable B volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob hφ.continuous hφc hGχ G
  have hD : Integrable D volume := integrable_compact_coeff_inner_gibbsVector_volume
    hV.continuous hprob (hχ.continuous.mul hφ.continuous) hχφc hGV G
  have hN : Integrable N volume := by
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (hχ.continuous.mul hφ.continuous) hχφc (u : E →₂[gibbsMeasure volume V] ℝ)
    simpa only [N, U, Pi.mul_apply, mul_comm, mul_left_comm, mul_assoc] using hh
  have hE : Integrable Eterm volume := by
    have hc : Continuous (fun x => φ x * euclideanLaplacian χ x) :=
      hφ.continuous.mul (euclideanLaplacian_contDiff_one hχ).continuous
    have hs : HasCompactSupport (fun x => φ x * euclideanLaplacian χ x) := by
      simpa only [Pi.mul_def] using hφc.mul_right (f' := euclideanLaplacian χ)
    have hh := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob hc hs
      (u : E →₂[gibbsMeasure volume V] ℝ)
    simpa only [Eterm, U, mul_comm, mul_left_comm, mul_assoc] using hh
  have he := gibbsOperatorEigen_volume_test_equation hV hprob rate u hχφ hχφc
  have hp (x : E) : inner ℝ (G x) (gradient (fun y => χ y * φ y) x + (χ x * φ x) • gradient V x) =
      A x + B x + D x := by
    rw [gradient_cutoff_mul (hχ.differentiable (by norm_num)) (hφ.differentiable (by norm_num))]
    simp only [inner_add_right, inner_smul_right]
    rfl
  change (∫ x, inner ℝ (G x)
    (gradient (fun y => χ y * φ y) x + (χ x * φ x) • gradient V x)) = _ at he
  simp_rw [hp] at he
  have ha := integral_add (hA.add hB) hD
  simp only [Pi.add_apply] at ha
  rw [ha, integral_add hA hB] at he
  have he' : (∫ x, A x) + (∫ x, B x) + (∫ x, D x) = rate * (∫ x, N x) := by
    simpa only [N, U, mul_assoc] using he
  have hl := gibbsSobolev_cutoff_laplacian_test hV hprob v hχ hχc hφ hφc
  rw [gibbsOperatorEigenSobolevLift_inclusion] at hl
  change (∫ x, χ x * U x * euclideanLaplacian φ x) =
    -(∫ x, A x) + (∫ x, B x) + (∫ x, Eterm x) at hl
  have hr : (∫ x, localizedOperatorEigenLaplacian hV hprob rate u χ x * φ x) =
      2 * (∫ x, B x) + (∫ x, D x) - rate * (∫ x, N x) + (∫ x, Eterm x) := by
    have hp' (x : E) : localizedOperatorEigenLaplacian hV hprob rate u χ x * φ x =
        (2 * B x + D x - rate * N x) + Eterm x := by
      dsimp only [localizedOperatorEigenLaplacian, B, D, N, Eterm, U, G, v]
      rw [real_inner_comm (gradient χ x), real_inner_comm (gradient V x)]
      ring
    simp_rw [hp']
    have ha1 := integral_add (((hB.const_mul 2).add hD).sub (hN.const_mul rate)) hE
    have hs1 := integral_sub ((hB.const_mul 2).add hD) (hN.const_mul rate)
    have ha2 := integral_add (hB.const_mul 2) hD
    simp only [Pi.add_apply, Pi.sub_apply] at ha1 hs1 ha2
    rw [ha1, hs1, ha2, integral_const_mul, integral_const_mul]
  rw [hr]
  change (∫ x, χ x * U x * euclideanLaplacian φ x) = _
  linarith

/-- The actual localized distributional Laplacian is genuinely Lebesgue L². -/
theorem localizedOperatorEigenLaplacian_memLp {V χ : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ) :
    MemLp (localizedOperatorEigenLaplacian hV hprob rate u χ) 2 volume := by
  let G := gibbsSobolevDerivative hV hprob (gibbsOperatorEigenSobolevLift hV hprob rate u)
  have hLower := gibbsOperatorEigen_local_rhs_memLp hV hprob rate u hχ.continuous hχc
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_num)
  have hCross : MemLp (fun x => inner ℝ (gradient χ x) (G x)) 2 volume := by
    have hi (i : Fin d) : MemLp (fun x => coordinateDerivative i χ x * (G x) i) 2 volume :=
      compact_cutoff_gibbsVector_coordinate_memLp_volume hV.continuous hprob
        (c1_coordinateDerivative_of_c2 hχ2 i).continuous
        (hχc.fderiv_apply ℝ (EuclideanSpace.single i 1)) G i
    have hh := memLp_finsetSum Finset.univ (fun i _ => hi i)
    convert hh using 1
    funext x
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.inner_apply, coordinateDerivative, fderiv_single_eq_gradient_coordinate]
  have hLapc : HasCompactSupport (euclideanLaplacian χ) := by
    have hh := hasCompactSupport_langevinDifferentialOperator (fun _ : E => (0 : ℝ)) hχc
    have hL : langevinDifferentialOperator (fun _ : E => (0 : ℝ)) χ = euclideanLaplacian χ := by
      funext x
      simp [langevinDifferentialOperator, gradient_fun_const]
    rw [← hL]
    exact hh
  have hLap := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob
    (euclideanLaplacian_contDiff_one hχ).continuous hLapc (u : E →₂[gibbsMeasure volume V] ℝ)
  convert (hLower.add (hCross.const_mul 2)).add hLap using 1
  funext x
  dsimp only [localizedOperatorEigenLaplacian, G]
  simp only [Pi.add_apply]
  ring

/-- The actual eigenfunction localization has uniformly L²-bounded Hessians
under every actual smooth compact mollification. This is the concrete local
weak H² estimate, derived without assuming a classical representative. -/
theorem gibbsOperatorEigen_mollified_local_hessian_energy_le {V χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hprob : IsProbabilityMeasure (gibbsMeasure volume V)) (rate : ℝ)
    (u : gibbsOperatorEigenspace hV hprob rate) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (φ : ContDiffBump (0 : E)) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i (bumpMollification φ
        (fun y => χ y * (u : E →₂[gibbsMeasure volume V] ℝ) y))) x) ^ 2) ≤
      ∫ x, localizedOperatorEigenLaplacian hV hprob rate u χ x ^ 2 := by
  have hwLp := compact_cutoff_gibbsLp_memLp_volume hV.continuous hprob hχ.continuous hχc
    (u : E →₂[gibbsMeasure volume V] ℝ)
  have hwc : HasCompactSupport (fun x => χ x * (u : E →₂[gibbsMeasure volume V] ℝ) x) := by
    simpa only [Pi.mul_def] using hχc.mul_right (f' := fun x => (u : E →₂[gibbsMeasure volume V] ℝ)
      x)
  have hFm : Measurable (localizedOperatorEigenLaplacian hV hprob rate u χ) := by
    have huM : Measurable (fun x => (u : E →₂[gibbsMeasure volume V] ℝ) x) :=
      (Lp.stronglyMeasurable (u : E →₂[gibbsMeasure volume V] ℝ)).measurable
    have hGM : Measurable (fun x => gibbsSobolevDerivative hV hprob
        (gibbsOperatorEigenSobolevLift hV hprob rate u) x) :=
      (Lp.stronglyMeasurable (gibbsSobolevDerivative hV hprob
        (gibbsOperatorEigenSobolevLift hV hprob rate u))).measurable
    have hGV := continuous_gradient_of_c1 (hV.of_le (by norm_num))
    have hGχ := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
    have hLap := (euclideanLaplacian_contDiff_one hχ).continuous
    have hχm := hχ.continuous.measurable
    unfold localizedOperatorEigenLaplacian
    fun_prop
  apply mollified_distributional_hessian_energy_le (hwLp.locallyIntegrable (by norm_num)) hwc hFm
    (localizedOperatorEigenLaplacian_memLp hV hprob rate u hχ hχc)
  intro ψ hψ hψc
  exact gibbsOperatorEigen_localized_distributional_laplacian hV hprob rate u hχ hχc hψ hψc

end CutoffRigidity
