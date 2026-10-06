/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCCutoffHeatPlateau

/-!
# Quantitative cutoff errors

The finite dimensional gradient estimates control the terms created by
spatial differentiation of the Gaussian cutoff.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Classical

noncomputable section

namespace ESS

/-- Each weak gradient component is bounded by the full Euclidean
gradient magnitude. -/
theorem uc_gradient_component_le
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (i j : Fin 3) :
    |Dv z i j| ≤ Real.sqrt (spatialGradientSq v Dv z) := by
  have hinner : Dv z i j ^ 2 ≤ ∑ k : Fin 3, Dv z i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Dv z i k))
      (Finset.mem_univ j)
  have houter : (∑ k : Fin 3, Dv z i k ^ 2) ≤
      ∑ l : Fin 3, ∑ k : Fin 3, Dv z l k ^ 2 :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (Dv z l k)))
      (Finset.mem_univ i)
  have hsq : Dv z i j ^ 2 ≤ spatialGradientSq v Dv z := by
    simpa only [spatialGradientSq] using hinner.trans houter
  exact Real.abs_le_sqrt hsq

/-- A scalar coefficient bounded componentwise by `M` produces a
controlled vector when contracted with the spatial gradient. -/
theorem uc_gradient_contraction_le
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) (d : Fin 3 → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hd : ∀ j, |d j| ≤ M) :
    vec3EuclideanNorm (fun i => ∑ j : Fin 3, d j * Dv z i j) ≤
      9 * M * Real.sqrt (spatialGradientSq v Dv z) := by
  calc
    vec3EuclideanNorm (fun i => ∑ j : Fin 3, d j * Dv z i j) ≤
        ∑ i : Fin 3, |∑ j : Fin 3, d j * Dv z i j| :=
      vec3EuclideanNorm_le_sum_abs _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |d j * Dv z i j| := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
          M * Real.sqrt (spatialGradientSq v Dv z) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hd j) (uc_gradient_component_le v Dv z i j)
        (abs_nonneg _) hM
    _ = 9 * M * Real.sqrt (spatialGradientSq v Dv z) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- The heat operator error caused by cutoff differentiation is bounded
by the cutoff derivatives and the original field energy. -/
theorem ucGaussianCutoff_heat_error_le
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z -
        (ucGaussianCutoff ρ hρ ε z) • ucWeakHeatVector D2v Dtv z) ≤
      |timePartial (ucGaussianCutoff ρ hρ ε) z +
        ∑ j : Fin 3,
          spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| *
        vec3EuclideanNorm (v z) +
      18 * (cutoffGradientConstant / ρ) *
        Real.sqrt (spatialGradientSq v Dv z) := by
  let A := timePartial (ucGaussianCutoff ρ hρ ε) z +
    ∑ j : Fin 3, spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z
  let d : Fin 3 → ℝ := fun j =>
    spatialPartial (ucGaussianCutoff ρ hρ ε) j z
  let M := cutoffGradientConstant / ρ
  have hM : 0 ≤ M :=
    (abs_nonneg _).trans (ucGaussianCutoff_spatialPartial_bound hρ ε z 0)
  have hd (j : Fin 3) : |d j| ≤ M :=
    ucGaussianCutoff_spatialPartial_bound hρ ε z j
  have heq :
      ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z -
        (ucGaussianCutoff ρ hρ ε z) • ucWeakHeatVector D2v Dtv z =
      A • v z + (2 : ℝ) • (fun i => ∑ j : Fin 3, d j * Dv z i j) := by
    funext i
    simp only [ucCutoffHeat, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    dsimp [A, d, ucGaussianCutoff]
    ring
  rw [heq]
  calc
    vec3EuclideanNorm (A • v z + (2 : ℝ) •
      (fun i => ∑ j : Fin 3, d j * Dv z i j)) ≤
      vec3EuclideanNorm (A • v z) +
        vec3EuclideanNorm ((2 : ℝ) •
          (fun i => ∑ j : Fin 3, d j * Dv z i j)) :=
        vec3EuclideanNorm_add_le _ _
    _ = |A| * vec3EuclideanNorm (v z) +
          2 * vec3EuclideanNorm
            (fun i => ∑ j : Fin 3, d j * Dv z i j) := by
      rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul]
      norm_num
    _ ≤ |A| * vec3EuclideanNorm (v z) +
          2 * (9 * M * Real.sqrt (spatialGradientSq v Dv z)) := by
      have hterm : 2 * vec3EuclideanNorm
          (fun i => ∑ j : Fin 3, d j * Dv z i j) ≤
          2 * (9 * M * Real.sqrt (spatialGradientSq v Dv z)) :=
        mul_le_mul_of_nonneg_left
          (uc_gradient_contraction_le v Dv z d M hM hd) (by norm_num)
      exact add_le_add le_rfl hterm
    _ = _ := by dsimp [A, M]; ring


/-- The trace of the cutoff Hessian is bounded by the three diagonal
second derivatives. -/
theorem ucGaussianCutoff_laplacian_abs_bound
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ) (z : ParabolicPoint) :
    |∑ j : Fin 3,
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| ≤
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  calc
    |∑ j : Fin 3,
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| ≤
        ∑ j : Fin 3,
          |spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact ucGaussianCutoff_spatialSecondPartial_bound hρ ε z j j
    _ = 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]


/-- The cutoff time derivative splits into a collar contribution and an
early-time contribution. -/
theorem ucGaussianCutoff_timePartial_local_bound
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    {z : ParabolicPoint} (hz : z ∈ ucCylinder ρ) :
    |timePartial (ucGaussianCutoff ρ hρ ε) z| ≤
      (if z ∈ ucCutoffRegion ρ then 32 else 0) +
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) := by
  classical
  let θ := ucSpatialCutoff ρ hρ z.1
  let η := ucFinalTimeCutoff z.2
  let χ := ucInitialTimeCutoff ε z.2
  let η' := deriv ucFinalTimeCutoff z.2
  let χ' := deriv (ucInitialTimeCutoff ε) z.2
  have hθ : |θ| ≤ 1 := by
    have h := ucSpatialCutoff_bounds hρ z.1
    change |ucSpatialCutoff ρ hρ z.1| ≤ 1
    rw [abs_of_nonneg h.1]
    exact h.2
  have hη : |η| ≤ 1 := by
    have h := ucFinalTimeCutoff_bounds z.2
    change |ucFinalTimeCutoff z.2| ≤ 1
    rw [abs_of_nonneg h.1]
    exact h.2
  have hχ : |χ| ≤ 1 := by
    have h := ucInitialTimeCutoff_bounds ε z.2
    change |ucInitialTimeCutoff ε z.2| ≤ 1
    rw [abs_of_nonneg h.1]
    exact h.2
  have hη' : |η'| ≤ 32 := ucFinalTimeCutoff_abs_deriv_le z.2
  have hχ' : |χ'| ≤ (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) :=
    ucInitialTimeCutoff_abs_deriv_le_early hε z.2
  have hfinal : |θ * η' * χ| ≤
      if z ∈ ucCutoffRegion ρ then 32 else 0 := by
    by_cases hinner : z ∈ ucInnerRegion ρ
    · have hzero : η' = 0 := ucFinalTimeCutoff_deriv_zero hinner.2.2
      have hnot : z ∉ ucCutoffRegion ρ := by
        intro hc
        exact hc.2 hinner
      simp [hzero, hnot]
    · have hc : z ∈ ucCutoffRegion ρ := ⟨hz, hinner⟩
      simp only [hc, ↓reduceIte, abs_mul]
      calc
        |θ| * |η'| * |χ| ≤ 1 * 32 * 1 := by gcongr
        _ = 32 := by ring
  have hinitial : |θ * η * χ'| ≤
      if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0 := by
    rw [abs_mul, abs_mul]
    have hcoef : 0 ≤ (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) :=
      (abs_nonneg _).trans hχ'
    calc
      |θ| * |η| * |χ'| ≤ 1 * 1 *
          (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) := by gcongr
      _ = _ := by ring
  rw [ucGaussianCutoff_timePartial hρ ε z,
    ucGaussianTimeCutoff_deriv]
  change |θ * (η' * χ + η * χ')| ≤ _
  have hrewrite : θ * (η' * χ + η * χ') =
      θ * η' * χ + θ * η * χ' := by ring
  rw [hrewrite]
  exact (abs_add_le _ _).trans (add_le_add hfinal hinitial)


/-- The cutoff Laplacian vanishes on the inner plateau and is bounded
on its collar. -/
theorem ucGaussianCutoff_laplacian_abs_local_bound
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucCylinder ρ) :
    |∑ j : Fin 3,
      spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| ≤
        if z ∈ ucCutoffRegion ρ then
          3 * (cutoffSecondDerivativeConstant / ρ ^ 2) else 0 := by
  classical
  by_cases hinner : z ∈ ucInnerRegion ρ
  · have hnot : z ∉ ucCutoffRegion ρ := by
      intro hc
      exact hc.2 hinner
    simp [hnot, fun j =>
      ucGaussianCutoff_spatialSecondPartial_zero_on_inner hρ ε hinner j j]
  · have hc : z ∈ ucCutoffRegion ρ := ⟨hz, hinner⟩
    simp only [hc, ↓reduceIte]
    exact ucGaussianCutoff_laplacian_abs_bound hρ ε z


/-- The spatial cutoff derivative vanishes off the collar inside the
normalized cylinder. -/
theorem ucGaussianCutoff_spatialPartial_abs_local_bound
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucCylinder ρ) (j : Fin 3) :
    |spatialPartial (ucGaussianCutoff ρ hρ ε) j z| ≤
      if z ∈ ucCutoffRegion ρ then cutoffGradientConstant / ρ else 0 := by
  classical
  by_cases hinner : z ∈ ucInnerRegion ρ
  · have hnot : z ∉ ucCutoffRegion ρ := by
      intro hc
      exact hc.2 hinner
    simp [hnot, ucGaussianCutoff_spatialPartial_zero_on_inner hρ ε hinner j]
  · have hc : z ∈ ucCutoffRegion ρ := ⟨hz, hinner⟩
    simp only [hc, ↓reduceIte]
    exact ucGaussianCutoff_spatialPartial_bound hρ ε z j


/-- The cutoff heat error on the inner region is exactly the derivative
of the initial time factor times the original field. -/
theorem ucGaussianCutoff_heat_error_eq_on_inner
    {ρ : ℝ} (hρ : 0 < ρ) (ε : ℝ)
    {z : ParabolicPoint} (hz : z ∈ ucInnerRegion ρ)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3) :
    ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z -
      (ucGaussianCutoff ρ hρ ε z) • ucWeakHeatVector D2v Dtv z =
        (deriv (ucInitialTimeCutoff ε) z.2) • v z := by
  have hθ := ucSpatialCutoff_eq_one hρ hz.1
  have hη := ucFinalTimeCutoff_eq_one hz.2.2.le
  have hcut : ucGaussianCutoff ρ hρ ε z =
      ucInitialTimeCutoff ε z.2 := by
    simp [ucGaussianCutoff, ucCutoffScalar, hθ, hη]
  rw [ucGaussianCutoff_heat_eq_on_inner hρ ε hz v Dv D2v Dtv, hcut]
  abel


/-- The cutoff heat error is supported on the spatial or final-time
collar and on the initial time transition. -/
theorem ucGaussianCutoff_heat_error_local_le
    {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    {z : ParabolicPoint} (hz : z ∈ ucCylinder ρ) :
    vec3EuclideanNorm
      (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
        (ucInitialTimeCutoff ε) v Dv D2v Dtv z -
        (ucGaussianCutoff ρ hρ ε z) • ucWeakHeatVector D2v Dtv z) ≤
      (if z ∈ ucCutoffRegion ρ then
        (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
          vec3EuclideanNorm (v z) +
        18 * (cutoffGradientConstant / ρ) *
          Real.sqrt (spatialGradientSq v Dv z) else 0) +
      (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
        vec3EuclideanNorm (v z) := by
  classical
  let E := if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0
  have hv : 0 ≤ vec3EuclideanNorm (v z) := vec3EuclideanNorm_nonneg _
  by_cases hc : z ∈ ucCutoffRegion ρ
  · have htime : |timePartial (ucGaussianCutoff ρ hρ ε) z| ≤
        32 + E := by
      simpa only [hc, ↓reduceIte, E] using
        ucGaussianCutoff_timePartial_local_bound hρ hε hz
    have hlap : |∑ j : Fin 3,
        spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| ≤
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      simpa only [hc, ↓reduceIte] using
        ucGaussianCutoff_laplacian_abs_local_bound hρ ε hz
    have hA : |timePartial (ucGaussianCutoff ρ hρ ε) z +
        ∑ j : Fin 3,
          spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| ≤
        32 + E + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      exact (abs_add_le _ _).trans (by linarith only [htime, hlap])
    have herror := ucGaussianCutoff_heat_error_le hρ ε
      v Dv D2v Dtv z
    simp only [hc, ↓reduceIte]
    calc
      _ ≤ |timePartial (ucGaussianCutoff ρ hρ ε) z +
            ∑ j : Fin 3,
              spatialSecondPartial (ucGaussianCutoff ρ hρ ε) j j z| *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) := herror
      _ ≤ (32 + E + 3 *
            (cutoffSecondDerivativeConstant / ρ ^ 2)) *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) :=
        add_le_add (mul_le_mul_of_nonneg_right hA hv) le_rfl
      _ = (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) +
          E * vec3EuclideanNorm (v z) := by ring
  · have hinner : z ∈ ucInnerRegion ρ := by
      by_contra hnot
      exact hc ⟨hz, hnot⟩
    rw [ucGaussianCutoff_heat_error_eq_on_inner hρ ε hinner
      v Dv D2v Dtv, vec3EuclideanNorm_smul]
    simp only [hc, ↓reduceIte, zero_add]
    exact mul_le_mul_of_nonneg_right
      (ucInitialTimeCutoff_abs_deriv_le_early hε z.2) hv


/-- The normalized differential inequality and the localized cutoff
errors control the heat operator of the compact field. -/
theorem ucGaussianCutoff_heat_ae_local_bound
    {ρ ε c₁ scale : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (v : ParabolicPoint → Vec3)
    (Dv : ParabolicPoint → Fin 3 → Vec3)
    (D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtv : ParabolicPoint → Vec3)
    (hineq : ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    ∀ᵐ z ∂(volume.restrict (ucCylinder ρ)),
      z ∈ ucCylinder ρ →
      vec3EuclideanNorm
        (ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
          (ucInitialTimeCutoff ε) v Dv D2v Dtv z) ≤
        (ucGaussianCutoff ρ hρ ε z) *
          (c₁ * scale * (vec3EuclideanNorm (v z) +
            Real.sqrt (spatialGradientSq v Dv z))) +
        (if z ∈ ucCutoffRegion ρ then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) +
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z) := by
  filter_upwards [hineq] with z hzineq hz
  let ξ := ucGaussianCutoff ρ hρ ε z
  let L := ucWeakHeatVector D2v Dtv z
  let P := ucCutoffHeat (ucSpatialCutoff ρ hρ) ucFinalTimeCutoff
    (ucInitialTimeCutoff ε) v Dv D2v Dtv z
  let E := P - ξ • L
  have hξ : 0 ≤ ξ := (ucGaussianCutoff_bounds hρ ε z).1
  have hmain := mul_le_mul_of_nonneg_left hzineq hξ
  have herror := ucGaussianCutoff_heat_error_local_le hρ hε
    v Dv D2v Dtv hz
  have heq : P = ξ • L + E := by dsimp [E]; abel
  change vec3EuclideanNorm P ≤ _
  change ξ * vec3EuclideanNorm L ≤ _ at hmain
  change vec3EuclideanNorm E ≤ _ at herror
  rw [heq]
  calc
    vec3EuclideanNorm (ξ • L + E) ≤
        vec3EuclideanNorm (ξ • L) + vec3EuclideanNorm E :=
      vec3EuclideanNorm_add_le _ _
    _ = ξ * vec3EuclideanNorm L + vec3EuclideanNorm E := by
      rw [vec3EuclideanNorm_smul, abs_of_nonneg hξ]
    _ ≤ ξ * (c₁ * scale * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) +
        (if z ∈ ucCutoffRegion ρ then
          (32 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2)) *
            vec3EuclideanNorm (v z) +
          18 * (cutoffGradientConstant / ρ) *
            Real.sqrt (spatialGradientSq v Dv z) else 0) +
        (if ε ≤ z.2 ∧ z.2 ≤ 2 * ε then 8 / ε else 0) *
          vec3EuclideanNorm (v z) :=
      by simpa only [add_assoc] using add_le_add hmain herror


end ESS
