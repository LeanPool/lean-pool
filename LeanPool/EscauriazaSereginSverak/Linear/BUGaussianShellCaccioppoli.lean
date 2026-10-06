/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCaccioppoli
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCellSum
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianCover
public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianTimeGrid
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays

/-!
# Weighted energy on the Gaussian transition shell

The collar cover, time grid, and local Caccioppoli estimate combine to bound
the weighted gradient energy by the weighted radial mass.
-/

public section


open MeasureTheory Set
attribute [local instance] Classical.propDecidable
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The Gaussian-weighted square of a field restricted to the radial region
needed for the collar estimate (`eq:bu-gaussian-collar`). -/
@[expose] def buGaussianRadialWeightedMass (ρ a : ℝ) (v : ParabolicPoint → Vec3) :
    ParabolicPoint → ℝ := fun z =>
  if ρ / 2 ≤ vec3EuclideanNorm z.1 then
    ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2 else 0

/-- The inner localization cylinder at a spatial center and time-grid index. -/
@[expose] def buGaussianShellInnerCell
    (r : ℝ) (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ) :
    Set ParabolicPoint :=
  spaceTimeSet (vec3Ball p.1.2 r)
    (buGaussianTimeGridInner (1 / 6) (r ^ 2) p.2)

/-- The larger localization cylinder surrounding the corresponding inner cell. -/
@[expose] def buGaussianShellOuterCell
    (r : ℝ) (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ) :
    Set ParabolicPoint :=
  spaceTimeSet (vec3Ball p.1.2 (2 * r))
    (buGaussianTimeGridOuter (1 / 6) (r ^ 2) p.2)

private theorem buGaussian_shell_weighted_data
    {ρ a : ℝ} (ha : 0 < a)
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      v Dv D2v Dtv)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let U : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
    let W : ParabolicPoint → ℝ := ucGaussianWeight a
    let G : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z
    let fG : ParabolicPoint → ℝ := U.indicator (fun z => W z * G z)
    let fM : ParabolicPoint → ℝ := U.indicator (buGaussianRadialWeightedMass ρ a v)
    MeasurableSet U ∧ Integrable fG volume ∧ Integrable fM volume ∧
      (∀ z ∈ U, 0 < z.2) ∧
      (∀ᵐ z ∂(volume : Measure ParabolicPoint), 0 ≤ fG z) ∧
      (∀ᵐ z ∂(volume : Measure ParabolicPoint), 0 ≤ fM z) := by
  let U : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
  let V : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let W : ParabolicPoint → ℝ := ucGaussianWeight a
  let G : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z
  let fG : ParabolicPoint → ℝ := U.indicator (fun z => W z * G z)
  let fM : ParabolicPoint → ℝ := U.indicator (buGaussianRadialWeightedMass ρ a v)
  have hUmeas : MeasurableSet U :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball 0 ρ) isOpen_Ioo).measurableSet
  have hRmeas : MeasurableSet
      {z : ParabolicPoint | ρ / 2 ≤ vec3EuclideanNorm z.1} := by
    exact measurableSet_le continuous_const.measurable
      (continuous_vec3EuclideanNorm.measurable.comp measurable_fst)
  have hEnergy0 := buGaussian_local_energy_integrable hweak hL2
  have hEnergy :
      Integrable (fun z => vec3EuclideanNorm (v z) ^ 2) (volume.restrict U) ∧
      Integrable (fun z => spatialGradientSq v Dv z) (volume.restrict U) := by
    simpa [U] using hEnergy0
  have hWmeas : AEStronglyMeasurable W (volume.restrict U) :=
    (ucGaussianWeight_measurable a).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hWbound : ∀ᵐ z ∂(volume.restrict U),
      W z ≤ ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [ae_restrict_mem hUmeas] with z hz
    exact ucGaussianWeight_le_after (by norm_num) (le_of_lt ha)
      hz.2.1.le hz.2.2.le
  have hWnormbound : ∀ᵐ z ∂(volume.restrict U),
      ‖W z‖ ≤ ((1 / 6 : ℝ) * Real.exp (-(1 / 3 : ℝ))) ^ (-2 * a) := by
    filter_upwards [hWbound, ae_restrict_mem hUmeas] with z hz hzmem
    have hzpos : 0 < z.2 := by
      have hzlo : (1 / 6 : ℝ) ≤ z.2 := hzmem.2.1.le
      norm_num at hzlo ⊢
      linarith only [hzlo]
    rw [Real.norm_eq_abs, abs_of_nonneg (ucGaussianWeight_nonneg a hzpos)]
    exact hz
  have hWVG : Integrable (fun z => W z * V z) (volume.restrict U) := by
    have h := hEnergy.1.bdd_mul hWmeas hWnormbound
    simpa [U, V, W, mul_comm] using h
  have hWGG : Integrable (fun z => W z * G z) (volume.restrict U) := by
    have h := hEnergy.2.bdd_mul hWmeas hWnormbound
    simpa [U, G, W, mul_comm] using h
  have hRadialWVG : Integrable
      (fun z => if ρ / 2 ≤ vec3EuclideanNorm z.1 then W z * V z else 0)
      (volume.restrict U) := by
    have h := hWVG.indicator hRmeas
    convert h using 1
    ext z
    by_cases hz : ρ / 2 ≤ vec3EuclideanNorm z.1 <;>
      simp [Set.indicator, hz]
  have hWGglobal : Integrable fG volume := by
    exact (integrable_indicator_iff hUmeas).2 hWGG
  have hMglobal : Integrable fM volume := by
    have hOn : Integrable (buGaussianRadialWeightedMass ρ a v)
        (volume.restrict U) := by
      convert hRadialWVG using 1
      ext z
      simp [buGaussianRadialWeightedMass, W, V]
    exact (integrable_indicator_iff hUmeas).2 hOn
  have htimepos (z : ParabolicPoint) (hz : z ∈ U) : 0 < z.2 := by
    have hz' := hz.2.1
    norm_num at hz' ⊢
    linarith only [hz']
  have hGnonneg : ∀ᵐ z ∂(volume : Measure ParabolicPoint), 0 ≤ fG z := by
    filter_upwards [] with z
    by_cases hz : z ∈ U
    · simp only [fG, Set.indicator_of_mem hz]
      exact mul_nonneg (ucGaussianWeight_nonneg a (htimepos z hz))
        (by unfold G spatialGradientSq; positivity)
    · simp [fG, hz]
  have hMnonneg : ∀ᵐ z ∂(volume : Measure ParabolicPoint), 0 ≤ fM z := by
    filter_upwards [] with z
    by_cases hz : z ∈ U
    · by_cases hrad : ρ / 2 ≤ vec3EuclideanNorm z.1
      · simp only [fM, Set.indicator_of_mem hz, buGaussianRadialWeightedMass]
        split_ifs with h
        · exact mul_nonneg (ucGaussianWeight_nonneg a (htimepos z hz))
            (sq_nonneg _)
        · exact False.elim (h hrad)
      · simp only [fM, Set.indicator_of_mem hz, buGaussianRadialWeightedMass]
        split_ifs with h
        · exact False.elim (hrad h)
        · exact le_rfl
    · simp [fM, hz]
  exact ⟨hUmeas, hWGglobal, hMglobal, htimepos, hGnonneg, hMnonneg⟩

private theorem buGaussian_shell_single_cell_bound
    {ρ a r c s : ℝ} {center : Vec3}
    (hρ : 0 < ρ) (ha : 0 < a) (hr : 0 < r)
    (hcenter : vec3EuclideanNorm center ≤ ρ - 1 / 2)
    (hspace : vec3Ball center (2 * r) ⊆ vec3Ball 0 ρ)
    (htime : Ioo s (s + (2 * r) ^ 2) ⊆ Ioo (1 / 6) 2)
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      v Dv D2v Dtv)
    (hcont : ContinuousOn v (vec3Ball 0 ρ ×ˢ Ico (1 / 6) 2))
    (hc : 0 ≤ c)
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (vec3EuclideanNorm (v z) + Real.sqrt (spatialGradientSq v Dv z))) :
    (∫ z in spaceTimeSet (vec3Ball center r) (Ioo s (s + r ^ 2)),
      ucGaussianWeight a z * spatialGradientSq v Dv z) ≤
      Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + c ^ 2 + 1 / ((2 * r) / 2) ^ 2)) *
        (∫ z in spaceTimeSet (vec3Ball center (2 * r))
          (Ioo s (s + (2 * r) ^ 2)),
          ucGaussianWeight a z * vec3EuclideanNorm (v z) ^ 2) := by
  have hcacci := buGaussian_weighted_caccioppoli_cell hρ ha
    (mul_pos (by norm_num : (0 : ℝ) < 2) hr) hcenter hspace htime
    hweak hcont hc hL2 hineq
  have hrad : (2 * r) / 2 = r := by ring
  have htimeSq : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
  rw [show (2 * r) / 2 = r from hrad,
    show (2 * r) ^ 2 = 4 * r ^ 2 from htimeSq] at hcacci
  simpa [hrad, htimeSq, mul_assoc] using hcacci

private theorem buGaussian_finite_cover_mass_bound
    {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} {P : Finset ι} {S U : Set X} {A B : ι → Set X}
    {fG fM mass W G V : X → ℝ} {K M : ℝ}
    (hTargetEq : (∫ x in S, fG x ∂μ) = ∫ x in S, W x * G x ∂μ)
    (hcover : (∫ x in S, fG x ∂μ) ≤ ∑ p ∈ P, ∫ x in A p, fG x ∂μ)
    (hgradEq : ∀ p ∈ P, (∫ x in A p, fG x ∂μ) =
      ∫ x in A p, W x * G x ∂μ)
    (hcell : ∀ p ∈ P, (∫ x in A p, W x * G x ∂μ) ≤
      K * (∫ x in B p, W x * V x ∂μ))
    (hmassEq : ∀ p ∈ P, (∫ x in B p, fM x ∂μ) =
      ∫ x in B p, W x * V x ∂μ)
    (hMsum : (∑ p ∈ P, ∫ x in B p, fM x ∂μ) ≤ M * ∫ x, fM x ∂μ)
    (hMassIntegral : (∫ x, fM x ∂μ) = ∫ x in U, mass x ∂μ)
    (hK : 0 ≤ K) :
    (∫ x in S, W x * G x ∂μ) ≤ K * (M * (∫ x in U, mass x ∂μ)) := by
  classical
  have hgradSumEq : (∑ p ∈ P, ∫ x in A p, fG x ∂μ) =
      ∑ p ∈ P, ∫ x in A p, W x * G x ∂μ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hgradEq p hp
  have hmassSumEq : (∑ p ∈ P, ∫ x in B p, fM x ∂μ) =
      ∑ p ∈ P, ∫ x in B p, W x * V x ∂μ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hmassEq p hp
  have hsumCacci : (∑ p ∈ P, ∫ x in A p, W x * G x ∂μ) ≤
      K * ∑ p ∈ P, ∫ x in B p, W x * V x ∂μ := by
    calc
      _ ≤ ∑ p ∈ P, K * ∫ x in B p, W x * V x ∂μ := by
        apply Finset.sum_le_sum
        intro p hp
        exact hcell p hp
      _ = _ := by rw [Finset.mul_sum]
  have hMassOverlap : (∑ p ∈ P, ∫ x in B p, W x * V x ∂μ) ≤
      M * ∫ x, fM x ∂μ := by rw [← hmassSumEq]; exact hMsum
  calc
    (∫ x in S, W x * G x ∂μ) = ∫ x in S, fG x ∂μ := hTargetEq.symm
    _ ≤ ∑ p ∈ P, ∫ x in A p, fG x ∂μ := hcover
    _ = ∑ p ∈ P, ∫ x in A p, W x * G x ∂μ := hgradSumEq
    _ ≤ K * ∑ p ∈ P, ∫ x in B p, W x * V x ∂μ := hsumCacci
    _ ≤ K * (M * ∫ x, fM x ∂μ) := by
      apply mul_le_mul_of_nonneg_left hMassOverlap
      exact hK
    _ = K * (M * ∫ x in U, mass x ∂μ) := by rw [hMassIntegral]

/-- Caccioppoli on the finitely many collar cells bounds the transition-shell
gradient by the weighted radial mass. (`eq:bu-gaussian-collar`) -/
theorem buGaussian_transition_shell_gradient_caccioppoli
    {ρ a r c : ℝ} (hρ : 4 < ρ) (ha : 0 < a) (hr : 0 < r)
    (hrle : r ≤ 1 / 16) (hc : 0 ≤ c)
    {v : ParabolicPoint → Vec3}
    {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtv : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo (1 / 6) 2)
      v Dv D2v Dtv)
    (hcont : ContinuousOn v (vec3Ball 0 ρ ×ˢ Ico (1 / 6) 2))
    (hL2 : (∫⁻ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
      ‖v z‖ₑ ^ (2 : ℝ) + ‖Dv z‖ₑ ^ (2 : ℝ) +
        ‖D2v z‖ₑ ^ (2 : ℝ) + ‖Dtv z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2))),
      vec3EuclideanNorm (ucWeakHeatVector D2v Dtv z) ≤
        c * (vec3EuclideanNorm (v z) +
          Real.sqrt (spatialGradientSq v Dv z))) :
    (∫ z in spaceTimeSet
      {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4} (Ioo (1 / 6) (23 / 12)),
      ucGaussianWeight a z * spatialGradientSq v Dv z) ≤
      (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
        36 * ρ ^ 2 * (2 * r) ^ 2)) *
        (256 * (1 + c ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
      (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ) *
      (∫ z in spaceTimeSet (vec3Ball 0 ρ) (Ioo (1 / 6) 2),
        buGaussianRadialWeightedMass ρ a v z) := by
  let σ : ℝ := 1 / 6
  let δ : ℝ := r ^ 2
  let T : ℝ := 23 / 12
  let U : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2)
  let S : Set ParabolicPoint := spaceTimeSet
    {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
      vec3EuclideanNorm y ≤ 3 * ρ / 4} (Ioo σ T)
  let W : ParabolicPoint → ℝ := ucGaussianWeight a
  let V : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (v z) ^ 2
  let G : ParabolicPoint → ℝ := fun z => spatialGradientSq v Dv z
  obtain ⟨Y, hY⟩ := exists_buGaussian_transition_cover_vec3 ρ r hρ hr hrle
  let J : Finset ℕ := Finset.range (buGaussianTimeGridCount σ T δ)
  let P := Y.product J
  let Uinner := buGaussianShellInnerCell r
  let Uouter := buGaussianShellOuterCell r
  let fG : ParabolicPoint → ℝ := U.indicator (fun z => W z * G z)
  let fM : ParabolicPoint → ℝ := U.indicator (buGaussianRadialWeightedMass ρ a v)
  have hσ : σ = 1 / 6 := rfl
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hTσ : σ < T := by norm_num [σ, T]
  have hρ_pos : 0 < ρ := by linarith only [hρ]
  have hmargin : T + 5 * δ ≤ 2 := by
    have hrSq : r ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).2 hrle
    dsimp [T, δ]
    nlinarith only [hrSq]
  have hUopen : IsOpen (vec3Ball 0 ρ) := isOpen_vec3Ball 0 ρ
  have hIopen : IsOpen (Ioo σ 2) := isOpen_Ioo
  have hShellSpatialMeas : MeasurableSet
      {y : Vec3 | 13 * ρ / 20 ≤ vec3EuclideanNorm y ∧
        vec3EuclideanNorm y ≤ 3 * ρ / 4} := by
    exact (measurableSet_le continuous_const.measurable
      continuous_vec3EuclideanNorm.measurable).inter
      (measurableSet_le continuous_vec3EuclideanNorm.measurable
        continuous_const.measurable)
  have hSmeas : MeasurableSet S := by
    exact hShellSpatialMeas.prod measurableSet_Ioo
  have hSsubsetU : S ⊆ U := by
    rintro z ⟨hy, ht⟩
    constructor
    · change vec3EuclideanNorm (z.1 - 0) < ρ
      rw [sub_zero]
      have hnorm := hy.2
      nlinarith only [hnorm, hρ]
    · exact ⟨ht.1, lt_trans ht.2 (by norm_num [T])⟩
  have hTargetEq : (∫ z in S, fG z ∂volume) = ∫ z in S, W z * G z ∂volume :=
    setIntegral_congr_fun hSmeas (fun z hz => by simp [fG, hSsubsetU hz])
  obtain ⟨hUmeas, hWGglobal, hMglobal, htimepos, hGnonneg, hMnonneg⟩ :=
    buGaussian_shell_weighted_data ha hweak hL2
  have hMassIntegral : (∫ z, fM z ∂volume) =
      ∫ z in U, buGaussianRadialWeightedMass ρ a v z ∂volume := by
    change (∫ z, U.indicator (buGaussianRadialWeightedMass ρ a v) z ∂volume) = _
    exact integral_indicator hUmeas
  have hBmeas : ∀ p ∈ Y, MeasurableSet (vec3Ball p.2 (2 * r)) := by
    intro p hp
    exact vec3Ball_measurable p.2 (2 * r)
  have hTmeas : ∀ j ∈ J,
      MeasurableSet (buGaussianTimeGridOuter σ δ j) := by
    intro j hj
    exact measurableSet_Ioo
  have hspacecount : ∀ y : Vec3,
      (∑ p ∈ Y, if y ∈ vec3Ball p.2 (2 * r) then 1 else 0) ≤
        Besicovitch.multiplicity BUGaussianSpace ^ 2 := by
    intro y
    have hcount : (∑ p ∈ Y, if y ∈ vec3Ball p.2 (2 * r) then 1 else 0) =
        (Y.filter fun p => y ∈ vec3Ball p.2 (2 * r)).card := by
      simp
    rw [hcount]
    exact hY.2.2.2.2 y
  have htimecount : ∀ s : ℝ,
      (∑ j ∈ J, if s ∈ buGaussianTimeGridOuter σ δ j then 1 else 0) ≤ 8 := by
    intro s
    exact buGaussian_time_grid_outer_multiplicity hδ J s
  have hMsum := integral_sum_le_of_cylinder_product_multiplicity
    (Y := Y) (J := J) (B := fun p => vec3Ball p.2 (2 * r))
    (T := fun j => buGaussianTimeGridOuter σ δ j)
    (N := Besicovitch.multiplicity BUGaussianSpace ^ 2) (K := 8)
    fM hMglobal hMnonneg hBmeas hTmeas hspacecount htimecount
  have hUouter (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) : Uouter p ⊆ U := by
    rcases Finset.mem_product.mp hp with ⟨hpY, hpJ⟩
    intro z hz
    rcases hz with ⟨hy, hs⟩
    constructor
    · exact hY.2.2.2.1 p.1 hpY hy
    · have hTcell := buGaussian_time_grid_outer_subset hTσ hδ hmargin
        p.2 (Finset.mem_range.mp hpJ)
      exact hTcell hs
  have hUinner (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) : Uinner p ⊆ U := by
    have houter := hUouter p hp
    intro z hz
    apply houter
    rcases hz with ⟨hy, hs⟩
    refine ⟨vec3Ball_mono (by nlinarith only [hr]) hy, ?_⟩
    have hδnonneg : 0 ≤ δ := hδ.le
    have htime : buGaussianTimeGridInner σ δ p.2 ⊆
        buGaussianTimeGridOuter σ δ p.2 := by
      intro s hs
      rcases hs with ⟨hlo, hhi⟩
      dsimp [buGaussianTimeGridInner, buGaussianTimeGridOuter,
        buGaussianTimeGridStart] at *
      constructor
      · exact hlo
      · linarith only [hhi, hδnonneg]
    exact htime hs
  have hUouterMeas (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) : MeasurableSet (Uouter p) := by
    rcases Finset.mem_product.mp hp with ⟨hpY, hpJ⟩
    exact (vec3Ball_measurable p.1.2 (2 * r)).prod measurableSet_Ioo
  have hUinnerMeas (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) : MeasurableSet (Uinner p) := by
    rcases Finset.mem_product.mp hp with ⟨hpY, hpJ⟩
    exact (vec3Ball_measurable p.1.2 r).prod measurableSet_Ioo
  have hcover : ∀ z ∈ S, ∃ p ∈ P, z ∈ Uinner p := by
    intro z hz
    rcases hz with ⟨hy, hs⟩
    obtain ⟨q, hqY, hqball⟩ := hY.2.2.1 z.1 hy.1 hy.2
    obtain ⟨j, hjJ, hjtime⟩ := buGaussian_time_grid_covers hTσ hδ z.2 hs
    refine ⟨(q, j), Finset.mem_product.mpr ⟨hqY, hjJ⟩, ?_⟩
    exact ⟨hqball, hjtime⟩
  have hgradCover := integral_le_sum_of_finite_cover
    (μ := volume) (S := S) (I := P) (U := Uinner) (f := fG)
    hWGglobal hGnonneg hSmeas
    (fun p hp => hUinnerMeas p hp)
    hcover
  have hgradEq (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) :
      (∫ z in Uinner p, fG z ∂volume) =
        (∫ z in Uinner p, W z * G z ∂volume) := by
    apply setIntegral_congr_fun (hUinnerMeas p hp)
    intro z hz
    simp [fG, hUinner p hp hz]
  have hmassEq (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) :
      (∫ z in Uouter p, fM z ∂volume) =
        (∫ z in Uouter p, W z * V z ∂volume) := by
    apply setIntegral_congr_fun (hUouterMeas p hp)
    intro z hz
    have hUz := hUouter p hp hz
    have hradial : ρ / 2 ≤ vec3EuclideanNorm z.1 := by
      rcases Finset.mem_product.mp hp with ⟨hpY, hpJ⟩
      have hcenter := hY.2.1 p.1 hpY
      have hdist : vec3EuclideanNorm (z.1 - p.1.2) < 2 * r := hz.1
      have hnormeq : vec3EuclideanNorm (p.1.2 - z.1) =
          vec3EuclideanNorm (z.1 - p.1.2) := by
        rw [show p.1.2 - z.1 = -(z.1 - p.1.2) by abel,
          vec3EuclideanNorm_neg]
      have htri := vec3EuclideanNorm_add_le (p.1.2 - z.1) z.1
      have heq : (p.1.2 - z.1) + z.1 = p.1.2 := by module
      rw [heq] at htri
      have hgap : ρ / 2 + 2 * r ≤ 13 * ρ / 20 := by
        nlinarith only [hρ, hrle]
      rw [hnormeq] at htri
      linarith only [hcenter, hdist, htri, hgap]
    simp [fM, buGaussianRadialWeightedMass, W, V, hUz, hradial]
  have hcell (p : (Fin (Besicovitch.multiplicity BUGaussianSpace) × Vec3) × ℕ)
      (hp : p ∈ P) :
      (∫ z in Uinner p, W z * G z ∂volume) ≤
        (Real.exp (2 * (56 * a * (2 * r) ^ 2 + 12 * ρ * (2 * r) +
          36 * ρ ^ 2 * (2 * r) ^ 2)) *
          (256 * (1 + c ^ 2 + 1 / ((2 * r) / 2) ^ 2))) *
          (∫ z in Uouter p, W z * V z ∂volume) := by
    rcases Finset.mem_product.mp hp with ⟨hpY, hpJ⟩
    have hsp : vec3Ball p.1.2 (2 * r) ⊆ vec3Ball 0 ρ :=
      hY.2.2.2.1 p.1 hpY
    have htime :
        Ioo (buGaussianTimeGridStart σ δ p.2)
          (buGaussianTimeGridStart σ δ p.2 + (2 * r) ^ 2) ⊆ Ioo σ 2 := by
      have hpJ' : p.2 < buGaussianTimeGridCount σ T δ := Finset.mem_range.mp hpJ
      have ht := buGaussian_time_grid_outer_subset hTσ hδ hmargin p.2 hpJ'
      have hend : buGaussianTimeGridStart σ δ p.2 + (2 * r) ^ 2 =
          buGaussianTimeGridStart σ δ p.2 + 4 * δ := by
        dsimp [δ]
        ring
      rw [hend]
      simpa [buGaussianTimeGridOuter, buGaussianTimeGridStart, δ] using ht
    have hfour : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
    simpa [Uinner, Uouter, buGaussianShellInnerCell, buGaussianShellOuterCell,
      buGaussianTimeGridInner, buGaussianTimeGridOuter, buGaussianTimeGridStart,
      σ, δ, hfour, G, V, W] using
      buGaussian_shell_single_cell_bound hρ_pos ha hr (hY.1 p.1 hpY) hsp htime
        hweak hcont hc hL2 hineq
  let Kcell : ℝ := Real.exp (2 * (56 * a * (2 * r) ^ 2 +
      12 * ρ * (2 * r) + 36 * ρ ^ 2 * (2 * r) ^ 2)) *
      (256 * (1 + c ^ 2 + 1 / ((2 * r) / 2) ^ 2))
  have hSgradient := buGaussian_finite_cover_mass_bound
    (μ := volume) (P := P) (S := S) (U := U)
    (A := Uinner) (B := Uouter) (fG := fG) (fM := fM)
    (mass := buGaussianRadialWeightedMass ρ a v) (W := W) (G := G)
    (V := V) (K := Kcell)
    (M := (8 * Besicovitch.multiplicity BUGaussianSpace ^ 2 : ℝ))
    hTargetEq hgradCover hgradEq hcell hmassEq (by
      simpa [P, Uouter, buGaussianShellOuterCell, σ, δ] using hMsum) hMassIntegral (by
      dsimp [Kcell]
      positivity)
  simpa [S, U, σ, T, Kcell, mul_assoc] using hSgradient

end ESS

end
