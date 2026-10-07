/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.PositiveBoundUnitEquations
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsTop
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsRestriction
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyResult

/-!
# Local velocity bounds on backward cylinders

Two local bounds from the proof of `lem:pv-positive-bound`, for a Leray–Hopf
solution with the critical L^∞_t L³_x bound and a slab L^{3/2} pressure
satisfying the momentum identity, on backward cylinders
B_{R/2}(x₀) × (t₀ - R²/4, t₀) with R² ≤ t₀ ≤ T (the cylinder may end at the
terminal time):

* `pv_local_bound_of_essLocal`: `thm:ess-local`, applied to the rescaled fields,
  gives some finite essential bound;
* `pv_epsilon_bound`: when the normalized velocity and pressure energy of the
  cylinder is small, `lem:lei-L4` and `lem:thmA-top` give the bound C / R
  with an absolute constant C.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The hypotheses of `thm:ess-local` for the rescaled fields on the unit
cylinder. -/
private theorem pv_unit_essLocal_data {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hLH : IsLerayHopfSolution T a u Du)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpMom : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    (x₀ : Vec3) {t₀ R : ℝ} (hR : 0 < R) (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) :
    let uR := CKN.rescaleVelocity R (x₀, t₀) u
    let DuR := CKN.rescaleGradient R (x₀, t₀) Du
    let pR := CKN.rescalePressure R (x₀, t₀) p
    AEStronglyMeasurable uR
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) ∧
    AEStronglyMeasurable DuR
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) ∧
    AEStronglyMeasurable pR
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) ∧
    essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖uR (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤ ∧
    (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖uR z‖ₑ ^ (2 : ℝ) + ‖DuR z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    MemLp pR (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) ∧
    essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (uR (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤ ∧
    (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => uR (x, t) i) (fun x => DuR (x, t) i)) ∧
    (∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, uR z i * spatialPartial ψ i z = 0) ∧
    (∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, uR z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              uR z i * uR z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              DuR z i j * spatialPartial (fun y => φ y i) j z
          - pR z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) := by
  intro uR DuR pR
  have hdata := pv_lerayHopf_suitableData hLH hpLp
  have hU := pv_unit_aestronglyMeasurable_comp x₀ hR hlow hup hLH.2.2.1
  have hDU := pv_unit_aestronglyMeasurable_comp x₀ hR hlow hup hLH.2.2.2.1
  have hP := pv_unit_pressure_memLp x₀ hR hlow hup hpLp
  refine ⟨hU.const_smul R, hDU.const_smul (R ^ 2), hP.aestronglyMeasurable,
    pv_unit_L2_essSup_lt_top x₀ hR hlow hup hLH.2.2.2.2.1,
    pv_unit_energy_lt_top x₀ hR hlow hup hLH.2.2.2.2.2.1, hP,
    pv_unit_L3_essSup_lt_top x₀ hR hlow hup hL3,
    pv_unit_weakGradient x₀ hR hlow hup hLH.2.2.1 hLH.2.2.2.1 hLH.2.2.2.2.2.2.1,
    pv_unit_divergence x₀ hR hlow hup
      (fun ψ hψ => pv_lerayHopf_divergence_spaceTime hLH hdata ψ hψ),
    pv_unit_momentum x₀ hR hlow hup
      (fun φ hφ => ⟨CKN.momentum_integrand_integrableOn_of_data hdata hφ, hpMom φ hφ⟩)⟩

/-- An essential bound for the rescaled velocity on a small unit-scale
cylinder gives the corresponding bound for the velocity on the original
cylinder. -/
theorem pv_ae_bound_of_rescaled {u : ParabolicPoint → Vec3} (x₀ : Vec3)
    {t₀ R α β B : ℝ} (hR : 0 < R)
    (hB : ∀ᵐ y ∂volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) α) (Ioo (-β) 0)),
      vec3EuclideanNorm (CKN.rescaleVelocity R (x₀, t₀) u y) ≤ B) :
    ∀ᵐ z ∂volume.restrict
        (spaceTimeSet (vec3Ball x₀ (R * α)) (Ioo (t₀ - R ^ 2 * β) t₀)),
      vec3EuclideanNorm (u z) ≤ B / R := by
  rw [← pv_ae_scalingParabolic_iff R hR (x₀, t₀)]
  have hsub : CKN.scalingParabolic R (x₀, t₀) ⁻¹'
      spaceTimeSet (vec3Ball x₀ (R * α)) (Ioo (t₀ - R ^ 2 * β) t₀) ⊆
      spaceTimeSet (vec3Ball (0 : Vec3) α) (Ioo (-β) 0) := by
    intro y hy
    obtain ⟨hyx, hyt⟩ := hy
    have hR2 : 0 < R ^ 2 := by positivity
    change vec3EuclideanNorm (x₀ + R • y.1 - x₀) < R * α at hyx
    change t₀ - R ^ 2 * β < t₀ + R ^ 2 * y.2 ∧ t₀ + R ^ 2 * y.2 < t₀ at hyt
    rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos hR] at hyx
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (y.1 - 0) < α
      rw [sub_zero]
      exact lt_of_mul_lt_mul_left hyx hR.le
    · have h : R ^ 2 * (-β) < R ^ 2 * y.2 := by linarith only [hyt.1]
      exact lt_of_mul_lt_mul_left h hR2.le
    · have h : R ^ 2 * y.2 < R ^ 2 * 0 := by linarith only [hyt.2]
      exact lt_of_mul_lt_mul_left h hR2.le
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hB] with y hy
  have hv : CKN.rescaleVelocity R (x₀, t₀) u y = R • u (CKN.scalingParabolic R (x₀, t₀) y) :=
    rfl
  rw [hv, vec3EuclideanNorm_smul, abs_of_pos hR] at hy
  rw [le_div_iff₀ hR, mul_comm]
  exact hy

/-- `thm:ess-local`, applied to the rescaled fields, bounds the velocity
essentially on a backward cylinder, which may end at the terminal time. -/
theorem pv_local_bound_of_essLocal
    (hE1 : ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
    ∀ p : ParabolicPoint → ℝ,
      AEStronglyMeasurable u
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable Du
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable p
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
        HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
      (∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict
            (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
          ParabolicHolderVecOn
            (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ)
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hLH : IsLerayHopfSolution T a u Du)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpMom : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0)
    (hL3 : essSup (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    (x₀ : Vec3) {t₀ R : ℝ} (hR : 0 < R) (hlow : R ^ 2 ≤ t₀) (hup : t₀ ≤ T) :
    ∃ B : ℝ, ∀ᵐ z ∂volume.restrict
        (spaceTimeSet (vec3Ball x₀ (R * (1 / 2))) (Ioo (t₀ - R ^ 2 * (1 / 4)) t₀)),
      vec3EuclideanNorm (u z) ≤ B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    pv_unit_essLocal_data hLH hpLp hpMom hL3 x₀ hR hlow hup
  obtain ⟨_, _, _, w, hw, B, _, _, _, hbound, _⟩ :=
    hE1 _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  refine ⟨B / R, pv_ae_bound_of_rescaled x₀ hR ?_⟩
  have hsub : spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2)) (Ioo (-(1 / 4)) 0) ⊆
      parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    refine ⟨hy, ?_, le_of_lt hs.2⟩
    have h := hs.1
    norm_num at h ⊢
    exact h
  have hmeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) (1 / 2)) (Ioo (-(1 / 4 : ℝ)) 0)) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioo
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hw,
    ae_restrict_mem hmeas] with y hy hyS
  rw [← hy]
  exact hbound y (subset_closure (hsub hyS))

private theorem pv_sq_rpow_threeHalves {R : ℝ} (hR : 0 ≤ R) :
    (R ^ 2) ^ (3 / 2 : ℝ) = R ^ 3 := by
  rw [← Real.rpow_two R, ← Real.rpow_mul hR]
  norm_num

/-- The velocity–pressure energy density scales with the factor R³. -/
private theorem pv_energyDensity_rescale {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {R : ℝ} (hR : 0 < R) (z₀ z : ParabolicPoint) :
    ENNReal.ofReal (vec3EuclideanNorm (CKN.rescaleVelocity R z₀ u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |CKN.rescalePressure R z₀ p z| ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (R ^ 3) *
        (ENNReal.ofReal (vec3EuclideanNorm (u (CKN.scalingParabolic R z₀ z))) ^ (3 : ℝ) +
          ENNReal.ofReal |p (CKN.scalingParabolic R z₀ z)| ^ (3 / 2 : ℝ)) := by
  have hv : CKN.rescaleVelocity R z₀ u z = R • u (CKN.scalingParabolic R z₀ z) := rfl
  have hq : CKN.rescalePressure R z₀ p z = R ^ 2 * p (CKN.scalingParabolic R z₀ z) := rfl
  rw [hv, hq, vec3EuclideanNorm_smul, abs_of_pos hR, abs_mul,
    abs_of_pos (pow_pos hR 2), ENNReal.ofReal_mul hR.le,
    ENNReal.ofReal_mul (pow_pos hR 2).le,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hR.le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (pow_pos hR 2).le (by norm_num),
    pv_sq_rpow_threeHalves hR.le, mul_add]
  norm_num

/-- The rescaled velocity–pressure energy of the half cylinder is R⁻²
times the energy of the original cylinder of radius R / 2, up to the
inclusion of cylinders. -/
private theorem pv_goodPointEnergy_rescale_le {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} (x₀ : Vec3) {t₀ R : ℝ} (hR : 0 < R) :
    goodPointEnergy (CKN.rescaleVelocity R (x₀, t₀) u)
        (CKN.rescalePressure R (x₀, t₀) p) 0 0 (1 / 2) ≤
      ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal (R⁻¹ ^ 5) *
        goodPointEnergy u p x₀ t₀ (R / 2)) := by
  have hsub : parabolicCylinder (0 : Vec3) 0 (1 / 2) ⊆
      CKN.scalingParabolic R (x₀, t₀) ⁻¹' parabolicCylinder x₀ t₀ (R / 2) := by
    rintro ⟨y, s⟩ ⟨hy, hs1, hs2⟩
    have hR2 : 0 < R ^ 2 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · change vec3EuclideanNorm (x₀ + R • y - x₀) < R / 2
      rw [add_sub_cancel_left, vec3EuclideanNorm_smul, abs_of_pos hR]
      have hy' : vec3EuclideanNorm y < 1 / 2 := by simpa using hy
      nlinarith only [hy', hR]
    · change t₀ - (R / 2) ^ 2 < t₀ + R ^ 2 * s
      have h : R ^ 2 * (0 - (1 / 2) ^ 2) < R ^ 2 * s := mul_lt_mul_of_pos_left hs1 hR2
      nlinarith only [h]
    · change t₀ + R ^ 2 * s ≤ t₀
      have h : R ^ 2 * s ≤ R ^ 2 * 0 := mul_le_mul_of_nonneg_left hs2 hR2.le
      linarith only [h]
  unfold goodPointEnergy
  calc
    _ ≤ ∫⁻ z in CKN.scalingParabolic R (x₀, t₀) ⁻¹' parabolicCylinder x₀ t₀ (R / 2),
          ENNReal.ofReal (vec3EuclideanNorm
              (CKN.rescaleVelocity R (x₀, t₀) u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |CKN.rescalePressure R (x₀, t₀) p z| ^ (3 / 2 : ℝ) :=
        lintegral_mono_set hsub
    _ = ∫⁻ z in CKN.scalingParabolic R (x₀, t₀) ⁻¹' parabolicCylinder x₀ t₀ (R / 2),
          ENNReal.ofReal (R ^ 3) *
            (ENNReal.ofReal (vec3EuclideanNorm
                (u (CKN.scalingParabolic R (x₀, t₀) z))) ^ (3 : ℝ) +
              ENNReal.ofReal |p (CKN.scalingParabolic R (x₀, t₀) z)| ^ (3 / 2 : ℝ)) :=
        lintegral_congr (fun z => pv_energyDensity_rescale hR (x₀, t₀) z)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        pv_lintegral_scalingParabolic R hR (x₀, t₀) _
          (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))]

/-- Small normalized velocity–pressure energy on a backward cylinder gives the
bound C / R on the quarter cylinder, with absolute constants, by
`lem:lei-L4` and `lem:thmA-top`. The cylinder may end at the terminal time. -/
theorem pv_epsilon_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
      ∀ {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
        {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ},
      IsLerayHopfSolution T a u Du →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      essSup (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      ∀ (x₀ : Vec3) {t₀ R : ℝ}, 0 < R → R ^ 2 ≤ t₀ → t₀ ≤ T →
      goodPointEnergy u p x₀ t₀ (R / 2) ≤ ENNReal.ofReal (η * R ^ 2) →
      ∀ᵐ z ∂volume.restrict
          (spaceTimeSet (vec3Ball x₀ (R * (1 / 4))) (Ioo (t₀ - R ^ 2 * (1 / 16)) t₀)),
        vec3EuclideanNorm (u z) ≤ C / R := by
  obtain ⟨ε₀, _, C₄, hε₀, _, _, hC₄, hreg⟩ := epsilonRegularityL3_top
  refine ⟨ε₀ / 64, 4 * C₄, by positivity, by positivity, ?_⟩
  intro T a u Du p hLH hpLp hpMom hL3 x₀ t₀ R hR hlow hup hsmall
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    pv_unit_essLocal_data hLH hpLp hpMom hL3 x₀ hR hlow hup
  have hsuit := (leiL4_of_essLocalData (r := 3 / 4) (by norm_num) (by norm_num)
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).2.2
  have hsuit' := isSuitableWeakSolution_restrict hsuit (isOpen_vec3Ball _ _) isOpen_Ioo
    ordConnected_Ioo (subset_refl _)
    (Ioo_subset_Ioo (by norm_num : (-1 : ℝ) ≤ 0 - (3 / 4) ^ 2) (le_refl (0 : ℝ)))
  have hscale := pv_goodPointEnergy_rescale_le (u := u) (p := p) x₀ (t₀ := t₀) hR
  have hsmallR : ENNReal.ofReal ((1 / 2 : ℝ)⁻¹ ^ 2) *
      goodPointEnergy (CKN.rescaleVelocity R (x₀, t₀) u)
        (CKN.rescalePressure R (x₀, t₀) p) 0 0 (1 / 2) < ENNReal.ofReal (ε₀ / 8) := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ)⁻¹ ^ 2) * (ENNReal.ofReal (R ^ 3) *
          (ENNReal.ofReal (R⁻¹ ^ 5) * ENNReal.ofReal (ε₀ / 64 * R ^ 2))) := by
        gcongr
        exact hscale.trans (by gcongr)
      _ = ENNReal.ofReal (ε₀ / 16) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
      _ < ENNReal.ofReal (ε₀ / 8) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith only [hε₀])
  obtain ⟨w, hw, hbound, _⟩ := hreg 0 0 (3 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num)
    hsuit' hsmallR
  apply pv_ae_bound_of_rescaled x₀ hR
  have hset : goodPointPastCylinder (0 : Vec3) 0 (1 / 2 / 2) =
      spaceTimeSet (vec3Ball (0 : Vec3) (1 / 4)) (Ioo (-(1 / 16)) 0) := by
    ext ⟨y, s⟩
    simp only [goodPointPastCylinder, spaceTimeSet]
    norm_num
  rw [← hset]
  have hmeas : MeasurableSet (goodPointPastCylinder (0 : Vec3) 0 (1 / 2 / 2)) := by
    rw [hset]
    exact (vec3Ball_measurable _ _).prod measurableSet_Ioo
  filter_upwards [hw, ae_restrict_mem hmeas] with y hy hyS
  rw [← hy]
  have hb := hbound y (subset_closure hyS)
  have hc : 2 * C₄ * (1 / 2 : ℝ)⁻¹ = 4 * C₄ := by norm_num; ring
  rw [hc] at hb
  exact hb

end ESS
