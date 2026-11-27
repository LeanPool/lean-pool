/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Lorentz covariance of the free-field model

Boosts along `𝐞₁` and spatial orthogonal maps (rotations and reflections) act on spacetime test
functions by `F ↦ F ∘ Λ` and on momenta through the mass shell.  This module proves the covariance
of the model of `FreeField/Defs.lean` under these maps (hence under their finite compositions, by
applying the results repeatedly).

* `boost η`: the boost of rapidity `η` along `𝐞₁`, a continuous linear automorphism of
  spacetime, `(t, 𝐱) ↦ (t cosh η + x₁ sinh η, 𝐱 + (t sinh η + x₁ (cosh η - 1)) 𝐞₁)` with
  `x₁ = ⟪𝐞₁, 𝐱⟫`; `boost_symm`, `boost_neg_boost`: `Λ(η)⁻¹ = Λ(-η)`; `minkowskiForm_boost`:
  it preserves the Minkowski form; `det_boost`, `measurePreserving_boost`: it has determinant
  `1` and preserves Lebesgue measure on spacetime.
* `shellBoost m η 𝐩 = 𝐩 + (ω_m(𝐩) sinh η + p₁ (cosh η - 1)) 𝐞₁`, the induced map of the mass
  shell: `boost_onShell`: `Λ(η)(ω_m(𝐩), 𝐩) = (ω_m(𝐩'), 𝐩')`; `dispersion_shellBoost`:
  `ω_m(𝐩') = ω_m(𝐩) cosh η + p₁ sinh η`; `shellBoost_neg_shellBoost`: `S(-η)` inverts `S(η)`.
* `integral_shellBoost_mul_weight` (key step): for `m ≠ 0` the measure `d³p / (2(2π)³ ω_m(𝐩))`
  is invariant under `shellBoost m η`, for every integrand (change of variables with Jacobian
  `det dS(𝐩) = ω_m(𝐩') / ω_m(𝐩)`, `det_shellBoostDeriv`).
* `RealTestFunction.compCLE`: `F ∘ Λ` for a continuous linear automorphism `Λ` of spacetime;
  `oneParticle_boost`: `κ_m(F ∘ Λ(η))(𝐩) = κ_m F(S_η 𝐩)`.
* `oneParticleInner_boost`: `⟨κ_m(F ∘ Λ(η)), κ_m(G ∘ Λ(η))⟩ = ⟨κ_m F, κ_m G⟩` for `m ≠ 0`.
* Rotations `(t, 𝐱) ↦ (t, R𝐱)`: `oneParticle_spatialRotation`,
  `oneParticleInner_spatialRotation` (every `m`).
* `FreeFieldVacuum.lorentz`: the vacuum system `W'(F) = W(F ∘ Λ)` (same vacuum) for any
  automorphism `Λ` preserving the one-particle inner product, with
  `localAlgebra (V.lorentz Λ _) O = localAlgebra V (Λ ⁻¹' O)`; the instances
  `FreeFieldVacuum.boosted` (`𝔄'(O) = 𝔄(Λ(-η) O)`) and `FreeFieldVacuum.rotated`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-! ### The first spatial unit vector -/

/-- `‖𝐞₁‖ = 1`. -/
theorem norm_e₁ : ‖e₁‖ = 1 := by
  simp [e₁]

/-- `⟪𝐞₁, 𝐞₁⟫ = 1`. -/
theorem inner_e₁_self : ⟪e₁, e₁⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_e₁, one_pow]

/-- `⟪𝐞₁, 𝐯 + c 𝐞₁⟫ = ⟪𝐞₁, 𝐯⟫ + c`. -/
theorem inner_e₁_add_smul (v : EuclideanSpace ℝ (Fin 3)) (c : ℝ) :
    ⟪e₁, v + c • e₁⟫_ℝ = ⟪e₁, v⟫_ℝ + c := by
  rw [inner_add_right, real_inner_smul_right, inner_e₁_self, mul_one]

/-- `⟪𝐮 + a 𝐞₁, 𝐰 + b 𝐞₁⟫ = ⟪𝐮, 𝐰⟫ + b ⟪𝐞₁, 𝐮⟫ + a ⟪𝐞₁, 𝐰⟫ + a b`. -/
theorem inner_add_smul_e₁ (u w : EuclideanSpace ℝ (Fin 3)) (a b : ℝ) :
    ⟪u + a • e₁, w + b • e₁⟫_ℝ = ⟪u, w⟫_ℝ + b * ⟪e₁, u⟫_ℝ + a * ⟪e₁, w⟫_ℝ + a * b := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_e₁_self, real_inner_comm e₁ u]
  ring

/-! ### Boosts along `𝐞₁` -/

/-- The boost of rapidity `η` along `𝐞₁` as a continuous linear map of spacetime:
`(t, 𝐱) ↦ (t cosh η + x₁ sinh η, 𝐱 + (t sinh η + x₁ (cosh η - 1)) 𝐞₁)`, `x₁ = ⟪𝐞₁, 𝐱⟫`. -/
noncomputable def boostCLM (η : ℝ) : Spacetime →L[ℝ] Spacetime :=
  ContinuousLinearMap.prod
    (Real.cosh η • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)) +
      Real.sinh η • (innerSL ℝ e₁).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
    (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)) +
      ContinuousLinearMap.smulRight
        (Real.sinh η • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)) +
          (Real.cosh η - 1) •
            (innerSL ℝ e₁).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))))
        e₁)

/-- The boost in coordinates. -/
theorem boostCLM_apply (η : ℝ) (x : Spacetime) :
    boostCLM η x = (Real.cosh η * x.1 + Real.sinh η * ⟪e₁, x.2⟫_ℝ,
      x.2 + (Real.sinh η * x.1 + (Real.cosh η - 1) * ⟪e₁, x.2⟫_ℝ) • e₁) :=
  rfl

/-- The boosts along `𝐞₁` form a one-parameter group: `Λ(a) Λ(b) = Λ(a + b)`. -/
theorem boostCLM_boostCLM (a b : ℝ) (x : Spacetime) :
    boostCLM a (boostCLM b x) = boostCLM (a + b) x := by
  obtain ⟨t, v⟩ := x
  have hv : ⟪e₁, v + (Real.sinh b * t + (Real.cosh b - 1) * ⟪e₁, v⟫_ℝ) • e₁⟫_ℝ =
      Real.sinh b * t + Real.cosh b * ⟪e₁, v⟫_ℝ := by
    rw [inner_e₁_add_smul]
    ring
  simp only [boostCLM_apply]
  refine Prod.ext ?_ ?_
  · change Real.cosh a * (Real.cosh b * t + Real.sinh b * ⟪e₁, v⟫_ℝ) +
        Real.sinh a * ⟪e₁, v + (Real.sinh b * t + (Real.cosh b - 1) * ⟪e₁, v⟫_ℝ) • e₁⟫_ℝ =
      Real.cosh (a + b) * t + Real.sinh (a + b) * ⟪e₁, v⟫_ℝ
    rw [hv, Real.cosh_add, Real.sinh_add]
    ring
  · change v + (Real.sinh b * t + (Real.cosh b - 1) * ⟪e₁, v⟫_ℝ) • e₁ +
        (Real.sinh a * (Real.cosh b * t + Real.sinh b * ⟪e₁, v⟫_ℝ) +
          (Real.cosh a - 1) *
            ⟪e₁, v + (Real.sinh b * t + (Real.cosh b - 1) * ⟪e₁, v⟫_ℝ) • e₁⟫_ℝ) • e₁ =
      v + (Real.sinh (a + b) * t + (Real.cosh (a + b) - 1) * ⟪e₁, v⟫_ℝ) • e₁
    have hc : (Real.sinh b * t + (Real.cosh b - 1) * ⟪e₁, v⟫_ℝ) +
        (Real.sinh a * (Real.cosh b * t + Real.sinh b * ⟪e₁, v⟫_ℝ) +
          (Real.cosh a - 1) * (Real.sinh b * t + Real.cosh b * ⟪e₁, v⟫_ℝ)) =
        Real.sinh (a + b) * t + (Real.cosh (a + b) - 1) * ⟪e₁, v⟫_ℝ := by
      rw [Real.cosh_add, Real.sinh_add]
      ring
    rw [hv, add_assoc, ← add_smul, hc]

/-- `Λ(0)` is the identity. -/
theorem boostCLM_zero (x : Spacetime) : boostCLM 0 x = x := by
  obtain ⟨t, v⟩ := x
  simp [boostCLM_apply]

/-- `Λ(-η) Λ(η) = 1`. -/
theorem boostCLM_neg_boostCLM (η : ℝ) (x : Spacetime) : boostCLM (-η) (boostCLM η x) = x := by
  rw [boostCLM_boostCLM, neg_add_cancel, boostCLM_zero]

/-- `Λ(η) Λ(-η) = 1`. -/
theorem boostCLM_boostCLM_neg (η : ℝ) (x : Spacetime) : boostCLM η (boostCLM (-η) x) = x := by
  rw [boostCLM_boostCLM, add_neg_cancel, boostCLM_zero]

/-- The boost of rapidity `η` along `𝐞₁` as a continuous linear automorphism of spacetime. -/
noncomputable def boost (η : ℝ) : Spacetime ≃L[ℝ] Spacetime :=
  ContinuousLinearEquiv.equivOfInverse (boostCLM η) (boostCLM (-η))
    (boostCLM_neg_boostCLM η) (boostCLM_boostCLM_neg η)

/-- `Λ(η) x = boostCLM η x`. -/
theorem boost_apply (η : ℝ) (x : Spacetime) : boost η x = boostCLM η x :=
  rfl

/-- `Λ(η)⁻¹ = Λ(-η)`. -/
theorem boost_symm (η : ℝ) : (boost η).symm = boost (-η) :=
  ContinuousLinearEquiv.ext (funext fun _ => rfl)

/-- `Λ(-η) Λ(η) x = x`. -/
theorem boost_neg_boost (η : ℝ) (x : Spacetime) : boost (-η) (boost η x) = x :=
  boostCLM_neg_boostCLM η x

/-- `Λ(η) Λ(-η) x = x`. -/
theorem boost_boost_neg (η : ℝ) (x : Spacetime) : boost η (boost (-η) x) = x :=
  boostCLM_boostCLM_neg η x

/-- `Λ(a) Λ(b) = Λ(a + b)`. -/
theorem boost_boost (a b : ℝ) (x : Spacetime) : boost a (boost b x) = boost (a + b) x :=
  boostCLM_boostCLM a b x

/-! ### The Minkowski form -/

/-- The Minkowski bilinear form `k⁰x⁰ - ⟪𝐤, 𝐱⟫` of signature `(+,-,-,-)`. -/
noncomputable def minkowskiForm (k x : Spacetime) : ℝ :=
  k.1 * x.1 - ⟪k.2, x.2⟫_ℝ

/-- Boosts preserve the Minkowski form. -/
theorem minkowskiForm_boost (η : ℝ) (k x : Spacetime) :
    minkowskiForm (boost η k) (boost η x) = minkowskiForm k x := by
  obtain ⟨k0, kv⟩ := k
  obtain ⟨x0, xv⟩ := x
  have h1 := Real.cosh_sq_sub_sinh_sq η
  simp only [minkowskiForm, boost_apply, boostCLM_apply]
  rw [inner_add_smul_e₁]
  linear_combination (k0 * x0 - ⟪e₁, kv⟫_ℝ * ⟪e₁, xv⟫_ℝ) * h1

/-! ### Determinant and Lebesgue measure -/

/-- Time reversal `(t, 𝐱) ↦ (-t, 𝐱)` as a linear map. -/
noncomputable def timeReversal : Spacetime →ₗ[ℝ] Spacetime where
  toFun x := (-x.1, x.2)
  map_add' x y := by
    refine Prod.ext ?_ rfl
    change -(x.1 + y.1) = -x.1 + -y.1
    exact neg_add x.1 y.1
  map_smul' c x := by
    refine Prod.ext ?_ rfl
    change -(c * x.1) = c * -x.1
    exact (mul_neg c x.1).symm

/-- Time reversal in coordinates. -/
theorem timeReversal_apply (x : Spacetime) : timeReversal x = (-x.1, x.2) :=
  rfl

/-- Time reversal conjugates `Λ(η)` to `Λ(-η)`. -/
theorem boostCLM_neg_apply (a : ℝ) (x : Spacetime) :
    boostCLM (-a) x = timeReversal (boostCLM a (timeReversal x)) := by
  obtain ⟨t, v⟩ := x
  simp only [boostCLM_apply, timeReversal_apply]
  refine Prod.ext ?_ ?_
  · change Real.cosh (-a) * t + Real.sinh (-a) * ⟪e₁, v⟫_ℝ =
      -(Real.cosh a * -t + Real.sinh a * ⟪e₁, v⟫_ℝ)
    rw [Real.cosh_neg, Real.sinh_neg]
    ring
  · change v + (Real.sinh (-a) * t + (Real.cosh (-a) - 1) * ⟪e₁, v⟫_ℝ) • e₁ =
      v + (Real.sinh a * -t + (Real.cosh a - 1) * ⟪e₁, v⟫_ℝ) • e₁
    rw [Real.cosh_neg, Real.sinh_neg, neg_mul, mul_neg]

/-- The boosts along `𝐞₁` have determinant `1`.  (`det Λ(a) det Λ(b) = det Λ(a + b)`, time
reversal gives `det Λ(-η) = det Λ(η)`, so `det Λ(η)² = 1`, and `det Λ(η) = det Λ(η/2)² ≥ 0`.) -/
theorem det_boostCLM (η : ℝ) :
    LinearMap.det (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) = 1 := by
  have hcomp : ∀ a b : ℝ, LinearMap.det (boostCLM a : Spacetime →ₗ[ℝ] Spacetime) *
      LinearMap.det (boostCLM b : Spacetime →ₗ[ℝ] Spacetime) =
      LinearMap.det (boostCLM (a + b) : Spacetime →ₗ[ℝ] Spacetime) := by
    intro a b
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun x => boostCLM_boostCLM a b x
  have hzero : LinearMap.det (boostCLM 0 : Spacetime →ₗ[ℝ] Spacetime) = 1 := by
    have h0 : (boostCLM 0 : Spacetime →ₗ[ℝ] Spacetime) = LinearMap.id :=
      LinearMap.ext fun x => boostCLM_zero x
    rw [h0, LinearMap.det_id]
  have hTT : timeReversal ∘ₗ timeReversal = LinearMap.id :=
    LinearMap.ext fun x => Prod.ext (neg_neg x.1) rfl
  have hT : LinearMap.det timeReversal * LinearMap.det timeReversal = 1 := by
    rw [← LinearMap.det_comp, hTT, LinearMap.det_id]
  have hneg : LinearMap.det (boostCLM (-η) : Spacetime →ₗ[ℝ] Spacetime) =
      LinearMap.det (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) := by
    have hconj : (boostCLM (-η) : Spacetime →ₗ[ℝ] Spacetime) =
        timeReversal ∘ₗ (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) ∘ₗ timeReversal :=
      LinearMap.ext fun x => boostCLM_neg_apply η x
    rw [hconj, LinearMap.det_comp, LinearMap.det_comp]
    linear_combination LinearMap.det (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) * hT
  have hsq : LinearMap.det (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) ^ 2 = 1 := by
    have h := hcomp (-η) η
    rw [neg_add_cancel, hzero, hneg] at h
    linear_combination h
  have hnonneg : 0 ≤ LinearMap.det (boostCLM η : Spacetime →ₗ[ℝ] Spacetime) := by
    have h := hcomp (η / 2) (η / 2)
    rw [add_halves] at h
    rw [← h]
    exact mul_self_nonneg _
  nlinarith [hsq, hnonneg]

/-- `det Λ(η) = 1`. -/
theorem det_boost (η : ℝ) : (boost η : Spacetime →L[ℝ] Spacetime).det = 1 :=
  det_boostCLM η

/-- Boosts preserve Lebesgue measure on spacetime. -/
theorem measurePreserving_boost (η : ℝ) :
    MeasurePreserving (boost η) (volume : Measure Spacetime) volume := by
  have : (volume : Measure Spacetime).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(boost η).continuous.measurable, ?_⟩
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Spacetime)
    (f := (boostCLM η : Spacetime →ₗ[ℝ] Spacetime)) (by rw [det_boostCLM]; exact one_ne_zero)
  rw [det_boostCLM, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

/-- Change of variables `y = Λ(η) x` in `d⁴x`. -/
theorem integral_comp_boost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ)
    (g : Spacetime → E) : ∫ x, g (boost η x) = ∫ x, g x :=
  (measurePreserving_boost η).integral_comp (boost η).toHomeomorph.measurableEmbedding g

/-! ### The mass shell and the boosted momentum -/

/-- `ω_m(𝐩)² = m² + |𝐩|²`. -/
theorem dispersion_sq (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    dispersion m p ^ 2 = m ^ 2 + ‖p‖ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg m) (sq_nonneg ‖p‖))

/-- `ω_m(𝐩) > 0` for `m ≠ 0`. -/
theorem dispersion_pos {m : ℝ} (hm : m ≠ 0) (p : EuclideanSpace ℝ (Fin 3)) :
    0 < dispersion m p :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hm) (sq_nonneg ‖p‖))

/-- `|𝐩| ≤ ω_m(𝐩)`. -/
theorem norm_le_dispersion (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ‖p‖ ≤ dispersion m p :=
  calc ‖p‖ = Real.sqrt (‖p‖ ^ 2) := (Real.sqrt_sq (norm_nonneg p)).symm
    _ ≤ Real.sqrt (m ^ 2 + ‖p‖ ^ 2) := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg m))
    _ = dispersion m p := rfl

/-- `|⟪𝐞₁, 𝐩⟫| ≤ |𝐩|`. -/
theorem abs_inner_e₁_le (p : EuclideanSpace ℝ (Fin 3)) : |⟪e₁, p⟫_ℝ| ≤ ‖p‖ := by
  have h := abs_real_inner_le_norm e₁ p
  rwa [norm_e₁, one_mul] at h

/-- `‖𝐩 + c 𝐞₁‖² = ‖𝐩‖² + 2 c ⟪𝐞₁, 𝐩⟫ + c²`. -/
theorem norm_add_smul_e₁_sq (p : EuclideanSpace ℝ (Fin 3)) (c : ℝ) :
    ‖p + c • e₁‖ ^ 2 = ‖p‖ ^ 2 + 2 * c * ⟪e₁, p⟫_ℝ + c ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, norm_e₁, mul_one,
    sq_abs, real_inner_comm e₁ p]
  ring

/-- The boosted momentum `𝐩' = 𝐩 + (ω_m(𝐩) sinh η + p₁ (cosh η - 1)) 𝐞₁`, `p₁ = ⟪𝐞₁, 𝐩⟫`, so
that `(ω_m(𝐩'), 𝐩') = Λ(η) (ω_m(𝐩), 𝐩)` (`boost_onShell`). -/
noncomputable def shellBoost (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  p + (Real.sinh η * dispersion m p + (Real.cosh η - 1) * ⟪e₁, p⟫_ℝ) • e₁

/-- The energy of the boosted momentum: `ω_m(𝐩') = ω_m(𝐩) cosh η + p₁ sinh η`. -/
theorem dispersion_shellBoost (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    dispersion m (shellBoost m η p) =
      Real.cosh η * dispersion m p + Real.sinh η * ⟪e₁, p⟫_ℝ := by
  have hω2 := dispersion_sq m p
  have hch := Real.cosh_sq_sub_sinh_sq η
  have hnonneg : 0 ≤ Real.cosh η * dispersion m p + Real.sinh η * ⟪e₁, p⟫_ℝ := by
    have hsh : |Real.sinh η| ≤ Real.cosh η := by
      refine abs_le.mpr ⟨?_, (Real.sinh_lt_cosh η).le⟩
      have h := Real.sinh_lt_cosh (-η)
      rw [Real.sinh_neg, Real.cosh_neg] at h
      linarith
    have hx : |⟪e₁, p⟫_ℝ| ≤ dispersion m p :=
      (abs_inner_e₁_le p).trans (norm_le_dispersion m p)
    have h1 : |Real.sinh η * ⟪e₁, p⟫_ℝ| ≤ Real.cosh η * dispersion m p := by
      rw [abs_mul]
      exact mul_le_mul hsh hx (abs_nonneg _) (Real.cosh_pos η).le
    linarith [neg_abs_le (Real.sinh η * ⟪e₁, p⟫_ℝ)]
  have hsq : m ^ 2 + ‖shellBoost m η p‖ ^ 2 =
      (Real.cosh η * dispersion m p + Real.sinh η * ⟪e₁, p⟫_ℝ) ^ 2 := by
    rw [shellBoost, norm_add_smul_e₁_sq]
    linear_combination (-1 : ℝ) * hω2 + (⟪e₁, p⟫_ℝ ^ 2 - dispersion m p ^ 2) * hch
  change Real.sqrt (m ^ 2 + ‖shellBoost m η p‖ ^ 2) = _
  rw [hsq, Real.sqrt_sq hnonneg]

/-- The point `(ω_m(𝐩), 𝐩)` of the mass shell. -/
noncomputable def onShell (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (dispersion m p, p)

/-- `Λ(η) (ω_m(𝐩), 𝐩) = (ω_m(𝐩'), 𝐩')` with `𝐩' = shellBoost m η 𝐩`. -/
theorem boost_onShell (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    boost η (onShell m p) = onShell m (shellBoost m η p) := by
  refine Prod.ext ?_ rfl
  change Real.cosh η * dispersion m p + Real.sinh η * ⟪e₁, p⟫_ℝ = dispersion m (shellBoost m η p)
  exact (dispersion_shellBoost m η p).symm

/-- The boosted momenta form a one-parameter group: `S(a) S(b) = S(a + b)`. -/
theorem shellBoost_shellBoost (m a b : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    shellBoost m a (shellBoost m b p) = shellBoost m (a + b) p := by
  have h : boost a (boost b (onShell m p)) = boost (a + b) (onShell m p) :=
    boost_boost a b (onShell m p)
  rw [boost_onShell, boost_onShell, boost_onShell] at h
  exact congrArg Prod.snd h

/-- `S(0) = 1`. -/
theorem shellBoost_zero (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : shellBoost m 0 p = p := by
  simp [shellBoost]

/-- `S(-η) S(η) = 1`: `shellBoost m (-η)` inverts `shellBoost m η`. -/
theorem shellBoost_neg_shellBoost (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    shellBoost m (-η) (shellBoost m η p) = p := by
  rw [shellBoost_shellBoost, neg_add_cancel, shellBoost_zero]

/-- `S(η) S(-η) = 1`. -/
theorem shellBoost_shellBoost_neg (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    shellBoost m η (shellBoost m (-η) p) = p := by
  rw [shellBoost_shellBoost, add_neg_cancel, shellBoost_zero]

/-- `shellBoost m η` is injective. -/
theorem shellBoost_injective (m η : ℝ) : Function.Injective (shellBoost m η) :=
  Function.LeftInverse.injective (shellBoost_neg_shellBoost m η)

/-- `shellBoost m η` is surjective. -/
theorem shellBoost_surjective (m η : ℝ) : Function.Surjective (shellBoost m η) :=
  Function.RightInverse.surjective (shellBoost_shellBoost_neg m η)

/-! ### Invariance of the shell measure `d³p / ω_m(𝐩)` -/

/-- `det (1 + ℓ(·) 𝐞₁) = 1 + ℓ(𝐞₁)` on `ℝ³`. -/
theorem det_id_add_smulRight_e₁ (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + ℓ.smulRight e₁).det = 1 + ℓ e₁ := by
  change LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + ℓ.smulRight e₁ :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) = 1 + ℓ e₁
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis, Matrix.det_fin_three]
  simp [LinearMap.toMatrix_apply, e₁]

/-- The derivative of `ω_m` for `m ≠ 0`: `dω_m(𝐩) = ω_m(𝐩)⁻¹ ⟪𝐩, ·⟫`. -/
theorem hasFDerivAt_dispersion {m : ℝ} (hm : m ≠ 0) (p : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (dispersion m) ((dispersion m p)⁻¹ • innerSL ℝ p) p := by
  have hu : m ^ 2 + ‖p‖ ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hm) (sq_nonneg ‖p‖)).ne'
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add (m ^ 2)).sqrt hu
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    dispersion]
  ring

/-- The derivative of `shellBoost m η` at `𝐩`:
`𝐯 ↦ 𝐯 + (sinh η ⟪𝐩, 𝐯⟫ / ω_m(𝐩) + (cosh η - 1) ⟪𝐞₁, 𝐯⟫) 𝐞₁`. -/
noncomputable def shellBoostDeriv (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
    (Real.sinh η • ((dispersion m p)⁻¹ • innerSL ℝ p) +
      (Real.cosh η - 1) • innerSL ℝ e₁).smulRight e₁

/-- `shellBoost m η` has derivative `shellBoostDeriv m η 𝐩` at `𝐩` (for `m ≠ 0`). -/
theorem hasFDerivAt_shellBoost {m : ℝ} (hm : m ≠ 0) (η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (shellBoost m η) (shellBoostDeriv m η p) p := by
  have h1 := (hasFDerivAt_dispersion hm p).const_mul (Real.sinh η)
  have h2 := ((innerSL ℝ e₁).hasFDerivAt (x := p)).const_mul (Real.cosh η - 1)
  exact (hasFDerivAt_id p).add ((h1.add h2).smul_const e₁)

/-- The value at `𝐞₁` of the linear form in `shellBoostDeriv`. -/
theorem shellBoostForm_apply_e₁ (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (Real.sinh η • ((dispersion m p)⁻¹ • innerSL ℝ p) + (Real.cosh η - 1) • innerSL ℝ e₁) e₁ =
      Real.sinh η * ((dispersion m p)⁻¹ * ⟪p, e₁⟫_ℝ) + (Real.cosh η - 1) := by
  simp only [_root_.add_apply, _root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    inner_e₁_self, mul_one]

/-- The Jacobian of the boosted momentum: `det dS(𝐩) = ω_m(𝐩') / ω_m(𝐩)`. -/
theorem det_shellBoostDeriv {m : ℝ} (hm : m ≠ 0) (η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (shellBoostDeriv m η p).det = dispersion m (shellBoost m η p) / dispersion m p := by
  have hω : dispersion m p ≠ 0 := (dispersion_pos hm p).ne'
  have hinv : (dispersion m p)⁻¹ * dispersion m p = 1 := inv_mul_cancel₀ hω
  rw [shellBoostDeriv, det_id_add_smulRight_e₁, shellBoostForm_apply_e₁, dispersion_shellBoost,
    real_inner_comm e₁ p, eq_div_iff hω]
  linear_combination (Real.sinh η * ⟪e₁, p⟫_ℝ) * hinv

/-- Pointwise form of the invariance: `|det dS(𝐩)| / ω_m(S𝐩) = 1 / ω_m(𝐩)`. -/
theorem abs_det_shellBoostDeriv_smul {m : ℝ} (hm : m ≠ 0) (η : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) (z : ℂ) :
    |(shellBoostDeriv m η p).det| •
        (z * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m (shellBoost m η p)) : ℝ) : ℂ)) =
      z * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  have h1 := dispersion_pos hm (shellBoost m η p)
  have h2 := dispersion_pos hm p
  have hK : 0 < 2 * (2 * Real.pi) ^ 3 := by positivity
  have hw : |(shellBoostDeriv m η p).det| *
      (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m (shellBoost m η p))) =
      1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) := by
    rw [det_shellBoostDeriv hm η p, abs_of_pos (div_pos h1 h2), mul_one_div, div_div,
      div_eq_div_iff (mul_pos h2 (mul_pos hK h1)).ne' (mul_pos hK h2).ne']
    ring
  rw [Complex.real_smul, ← hw, Complex.ofReal_mul]
  ring

/-- **Invariance of the shell measure** `d³p / (2(2π)³ ω_m(𝐩))` under the boosts of the mass
shell: for `m ≠ 0`, every rapidity `η` and every `g`,
`∫ g(S_η 𝐩) d³p / (2(2π)³ω_m(𝐩)) = ∫ g(𝐩) d³p / (2(2π)³ω_m(𝐩))` (no integrability hypothesis:
both sides are change-of-variables images of each other). -/
theorem integral_shellBoost_mul_weight {m : ℝ} (hm : m ≠ 0) (η : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) :
    ∫ p, g (shellBoost m η p) * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ∫ p, g p * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) := by
  have hderiv : ∀ p ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 3))),
      HasFDerivWithinAt (shellBoost m η) (shellBoostDeriv m η p) Set.univ p :=
    fun p _ => (hasFDerivAt_shellBoost hm η p).hasFDerivWithinAt
  have hcov : ∫ q, g q * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q) : ℝ) : ℂ) =
      ∫ p, |(shellBoostDeriv m η p).det| • (g (shellBoost m η p) *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m (shellBoost m η p)) : ℝ) : ℂ)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hderiv
      (shellBoost_injective m η).injOn
      (fun q => g q * ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q) : ℝ) : ℂ))
    rw [Set.image_univ, (shellBoost_surjective m η).range_eq, Measure.restrict_univ] at h
    exact h
  rw [hcov]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact (abs_det_shellBoostDeriv_smul hm η p (g (shellBoost m η p))).symm

/-! ### Covariance of the one-particle wave functions -/

/-- The composition `F ∘ Λ` of a real test function with a continuous linear automorphism `Λ`
of spacetime, again a real test function. -/
noncomputable def RealTestFunction.compCLE (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : RealTestFunction) : RealTestFunction :=
  ⟨F.1 ∘ Λ, F.2.1.comp Λ.contDiff, F.2.2.comp_homeomorph Λ.toHomeomorph⟩

/-- `(F ∘ Λ)(x) = F(Λ x)`. -/
theorem RealTestFunction.compCLE_apply (Λ : Spacetime ≃L[ℝ] Spacetime) (F : RealTestFunction)
    (x : Spacetime) : (F.compCLE Λ).1 x = F.1 (Λ x) :=
  rfl

/-- `(F + G) ∘ Λ = F ∘ Λ + G ∘ Λ`. -/
theorem RealTestFunction.compCLE_add (Λ : Spacetime ≃L[ℝ] Spacetime) (F G : RealTestFunction) :
    (F + G).compCLE Λ = F.compCLE Λ + G.compCLE Λ :=
  Subtype.ext (funext fun _ => rfl)

/-- `(F ∘ Λ⁻¹) ∘ Λ = F`. -/
theorem RealTestFunction.compCLE_symm_compCLE (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : RealTestFunction) : (F.compCLE Λ.symm).compCLE Λ = F :=
  Subtype.ext (funext fun x => congrArg F.1 (Λ.symm_apply_apply x))

/-- `(F ∘ Λ) ∘ Λ⁻¹ = F`. -/
theorem RealTestFunction.compCLE_compCLE_symm (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : RealTestFunction) : (F.compCLE Λ).compCLE Λ.symm = F :=
  Subtype.ext (funext fun x => congrArg F.1 (Λ.apply_symm_apply x))

/-- `tsupport (F ∘ Λ) = Λ⁻¹ (tsupport F)`. -/
theorem RealTestFunction.tsupport_compCLE (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : RealTestFunction) : tsupport (F.compCLE Λ).1 = Λ ⁻¹' tsupport F.1 :=
  tsupport_comp_eq_preimage F.1 Λ.toHomeomorph

/-- Covariance of `κ_m` under a volume-preserving automorphism `Λ` of spacetime: if the plane
waves satisfy `ω_m(𝐩) x⁰ - ⟪𝐩, 𝐱⟫ = ω_m(𝐪) y⁰ - ⟪𝐪, 𝐲⟫` with `y = Λ x`, for all `x`, then
`κ_m(F ∘ Λ)(𝐩) = κ_m F(𝐪)` (substitution `y = Λ x` in `d⁴x`). -/
theorem oneParticle_compCLE {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : MeasurePreserving Λ (volume : Measure Spacetime) volume)
    {p q : EuclideanSpace ℝ (Fin 3)}
    (hphase : ∀ x : Spacetime, dispersion m p * x.1 - ⟪p, x.2⟫_ℝ =
      dispersion m q * (Λ x).1 - ⟪q, (Λ x).2⟫_ℝ)
    (F : RealTestFunction) :
    oneParticle m (F.compCLE Λ) p = oneParticle m F q := by
  have hpt : ∀ x : Spacetime, oneParticleIntegrand m (F.compCLE Λ) p x =
      oneParticleIntegrand m F q (Λ x) := by
    intro x
    change Complex.exp (Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ)) *
        ((F.1 (Λ x) : ℝ) : ℂ) =
      Complex.exp (Complex.I * ((dispersion m q * (Λ x).1 - ⟪q, (Λ x).2⟫_ℝ : ℝ) : ℂ)) *
        ((F.1 (Λ x) : ℝ) : ℂ)
    rw [hphase x]
  calc oneParticle m (F.compCLE Λ) p
      = ∫ x : Spacetime, oneParticleIntegrand m F q (Λ x) := by
        rw [oneParticle_eq_integral]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ y : Spacetime, oneParticleIntegrand m F q y :=
        hΛ.integral_comp Λ.toHomeomorph.measurableEmbedding (oneParticleIntegrand m F q)
    _ = oneParticle m F q := (oneParticle_eq_integral m F q).symm

/-- **Covariance of `κ_m` under boosts**: `κ_m(F ∘ Λ(η))(𝐩) = κ_m F(S_η 𝐩)`, where
`(ω_m(S_η 𝐩), S_η 𝐩) = Λ(η)(ω_m(𝐩), 𝐩)`.  (By the Minkowski invariance
`⟨k, Λ⁻¹y⟩ = ⟨Λk, y⟩` and `d⁴(Λ x) = d⁴x`.) -/
theorem oneParticle_boost (m η : ℝ) (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (F.compCLE (boost η)) p = oneParticle m F (shellBoost m η p) := by
  refine oneParticle_compCLE (boost η) (measurePreserving_boost η) (fun x => ?_) F
  have h := minkowskiForm_boost η (onShell m p) x
  rw [boost_onShell] at h
  exact h.symm

/-! ### Lorentz invariance of the one-particle inner product -/

/-- **Lorentz invariance of the one-particle inner product**: for `m ≠ 0`,
`⟨κ_m(F ∘ Λ(η)), κ_m(G ∘ Λ(η))⟩ = ⟨κ_m F, κ_m G⟩`. -/
theorem oneParticleInner_boost {m : ℝ} (hm : m ≠ 0) (η : ℝ) (F G : RealTestFunction) :
    oneParticleInner m (F.compCLE (boost η)) (G.compCLE (boost η)) =
      oneParticleInner m F G := by
  unfold oneParticleInner
  simp only [oneParticle_boost]
  exact integral_shellBoost_mul_weight hm η
    (fun q => conj (oneParticle m F q) * oneParticle m G q)

/-! ### Spatial rotations -/

/-- The spatial rotation `(t, 𝐱) ↦ (t, R𝐱)` by a linear isometry `R` of `ℝ³`. -/
noncomputable def spatialRotation
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    Spacetime ≃L[ℝ] Spacetime :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr R.toContinuousLinearEquiv

/-- The rotation in coordinates. -/
theorem spatialRotation_apply (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : Spacetime) : spatialRotation R x = (x.1, R x.2) :=
  rfl

/-- Spatial rotations preserve Lebesgue measure on spacetime. -/
theorem measurePreserving_spatialRotation
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    MeasurePreserving (spatialRotation R) (volume : Measure Spacetime) volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod R.measurePreserving
  exact h

/-- `ω_m(R𝐩) = ω_m(𝐩)`. -/
theorem dispersion_linearIsometryEquiv (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 3)) : dispersion m (R p) = dispersion m p := by
  change Real.sqrt (m ^ 2 + ‖R p‖ ^ 2) = Real.sqrt (m ^ 2 + ‖p‖ ^ 2)
  rw [LinearIsometryEquiv.norm_map]

/-- Covariance of `κ_m` under rotations: `κ_m(F ∘ R)(𝐩) = κ_m F(R𝐩)`. -/
theorem oneParticle_spatialRotation (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (F.compCLE (spatialRotation R)) p = oneParticle m F (R p) := by
  refine oneParticle_compCLE (spatialRotation R) (measurePreserving_spatialRotation R)
    (fun x => ?_) F
  change dispersion m p * x.1 - ⟪p, x.2⟫_ℝ = dispersion m (R p) * x.1 - ⟪R p, R x.2⟫_ℝ
  rw [dispersion_linearIsometryEquiv, LinearIsometryEquiv.inner_map_map]

/-- Rotation invariance of the one-particle inner product (for every `m`):
`⟨κ_m(F ∘ R), κ_m(G ∘ R)⟩ = ⟨κ_m F, κ_m G⟩`. -/
theorem oneParticleInner_spatialRotation (m : ℝ)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (F G : RealTestFunction) :
    oneParticleInner m (F.compCLE (spatialRotation R)) (G.compCLE (spatialRotation R)) =
      oneParticleInner m F G := by
  unfold oneParticleInner
  simp only [oneParticle_spatialRotation]
  have h := R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun q => conj (oneParticle m F q) * oneParticle m G q *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m q) : ℝ) : ℂ))
  simp only [dispersion_linearIsometryEquiv] at h
  exact h

/-! ### The transported vacuum system and its local algebras -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vacuum system transported by a spacetime automorphism `Λ` that leaves the one-particle
inner product invariant: `W'(F) = W(F ∘ Λ)`, same vacuum. -/
noncomputable def FreeFieldVacuum.lorentz {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G) :
    FreeFieldVacuum m H where
  weyl F := V.weyl (F.compCLE Λ)
  vacuum := V.vacuum
  weyl_mem_unitary F := V.weyl_mem_unitary (F.compCLE Λ)
  weyl_mul F G := by
    show V.weyl (F.compCLE Λ) * V.weyl (G.compCLE Λ) =
      Complex.exp (-(Complex.I * ((oneParticleInner m F G).im : ℂ))) •
        V.weyl ((F + G).compCLE Λ)
    rw [RealTestFunction.compCLE_add, ← hΛ F G]
    exact V.weyl_mul (F.compCLE Λ) (G.compCLE Λ)
  vacuum_norm := V.vacuum_norm
  vacuum_weyl F := by
    change ⟪V.vacuum, V.weyl (F.compCLE Λ) V.vacuum⟫_ℂ =
      ((Real.exp (-((oneParticleInner m F F).re / 2)) : ℝ) : ℂ)
    rw [← hΛ F F]
    exact V.vacuum_weyl (F.compCLE Λ)
  cyclic := by
    have hrange : (Set.range fun F : RealTestFunction => V.weyl (F.compCLE Λ) V.vacuum) =
        Set.range fun F : RealTestFunction => V.weyl F V.vacuum := by
      ext x
      constructor
      · rintro ⟨F, rfl⟩
        exact ⟨F.compCLE Λ, rfl⟩
      · rintro ⟨F, rfl⟩
        exact ⟨F.compCLE Λ.symm, congrArg (fun K => V.weyl K V.vacuum)
          (RealTestFunction.compCLE_symm_compCLE Λ F)⟩
    change (Submodule.span ℂ
      (Set.range fun F : RealTestFunction => V.weyl (F.compCLE Λ) V.vacuum)).topologicalClosure = ⊤
    rw [hrange]
    exact V.cyclic

/-- The transported system has the Weyl operators `W'(F) = W(F ∘ Λ)`. -/
theorem FreeFieldVacuum.lorentz_weyl {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G)
    (F : RealTestFunction) : (V.lorentz Λ hΛ).weyl F = V.weyl (F.compCLE Λ) :=
  rfl

/-- The transported system has the same vacuum vector. -/
theorem FreeFieldVacuum.lorentz_vacuum {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G) :
    (V.lorentz Λ hΛ).vacuum = V.vacuum :=
  rfl

/-- The local algebras of the transported system: `𝔄'(O) = 𝔄(Λ⁻¹ O)`. -/
theorem FreeFieldVacuum.localAlgebra_lorentz {m : ℝ} (V : FreeFieldVacuum m H)
    (Λ : Spacetime ≃L[ℝ] Spacetime)
    (hΛ : ∀ F G : RealTestFunction,
      oneParticleInner m (F.compCLE Λ) (G.compCLE Λ) = oneParticleInner m F G)
    (O : Set Spacetime) :
    localAlgebra (V.lorentz Λ hΛ) O = localAlgebra V (Λ ⁻¹' O) := by
  unfold localAlgebra
  congr 1
  ext T
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F.compCLE Λ, ?_, rfl⟩
    rw [RealTestFunction.tsupport_compCLE]
    exact Set.preimage_mono hF
  · rintro ⟨G, hG, rfl⟩
    refine ⟨G.compCLE Λ.symm, ?_, ?_⟩
    · intro x hx
      rw [RealTestFunction.tsupport_compCLE] at hx
      have hx' : Λ.symm x ∈ tsupport G.1 := hx
      have h := hG hx'
      rwa [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] at h
    · change V.weyl G = V.weyl ((G.compCLE Λ.symm).compCLE Λ)
      rw [RealTestFunction.compCLE_symm_compCLE]

/-- The boosted vacuum system (for `m ≠ 0`): `W'(F) = W(F ∘ Λ(η))`, same vacuum. -/
noncomputable def FreeFieldVacuum.boosted {m : ℝ} (V : FreeFieldVacuum m H) (hm : m ≠ 0)
    (η : ℝ) : FreeFieldVacuum m H :=
  V.lorentz (boost η) (oneParticleInner_boost hm η)

/-- The local algebras of the boosted system: `𝔄'(O) = 𝔄(Λ(η)⁻¹ O) = 𝔄(Λ(-η) O)`. -/
theorem FreeFieldVacuum.localAlgebra_boosted {m : ℝ} (V : FreeFieldVacuum m H) (hm : m ≠ 0)
    (η : ℝ) (O : Set Spacetime) :
    localAlgebra (V.boosted hm η) O = localAlgebra V (boost (-η) '' O) := by
  rw [← boost_symm, ContinuousLinearEquiv.image_symm_eq_preimage]
  exact V.localAlgebra_lorentz (boost η) (oneParticleInner_boost hm η) O

/-- The rotated vacuum system: `W'(F) = W(F ∘ R)`, same vacuum. -/
noncomputable def FreeFieldVacuum.rotated {m : ℝ} (V : FreeFieldVacuum m H)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) : FreeFieldVacuum m H :=
  V.lorentz (spatialRotation R) (oneParticleInner_spatialRotation m R)

/-- The local algebras of the rotated system: `𝔄'(O) = 𝔄(R⁻¹ O)`. -/
theorem FreeFieldVacuum.localAlgebra_rotated {m : ℝ} (V : FreeFieldVacuum m H)
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (O : Set Spacetime) :
    localAlgebra (V.rotated R) O = localAlgebra V (spatialRotation R ⁻¹' O) :=
  V.localAlgebra_lorentz (spatialRotation R) (oneParticleInner_spatialRotation m R) O

end VacuumBellSeparation
