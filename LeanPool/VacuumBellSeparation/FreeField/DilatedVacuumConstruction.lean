/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness
public import LeanPool.VacuumBellSeparation.FreeField.Statements

/-!
# Staged literal construction

Exact original declarations; verification target proofs are staged separately.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

theorem contDiff_dilate (c : ℝ) (F : RealTestFunction) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Spacetime => c ^ 3 * F.1 (c • y)) := by
  exact contDiff_const.mul (F.2.1.comp (contDiff_const_smul c))

theorem hasCompactSupport_dilate (c : ℝ) (F : RealTestFunction) :
    HasCompactSupport (fun y : Spacetime => c ^ 3 * F.1 (c • y)) := by
  by_cases hc : c = 0
  · have h0 : (fun y : Spacetime => c ^ 3 * F.1 (c • y)) = 0 := by
      funext y
      change c ^ 3 * F.1 (c • y) = 0
      rw [hc]
      ring1
    rw [h0]
    exact HasCompactSupport.zero
  · exact (F.2.2.comp_smul hc).mul_left

/-- The dilation `(D_c F)(y) = c³ F(c y)` of a real test function. -/
noncomputable def dilate (c : ℝ) (F : RealTestFunction) : RealTestFunction :=
  ⟨fun y => c ^ 3 * F.1 (c • y), contDiff_dilate c F, hasCompactSupport_dilate c F⟩


theorem dilate_add (c : ℝ) (F G : RealTestFunction) :
    dilate c (F + G) = dilate c F + dilate c G := by
  apply Subtype.ext
  funext y
  change c ^ 3 * (F.1 (c • y) + G.1 (c • y)) = c ^ 3 * F.1 (c • y) + c ^ 3 * G.1 (c • y)
  ring

theorem dilate_inv_dilate {c : ℝ} (hc : c ≠ 0) (F : RealTestFunction) :
    dilate c⁻¹ (dilate c F) = F := by
  apply Subtype.ext
  funext y
  change c⁻¹ ^ 3 * (c ^ 3 * F.1 (c • c⁻¹ • y)) = F.1 y
  rw [smul_inv_smul₀ hc y, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc, one_pow, one_mul]


theorem finrank_spacetime : Module.finrank ℝ Spacetime = 4 := by
  simp

theorem finrank_momentum : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
  finrank_euclideanSpace_fin

/-- `ω_{mR}(R 𝐩) = R ω_m(𝐩)` for `R ≥ 0`. -/
theorem dispersion_smul (m : ℝ) {R : ℝ} (hR : 0 ≤ R) (p : EuclideanSpace ℝ (Fin 3)) :
    dispersion (m * R) (R • p) = R * dispersion m p := by
  change Real.sqrt ((m * R) ^ 2 + ‖R • p‖ ^ 2) = R * Real.sqrt (m ^ 2 + ‖p‖ ^ 2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR,
    show (m * R) ^ 2 + (R * ‖p‖) ^ 2 = R ^ 2 * (m ^ 2 + ‖p‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR]

/-! ### (a) The one-particle wave function of a dilated test function -/

/-- `κ_{mR}(D_R F)(R 𝐩) = R⁻¹ κ_m F(𝐩)`. -/
theorem oneParticle_dilate (m : ℝ) {R : ℝ} (hR : 0 < R) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle (m * R) (dilate R F) (R • p) = ((R⁻¹ : ℝ) : ℂ) * oneParticle m F p := by
  have hpt : ∀ y : Spacetime, oneParticleIntegrand (m * R) (dilate R F) (R • p) y =
      ((R ^ 3 : ℝ) : ℂ) * oneParticleIntegrand m F p (R • y) := by
    intro y
    have harg : dispersion (m * R) (R • p) * y.1 - ⟪R • p, y.2⟫_ℝ =
        dispersion m p * (R • y).1 - ⟪p, (R • y).2⟫_ℝ := by
      rw [dispersion_smul m hR.le p, real_inner_smul_left]
      change R * dispersion m p * y.1 - R * ⟪p, y.2⟫_ℝ =
        dispersion m p * (R * y.1) - ⟪p, R • y.2⟫_ℝ
      rw [real_inner_smul_right]
      ring1
    change Complex.exp (Complex.I * ((dispersion (m * R) (R • p) * y.1 - ⟪R • p, y.2⟫_ℝ : ℝ) : ℂ)) *
        ((R ^ 3 * F.1 (R • y) : ℝ) : ℂ) =
      ((R ^ 3 : ℝ) : ℂ) * (Complex.exp (Complex.I *
        ((dispersion m p * (R • y).1 - ⟪p, (R • y).2⟫_ℝ : ℝ) : ℂ)) * ((F.1 (R • y) : ℝ) : ℂ))
    rw [harg, Complex.ofReal_mul]
    ring
  -- Change of variables `x = R y` in `d⁴x`.  The statement keeps `Module.finrank ℝ Spacetime`
  -- (elaborated here, so `finrank_spacetime` rewrites it syntactically in `hconst`); `exact`
  -- matches the instance paths of `integral_comp_smul` up to defeq.
  have hcov : ∫ y : Spacetime, oneParticleIntegrand m F p (R • y) =
      |(R ^ Module.finrank ℝ Spacetime)⁻¹| • oneParticle m F p := by
    have : (volume : Measure Spacetime).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    exact Measure.integral_comp_smul (volume : Measure Spacetime) (oneParticleIntegrand m F p) R
  have hconst : R ^ 3 * |(R ^ Module.finrank ℝ Spacetime)⁻¹| = R⁻¹ := by
    rw [finrank_spacetime, abs_of_pos (inv_pos.mpr (pow_pos hR 4))]
    have h4 : R ^ 4 = R ^ 3 * R := by ring
    rw [h4, mul_inv, mul_inv_cancel_left₀ (pow_ne_zero 3 hR.ne')]
  calc oneParticle (m * R) (dilate R F) (R • p)
      = ∫ y : Spacetime, ((R ^ 3 : ℝ) : ℂ) * oneParticleIntegrand m F p (R • y) := by
        rw [oneParticle_eq_integral]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact hpt y
    _ = ((R ^ 3 : ℝ) : ℂ) * ∫ y : Spacetime, oneParticleIntegrand m F p (R • y) :=
        integral_const_mul _ _
    _ = ((R ^ 3 : ℝ) : ℂ) * (|(R ^ Module.finrank ℝ Spacetime)⁻¹| • oneParticle m F p) := by
        rw [hcov]
    _ = ((R⁻¹ : ℝ) : ℂ) * oneParticle m F p := by
        rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hconst]

/-! ### (b) The one-particle inner product is dilation invariant -/


/-- The integrand of `oneParticleInner m F G`. -/
noncomputable def oneParticleInnerIntegrand (m : ℝ) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  conj (oneParticle m F p) * oneParticle m G p *
    ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)


theorem oneParticleInnerIntegrand_dilate (m : ℝ) {R : ℝ} (hR : 0 < R) (F G : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticleInnerIntegrand (m * R) (dilate R F) (dilate R G) (R • p) =
      ((R ^ 3)⁻¹ : ℝ) • oneParticleInnerIntegrand m F G p := by
  have hw : (1 / (2 * (2 * Real.pi) ^ 3 * dispersion (m * R) (R • p)) : ℝ) =
      R⁻¹ * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) := by
    rw [dispersion_smul m hR.le p]
    ring1
  have hc : ((R ^ 3)⁻¹ : ℝ) = R⁻¹ * R⁻¹ * R⁻¹ := by
    ring1
  -- `r • z = ↑r * z` for `r : ℝ`, `z : ℂ` (stated here so that `rw [hsmul]` matches syntactically).
  have hsmul : ((R ^ 3)⁻¹ : ℝ) • oneParticleInnerIntegrand m F G p =
      (((R ^ 3)⁻¹ : ℝ) : ℂ) * oneParticleInnerIntegrand m F G p :=
    Complex.real_smul
  rw [hsmul]
  change conj (oneParticle (m * R) (dilate R F) (R • p)) * oneParticle (m * R) (dilate R G)
    (R • p) *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion (m * R) (R • p)) : ℝ) : ℂ) =
    (((R ^ 3)⁻¹ : ℝ) : ℂ) * (conj (oneParticle m F p) * oneParticle m G p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ))
  rw [oneParticle_dilate m hR F p, oneParticle_dilate m hR G p, hw, hc, map_mul,
    Complex.conj_ofReal]
  simp only [Complex.ofReal_mul]
  ring1

/-- `⟨κ_{mR} D_R F, κ_{mR} D_R G⟩ = ⟨κ_m F, κ_m G⟩` for `R > 0`. -/
theorem oneParticleInner_dilate (m : ℝ) {R : ℝ} (hR : 0 < R) (F G : RealTestFunction) :
    oneParticleInner (m * R) (dilate R F) (dilate R G) = oneParticleInner m F G := by
  have hR3 : (R ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 hR.ne'
  -- Change of variables `𝐪 = R 𝐩` in `d³p` (statement elaborated here; `exact`-style term
  -- matches `integral_comp_smul` up to defeq, `oneParticleInner` unfolds to the integral).
  have hcov : ∫ p : EuclideanSpace ℝ (Fin 3),
      oneParticleInnerIntegrand (m * R) (dilate R F) (dilate R G) (R • p) =
      |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| •
        oneParticleInner (m * R) (dilate R F) (dilate R G) :=
    Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (oneParticleInnerIntegrand (m * R) (dilate R F) (dilate R G)) R
  have habs : |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| = (R ^ 3)⁻¹ := by
    rw [finrank_momentum]
    exact abs_of_pos (inv_pos.mpr (pow_pos hR 3))
  have hpt : ∫ p : EuclideanSpace ℝ (Fin 3),
      oneParticleInnerIntegrand (m * R) (dilate R F) (dilate R G) (R • p) =
      ((R ^ 3)⁻¹ : ℝ) • oneParticleInner m F G := by
    calc ∫ p : EuclideanSpace ℝ (Fin 3),
          oneParticleInnerIntegrand (m * R) (dilate R F) (dilate R G) (R • p)
        = ∫ p, ((R ^ 3)⁻¹ : ℝ) • oneParticleInnerIntegrand m F G p := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact oneParticleInnerIntegrand_dilate m hR F G p
      _ = ((R ^ 3)⁻¹ : ℝ) • ∫ p, oneParticleInnerIntegrand m F G p :=
          integral_smul _ _
      _ = ((R ^ 3)⁻¹ : ℝ) • oneParticleInner m F G := rfl
  have key : ((R ^ 3)⁻¹ : ℝ) • oneParticleInner (m * R) (dilate R F) (dilate R G) =
      ((R ^ 3)⁻¹ : ℝ) • oneParticleInner m F G := by
    rw [← hpt, hcov, habs]
  -- Cancel the nonzero real factor `(R³)⁻¹` (needs only the `MulAction ℝ ℂ`).
  calc oneParticleInner (m * R) (dilate R F) (dilate R G)
      = (R ^ 3 : ℝ) • (((R ^ 3)⁻¹ : ℝ) • oneParticleInner (m * R) (dilate R F) (dilate R G)) :=
        (smul_inv_smul₀ hR3 (oneParticleInner (m * R) (dilate R F) (dilate R G))).symm
    _ = (R ^ 3 : ℝ) • (((R ^ 3)⁻¹ : ℝ) • oneParticleInner m F G) := by rw [key]
    _ = oneParticleInner m F G := smul_inv_smul₀ hR3 (oneParticleInner m F G)

/-- `⟨κ_m D_{R⁻¹} F, κ_m D_{R⁻¹} G⟩ = ⟨κ_{mR} F, κ_{mR} G⟩` for `R > 0`. -/
theorem oneParticleInner_dilate_inv (m : ℝ) {R : ℝ} (hR : 0 < R) (F G : RealTestFunction) :
    oneParticleInner m (dilate R⁻¹ F) (dilate R⁻¹ G) = oneParticleInner (m * R) F G := by
  have h := oneParticleInner_dilate (m * R) (inv_pos.mpr hR) F G
  rwa [mul_inv_cancel_right₀ hR.ne' m] at h


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-- The dilated vacuum system of mass `mR`: `W'(F) = W(D_{R⁻¹} F)`, same vacuum. -/
noncomputable def FreeFieldVacuum.dilated {m : ℝ} (V : FreeFieldVacuum m H) {R : ℝ}
    (hR : 0 < R) : FreeFieldVacuum (m * R) H where
  weyl F := V.weyl (dilate R⁻¹ F)
  vacuum := V.vacuum
  weyl_mem_unitary F := V.weyl_mem_unitary (dilate R⁻¹ F)
  weyl_mul F G := by
    show V.weyl (dilate R⁻¹ F) * V.weyl (dilate R⁻¹ G) =
      Complex.exp (-(Complex.I * ((oneParticleInner (m * R) F G).im : ℂ))) •
        V.weyl (dilate R⁻¹ (F + G))
    rw [dilate_add R⁻¹ F G, ← oneParticleInner_dilate_inv m hR F G]
    exact V.weyl_mul (dilate R⁻¹ F) (dilate R⁻¹ G)
  vacuum_norm := V.vacuum_norm
  vacuum_weyl F := by
    change ⟪V.vacuum, V.weyl (dilate R⁻¹ F) V.vacuum⟫_ℂ =
      ((Real.exp (-((oneParticleInner (m * R) F F).re / 2)) : ℝ) : ℂ)
    rw [← oneParticleInner_dilate_inv m hR F F]
    exact V.vacuum_weyl (dilate R⁻¹ F)
  cyclic := by
    have hrange : (Set.range fun F => V.weyl (dilate R⁻¹ F) V.vacuum) =
        Set.range fun F => V.weyl F V.vacuum := by
      ext x
      constructor
      · rintro ⟨F, rfl⟩
        exact ⟨dilate R⁻¹ F, rfl⟩
      · rintro ⟨F, rfl⟩
        exact ⟨dilate R F, congrArg (fun K => V.weyl K V.vacuum) (dilate_inv_dilate hR.ne' F)⟩
    change (Submodule.span ℂ (Set.range fun F => V.weyl (dilate R⁻¹ F) V.vacuum)).topologicalClosure
      = ⊤
    rw [hrange]
    exact V.cyclic


end VacuumBellSeparation
