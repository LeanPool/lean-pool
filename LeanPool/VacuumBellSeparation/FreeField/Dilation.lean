/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DilatedVacuumConstruction
public import LeanPool.VacuumBellSeparation.FreeField.Uniqueness
public import LeanPool.VacuumBellSeparation.FreeField.Statements

/-!
# Lemma 2.1 (dilation)

For `R > 0` the dilation of a real test function is `(D_R F)(y) = R³ F(R y)`.  Then

* `oneParticle_dilate`: `κ_{mR}(D_R F)(R 𝐩) = R⁻¹ κ_m F(𝐩)` (substitution `x = R y` in `d⁴x`);
* `oneParticleInner_dilate`: `⟨κ_{mR} D_R F, κ_{mR} D_R G⟩ = ⟨κ_m F, κ_m G⟩` (substitution
  `𝐪 = R 𝐩` in `d³p`, with `ω_{mR}(R 𝐩) = R ω_m(𝐩)`);
* `FreeFieldVacuum.dilated`: from a vacuum system `V` of mass `m`, the vacuum system of mass
  `mR` with `W'(F) = W(D_{R⁻¹} F)` and the same vacuum;
* `FreeFieldVacuum.freeFieldBell_dilated`: `β` of the dilated system for `(1, L/R)` equals
  `β_m(R, L)` of `V` (the local algebras of `D_1`, `D_1 + (0, (L/R)𝐞₁)` for `V'` are those of
  `D_R`, `D_R + (0, L𝐞₁)` for `V`);
* `lemma_2_1 : Lemma_2_1`, with `FreeFieldVacuum.freeFieldBell_eq`, and
  `freeFieldBell_eq_dilated`, the same identity without the hypotheses `0 < m`, `0 < L`.

The manuscript's source transformation (2.5) acts on time-zero data `(f, g)`; the model uses
spacetime test functions, so the dilation-invariance of the one-particle inner product (its real
part is the vacuum covariance and its imaginary part half the symplectic form, as in (2.6)) and
the vacuum-preserving identification of local algebras are proved here in that formulation.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

/-! ### The dilation of test functions -/

theorem dilate_apply (c : ℝ) (F : RealTestFunction) (y : Spacetime) :
    (dilate c F).1 y = c ^ 3 * F.1 (c • y) := rfl

/-- `c x ∈ tsupport F` for every `x ∈ tsupport (D_c F)`. -/
theorem mem_tsupport_dilate {c : ℝ} {F : RealTestFunction} {x : Spacetime}
    (hx : x ∈ tsupport (dilate c F).1) : c • x ∈ tsupport F.1 := by
  have h1 : tsupport (dilate c F).1 ⊆ tsupport (fun y : Spacetime => F.1 (c • y)) :=
    tsupport_mul_subset_right
  have h2 : tsupport (fun y : Spacetime => F.1 (c • y)) ⊆
      (fun y : Spacetime => c • y) ⁻¹' tsupport F.1 :=
    tsupport_comp_subset_preimage F.1 (continuous_const_smul c)
  exact h2 (h1 hx)

/-! ### Dimension of spacetime and the dispersion relation under dilations -/

theorem oneParticleInner_eq_integral (m : ℝ) (F G : RealTestFunction) :
    oneParticleInner m F G = ∫ p, oneParticleInnerIntegrand m F G p := rfl

/-! ### (c) Double cones under dilations -/

theorem smul_mem_doubleCone_iff {R : ℝ} (hR : 0 < R) (a x : Spacetime) (r : ℝ) :
    R • x ∈ doubleCone (R • a) (R * r) ↔ x ∈ doubleCone a r := by
  have h1 : |R * x.1 - R * a.1| = R * |x.1 - a.1| := by
    rw [← mul_sub, abs_mul, abs_of_pos hR]
  have h2 : ‖R • x.2 - R • a.2‖ = R * ‖x.2 - a.2‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  change |R * x.1 - R * a.1| + ‖R • x.2 - R • a.2‖ < R * r ↔ |x.1 - a.1| + ‖x.2 - a.2‖ < r
  rw [h1, h2, ← mul_add]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h hR.le
  · intro h
    exact mul_lt_mul_of_pos_left h hR

theorem smul_centre {R : ℝ} (hR : R ≠ 0) (L : ℝ) :
    R • (((0 : ℝ), (L / R) • e₁) : Spacetime) = ((0 : ℝ), L • e₁) := by
  refine Prod.ext ?_ ?_
  · change R * 0 = 0
    exact mul_zero R
  · change R • (L / R) • e₁ = L • e₁
    rw [smul_smul, mul_div_cancel₀ L hR]

/-! ### (d) The dilated vacuum system -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem FreeFieldVacuum.localAlgebra_dilated {m : ℝ} (V : FreeFieldVacuum m H) {R : ℝ}
    (hR : 0 < R) (a : Spacetime) (r : ℝ) :
    localAlgebra (V.dilated hR) (doubleCone a r) =
      localAlgebra V (doubleCone (R • a) (R * r)) := by
  unfold localAlgebra
  congr 1
  ext T
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨dilate R⁻¹ F, ?_, rfl⟩
    intro x hx
    have h3 := (smul_mem_doubleCone_iff hR a (R⁻¹ • x) r).mpr (hF (mem_tsupport_dilate hx))
    rwa [smul_inv_smul₀ hR.ne' x] at h3
  · rintro ⟨G, hG, rfl⟩
    refine ⟨dilate R G, ?_, ?_⟩
    · intro x hx
      exact (smul_mem_doubleCone_iff hR a x r).mp (hG (mem_tsupport_dilate hx))
    · change V.weyl G = V.weyl (dilate R⁻¹ (dilate R G))
      rw [dilate_inv_dilate hR.ne' G]

/-- `β` of the dilated system for `(1, L/R)` is `β_m(R, L)` of `V`. -/
theorem FreeFieldVacuum.freeFieldBell_dilated {m : ℝ} (V : FreeFieldVacuum m H) {R : ℝ}
    (hR : 0 < R) (L : ℝ) :
    freeFieldBell (V.dilated hR) 1 (L / R) = freeFieldBell V R L := by
  have hA : localAlgebra (V.dilated hR) (doubleCone 0 1) = localAlgebra V (doubleCone 0 R) := by
    rw [V.localAlgebra_dilated hR, smul_zero, mul_one]
  have hB : localAlgebra (V.dilated hR) (doubleCone ((0 : ℝ), (L / R) • e₁) 1) =
      localAlgebra V (doubleCone ((0 : ℝ), L • e₁) R) := by
    rw [V.localAlgebra_dilated hR, mul_one, smul_centre hR.ne' L]
  change bellCorrelation (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra (V.dilated hR) (doubleCone 0 1))
      (localAlgebra (V.dilated hR) (doubleCone ((0 : ℝ), (L / R) • e₁) 1)) =
    bellCorrelation (vectorState V.vacuum V.vacuum_norm)
      (localAlgebra V (doubleCone 0 R)) (localAlgebra V (doubleCone ((0 : ℝ), L • e₁) R))
  rw [hA, hB]

/-! ### (e) Lemma 2.1 -/

/-- **Lemma 2.1 (dilation)**: `β_m(R, L) = β_{mR}(1, L/R)` for any vacuum systems. -/
theorem lemma_2_1 : Lemma_2_1 := by
  intro m R L _ hR _ H _ _ _ V H' _ _ _ V'
  exact (V.freeFieldBell_dilated hR L).symm.trans
    (FreeFieldVacuum.freeFieldBell_eq (V.dilated hR) V' 1 (L / R))

/-- Lemma 2.1 without the hypotheses `0 < m` and `0 < L` of `Lemma_2_1` (the manuscript states
the identity for every separation): `β_m(R, L) = β_{mR}(1, L/R)` for `R > 0` and any two vacuum
systems. -/
theorem freeFieldBell_eq_dilated {m R : ℝ} (hR : 0 < R) (L : ℝ) (V : FreeFieldVacuum m H)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (V' : FreeFieldVacuum (m * R) H') :
    freeFieldBell V R L = freeFieldBell V' 1 (L / R) :=
  (V.freeFieldBell_dilated hR L).symm.trans
    (FreeFieldVacuum.freeFieldBell_eq (V.dilated hR) V' 1 (L / R))

end VacuumBellSeparation
