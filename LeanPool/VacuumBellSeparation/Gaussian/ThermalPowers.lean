/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalDensity

/-!
# Actual functional-calculus powers of the thermal density

Continuous real functional calculus preserves eigenvectors. Applying this
to the infinite number basis proves the trace formula for positive real
powers of the one-mode density. In particular these are actual CFC powers,
not a separate coefficientwise operator definition.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter Topology
open scoped lp ENNReal ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
theorem eigenvalue_mem_real_spectrum {A : E →L[ℂ] E} {x : E} {r : ℝ}
    (hx : x ≠ 0) (hAx : A x = r • x) : r ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have hz : (u : E →L[ℂ] E) x = 0 := by
    rw [hu]
    change r • x - A x = 0
    rw [hAx, sub_self]
  have hh := congrArg (fun z => (↑u⁻¹ : E →L[ℂ] E) z) hz
  rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_zero] at hh
  exact hx hh

/-- Functional calculus on a real-spectrum eigenvector, first for the
continuous-map homomorphism. The proof uses uniform polynomial density. -/
theorem cfcHom_apply_eigenvector {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {r : ℝ} (hr : r ∈ spectrum ℝ A) {x : E} (hAx : A x = r • x)
    (f : C(spectrum ℝ A, ℝ)) :
    (cfcHom hA f) x = f ⟨r, hr⟩ • x := by
  induction f using ContinuousMap.induction_on_of_compact with
  | const t =>
    change (cfcHom hA (algebraMap ℝ C(spectrum ℝ A, ℝ) t)) x = t • x
    rw [AlgHomClass.commutes]
    change (t • (1 : E →L[ℂ] E)) x = t • x
    rw [smul_apply, one_apply_eq_self]
  | id =>
    simpa only [cfcHom_id, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using hAx
  | star_id =>
    simpa only [map_star, cfcHom_id, hA.star_eq, star_trivial,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply] using hAx
  | add f g hf hg =>
    simp only [map_add, add_apply, hf, hg, ContinuousMap.add_apply, add_smul]
  | mul f g hf hg =>
    simp only [map_mul, mul_apply_eq_comp, hg, map_smul_of_tower, hf,
      ContinuousMap.mul_apply, smul_smul, mul_comm]
  | frequently f hf =>
    have heval : Continuous (fun g : C(spectrum ℝ A, ℝ) => g ⟨r, hr⟩) :=
      continuous_eval_const (⟨r, hr⟩ : spectrum ℝ A)
    have hsmul : Continuous (fun g : C(spectrum ℝ A, ℝ) => g ⟨r, hr⟩ • x) :=
      heval.smul (continuous_const : Continuous (fun _ : C(spectrum ℝ A, ℝ) => x))
    have hc : IsClosed {g : C(spectrum ℝ A, ℝ) |
        (cfcHom hA g) x = g ⟨r, hr⟩ • x} :=
      isClosed_eq ((cfcHom_continuous hA (R := ℝ)).clm_apply continuous_const)
        hsmul
    exact hc.mem_of_frequently_of_tendsto hf tendsto_id

theorem cfc_apply_eigenvector {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {r : ℝ} (hr : r ∈ spectrum ℝ A) {x : E} (hAx : A x = r • x)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc f A x = f r • x := by
  rw [cfc_apply f A hA hf]
  exact cfcHom_apply_eigenvector hA hr hAx ⟨_, hf.domRestrict⟩

theorem rpow_apply_eigenvector {A : E →L[ℂ] E} (hA : 0 ≤ A)
    {r : ℝ} (hr : r ∈ spectrum ℝ A) {x : E} (hAx : A x = r • x)
    {τ : ℝ} (hτ : 0 < τ) : (A ^ τ) x = r ^ τ • x := by
  rw [CFC.rpow_eq_cfc_real hA]
  apply cfc_apply_eigenvector hA.isSelfAdjoint hr hAx
  exact (Real.continuous_rpow_const hτ.le).continuousOn

/-- Canonical Hilbert-operator structures resolved before specializing the carrier alias. -/
theorem hilbertOperator_realCFC :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

theorem hilbertOperator_starOrder : StarOrderedRing (E →L[ℂ] E) := inferInstance

theorem hilbertOperator_nonnegSpectrum : NonnegSpectrumClass ℝ (E →L[ℂ] E) :=
  inferInstance

/-- Expose the concrete lp instances at the carrier alias before asking for
operator CFC instances. These are the existing Mathlib Hilbert structures. -/
noncomputable instance oscillatorNormedAddCommGroup : NormedAddCommGroup OscillatorSpace :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℂ) 2))

noncomputable instance oscillatorInnerProductSpace : InnerProductSpace ℂ OscillatorSpace :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun _ : ℕ => ℂ) 2))

noncomputable instance oscillator_completeSpace : CompleteSpace OscillatorSpace :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℕ => ℂ) 2))

noncomputable instance oscillatorOperatorCStarAlgebra :
    CStarAlgebra (OscillatorSpace →L[ℂ] OscillatorSpace) :=
  inferInstanceAs (CStarAlgebra
    ((lp (fun _ : ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : ℕ => ℂ) 2)))

instance oscillator_realCFC :
    IsometricContinuousFunctionalCalculus ℝ (OscillatorSpace →L[ℂ] OscillatorSpace)
      IsSelfAdjoint := hilbertOperator_realCFC (E := OscillatorSpace)

instance oscillator_starOrder : StarOrderedRing (OscillatorSpace →L[ℂ] OscillatorSpace) :=
  hilbertOperator_starOrder (E := OscillatorSpace)

instance oscillator_nonnegSpectrum :
    NonnegSpectrumClass ℝ (OscillatorSpace →L[ℂ] OscillatorSpace) :=
  hilbertOperator_nonnegSpectrum (E := OscillatorSpace)

theorem thermalDensity_rpow_apply_numberBasis {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (k : ℕ) :
    (thermalDensity q ^ τ) (numberBasis k) =
      thermalWeight q k ^ τ • numberBasis k := by
  have hk : numberBasis k ≠ 0 := by
    intro hz
    have h := numberBasis.orthonormal.norm_eq_one k
    rw [hz, norm_zero] at h
    norm_num at h
  have heig := thermalDensity_apply_numberBasis hq₀ hq₁ k
  exact rpow_apply_eigenvector (thermalDensity_nonneg hq₀ hq₁)
    (eigenvalue_mem_real_spectrum hk heig) heig hτ

theorem thermalWeight_rpow {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (τ : ℝ) (k : ℕ) :
    thermalWeight q k ^ τ = (1 - q) ^ τ * (q ^ τ) ^ k := by
  rw [thermalWeight, Real.mul_rpow (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k),
    ← Real.rpow_natCast_mul hq₀, mul_comm (k : ℝ), Real.rpow_mul_natCast hq₀]

theorem hasSum_thermalWeight_rpow {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    HasSum (fun k => thermalWeight q k ^ τ) ((1 - q) ^ τ / (1 - q ^ τ)) := by
  have h := (hasSum_geometric_of_lt_one (Real.rpow_nonneg hq₀ τ)
    (Real.rpow_lt_one hq₀ hq₁ hτ)).mul_left ((1 - q) ^ τ)
  simpa only [thermalWeight_rpow hq₀ hq₁, div_eq_mul_inv] using h

/-- Trace formula for the actual positive operator power on ℓ². This remains
valid at the pure endpoint `q=0` when the exponent is positive. -/
theorem positiveTrace_thermalDensity_rpow {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    positiveTrace (thermalDensity q ^ τ) =
      ENNReal.ofReal ((1 - q) ^ τ / (1 - q ^ τ)) := by
  rw [positiveTrace_eq_tsum_diagonal numberBasis CFC.rpow_nonneg]
  have heq (k : ℕ) :
      (inner ℂ (numberBasis k) ((thermalDensity q ^ τ) (numberBasis k))).re =
        thermalWeight q k ^ τ := by
    rw [thermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
      inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
      numberBasis.orthonormal.norm_eq_one]
    simp [Algebra.smul_def]
  simp_rw [heq]
  have hw (k : ℕ) : 0 ≤ thermalWeight q k ^ τ :=
    Real.rpow_nonneg (show 0 ≤ thermalWeight q k from
      mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)) τ
  rw [← ENNReal.ofReal_tsum_of_nonneg
    hw
    (hasSum_thermalWeight_rpow hq₀ hq₁ hτ).summable,
    (hasSum_thermalWeight_rpow hq₀ hq₁ hτ).tsum_eq]

theorem thermalDensity_rpow_isPositiveTraceClass {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) :
    IsPositiveTraceClass (thermalDensity q ^ τ) := by
  refine ⟨CFC.rpow_nonneg, ?_⟩
  rw [positiveTrace_thermalDensity_rpow hq₀ hq₁ hτ]
  exact ENNReal.ofReal_lt_top

end VacuumBellSeparation.Gaussian
