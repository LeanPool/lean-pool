/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.Norm
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.Periodic
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Corollary 2, second part: a shorter proof of the upper bound, on the torus

An alternative proof of the upper bound `‖𝒮‖_p ≤ p* − 1` of `(eq:BA-sharp-norm)`
(`Agazzi.beurlingNorm_le_of_torus`). It is not the paper's route and is not used by
`Agazzi.corollary2_norm`, which follows the planar arguments that the paper cites
(`Agazzi.beurlingNorm_le`, in `Agazzi.Corollary2.Norm`). It is shorter: it needs neither the
Cauchy transform nor cut-offs, since the paper's Corollary 2 is already periodic.

1. For smooth `ℤ²`-periodic `u : ℝ² → ℂ` and `φ = (Re u, Im u)`, `a₊ (D φ) = ∂u` and
   `a₋ (D φ) = ∂_zbar u` (`Agazzi.Corollary2NormTorus.conformalPart_jacobian_toRealPair`,
   `Agazzi.Corollary2NormTorus.anticonformalPart_jacobian_toRealPair`).
2. The first assertion of Corollary 2 at `A = 0` (`corollary2`; `B_p (0) = 0`) gives
   `∫_Q B_p (D φ) ≥ 0`; with `α_p B_p = Φ_p (a₊, a₋)` or `Φ_p (a₋, a₊)` and Burkholder's inequality
   `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p` (`External.BaernsteinMontgomerySmith.phi_le`), and for
   `p < 2` the interchange `u ↦ ū`: `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂_zbar u‖_{L^p (Q)}`
   (`Agazzi.Corollary2NormTorus.eLpNorm_dzPi_le`).
3. Every mean-zero trigonometric polynomial `h` is `∂_zbar u` for a smooth periodic `u`
   (`UnitAddTorus.exists_dzbarPi_eq`), and then `𝓑 h = ∂u`
   (`HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi`): the norm of the
   Beurling–Ahlfors multiplier on `L^p_0 (𝕋²)` is at most `p* − 1`
   (`Agazzi.Corollary2NormTorus.torusBeurlingPowNorm_one_le`).
4. Transference from `𝕋²` to `ℂ` (Hytönen–van Neerven–Veraar–Weis, Corollary 5.7.6, in the
   package `HarmonicAnalysis`: `HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`).

This was the proof of the upper bound in the first round of the formalization; it is kept as a
shorter proof, checked in Lean.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set UnitAddTorus HarmonicAnalysis
open scoped ENNReal ComplexConjugate ContDiff Real

namespace Agazzi.Corollary2NormTorus

open External.BaernsteinMontgomerySmith (Phi alpha phi_le)
open Corollary2Norm (bms_pStar_eq le_pStar alpha_pos burkholderB_zero
  alpha_mul_burkholderB_of_lt_two alpha_mul_burkholderB_of_two_le)


/-! ### The Wirtinger derivatives and the jacobian -/

/-- The map `φ = (Re u, Im u) : ℝ² → ℝ²` of `u : ℝ² → ℂ` (with `ℂ ≅ ℝ²`, `x + iy ↦ (x, y)`). -/
def toRealPair (u : (Fin 2 → ℝ) → ℂ) (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![(u y).re, (u y).im]

theorem contDiff_toRealPair {n : WithTop ℕ∞} {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (toRealPair u) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · simp only [toRealPair, Fin.zero_eta, Matrix.cons_val_zero]
    exact Complex.reCLM.contDiff.comp hu
  · simp only [toRealPair, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Complex.imCLM.contDiff.comp hu

theorem isPeriodic_toRealPair {u : (Fin 2 → ℝ) → ℂ} (hu : UnitAddTorus.IsPeriodic u) :
    Agazzi.IsPeriodic (toRealPair u) := fun x k => by
  simp only [toRealPair, hu x k]

private lemma fderiv_re {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hu : DifferentiableAt ℝ u x)
    (v : Fin 2 → ℝ) : fderiv ℝ (fun y => (u y).re) x v = (fderiv ℝ u x v).re := by
  have h := (Complex.reCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  have e : (fun y => (u y).re) = Complex.reCLM ∘ u := rfl
  rw [e, h]
  rfl

private lemma fderiv_im {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ} (hu : DifferentiableAt ℝ u x)
    (v : Fin 2 → ℝ) : fderiv ℝ (fun y => (u y).im) x v = (fderiv ℝ u x v).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  have e : (fun y => (u y).im) = Complex.imCLM ∘ u := rfl
  rw [e, h]
  rfl

private lemma jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) (j : Fin 2) :
    jacobian (toRealPair u) x 0 j = (fderiv ℝ u x (Pi.single j 1)).re ∧
      jacobian (toRealPair u) x 1 j = (fderiv ℝ u x (Pi.single j 1)).im := by
  have h0 : (fun y => toRealPair u y 0) = fun y => (u y).re := by
    funext y; simp [toRealPair]
  have h1 : (fun y => toRealPair u y 1) = fun y => (u y).im := by
    funext y; simp [toRealPair]
  simp only [jacobian, Matrix.of_apply, h0, h1]
  exact ⟨fderiv_re hu _, fderiv_im hu _⟩

/-- `a₊ (D φ) = ∂u` for `φ = (Re u, Im u)`, at a point where `u` is differentiable. -/
theorem conformalPart_jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    conformalPart (jacobian (toRealPair u) x) = dzPi u x := by
  obtain ⟨a0, b0⟩ := jacobian_toRealPair hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealPair hu 1
  apply Complex.ext <;>
    simp [conformalPart, dzPi, a0, b0, a1, b1, Complex.mul_re, Complex.mul_im] <;> ring

/-- `a₋ (D φ) = ∂_zbar u` for `φ = (Re u, Im u)`, at a point where `u` is differentiable. -/
theorem anticonformalPart_jacobian_toRealPair {u : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hu : DifferentiableAt ℝ u x) :
    anticonformalPart (jacobian (toRealPair u) x) = dzbarPi u x := by
  obtain ⟨a0, b0⟩ := jacobian_toRealPair hu 0
  obtain ⟨a1, b1⟩ := jacobian_toRealPair hu 1
  apply Complex.ext <;>
    simp [anticonformalPart, dzbarPi, a0, b0, a1, b1, Complex.mul_re, Complex.mul_im] <;> ring

/-! ### The interchangeability of `∂` and `∂_zbar` -/

private lemma fderiv_conj (u : (Fin 2 → ℝ) → ℂ) (x v : Fin 2 → ℝ) :
    fderiv ℝ (fun y => conj (u y)) x v = conj (fderiv ℝ u x v) := by
  simp only [starRingEnd_apply, fderiv_star]
  rfl

/-- `∂ū = conj (∂_zbar u)`. -/
theorem dzPi_conj (u : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    dzPi (fun y => conj (u y)) x = conj (dzbarPi u x) := by
  simp only [dzPi, dzbarPi, fderiv_conj, map_mul, map_add, map_inv₀, map_ofNat, Complex.conj_I]
  ring

/-- `∂_zbarū = conj (∂u)`. -/
theorem dzbarPi_conj (u : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    dzbarPi (fun y => conj (u y)) x = conj (dzPi u x) := by
  simp only [dzPi, dzbarPi, fderiv_conj, map_mul, map_sub, map_inv₀, map_ofNat, Complex.conj_I]
  ring

theorem contDiff_conj {n : WithTop ℕ∞} {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n fun y => conj (u y) :=
  Complex.conjCLE.contDiff.comp hu

theorem isPeriodic_conj {u : (Fin 2 → ℝ) → ℂ} (hu : UnitAddTorus.IsPeriodic u) :
    UnitAddTorus.IsPeriodic fun y => conj (u y) := fun x k => by
  simp only [hu x k]

/-! ### Integrals and `L^p` norms over the torus as over the unit square -/

/-- Integrals over `𝕋^ι` (with Mathlib's measure, of total mass one) are integrals over the open
unit cube `(0, 1)^ι`. -/
theorem lintegral_torus_eq_cube {ι : Type*} [Fintype ι] (f : UnitAddTorus ι → ℝ≥0∞) :
    ∫⁻ z, f z = ∫⁻ x in cube ι, f (ofPi x) := by
  have hvol : (volume : Measure (UnitAddTorus ι)) =
      @volume _ (@MeasureSpace.pi ι _ (fun _ => UnitAddCircle)
        (fun _ => instMeasureSpaceUnitAddCircle)) :=
    volume_eq_pi_haarAddCircle
  rw [hvol, UnitAddTorus.lintegral_preimage f 0]
  have h1 : {x : ι → ℝ | ∀ i, x i ∈ Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} =
      univ.pi fun _ => Ioc (0 : ℝ) 1 := by
    ext x; simp
  rw [h1]
  exact setLIntegral_congr
    (Measure.univ_pi_Ioo_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm).symm

/-- `L^p` norms over `𝕋^ι` (with Mathlib's measure, of total mass one) are `L^p` norms over the open
unit cube `(0, 1)^ι`, for continuous functions and `0 < p < ∞`. -/
theorem eLpNorm_torus_eq_cube {ι : Type*} [Fintype ι] {F : UnitAddTorus ι → ℂ}
    (hF : Continuous F) {p : ℝ} (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) volume =
      eLpNorm (fun x => F (ofPi x)) (ENNReal.ofReal p) (volume.restrict (cube ι)) := by
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal h0 ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal h0 ENNReal.ofReal_ne_top
      (f := fun x => F (ofPi x)) (hF.comp continuous_ofPi).aestronglyMeasurable,
    lintegral_torus_eq_cube (fun z => ‖F z‖ₑ ^ (ENNReal.ofReal p).toReal)]

/-! ### Trigonometric polynomials as functions on `ℝ^ι` -/

theorem trigPoly_ofPi_eq {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    (fun x => trigPoly c (ofPi x)) = fun x => ∑ n ∈ c.support, c n * mFourier n (ofPi x) := by
  funext x
  simp [trigPoly, Finsupp.sum]

theorem contDiff_mFourier_ofPi {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    ContDiff ℝ ∞ fun x : ι → ℝ => mFourier n (ofPi x) := by
  simp_rw [mFourier_ofPi]
  refine Complex.contDiff_exp.comp (contDiff_const.mul (ContDiff.sum fun i _ => ?_))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : ι => ℝ) i))

/-- A trigonometric polynomial, as a function on `ℝ^ι`, is smooth. -/
theorem contDiff_trigPoly_ofPi {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    ContDiff ℝ ∞ fun x => trigPoly c (ofPi x) := by
  rw [trigPoly_ofPi_eq]
  exact ContDiff.sum fun n _ => contDiff_const.mul (contDiff_mFourier_ofPi n)

/-- A trigonometric polynomial, as a function on `ℝ^ι`, is `ℤ^ι`-periodic. -/
theorem isPeriodic_trigPoly_ofPi {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    UnitAddTorus.IsPeriodic fun x => trigPoly c (ofPi x) := fun x k => by
  simp only [ofPi_add_int]

/-- The mean of a trigonometric polynomial over the cube is its coefficient `c₀`. -/
theorem cubeFourierCoeff_trigPoly_ofPi_zero {ι : Type*} [Fintype ι] (c : (ι → ℤ) →₀ ℂ) :
    cubeFourierCoeff (fun x => trigPoly c (ofPi x)) 0 = c 0 := by
  rw [trigPoly_ofPi_eq, cubeFourierCoeff_trig]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm


/-! ### Step 2: `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂_zbar u‖_{L^p (Q)}` -/

/-- From `0 ≤ ∫_Q Φ_p (f, g)` and Burkholder's inequality `Φ_p (z, w) ≤ (p* − 1)^p |z|^p − |w|^p`:
`∫_Q |g|^p ≤ (p* − 1)^p ∫_Q |f|^p`, for continuous `f`, `g`. -/
theorem integral_rpow_le_of_integral_phi_nonneg {p : ℝ} (hp : 1 < p)
    {f g : (Fin 2 → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : 0 ≤ ∫ x in unitSquare, Phi p (f x) (g x)) :
    ∫ x in unitSquare, ‖g x‖ ^ p ≤ (pStar p - 1) ^ p * ∫ x in unitSquare, ‖f x‖ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hF : IntegrableOn (fun x => ‖f x‖ ^ p) unitSquare :=
    integrableOn_cube_of_continuous (hf.norm.rpow_const fun _ => Or.inr hp0)
  have hG : IntegrableOn (fun x => ‖g x‖ ^ p) unitSquare :=
    integrableOn_cube_of_continuous (hg.norm.rpow_const fun _ => Or.inr hp0)
  have hPhi : IntegrableOn (fun x => Phi p (f x) (g x)) unitSquare := by
    refine integrableOn_cube_of_continuous ?_
    unfold Phi
    exact (continuous_const.mul ((continuous_const.mul hf.norm).sub hg.norm)).mul
      ((hf.norm.add hg.norm).rpow_const fun _ => Or.inr (by linarith))
  have hR : IntegrableOn (fun x => (pStar p - 1) ^ p * ‖f x‖ ^ p - ‖g x‖ ^ p) unitSquare :=
    (hF.const_mul _).sub hG
  have hmono := setIntegral_mono hPhi hR fun x => by
    simpa only [bms_pStar_eq] using phi_le hp (f x) (g x)
  rw [integral_sub (hF.const_mul _) hG, integral_const_mul] at hmono
  linarith

/-- `0 ≤ ∫_Q α_p B_p (D φ)` for `φ = (Re u, Im u)`: Corollary 2 at `A = 0`. -/
theorem integral_alpha_mul_burkholderB_nonneg {p : ℝ} (hp : 1 < p) {u : (Fin 2 → ℝ) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    0 ≤ ∫ x in unitSquare, alpha p * burkholderB p (jacobian (toRealPair u) x) := by
  have h := corollary2 hp 0 (contDiff_toRealPair hu) (isPeriodic_toRealPair hper)
  simp only [zero_add, burkholderB_zero, sub_zero] at h
  rw [integral_const_mul]
  exact mul_nonneg (alpha_pos hp).le h

/-- Step 2 for `1 < p < 2`: `∫_Q |∂_zbar u|^p ≤ (p* − 1)^p ∫_Q |∂u|^p` for smooth periodic `u`. -/
theorem integral_norm_dzbarPi_rpow_le_of_lt_two {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzPi u x‖ ^ p := by
  refine integral_rpow_le_of_integral_phi_nonneg hp (contDiff_dzPi hu).continuous
    (contDiff_dzbarPi hu).continuous ?_
  have hd : ∀ x, DifferentiableAt ℝ u x := hu.differentiable (by simp)
  have e : (fun x => Phi p (dzPi u x) (dzbarPi u x)) =
      fun x => alpha p * burkholderB p (jacobian (toRealPair u) x) := by
    funext x
    rw [alpha_mul_burkholderB_of_lt_two hp2, conformalPart_jacobian_toRealPair (hd x),
      anticonformalPart_jacobian_toRealPair (hd x)]
  rw [e]
  exact integral_alpha_mul_burkholderB_nonneg hp hu hper

/-- Step 2 for `2 ≤ p`: `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂_zbar u|^p` for smooth periodic `u`. -/
theorem integral_norm_dzPi_rpow_le_of_two_le {p : ℝ} (hp2 : 2 ≤ p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p := by
  have hp : 1 < p := by linarith
  refine integral_rpow_le_of_integral_phi_nonneg hp (contDiff_dzbarPi hu).continuous
    (contDiff_dzPi hu).continuous ?_
  have hd : ∀ x, DifferentiableAt ℝ u x := hu.differentiable (by simp)
  have e : (fun x => Phi p (dzbarPi u x) (dzPi u x)) =
      fun x => alpha p * burkholderB p (jacobian (toRealPair u) x) := by
    funext x
    rw [alpha_mul_burkholderB_of_two_le hp2, conformalPart_jacobian_toRealPair (hd x),
      anticonformalPart_jacobian_toRealPair (hd x)]
  rw [e]
  exact integral_alpha_mul_burkholderB_nonneg hp hu hper

/-- Step 2: `∫_Q |∂u|^p ≤ (p* − 1)^p ∫_Q |∂_zbar u|^p` for smooth periodic `u` and `1 < p`. For `p
< 2`,
the inequality for `p < 2` applied to `ū`, by the interchangeability of `∂` and `∂_zbar`
(Baernstein–Montgomery-Smith, §1: `∂ū = conj (∂_zbar u)`, `∂_zbarū = conj (∂u)`). This is the
source's
argument; duality (`HarmonicAnalysis.beurlingPowNorm_conjExponent`, `‖𝒮‖_p = ‖𝒮‖_{p'}`) would
also reduce `p < 2` to `p' > 2`, at the level of the norm on `L^p (ℂ)`. -/
theorem integral_norm_dzPi_rpow_le {p : ℝ} (hp : 1 < p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    ∫ x in unitSquare, ‖dzPi u x‖ ^ p ≤
      (pStar p - 1) ^ p * ∫ x in unitSquare, ‖dzbarPi u x‖ ^ p := by
  rcases lt_or_ge p 2 with hp2 | hp2
  · have h := integral_norm_dzbarPi_rpow_le_of_lt_two hp hp2 (contDiff_conj hu)
      (isPeriodic_conj hper)
    simpa only [dzPi_conj, dzbarPi_conj, Complex.norm_conj] using h
  · exact integral_norm_dzPi_rpow_le_of_two_le hp2 hu hper

/-- Step 2, in `L^p` norms: `‖∂u‖_{L^p (Q)} ≤ (p* − 1) ‖∂_zbar u‖_{L^p (Q)}` for smooth periodic
`u` and
`1 < p`. -/
theorem eLpNorm_dzPi_le {p : ℝ} (hp : 1 < p)
    {u : (Fin 2 → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u) (hper : UnitAddTorus.IsPeriodic u) :
    eLpNorm (dzPi u) (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) ≤
      ENNReal.ofReal (pStar p - 1) *
        eLpNorm (dzbarPi u) (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) := by
  have hp0 : 0 < p := by linarith
  have h0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hc : 0 ≤ pStar p - 1 := by linarith [le_pStar p]
  have hmem : ∀ g : (Fin 2 → ℝ) → ℂ, Continuous g → UnitAddTorus.IsPeriodic g →
      MemLp g (ENNReal.ofReal p) (volume.restrict (cube (Fin 2))) := by
    intro g hg hgp
    obtain ⟨C, hC⟩ := hgp.exists_bound hg
    exact MemLp.of_bound hg.aestronglyMeasurable C (ae_of_all _ hC)
  rw [(hmem _ (contDiff_dzPi hu).continuous (isPeriodic_dzPi hper)).eLpNorm_eq_integral_rpow_norm
      h0 ENNReal.ofReal_ne_top,
    (hmem _ (contDiff_dzbarPi hu).continuous
      (isPeriodic_dzbarPi hper)).eLpNorm_eq_integral_rpow_norm h0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hI2 : 0 ≤ ∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p :=
    integral_nonneg fun x => by positivity
  calc (∫ x in cube (Fin 2), ‖dzPi u x‖ ^ p) ^ p⁻¹
      ≤ ((pStar p - 1) ^ p * ∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x => by positivity)
          (integral_norm_dzPi_rpow_le hp hu hper) (inv_nonneg.2 hp0.le)
    _ = (pStar p - 1) * (∫ x in cube (Fin 2), ‖dzbarPi u x‖ ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (by positivity) hI2, Real.rpow_rpow_inv hc hp0.ne']

/-! ### Step 3: the bound on the torus -/

/-- `‖𝓑 h‖_{L^p (𝕋²)} ≤ (p* − 1) ‖h‖_{L^p (𝕋²)}` for every mean-zero trigonometric polynomial `h`
(coefficients `c`, `c₀ = 0`): `h = ∂_zbar u` for a smooth periodic `u`, and `𝓑 h = ∂u`. -/
theorem eLpNorm_torusBeurlingPow_le {p : ℝ} (hp : 1 < p) (c : (Fin 2 → ℤ) →₀ ℂ) (hc : c 0 = 0) :
    eLpNorm (HarmonicAnalysis.torusBeurlingPow 1 c) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (pStar p - 1) *
        eLpNorm (HarmonicAnalysis.trigPoly c) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  obtain ⟨u, hu, hup, -, hdu⟩ := exists_dzbarPi_eq (contDiff_trigPoly_ofPi c)
    (isPeriodic_trigPoly_ofPi c) (by rw [cubeFourierCoeff_trigPoly_ofPi_zero, hc])
  have key : (fun x => HarmonicAnalysis.torusBeurlingPow 1 c (ofPi x)) = dzPi u := by
    rw [← HarmonicAnalysis.periodicMultiplier_beurlingSymbol_dzbarPi hu hup, hdu,
      ← HarmonicAnalysis.periodicMultiplier_trigPoly 1 c]
    simp only [pow_one]
  have hcont : Continuous (HarmonicAnalysis.torusBeurlingPow 1 c) :=
    HarmonicAnalysis.continuous_torusMultiplier _ c
  rw [eLpNorm_torus_eq_cube hcont hp0,
    eLpNorm_torus_eq_cube (HarmonicAnalysis.continuous_trigPoly c) hp0, key, ← hdu]
  exact eLpNorm_dzPi_le hp hu hup

/-- Step 3: the norm of the Beurling–Ahlfors multiplier on `L^p_0 (𝕋²)` is at most `p* − 1`. -/
theorem torusBeurlingPowNorm_one_le {p : ℝ} (hp : 1 < p) :
    HarmonicAnalysis.torusBeurlingPowNorm 1 p ≤ ENNReal.ofReal (pStar p - 1) :=
  iSup₂_le fun c hc => ENNReal.div_le_of_le_mul (eLpNorm_torusBeurlingPow_le hp c hc)

end Agazzi.Corollary2NormTorus

namespace Agazzi

/-- **A shorter proof of the upper bound in `(eq:BA-sharp-norm)`**, `‖𝒮‖_p ≤ p* − 1` for
`1 < p < ∞`, not used by `corollary2_norm`: Corollary 2 on the torus at `A = 0` and Burkholder's
inequality give the bound on `L^p_0 (𝕋²)` (`Corollary2NormTorus.torusBeurlingPowNorm_one_le`),
and transference (Hytönen–van Neerven–Veraar–Weis, Corollary 5.7.6,
`HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm`) gives `L^p (ℂ)`. It is shorter than
the paper's planar route (`beurlingNorm_le`): no Cauchy transform and no cut-offs. -/
theorem beurlingNorm_le_of_torus {p : ℝ} (hp : 1 < p) :
    beurlingNorm p ≤ ENNReal.ofReal (pStar p - 1) := by
  rw [beurlingNorm_eq_beurlingPowNorm]
  exact (HarmonicAnalysis.beurlingPowNorm_le_torusBeurlingPowNorm 1 hp).trans
    (Corollary2NormTorus.torusBeurlingPowNorm_one_le hp)

end Agazzi
