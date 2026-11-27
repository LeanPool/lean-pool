/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentGaussianMoments
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual Gaussian monomials in complex-plane L²

Normalized Gaussian monomials form an orthonormal family for complex
Lebesgue measure. The pinned Hilbert-sum construction therefore supplies
an actual isometry from the infinite oscillator ℓ² space into this L²
space. No surjectivity onto all L², pointwise evaluation theorem, or
Gaussian sandwich formula is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate

/-- Bargmann monomial given by `(Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt (Real.pi * (n.factorial : ℝ))
: ℝ) * z ^ n`. -/
noncomputable def bargmannMonomial (n : ℕ) (z : ℂ) : ℂ :=
  (Real.exp (-‖z‖ ^ 2 / 2) / Real.sqrt (Real.pi * (n.factorial : ℝ)) : ℝ) * z ^ n

theorem bargmannMonomial_norm_sq (n : ℕ) (z : ℂ) :
    ‖bargmannMonomial n z‖ ^ 2 =
      (‖z‖ ^ (2 * n) * Real.exp (-‖z‖ ^ 2)) / (Real.pi * (n.factorial : ℝ)) := by
  have hexp : Real.exp (-‖z‖ ^ 2 / 2) ^ 2 = Real.exp (-‖z‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [bargmannMonomial, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, div_pow, Real.sq_sqrt (by positivity), hexp, norm_pow, ← pow_mul]
  rw [Nat.mul_comm n 2]
  ring

theorem memLp_bargmannMonomial (n : ℕ) :
    MemLp (bargmannMonomial n) 2 (volume : Measure ℂ) := by
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr
  · have h := (integrable_gaussian_radial_even_moment (a := 1) (by norm_num) n).div_const
      (Real.pi * (n.factorial : ℝ))
    simpa only [bargmannMonomial_norm_sq, neg_mul, one_mul] using h
  · have hc : Continuous (bargmannMonomial n) := by unfold bargmannMonomial; fun_prop
    exact hc.aestronglyMeasurable

theorem integral_bargmannMonomial_norm_sq (n : ℕ) :
    (∫ z : ℂ, ‖bargmannMonomial n z‖ ^ 2) = 1 := by
  simp_rw [bargmannMonomial_norm_sq]
  rw [integral_div]
  have h := integral_gaussian_radial_even_moment (a := 1) (by norm_num) n
  simp only [neg_mul, one_mul, one_pow, div_one] at h
  rw [h, div_self (by positivity : Real.pi * (n.factorial : ℝ) ≠ 0)]

theorem bargmannMonomial_inner (m n : ℕ) (z : ℂ) :
    inner ℂ (bargmannMonomial m z) (bargmannMonomial n z) =
      (Real.sqrt (Real.pi * (m.factorial : ℝ)) *
        Real.sqrt (Real.pi * (n.factorial : ℝ)) : ℂ)⁻¹ *
      ((Real.exp (-‖z‖ ^ 2) : ℂ) * conj z ^ m * z ^ n) := by
  have hexp : Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (-‖z‖ ^ 2 / 2) =
      Real.exp (-‖z‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  rw [RCLike.inner_apply', bargmannMonomial, bargmannMonomial,
    map_mul, map_pow, Complex.conj_ofReal]
  push_cast
  calc
    _ = (((Real.exp (-‖z‖ ^ 2 / 2) * Real.exp (-‖z‖ ^ 2 / 2) : ℝ) : ℂ) /
        ((Real.sqrt (Real.pi * (m.factorial : ℝ)) : ℂ) *
          (Real.sqrt (Real.pi * (n.factorial : ℝ)) : ℂ))) *
          conj z ^ m * z ^ n := by push_cast; ring
    _ = _ := by
      have hc : Complex.exp (-((‖z‖ : ℝ) : ℂ) ^ 2) =
          ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        rfl
      rw [hexp, hc]
      ring

/-- The Gaussian monomial as an actual L² equivalence class. -/
noncomputable def bargmannBasisVector (n : ℕ) : Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_bargmannMonomial n).toLp (bargmannMonomial n)

theorem inner_bargmannBasisVector (m n : ℕ) :
    inner ℂ (bargmannBasisVector m) (bargmannBasisVector n) =
      if m = n then 1 else 0 := by
  rw [L2.inner_def]
  have hae : (fun z => inner ℂ (bargmannBasisVector m z) (bargmannBasisVector n z))
      =ᵐ[volume] fun z => inner ℂ (bargmannMonomial m z) (bargmannMonomial n z) := by
    filter_upwards [(memLp_bargmannMonomial m).coeFn_toLp,
      (memLp_bargmannMonomial n).coeFn_toLp] with z hm hn
    change inner ℂ (((memLp_bargmannMonomial m).toLp (bargmannMonomial m) :
      Lp ℂ 2 (volume : Measure ℂ)) z)
      (((memLp_bargmannMonomial n).toLp (bargmannMonomial n) :
      Lp ℂ 2 (volume : Measure ℂ)) z) = _
    rw [hm, hn]
  rw [integral_congr_ae hae]
  by_cases hmn : m = n
  · subst m
    simp only [ite_true, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, integral_bargmannMonomial_norm_sq, Complex.ofReal_one]
  · simp only [hmn, ite_false]
    simp_rw [bargmannMonomial_inner]
    rw [integral_const_mul]
    have h := integral_gaussian_monomial (a := 1) (by norm_num) m n
    simp only [neg_mul, one_mul, hmn, ite_false] at h
    rw [h, mul_zero]

theorem orthonormal_bargmannBasisVector : Orthonormal ℂ bargmannBasisVector :=
  orthonormal_iff_ite.mpr inner_bargmannBasisVector

/-- A genuine infinite-dimensional Bargmann isometry into complex-plane L².
Its range is the closed span of the Gaussian monomials; no assertion that
this range is the whole L² space is made here. -/
noncomputable def bargmannL2 : OscillatorSpace →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  orthonormal_bargmannBasisVector.orthogonalFamily.linearIsometry

theorem bargmannL2_apply_single (n : ℕ) (c : ℂ) :
    bargmannL2 (lp.single 2 n c) = c • bargmannBasisVector n := by
  rw [bargmannL2, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

theorem norm_bargmannL2 (x : OscillatorSpace) : ‖bargmannL2 x‖ = ‖x‖ :=
  bargmannL2.norm_map x

end VacuumBellSeparation.Gaussian
