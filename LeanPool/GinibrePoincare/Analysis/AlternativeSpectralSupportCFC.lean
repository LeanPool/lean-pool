/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeSpectralSupportCFC.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
/-!
# Alternative spectral support CFC

Part of the poincaré deficits and equality development of the
Ginibre Poincaré formalization.

Main results: `spectralSupportCFC_pencil_isUnit_of_positive_polynomial`,
`spectralSupportCFC_spectrum_gap_of_adjoint_form`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The polynomial `r * (1 - r) ^ 2 * (1 - 3 * r)`, whose nonnegativity on a spectrum contained
in `[0, 1]` confines the spectrum to `[0, 1/3] ∪ {1}`. -/
def spectralSupportPolynomial (r : ℝ) : ℝ := r*(1-r)^2*(1-3*r)

theorem spectralSupportCFC_spectrum_gap (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hPos : (cfc spectralSupportPolynomial R).IsPositive) :
    spectrum ℝ R ⊆ Icc (0 : ℝ) (1/3) ∪ {1} := by
  have hp : ∀ r ∈ spectrum ℝ R, 0 ≤ spectralSupportPolynomial r :=
    (cfc_nonneg_iff spectralSupportPolynomial R (by unfold spectralSupportPolynomial;fun_prop)
        hR).mp
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hPos)
  intro r hr
  have hb := hSpec hr
  by_cases hthird : r ≤ 1/3
  · exact Or.inl ⟨hb.1, hthird⟩
  · right
    change r = 1
    by_contra he
    have h0 : 0 < r := by linarith
    have hs : 0 < (1-r)^2 := sq_pos_of_ne_zero (by intro hz;apply he;linarith)
    have hn : 1-3*r < 0 := by linarith
    have hnegative : spectralSupportPolynomial r < 0 := mul_neg_of_pos_of_neg (mul_pos h0 hs) hn
    exact (not_lt_of_ge (hp r hr)) hnegative

theorem spectralSupportCFC_affine_nonzero (lam r : ℝ) (hlam : -2 < lam) (hne : lam ≠ 0)
    (hr : r ∈ Icc (0 : ℝ) (1 / 3) ∪ {1}) : 1+(lam-1)*r ≠ 0 := by
  rcases hr with hr | hr
  · by_cases hz : r = 0
    · simp [hz]
    · have hpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hz)
      have hm : 0 < (lam+2)*r := mul_pos (by linarith) hpos
      have hn : 0 ≤ 1-3*r := by linarith [hr.2]
      nlinarith
  · have he : r = 1 := hr
    subst r
    simpa using hne

theorem spectralSupportCFC_real_pencil_isUnit (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) (1 / 3) ∪ {1})
    (lam : ℝ) (hlam : -2 < lam) (hne : lam ≠ 0) : IsUnit (1+(lam-1) • R) := by
  have hu : IsUnit (cfc (fun r : ℝ => 1+(lam-1)*r) R) :=
    (isUnit_cfc_iff _ R (by fun_prop) hR).mpr
      (fun r hr => spectralSupportCFC_affine_nonzero lam r hlam hne (hSpec hr))
  rw [cfc_const_add 1 (fun r : ℝ => (lam-1)*r) R (by fun_prop) hR,
    cfc_const_mul_id (lam-1) R hR, map_one] at hu
  exact hu

theorem spectralSupportCFC_pencil_isUnit (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) (1 / 3) ∪ {1})
    (lam : ℝ) (hlam : -2 < lam) (hne : lam ≠ 0) :
    IsUnit (1+((lam : ℂ)-1) • R) := by
  have hs : (lam-1 : ℝ) • R = ((lam : ℂ)-1) • R := by
    ext x
    change (lam-1 : ℝ) • (R x) = ((lam : ℂ)-1) • (R x)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ((lam-1 : ℝ) : ℂ) • (R x) = ((lam : ℂ)-1) • (R x)
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  rw [←hs]
  exact spectralSupportCFC_real_pencil_isUnit R hR hSpec lam hlam hne

theorem spectralSupportCFC_pencil_isUnit_of_positive_polynomial
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hPos : (cfc (fun r : ℝ => r*(1-r)^2*(1-3*r)) R).IsPositive)
    (lam : ℝ) (hlam : -2 < lam) (hne : lam ≠ 0) :
    IsUnit (1+((lam : ℂ)-1) • R) :=
  spectralSupportCFC_pencil_isUnit R hR (spectralSupportCFC_spectrum_gap R hR hSpec hPos) lam hlam
      hne

theorem spectralSupportCFC_polynomial_algebra (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    cfc spectralSupportPolynomial R = R*(1-R)^2*(1-(3 : ℝ) • R) := by
  unfold spectralSupportPolynomial
  rw [cfc_mul (fun r : ℝ => r*(1-r)^2) (fun r : ℝ => 1-3*r) R (by fun_prop) (by fun_prop),
    cfc_mul (fun r : ℝ => r) (fun r : ℝ => (1-r)^2) R (by fun_prop) (by fun_prop),
    cfc_id' ℝ R hR, cfc_pow (fun r : ℝ => 1-r) 2 R (by fun_prop) hR,
    cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => r) R (by fun_prop) (by fun_prop),
    cfc_sub (fun _ : ℝ => 1) (fun r : ℝ => 3*r) R (by fun_prop) (by fun_prop),
    cfc_id' ℝ R hR, cfc_const_mul_id 3 R hR, cfc_const_one ℝ R hR]

theorem spectralSupportCFC_polynomial_adjoint_form (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) :
    cfc (fun r : ℝ => r*(1-r)^2*(1-3*r)) R =
      star (1-R)*R*(1-R) - (3 : ℝ) • (star (R*(1-R))*(R*(1-R))) := by
  rw [show (fun r : ℝ => r*(1-r)^2*(1-3*r)) = spectralSupportPolynomial from rfl,
    spectralSupportCFC_polynomial_algebra R hR]
  simp only [star_sub, star_one, star_mul, hR.star_eq, Algebra.smul_def, map_ofNat]
  noncomm_ring

theorem spectralSupportCFC_spectrum_gap_of_adjoint_form
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (hSpec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hPos : (star (1 - R) * R * (1 - R) - (3 : ℝ) • (star (R * (1 - R)) * (R * (1 -
        R)))).IsPositive) :
    spectrum ℝ R ⊆ Icc (0 : ℝ) (1/3) ∪ {1} := by
  have hp : (cfc spectralSupportPolynomial R).IsPositive := by
    rw [show spectralSupportPolynomial = (fun r : ℝ => r*(1-r)^2*(1-3*r)) from rfl,
      spectralSupportCFC_polynomial_adjoint_form R hR]
    exact hPos
  exact spectralSupportCFC_spectrum_gap R hR hSpec hp

end
end GinibrePoincare
