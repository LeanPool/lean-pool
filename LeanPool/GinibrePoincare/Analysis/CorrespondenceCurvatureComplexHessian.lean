/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceCurvatureComplexHessian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaCutoff

/-!
# Correspondence curvature complex hessian

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondence_gaussian_strict_plurisubharmonic`.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped ComplexConjugate ContDiff

/-- Literal flat complex Hessian (2.20) of the Gaussian potential Φ=n|z|². -/
theorem correspondence_gaussian_complex_hessian (n : ℕ) (j k : Fin n)
    (z : Configuration n) :
    bkPartial (dbarComponent (fun w : Configuration n =>
      ((n : ℝ)*configurationNormSq w : ℂ)) k) j z =
      if j = k then (n : ℂ) else 0 := by
  have he : dbarComponent (fun w : Configuration n =>
      ((n : ℝ)*configurationNormSq w : ℂ)) k =
      fun w => (n : ℂ)*w k := by
    funext w
    have h := bkRadial_dbar (fun r : ℝ => (n : ℝ)*r)
      (contDiff_const.mul contDiff_id) k w
    simpa using h
  rw [he]
  let L : Configuration n →L[ℝ] ℂ := (n : ℂ) • ContinuousLinearMap.proj k
  have hL : (fun w : Configuration n => (n : ℂ)*w k) = L := by funext w; rfl
  rw [hL]
  unfold bkPartial bkDirectional
  rw [L.fderiv]
  simp only [L, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
  by_cases hjk : j = k
  · subst k
    simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp [hjk, Ne.symm hjk]

/-- Strict plurisubharmonicity follows for every nonzero complex tangent vector. -/
theorem correspondence_gaussian_strict_plurisubharmonic (n : ℕ) (hn : 0 < n)
    (z v : Configuration n) (hv : v ≠ 0) :
    0 < (∑ j : Fin n, ∑ k : Fin n, conj (v j)*
      bkPartial (dbarComponent (fun w : Configuration n =>
        ((n : ℝ)*configurationNormSq w : ℂ)) k) j z*v k).re := by
  classical
  simp_rw [correspondence_gaussian_complex_hessian]
  have he (j : Fin n) : (∑ k : Fin n, conj (v j)*(if j=k then (n : ℂ) else 0)*v k) =
      (n : ℂ)*(Complex.normSq (v j) : ℂ) := by
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  simp_rw [he, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  rw [← Finset.mul_sum]
  apply mul_pos (Nat.cast_pos.mpr hn)
  have hex : ∃j : Fin n, v j≠0 := by
    by_contra h
    apply hv
    ext j
    simpa using not_exists.mp h j
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_pos' (fun k hk => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _,
      Complex.normSq_pos.mpr hj⟩

end
end GinibrePoincare

