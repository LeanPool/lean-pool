/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSpectralSobolevPolynomialDomain.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSpectralSobolevReindex

/-! # Actual full weak derivatives through a polynomial collision locus -/

@[expose] public section
open MeasureTheory MvPolynomial
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem polynomial_collision_coordinate_weak_test (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : Configuration (d + 1) → ℝ) (hF : Continuous F)
    (hd : ∀ z, eval z p ≠ 0 → DifferentiableAt ℝ F z)
    (hf : LocallyIntegrable F volume)
    (k : Fin (d + 1) × Fin 2)
    (hg : LocallyIntegrable (fun z => fderiv ℝ F z (ginibreCoordinateDirection k)) volume)
    (θ : Configuration (d + 1) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    (∫ z, fderiv ℝ F z (ginibreCoordinateDirection k) * θ z) =
      -(∫ z, F z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  classical
  let L := configurationFirstReindex k.1
  let σ := Equiv.swap (0 : Fin (d + 1)) k.1
  let q := MvPolynomial.renameEquiv ℂ σ.symm p
  have hq : q ≠ 0 := by
    intro h
    exact hp ((MvPolynomial.renameEquiv ℂ σ.symm).injective (by simpa [q] using h))
  have heval (z : Configuration (d + 1)) : eval z q = eval (L z) p := by
    change eval z (MvPolynomial.rename σ.symm p) = _
    rw [MvPolynomial.eval_rename]
    rfl
  have hdq (z : Configuration (d + 1)) (hz : eval z q ≠ 0) :
      DifferentiableAt ℝ (F ∘ L) z := by
    rw [heval] at hz
    exact (hd _ hz).comp z L.differentiableAt
  let a : ℂ := if k.2 = 0 then 1 else Complex.I
  let v : Configuration (d + 1) := Fin.cons a 0
  have hv : L v = ginibreCoordinateDirection k := by
    rw [configurationFirstReindex_direction]
    by_cases hk : k.2 = 0 <;>
      simp [a, ginibreCoordinateDirection, hk, realCoordinateDirection,
          imaginaryCoordinateDirection]
  have hder (f : Configuration (d + 1) → ℝ) (z : Configuration (d + 1)) :
      fderiv ℝ (f ∘ L) z v = fderiv ℝ f (L z) (ginibreCoordinateDirection k) := by
    rw [L.comp_right_fderiv]
    exact congrArg (fderiv ℝ f (L z)) hv
  have hgl : LocallyIntegrable (fun z => fderiv ℝ (F ∘ L) z v) volume := by
    apply (configurationFirstReindex_locallyIntegrable k.1 _ hg).congr
    exact Filter.Eventually.of_forall fun z => (hder F z).symm
  have hθl : ContDiff ℝ ∞ (θ ∘ L) := hθ.comp L.contDiff
  have hcl : HasCompactSupport (θ ∘ L) := hc.comp_homeomorph L.toHomeomorph
  have hfirst : (∫ z, fderiv ℝ (F ∘ L) z v * (θ ∘ L) z) =
      -(∫ z, (F ∘ L) z * fderiv ℝ (θ ∘ L) z v) := by
    by_cases hk : k.2 = 0
    · have hv' : v = Fin.cons (1 : ℂ) 0 := by simp [v, a, hk]
      rw [hv'] at hgl ⊢
      exact polynomial_collision_real_first_weak_test d q hq (F ∘ L)
        (hF.comp L.continuous) hdq
        (configurationFirstReindex_locallyIntegrable k.1 F hf) hgl (θ ∘ L) hθl hcl
    · have hv' : v = Fin.cons Complex.I 0 := by simp [v, a, hk]
      rw [hv'] at hgl ⊢
      exact polynomial_collision_imag_first_weak_test d q hq (F ∘ L)
        (hF.comp L.continuous) hdq
        (configurationFirstReindex_locallyIntegrable k.1 F hf) hgl (θ ∘ L) hθl hcl
  have hMP := configurationFirstReindex_volume_preserving k.1
  rw [← hMP.integral_comp L.toHomeomorph.measurableEmbedding
      (fun z => fderiv ℝ F z (ginibreCoordinateDirection k) * θ z),
    ← hMP.integral_comp L.toHomeomorph.measurableEmbedding
      (fun z => F z * fderiv ℝ θ z (ginibreCoordinateDirection k))]
  simp only [hder] at hfirst
  simpa only [Function.comp_def] using hfirst

end
end GinibrePoincare
