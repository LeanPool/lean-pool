/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianDrift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonian

/-! The implemented Langevin drift is the negative Hamiltonian gradient. -/

@[expose] public section
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

theorem ginibreCoulombInteraction_re (n : ℕ) (z : Configuration n) (j : Fin n) :
    (ginibreCoulombInteraction n z j).re =
      ∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).re := by
  unfold ginibreCoulombInteraction
  rw [show (∑ k : Fin n, (z j-z k)/(Complex.normSq (z j-z k) : ℂ)).re =
      ∑ k : Fin n, ((z j-z k)/(Complex.normSq (z j-z k) : ℂ)).re by
    exact map_sum Complex.reCLM _ _]
  simp_rw [Complex.div_ofReal_re, ← Complex.inv_re]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm.trans (by simp)

theorem ginibreCoulombInteraction_im (n : ℕ) (z : Configuration n) (j : Fin n) :
    (ginibreCoulombInteraction n z j).im =
      -(∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).im) := by
  unfold ginibreCoulombInteraction
  rw [show (∑ k : Fin n, (z j-z k)/(Complex.normSq (z j-z k) : ℂ)).im =
      ∑ k : Fin n, ((z j-z k)/(Complex.normSq (z j-z k) : ℂ)).im by
    exact map_sum Complex.imCLM _ _]
  have hh : ∀ k, ((z j-z k)/(Complex.normSq (z j-z k) : ℂ)).im =
      -((z j-z k)⁻¹).im := by
    intro k
    simp only [Complex.div_ofReal_im, Complex.inv_im]
    ring
  simp_rw [hh, Finset.sum_neg_distrib]
  congr 1
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm.trans (by simp)

theorem ginibreLangevinDrift_re_hamiltonian {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    (ginibreLangevinDrift n α z j).re =
      -(α / (n : ℝ)^2) *
        fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j) := by
  rw [fderiv_ginibreHamiltonian_realCoordinate hn z hz j]
  unfold ginibreLangevinDrift ginibreRealDriftCoordinate
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [ginibreCoulombInteraction_re]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hne]
 ; ring

theorem ginibreLangevinDrift_im_hamiltonian {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    (ginibreLangevinDrift n α z j).im =
      -(α / (n : ℝ)^2) *
        fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j) := by
  rw [fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz j]
  unfold ginibreLangevinDrift ginibreImagDriftCoordinate
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [ginibreCoulombInteraction_im]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hne]
 ; ring

end
end GinibrePoincare
