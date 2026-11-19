/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixUnitaryCenteredPhaseFactorization.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixUnitaryDiagonalPhase

/-!
# Matrix unitary centered phase factorization

Part of the matrix lift and eigenvector overlaps development of the
Ginibre Poincaré formalization.

Main results: `matrixUnitary_centered_phase_factorization`.
-/

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section

theorem matrixInverseCayley_continuousAt {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hden : IsUnit (U + 1)) : ContinuousAt matrixInverseCayley U := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hi : ContinuousAt (Ring.inverse : M → M) (U + 1) := by
    have h := NormedRing.inverse_continuousAt hden.unit
    rw [hden.unit_spec] at h
    exact h
  have hsum : ContinuousAt (fun V : M => V + 1) U := by fun_prop
  have hsub : ContinuousAt (fun V : M => V - 1) U := by fun_prop
  have hinv : ContinuousAt (fun V : M => Ring.inverse (V + 1)) U :=
    Filter.Tendsto.comp (show Tendsto Ring.inverse (𝓝 (U + 1)) (𝓝 (Ring.inverse (U + 1))) from hi)
      (show Tendsto (fun V : M => V + 1) (𝓝 U) (𝓝 (U + 1)) from hsum)
  have hc := hsub.mul hinv
  have hf : (matrixInverseCayley : M → M) =
      (fun V => (V - 1) * Ring.inverse (V + 1)) := by
    funext V
    rw [matrixInverseCayley, Matrix.nonsing_inv_eq_ringInverse]
  rw [hf]
  exact hc

theorem matrixUnitaryPhaseParameter_continuous (n : ℕ) : Continuous (matrixUnitaryPhaseParameter n)
    := by
  let C := MatrixSkewCoordinates n
  let M := Matrix (Fin n) (Fin n) ℂ
  let S := (schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ (SchurLowerIndex n → ℂ) (Fin n → ℝ))
  let D := (matrixSkewDiagonalCLM n).comp (ContinuousLinearMap.snd ℝ (SchurLowerIndex n → ℂ) (Fin n
      → ℝ))
  have he : Continuous (exp : M → M) := exp_continuous
  have hc := (he.comp S.continuous).mul (he.comp D.continuous)
  have hf : matrixUnitaryPhaseParameter n = (fun p : C => exp (S p) * exp (D p)) := by
    funext p
    change exp (schurSkewCombination p.1) * exp (matrixSkewDiagonalCLM n p.2) =
      exp (schurSkewCLM n p.1) * exp (matrixSkewDiagonalCLM n p.2)
    rw [schurSkewCLM_apply]
  rw [hf]
  exact hc

/-- The actual unitary phase chart admits arbitrarily small local inverses at every
point of its source with invertible Cayley denominator, not only at the identity. -/
theorem matrixUnitary_centered_phase_factorization (n : ℕ)
    (p0 : MatrixSkewCoordinates n) (hp0 : p0 ∈ (matrixUnitaryPhaseLocalChart n).source)
    (hden : IsUnit (matrixUnitaryPhaseParameter n p0 + 1))
    (N : Set (MatrixSkewCoordinates n)) (hN : N ∈ 𝓝 p0) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 (matrixUnitaryPhaseParameter n p0),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
        ∃ p ∈ N, matrixUnitaryPhaseParameter n p = U := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let C := MatrixSkewCoordinates n
  let U0 := matrixUnitaryPhaseParameter n p0
  let e := matrixUnitaryPhaseLocalChart n
  let R : M →L[ℝ] C := (matrixSkewReadCoordinates n).toContinuousLinearMap
  let w : M → C := fun U => R (matrixInverseCayley U)
  have hw0 : w U0 = e p0 := rfl
  have hw : ContinuousAt w U0 := R.continuous.continuousAt.comp (matrixInverseCayley_continuousAt U0
      hden)
  have htarget : w U0 ∈ e.target := hw0 ▸ e.map_source hp0
  let p : M → C := fun U => e.symm (w U)
  have hpbase : p U0 = p0 := e.left_inv hp0
  have hp : ContinuousAt p U0 := (e.continuousAt_symm htarget).comp hw
  have hparam : ContinuousAt (matrixUnitaryPhaseParameter n) (p U0) :=
    (matrixUnitaryPhaseParameter_continuous n).continuousAt
  have hdP : ContinuousAt (fun U : M => (matrixUnitaryPhaseParameter n (p U) + 1).det) U0 := by
    have hh := hparam.comp hp
    fun_prop
  have hnP : (matrixUnitaryPhaseParameter n (p U0) + 1).det ≠ 0 := by
    rw [hpbase]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hden)
  have hdU : ContinuousAt (fun U : M => (U + 1).det) U0 := by fun_prop
  have hnU : (U0 + 1).det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hden)
  have hevent : ∀ᶠ U : M in 𝓝 U0, w U ∈ e.target := hw (e.open_target.mem_nhds htarget)
  have hpN : ∀ᶠ U : M in 𝓝 U0, p U ∈ N := hp (by rw [hpbase]; exact hN)
  filter_upwards [hevent, hdP.eventually_ne hnP, hdU.eventually_ne hnU, hpN] with U htargetU hP
      hdenU hmem
  intro hunit
  refine ⟨p U, hmem, matrixUnitaryPhaseParameter_eq_of_coordinates n U hunit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdenU)) (p U)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hP)) ?_⟩
  exact e.right_inv htargetU

end
end GinibrePoincare
