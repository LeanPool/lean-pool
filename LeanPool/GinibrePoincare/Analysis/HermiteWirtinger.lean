/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteWirtinger.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MultivariateComplexHermite
public import LeanPool.GinibrePoincare.Concrete.Wirtinger
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Complex Hermite functions and concrete Wirtinger derivatives

This file connects formal partial differentiation of the two-variable
Hermite polynomial with the real-Fréchet definition of `dbar` used by the
concrete Ginibre development.
-/


@[expose] public section


namespace GinibrePoincare

open scoped BigOperators ComplexConjugate

namespace ComplexHermite

noncomputable section

def diagonalEval (P : Poly) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, conj z] P

def diagonalEvalPublic (P : Poly) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, conj z] P

def dbarOne (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- Public one-variable Wirtinger `dbar` operator. -/
def dbarOnePublic (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

theorem dbarOnePublic_eq_dbarOne (f : ℂ → ℂ) :
    dbarOnePublic f = dbarOne f := rfl

private theorem differentiable_diagonalEval (P : Poly) :
    Differentiable ℝ (diagonalEval P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEval (MvPolynomial.C a) = fun _ : ℂ => a by
        funext z
        simp [diagonalEval]]
      exact (differentiable_const (c := a) :
        Differentiable ℝ (fun _ : ℂ => a))
  | add P Q hP hQ =>
      rw [show diagonalEval (P + Q) = diagonalEval P + diagonalEval Q by
        funext z
        simp [diagonalEval]]
      exact hP.add hQ
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEval (P * MvPolynomial.X (0 : ComplexHermiteIndex)) =
            diagonalEval P * id by
          funext z
          simp [diagonalEval]]
        exact hP.mul differentiable_id
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hzero
            apply hi
            apply Fin.ext
            simpa using hzero
          apply Fin.ext
          omega
        subst i
        rw [show diagonalEval (P * MvPolynomial.X (1 : ComplexHermiteIndex)) =
            diagonalEval P * (conj : ℂ → ℂ) by
          funext z
          simp [diagonalEval]]
        exact hP.mul Complex.conjCLE.differentiable

theorem differentiable_diagonalEval_public (P : Poly) :
    Differentiable ℝ (diagonalEval P) := differentiable_diagonalEval P

theorem contDiff_diagonalEval_public (P : Poly) :
    ContDiff ℝ 1 (diagonalEval P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEval (MvPolynomial.C a) = fun _ : ℂ ↦ a by
        funext z; simp [diagonalEval]]
      fun_prop
  | add P Q hP hQ =>
      rw [show diagonalEval (P + Q) = diagonalEval P + diagonalEval Q by
        funext z; simp [diagonalEval]]
      exact hP.add hQ
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEval (P * MvPolynomial.X 0) = diagonalEval P * id by
          funext z; simp [diagonalEval]]
        exact hP.mul contDiff_id
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hz; apply hi; apply Fin.ext; simpa using hz
          apply Fin.ext
          omega
        subst i
        rw [show diagonalEval (P * MvPolynomial.X 1) =
            diagonalEval P * (conj : ℂ → ℂ) by
          funext z; simp [diagonalEval]]
        exact hP.mul Complex.conjCLE.contDiff

theorem exists_fderiv_diagonalEval_polynomial (P : Poly) (v : ℂ) :
    ∃ Q : Poly, ∀ z : ℂ,
      (fderiv ℝ (diagonalEval P) z) v = diagonalEval Q z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      intro z
      rw [show diagonalEval (MvPolynomial.C a) = fun _ : ℂ ↦ a by
        funext w; simp [diagonalEval]]
      simp [diagonalEval]
  | add P Q hP hQ =>
      obtain ⟨R, hR⟩ := hP
      obtain ⟨S, hS⟩ := hQ
      refine ⟨R + S, ?_⟩
      intro z
      rw [show diagonalEval (P + Q) = diagonalEval P + diagonalEval Q by
        funext w; simp [diagonalEval],
        fderiv_add ((differentiable_diagonalEval P) z)
          ((differentiable_diagonalEval Q) z)]
      simp [hR, hS, diagonalEval]
  | mul_X P i hP =>
      obtain ⟨Q, hQ⟩ := hP
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        refine ⟨Q * MvPolynomial.X 0 + MvPolynomial.C v * P, ?_⟩
        intro z
        rw [show diagonalEval (P * MvPolynomial.X 0) = diagonalEval P * id by
          funext w; simp [diagonalEval],
          fderiv_mul ((differentiable_diagonalEval P) z) differentiableAt_id]
        simp [hQ, diagonalEval]
        ring
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hz
            apply hi
            apply Fin.ext
            simpa using hz
          apply Fin.ext
          omega
        subst i
        refine ⟨Q * MvPolynomial.X 1 + MvPolynomial.C (conj v) * P, ?_⟩
        intro z
        rw [show diagonalEval (P * MvPolynomial.X 1) =
            diagonalEval P * (conj : ℂ → ℂ) by
          funext w; simp [diagonalEval],
          fderiv_mul ((differentiable_diagonalEval P) z)
            (Complex.differentiable_conj z)]
        have hc : (fderiv ℝ (conj : ℂ → ℂ) z) v = conj v := by
          change (fderiv ℝ (Complex.conjCLE : ℂ → ℂ) z) v = _
          rw [Complex.conjCLE.hasFDerivAt.fderiv]
          rfl
        simp [hQ, diagonalEval, hc]
        ring

theorem contDiff_diagonalEvalPublic (P : Poly) :
    ContDiff ℝ 1 (diagonalEvalPublic P) :=
  contDiff_diagonalEval_public P

theorem exists_fderiv_diagonalEvalPublic_polynomial (P : Poly) (v : ℂ) :
    ∃ Q : Poly, ∀ z : ℂ,
      (fderiv ℝ (diagonalEvalPublic P) z) v = diagonalEvalPublic Q z :=
  exists_fderiv_diagonalEval_polynomial P v

private theorem dbarOne_add {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dbarOne (fun w => f w + g w) z = dbarOne f z + dbarOne g z := by
  change dbarOne (f + g) z = dbarOne f z + dbarOne g z
  rw [dbarOne, dbarOne, dbarOne, fderiv_add (hf z) (hg z)]
  simp only [add_apply]
  ring

private theorem dbarOne_mul {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dbarOne (fun w => f w * g w) z =
      dbarOne f z * g z + f z * dbarOne g z := by
  change dbarOne (f * g) z = dbarOne f z * g z + f z * dbarOne g z
  rw [dbarOne, dbarOne, dbarOne, fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem dbarOnePublic_mul {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dbarOnePublic (fun w ↦ f w * g w) z =
      dbarOnePublic f z * g z + f z * dbarOnePublic g z := by
  change dbarOne (fun w ↦ f w * g w) z =
    dbarOne f z * g z + f z * dbarOne g z
  exact dbarOne_mul hf hg z

@[simp] private theorem dbarOne_id (z : ℂ) : dbarOne id z = 0 := by
  rw [dbarOne, (hasFDerivAt_id z).fderiv]
  simp

@[simp] private theorem dbarOne_conj (z : ℂ) : dbarOne conj z = 1 := by
  change dbarOne (fun z => Complex.conjCLE z) z = 1
  rw [dbarOne, Complex.conjCLE.fderiv]
  norm_num [Complex.conjCLE_apply]

/-- Diagonal evaluation turns formal differentiation in `W` into the
real-Fréchet Wirtinger derivative. -/
private theorem dbarOne_diagonalEval (P : Poly) (z : ℂ) :
    dbarOne (diagonalEval P) z =
      diagonalEval (MvPolynomial.pderiv (1 : ComplexHermiteIndex) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEval (MvPolynomial.C a) = fun _ : ℂ => a by
        funext w
        simp [diagonalEval]]
      simp [dbarOne, diagonalEval]
  | add P Q hP hQ =>
      rw [show diagonalEval (P + Q) = fun z => diagonalEval P z + diagonalEval Q z by
        funext w
        simp [diagonalEval]]
      rw [dbarOne_add (differentiable_diagonalEval P)
        (differentiable_diagonalEval Q), hP, hQ]
      simp [diagonalEval]
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEval (P * MvPolynomial.X (0 : ComplexHermiteIndex)) =
            fun z => diagonalEval P z * id z by
          funext w
          simp [diagonalEval]]
        rw [dbarOne_mul (differentiable_diagonalEval P) differentiable_id,
          hP, dbarOne_id]
        simp [diagonalEval]
        ring
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hzero
            apply hi
            apply Fin.ext
            simpa using hzero
          apply Fin.ext
          omega
        subst i
        rw [show diagonalEval (P * MvPolynomial.X (1 : ComplexHermiteIndex)) =
            fun z => diagonalEval P z * conj z by
          funext w
          simp [diagonalEval]]
        rw [dbarOne_mul (g := conj) (differentiable_diagonalEval P)
          Complex.conjCLE.differentiable, hP, dbarOne_conj]
        simp [diagonalEval]
        ring

/-- Exact univariate Wirtinger lowering after normalized diagonal
evaluation. -/
theorem dbarOne_normalizedEval (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    dbarOne (normalizedEval n hn p q) z =
      Real.sqrt (n * q : ℕ) * normalizedEval n hn p (q - 1) z := by
  rw [show normalizedEval n hn p q = diagonalEval (normalized n hn p q) by rfl,
    dbarOne_diagonalEval, pderiv_W_normalized]
  simp [diagonalEval, normalizedEval]

theorem dbarOne_normalizedEval_public (n : ℕ) (hn : 0 < n)
    (p q : ℕ) (z : ℂ) :
    dbarOnePublic (normalizedEval n hn p q) z =
      Real.sqrt (n * q : ℕ) * normalizedEval n hn p (q - 1) z := by
  rw [dbarOnePublic_eq_dbarOne]
  exact dbarOne_normalizedEval n hn p q z

theorem differentiable_normalizedEval (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Differentiable ℝ (normalizedEval n hn p q) := by
  rw [show normalizedEval n hn p q = diagonalEval (normalized n hn p q) by rfl]
  exact differentiable_diagonalEval _

private theorem dbarComponent_coordinateLift {m : ℕ} (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (i j : Fin m) (z : Configuration m) :
    dbarComponent (fun w => f (w i)) j z =
      if i = j then dbarOne f (z i) else 0 := by
  have hcomp : (fun w : Configuration m => f (w i)) =
      f ∘ (ContinuousLinearMap.proj i : Configuration m →L[ℝ] ℂ) := rfl
  rw [dbarComponent, hcomp,
    fderiv_comp (𝕜 := ℝ) z (hf (z i))
      (ContinuousLinearMap.proj i).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [dbarOne]
  by_cases hij : i = j
  · subst j
    simp [realCoordinateDirection, imaginaryCoordinateDirection,
      coordinateDirection]
  · simp [realCoordinateDirection, imaginaryCoordinateDirection,
      coordinateDirection, hij]

/-- Concrete coordinate `dbar` lowering for a single normalized Hermite factor
lifted to configuration space. -/
theorem dbarComponent_normalizedEval_coordinate {m n : ℕ} (hn : 0 < n)
    (p q : ℕ) (i j : Fin m) (z : Configuration m) :
    dbarComponent (fun w => normalizedEval n hn p q (w i)) j z =
      if i = j then
        Real.sqrt (n * q : ℕ) * normalizedEval n hn p (q - 1) (z i)
      else 0 := by
  rw [dbarComponent_coordinateLift _ (differentiable_normalizedEval n hn p q)]
  split_ifs with hij
  · rw [dbarOne_normalizedEval]
  · rfl

private theorem dbarComponent_finsetProd {m : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Configuration m → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin m) (z : Configuration m) :
    dbarComponent (fun w => ∏ i ∈ s, f i w) j z =
      ∑ i ∈ s, (∏ k ∈ s.erase i, f k z) * dbarComponent (f i) j z := by
  unfold dbarComponent
  rw [fderiv_finsetProd (u := s) (g := f) (fun i hi => (hf i hi z))]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Lower the `j`th entry of a multi-index, using truncated natural
subtraction at zero. -/
def lowerAt {n : ℕ} (q : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  Function.update q j (q j - 1)

/-- Exact concrete coordinatewise `dbar` lowering for a multivariate normalized
complex Hermite function. -/
theorem dbarComponent_multivariateNormalized (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    dbarComponent (multivariateNormalized n hn p q) j z =
      Real.sqrt (n * q j : ℕ) *
        multivariateNormalized n hn p (lowerAt q j) z := by
  rw [show multivariateNormalized n hn p q =
      fun w => ∏ i ∈ Finset.univ,
        normalizedEval n hn (p i) (q i) (w i) by
    funext w
    simp [multivariateNormalized]]
  rw [dbarComponent_finsetProd Finset.univ
    (fun i w => normalizedEval n hn (p i) (q i) (w i))]
  · simp_rw [dbarComponent_normalizedEval_coordinate]
    rw [Finset.sum_eq_single j]
    · simp only [ite_eq_left]
      unfold multivariateNormalized lowerAt
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i => normalizedEval n hn (p i)
          ((Function.update q j (q j - 1)) i) (z i)) (Finset.mem_univ j)]
      simp only [Function.update_self]
      have hprod :
          (∏ x ∈ Finset.univ.erase j,
              normalizedEval n hn (p x) (Function.update q j (q j - 1) x) (z x)) =
            ∏ x ∈ Finset.univ.erase j,
              normalizedEval n hn (p x) (q x) (z x) := by
        apply Finset.prod_congr rfl
        intro k hk
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      rw [hprod]
      ring
    · intro i hi hij
      simp [hij]
    · simp
  · intro i hi
    exact (differentiable_normalizedEval n hn (p i) (q i)).comp
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).differentiable

end

end ComplexHermite
end GinibrePoincare
