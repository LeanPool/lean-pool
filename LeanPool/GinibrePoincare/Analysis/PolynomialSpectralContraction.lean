/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialSpectralContraction.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialSpectralEvolution

/-! # Actual Ginibre L² contraction of finite spectral evolution

The finite Hermite–Laguerre spectral evolution is contractive in the actual
Ginibre L² norm. This provides the boundedness step for extension to the closed
polynomial sector, without identifying that sector with the full diffusion.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section

private theorem polynomialEigenfunctionL2_orthogonal (n : ℕ) (hn : 2 ≤ n)
    (i j : PolynomialEigenfunctionData n) (hij : i ≠ j) :
    inner ℂ (polynomialEigenfunctionL2 n hn i) (polynomialEigenfunctionL2 n hn j) = 0 := by
  rw [inner_polynomialEigenfunctionL2]
  apply polynomialEigenfunction_equilibrium_orthogonal n hn
  rintro ⟨ha, hb, hm⟩
  apply hij
  cases i
  cases j
  simp_all

/-- Pythagoras for finite combinations of the actual equilibrium L² vectors. -/
theorem polynomialEigenfunctionL2_norm_sq_sum (n : ℕ) (hn : 2 ≤ n)
    (s : Finset (PolynomialEigenfunctionData n)) (c : PolynomialEigenfunctionData n → ℂ) :
    ‖∑ i ∈ s, c i • polynomialEigenfunctionL2 n hn i‖ ^ 2 =
      ∑ i ∈ s, ‖c i • polynomialEigenfunctionL2 n hn i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
    have ho : inner ℂ (c i • polynomialEigenfunctionL2 n hn i)
        (∑ j ∈ s, c j • polynomialEigenfunctionL2 n hn j) = 0 := by
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [inner_smul_left, inner_smul_right,
        polynomialEigenfunctionL2_orthogonal n hn i j (by aesop)]
      simp
    rw [Finset.sum_insert hi, Finset.sum_insert hi, norm_add_sq (𝕜 := ℂ), ho, hs]
    simp

/-- Finite spectral evolution in actual Ginibre L². -/
def finitePolynomialSpectralEvolution (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (s : Finset (PolynomialEigenfunctionData n)) (c : PolynomialEigenfunctionData n → ℂ) :
    GinibrePolynomialL2 n :=
  ∑ i ∈ s, (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) •
    (c i • polynomialEigenfunctionL2 n hn i)

/-- Actual norm contraction, rather than only a bound on formal coefficients. -/
theorem finitePolynomialSpectralEvolution_contracts (n : ℕ) (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (s : Finset (PolynomialEigenfunctionData n))
    (c : PolynomialEigenfunctionData n → ℂ) :
    ‖finitePolynomialSpectralEvolution n hn t s c‖ ≤
      ‖∑ i ∈ s, c i • polynomialEigenfunctionL2 n hn i‖ := by
  have hsq : ‖finitePolynomialSpectralEvolution n hn t s c‖ ^ 2 ≤
      ‖∑ i ∈ s, c i • polynomialEigenfunctionL2 n hn i‖ ^ 2 := by
    unfold finitePolynomialSpectralEvolution
    simp_rw [smul_smul]
    rw [polynomialEigenfunctionL2_norm_sq_sum, polynomialEigenfunctionL2_norm_sq_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [← smul_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he := polynomialSpectralEvolution_multiplier_le_one n i ht
    have hx := norm_nonneg (c i • polynomialEigenfunctionL2 n hn i)
    have hb : Real.exp (-eigenvalue n i.a i.b i.m * t) *
        ‖c i • polynomialEigenfunctionL2 n hn i‖ ≤
          ‖c i • polynomialEigenfunctionL2 n hn i‖ := by nlinarith
    gcongr
  nlinarith [norm_nonneg (finitePolynomialSpectralEvolution n hn t s c),
    norm_nonneg (∑ i ∈ s, c i • polynomialEigenfunctionL2 n hn i)]

/-- Strong continuity of finite spectral evolution in actual Ginibre L². -/
theorem finitePolynomialSpectralEvolution_continuous (n : ℕ) (hn : 2 ≤ n)
    (s : Finset (PolynomialEigenfunctionData n)) (c : PolynomialEigenfunctionData n → ℂ) :
    Continuous (fun t => finitePolynomialSpectralEvolution n hn t s c) := by
  unfold finitePolynomialSpectralEvolution
  fun_prop

/-- Exact L² time derivative of every finite spectral evolution. -/
theorem finitePolynomialSpectralEvolution_hasDerivAt (n : ℕ) (hn : 2 ≤ n)
    (s : Finset (PolynomialEigenfunctionData n)) (c : PolynomialEigenfunctionData n → ℂ)
    (t : ℝ) :
    HasDerivAt (fun u => finitePolynomialSpectralEvolution n hn u s c)
      (∑ i ∈ s, (-(eigenvalue n i.a i.b i.m : ℂ) *
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ)) •
          (c i • polynomialEigenfunctionL2 n hn i)) t := by
  unfold finitePolynomialSpectralEvolution
  apply HasDerivAt.fun_sum
  intro i hi
  have h := (((hasDerivAt_id t).const_mul (-eigenvalue n i.a i.b i.m)).exp).ofReal_comp
  have h' : HasDerivAt
      (fun u : ℝ => (Real.exp (-eigenvalue n i.a i.b i.m * u) : ℂ))
      (-(eigenvalue n i.a i.b i.m : ℂ) *
        (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ)) t := by
    convert h using 1 <;> (try simp only [id_eq, mul_one]); push_cast; ring
  exact h'.smul_const (c i • polynomialEigenfunctionL2 n hn i)

/-- Each strictly positive spectral mode tends to zero in actual Ginibre L². -/
theorem polynomialSpectralEvolution_positive_mode_tendsto_zero (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) (hi : 0 < i.a + i.b + 2 * i.m) :
    Tendsto (fun t : ℝ => (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) •
      polynomialEigenfunctionL2 n hn i) atTop (𝓝 0) := by
  have hr : 0 < eigenvalue n i.a i.b i.m := by
    unfold eigenvalue
    have hsum : 0 < (i.a : ℝ) + i.b + 2 * i.m := by exact_mod_cast hi
    positivity
  have he : Tendsto (fun t : ℝ => Real.exp (-eigenvalue n i.a i.b i.m * t))
      atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hr)).mpr tendsto_id)
  convert (Complex.continuous_ofReal.tendsto 0 |>.comp he).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => polynomialEigenfunctionL2 n hn i)
        atTop (𝓝 (polynomialEigenfunctionL2 n hn i))) using 1 <;> simp

end
end GinibrePoincare
