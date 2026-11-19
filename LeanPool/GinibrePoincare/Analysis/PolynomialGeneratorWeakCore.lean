/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorWeakCore.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorClosure
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! # The polynomial closure satisfies the full test-core weak equation
The weak graph below is a closed relation defined by every actual compact,
collision-free symmetric test function. No density, uniqueness, graph-core
approximation or diffusion identification is assumed or claimed.
-/

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section

theorem memLp_coreObservable {n : ℕ} (hn : 0 < n) {f : Configuration n → ℝ}
    (hf : IsTheoremOneNineCore f) : MemLp (fun z => (f z : ℂ)) 2 (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (Complex.continuous_ofReal.comp hf.1.continuous).memLp_of_hasCompactSupport
    (hf.2.1.comp_left Complex.ofReal_zero)

/-- A real Theorem 1.9 core function `f`, viewed as a complex vector of Ginibre `L²`. -/
def coreObservableL2 {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : Lp ℂ 2 (ginibreMeasure n) :=
  (memLp_coreObservable hn hf).toLp (fun z => (f z : ℂ))

theorem coreObservableL2_coeFn {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) : coreObservableL2 hn f hf =ᵐ[ginibreMeasure n] fun z => (f z : ℂ)
        :=
  (memLp_coreObservable hn hf).coeFn_toLp

/-- Smoothness of the actual, noncompact polynomial eigenfunctions. -/
theorem contDiff_polynomialEigenfunction (n : ℕ) (i : PolynomialEigenfunctionData n) :
    ContDiff ℝ ∞ (polynomialEigenfunction n i) := by
  have hH : ContDiff ℝ ∞ (ComplexHermite.normalizedEval 1 (by decide) i.a i.b) := by
    unfold ComplexHermite.normalizedEval ComplexHermite.normalized ComplexHermite.raw
    simp only [map_mul, map_sum, map_pow, MvPolynomial.eval_C,
      ComplexHermite.Z, ComplexHermite.W, MvPolynomial.eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro k hk
    exact (contDiff_const.mul (contDiff_id.pow _)).mul
      ((ContinuousLinearEquiv.contDiff Complex.conjCLE).pow _)
  have hS : ContDiff ℝ ∞ (SObservable : Configuration n → ℂ) := by
    have he : (SObservable : Configuration n → ℂ) = coordinateSumCLM n :=
      funext fun z => (coordinateSumCLM_apply n z).symm
    rw [he]
    exact (coordinateSumCLM n).contDiff
  have hR : ContDiff ℝ ∞ (RPoly : Configuration n → ℝ) := by
    unfold RPoly pairwiseRadius
    simp only [Complex.normSq_apply]
    apply ContDiff.sum
    intro j hj
    apply ContDiff.sum
    intro k hk
    have hd : ContDiff ℝ ∞ (fun z : Configuration n => z j - z k) :=
      (contDiff_apply ℝ (fun _ => ℂ) j).sub (contDiff_apply ℝ (fun _ => ℂ) k)
    have hr := Complex.reCLM.contDiff.comp hd
    have hi := Complex.imCLM.contDiff.comp hd
    exact (hr.mul hr).add (hi.mul hi)
  unfold polynomialEigenfunction
  exact (hH.comp hS).mul (Complex.ofRealCLM.contDiff.comp
    ((Laguerre.polynomial _ i.m).contDiff_aeval (𝕜 := ℝ) (n := ∞) |>.comp hR))

/-- The actual differential generator of each polynomial is in Ginibre L². -/
theorem memLp_polynomialEigenfunction_generator (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    MemLp (complexGinibrePregenerator n (polynomialEigenfunction n i)) 2 (ginibreMeasure n) := by
  apply ((polynomialEigenfunction_memLp_two n hn i.a i.b i.m).const_mul
    (-(eigenvalue n i.a i.b i.m : ℂ))).ae_eq
  filter_upwards [polynomialEigenfunction_eigenvalue_equation_ae n hn i.a i.b i.m] with z he
  simp only [eigenvalue] at *
  push_cast
  linear_combination he

private theorem complex_mixed_green {n : ℕ} (hn : 0 < n) {f : Configuration n → ℝ}
    (hf : IsTheoremOneNineCore f) {g : Configuration n → ℂ} (hg : ContDiff ℝ ∞ g)
    (hgi : MemLp g 2 (ginibreMeasure n))
    (hAi : MemLp (complexGinibrePregenerator n g) 2 (ginibreMeasure n)) :
    (∫ z, (f z : ℂ) * complexGinibrePregenerator n g z ∂ginibreMeasure n) =
      ∫ z, (ginibrePregenerator n f z : ℂ) * g z ∂ginibreMeasure n := by
  have hl : Integrable (fun z => (f z : ℂ) * complexGinibrePregenerator n g z) (ginibreMeasure n) :=
    (memLp_coreObservable hn hf).integrable_mul hAi
  have hr : Integrable (fun z => (ginibrePregenerator n f z : ℂ) * g z) (ginibreMeasure n) :=
    (memLp_ginibrePregenerator_of_core hn f hf).integrable_mul hgi
  apply Complex.ext
  · have hrl : (∫ z, (f z : ℂ) * complexGinibrePregenerator n g z ∂ginibreMeasure n).re =
        ∫ z, ((f z : ℂ) * complexGinibrePregenerator n g z).re ∂ginibreMeasure n := by
      simpa using (integral_re hl).symm
    have hrr : (∫ z, (ginibrePregenerator n f z : ℂ) * g z ∂ginibreMeasure n).re =
        ∫ z, ((ginibrePregenerator n f z : ℂ) * g z).re ∂ginibreMeasure n := by
      simpa using (integral_re hr).symm
    rw [hrl, hrr]
    simpa [complexGinibrePregenerator, Complex.mul_re, mul_comm, Function.comp_def,
        Complex.reCLM_apply] using
      ginibre_mixed_green_identity hn hf (Complex.reCLM.contDiff.comp hg)
  · have hil : (∫ z, (f z : ℂ) * complexGinibrePregenerator n g z ∂ginibreMeasure n).im =
        ∫ z, ((f z : ℂ) * complexGinibrePregenerator n g z).im ∂ginibreMeasure n := by
      simpa using (integral_im hl).symm
    have hir : (∫ z, (ginibrePregenerator n f z : ℂ) * g z ∂ginibreMeasure n).im =
        ∫ z, ((ginibrePregenerator n f z : ℂ) * g z).im ∂ginibreMeasure n := by
      simpa using (integral_im hr).symm
    rw [hil, hir]
    simpa [complexGinibrePregenerator, Complex.mul_im, mul_comm, Function.comp_def,
        Complex.imCLM_apply] using
      ginibre_mixed_green_identity hn hf (Complex.imCLM.contDiff.comp hg)

/-- Polynomial eigenfunctions satisfy the weak generator equation against every full core test. -/
theorem polynomialEigenfunction_full_core_weak_equation (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    inner ℂ (coreObservableL2 (by omega) f hf)
      ((closedPolynomialGenerator n hn) ⟨polynomialEigenfunctionL2 n hn i,
        polynomialEigenfunction_mem_closedGenerator_domain n hn i⟩) =
      inner ℂ (ginibrePregeneratorL2 (by omega) f hf) (polynomialEigenfunctionL2 n hn i) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ z, (f z : ℂ) * complexGinibrePregenerator n (polynomialEigenfunction n i) z
        ∂ginibreMeasure n := by
      apply integral_congr_ae
      filter_upwards [coreObservableL2_coeFn (by omega) f hf,
        closedPolynomialGenerator_agrees_concrete n hn i] with z hf hg
      rw [hf, hg, RCLike.inner_apply, Complex.conj_ofReal]
      ring
    _ = ∫ z, (ginibrePregenerator n f z : ℂ) * polynomialEigenfunction n i z ∂ginibreMeasure n :=
      complex_mixed_green (by omega) hf (contDiff_polynomialEigenfunction n i)
        (polynomialEigenfunction_memLp_two n hn i.a i.b i.m)
        (memLp_polynomialEigenfunction_generator n hn i)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ginibrePregeneratorL2_coeFn (by omega) f hf,
        polynomialEigenfunctionL2_coeFn n hn i] with z hf hg
      rw [hf, hg, RCLike.inner_apply, Complex.conj_ofReal]
      ring

/-- The full test-core weak graph; this is a relation until core density is proved. -/
def ginibreWeakCoreGraph (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (GinibrePolynomialL2 n × GinibrePolynomialL2 n) where
  carrier := {p | ∀ (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f),
    inner ℂ (coreObservableL2 hn f hf) p.2 = inner ℂ (ginibrePregeneratorL2 hn f hf) p.1}
  zero_mem' := by intro f hf; simp
  add_mem' := by intro p q hp hq f hf; simp [inner_add_right, hp f hf, hq f hf]
  smul_mem' := by intro c p hp f hf; simp [inner_smul_right, hp f hf]

/-- All full-core weak constraints survive L² graph limits. -/
theorem ginibreWeakCoreGraph_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreWeakCoreGraph n hn : Set (GinibrePolynomialL2 n × GinibrePolynomialL2 n)) := by
  have he : (ginibreWeakCoreGraph n hn : Set (GinibrePolynomialL2 n × GinibrePolynomialL2 n)) =
      ⋂ (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f),
        {p | inner ℂ (coreObservableL2 hn f hf) p.2 = inner ℂ (ginibrePregeneratorL2 hn f hf) p.1}
            := by
    ext p; simp [ginibreWeakCoreGraph]
  rw [he]
  apply isClosed_iInter; intro f
  apply isClosed_iInter; intro hf
  apply isClosed_eq <;> fun_prop

/-- The entire closed polynomial graph satisfies the actual full-core weak equation. -/
theorem closedPolynomialGenerator_graph_le_weakCoreGraph (n : ℕ) (hn : 2 ≤ n) :
    (closedPolynomialGenerator n hn).graph ≤ ginibreWeakCoreGraph n (by omega) := by
  rw [closedPolynomialGenerator_graph]
  apply Submodule.topologicalClosure_minimal _ ?_ (ginibreWeakCoreGraph_isClosed n (by omega))
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  intro f hf
  have he := polynomialEigenfunction_full_core_weak_equation n hn i f hf
  rw [closedPolynomialGenerator_eigenvalue] at he
  exact he

end
end GinibrePoincare
