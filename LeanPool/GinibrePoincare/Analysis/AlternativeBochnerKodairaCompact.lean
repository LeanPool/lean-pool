/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBochnerKodairaCompact.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBochnerKodairaDifferential

/-! # Gaussian integration by parts on actual compact smooth tests -/

@[expose] public section
open MeasureTheory
open scoped ContDiff ComplexConjugate BigOperators
namespace GinibrePoincare
noncomputable section

/-- A smooth compactly supported complex function on configurations. -/
structure BKCompactTest (n : ℕ) where
  /-- The underlying function. -/
  toFun : Configuration n → ℂ
  smooth : ContDiff ℝ ∞ toFun
  compact : HasCompactSupport toFun

instance {n : ℕ} : CoeFun (BKCompactTest n) (fun _ => Configuration n → ℂ) := ⟨BKCompactTest.toFun⟩

/-- The coordinate derivative `dbar_j f` of a compact smooth test, again a compact smooth test. -/
def BKCompactTest.dbar {n : ℕ} (f : BKCompactTest n) (j : Fin n) : BKCompactTest n :=
  ⟨dbarComponent f j, bkDbar_contDiff f.smooth j, hasCompactSupport_dbarComponent f.compact j⟩

/-- The Gaussian adjoint `gaussianDbarAdjointTest j f` of `dbar_j` applied to a compact smooth
test, again a compact smooth test. -/
def BKCompactTest.adjoint {n : ℕ} (f : BKCompactTest n) (j : Fin n) : BKCompactTest n :=
  ⟨gaussianDbarAdjointTest j f, bkAdjoint_contDiff f.smooth j, bkAdjoint_compact f.compact j⟩

/-- A compact smooth test as a vector of Gaussian `L²`. -/
def BKCompactTest.l2 {n : ℕ} (f : BKCompactTest n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  smoothCompactL2 f (f.smooth.of_le (by simp)) f.compact

theorem BKCompactTest.l2_coe {n : ℕ} (f : BKCompactTest n) :
    (f.l2 : Configuration n → ℂ) =ᵐ[complexGaussianMeasure n] f :=
  smoothCompactL2_coeFn f (f.smooth.of_le (by simp)) f.compact

/-- Genuine Gaussian integration by parts between any two compact smooth tests. -/
theorem bkCompact_adjoint_pairing {n : ℕ} (hn : 0 < n)
    (f g : BKCompactTest n) (j : Fin n) :
    inner ℂ g.l2 (f.dbar j).l2 = inner ℂ (g.adjoint j).l2 f.l2 := by
  have hweak := gaussian_smooth_weak_dbar hn j f.l2 (f.dbar j).l2 f
    (f.smooth.of_le (by simp)) f.l2_coe (f.dbar j).l2_coe
  have hh := hweak g (g.smooth.of_le (by simp)) g.compact
  have he : gaussianDbarAdjointTestL2 j g (g.smooth.of_le (by simp)) g.compact =
      (g.adjoint j).l2 := by
    apply Lp.ext
    filter_upwards [(gaussianDbarAdjointTest_memLp j g
      (g.smooth.of_le (by simp)) g.compact).coeFn_toLp, (g.adjoint j).l2_coe] with z hz hg
    exact hz.trans hg.symm
  simpa only [BKCompactTest.l2, he] using hh

theorem bkCompact_dbar_comm {n : ℕ} (f : BKCompactTest n) (j k : Fin n) :
    ((f.dbar k).dbar j).l2 = ((f.dbar j).dbar k).l2 := by
  apply Lp.ext
  filter_upwards [((f.dbar k).dbar j).l2_coe, ((f.dbar j).dbar k).l2_coe] with z hz hz'
  rw [hz, hz']
  exact bkDbar_comm f.smooth j k z

theorem bkCompact_commutator {n : ℕ} (f : BKCompactTest n) (j k : Fin n) :
    ((f.adjoint k).dbar j).l2 = ((f.dbar j).adjoint k).l2 +
      if j = k then (n : ℂ) • f.l2 else 0 := by
  apply Lp.ext
  filter_upwards [((f.adjoint k).dbar j).l2_coe,
    ((f.dbar j).adjoint k).l2_coe, f.l2_coe,
    Lp.coeFn_add ((f.dbar j).adjoint k).l2 (if j = k then (n : ℂ) • f.l2 else 0),
    Lp.coeFn_smul (n : ℂ) f.l2, Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z h1 h2 h3 h4 h5
        h6
  rw [h4, Pi.add_apply, h1, h2]
  by_cases hjk : j = k
  · simp only [hjk, ite_true, h5, Pi.smul_apply, smul_eq_mul, h3]
    simpa [hjk, BKCompactTest.dbar, BKCompactTest.adjoint] using bkDbar_adjoint_comm f.smooth j k z
  · simp only [hjk, ite_false, h6, Pi.zero_apply, add_zero]
    simpa [hjk, BKCompactTest.dbar, BKCompactTest.adjoint] using bkDbar_adjoint_comm f.smooth j k z

theorem bkCompact_adjoint_pairing_right {n : ℕ} (hn : 0 < n)
    (f g : BKCompactTest n) (j : Fin n) :
    inner ℂ f.l2 (g.adjoint j).l2 = inner ℂ (f.dbar j).l2 g.l2 := by
  have h := congrArg conj (bkCompact_adjoint_pairing hn f g j)
  simpa only [inner_conj_symm] using h.symm

/-- The two integration-by-parts steps and commutator in (6.8), before summing. -/
theorem bkCompact_number_pair {n : ℕ} (hn : 0 < n)
    (f : BKCompactTest n) (j k : Fin n) :
    inner ℂ ((f.dbar j).adjoint j).l2 ((f.dbar k).adjoint k).l2 =
      (‖((f.dbar j).dbar k).l2‖ ^ 2 : ℂ) +
        if j = k then (n : ℂ) * (‖(f.dbar j).l2‖ ^ 2 : ℂ) else 0 := by
  rw [← bkCompact_adjoint_pairing hn ((f.dbar k).adjoint k) (f.dbar j) j,
    bkCompact_commutator, inner_add_right]
  rw [bkCompact_adjoint_pairing_right hn (f.dbar j) ((f.dbar k).dbar j) k,
    bkCompact_dbar_comm f j k, inner_self_eq_norm_sq_to_K]
  by_cases hjk : j = k
  · subst k
    simp [inner_smul_right, inner_self_eq_norm_sq_to_K]
  · simp [hjk]

/-- Actual Gaussian number operator on the compact smooth domain. -/
def bkCompactNumberL2 {n : ℕ} (f : BKCompactTest n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  ∑ j : Fin n, ((f.dbar j).adjoint j).l2

/-- Integrated Bochner–Kodaira identity (6.8), independently of Hermite expansions. -/
theorem bkCompact_integrated_identity {n : ℕ} (hn : 0 < n) (f : BKCompactTest n) :
    ‖bkCompactNumberL2 f‖ ^ 2 =
      (∑ j : Fin n, ∑ k : Fin n, ‖((f.dbar j).dbar k).l2‖ ^ 2) +
        (n : ℝ) * ∑ j : Fin n, ‖(f.dbar j).l2‖ ^ 2 := by
  have hi : (‖bkCompactNumberL2 f‖ ^ 2 : ℂ) =
      ((∑ j : Fin n, ∑ k : Fin n, ‖((f.dbar j).dbar k).l2‖ ^ 2) +
        (n : ℝ) * ∑ j : Fin n, ‖(f.dbar j).l2‖ ^ 2 : ℝ) := by
    rw [show (‖bkCompactNumberL2 f‖ ^ 2 : ℂ) = inner ℂ (bkCompactNumberL2 f) (bkCompactNumberL2 f)
        by
      exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (bkCompactNumberL2 f)).symm]
    unfold bkCompactNumberL2
    rw [sum_inner]
    simp_rw [inner_sum]
    simp_rw [bkCompact_number_pair hn f]
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  exact_mod_cast hi

end
end GinibrePoincare

