/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityConjugateProjection.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakHolomorphic
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityConjugateModeDetection
public import LeanPool.GinibrePoincare.Analysis.HolomorphicQuotientPhaseProjection

/-!
# Ginibre Equality Conjugate Projection
-/


@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
open scoped ComplexConjugate

private theorem ginibreLp_star_complex_smul {n : ℕ} (c : ℂ) (f : Lp ℂ 2 (ginibreMeasure n)) :
    star (c•f)=conj c•star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c•f), Lp.coeFn_smul c f, Lp.coeFn_star f,
    Lp.coeFn_smul (conj c) (star f)] with z hcf hs hf ht
  rw [hcf, ht]
  simp only [Pi.star_apply, Pi.smul_apply] at hs hf ⊢
  rw [hs, hf]
  simp

def ginibreFullConjugateAntiMode (n : ℕ) (hn : 0 < n) (k : ℕ) :
    Lp ℂ 2 (ginibreMeasure n) →L[ℝ] Lp ℂ 2 (complexGaussianMeasure n) :=
  ((hermiteAntiDegreeProjection n hn k).restrictScalars ℝ).comp
    (((normalizedVandermondeL2 n hn).toContinuousLinearMap.restrictScalars ℝ).comp
      (ginibreFullLpConjugationIsometry n).toContinuousLinearMap)

private theorem conjugateAntiMode_complex_smul {n : ℕ} (hn : 0 < n) (k : ℕ)
    (c : ℂ) (f : Lp ℂ 2 (ginibreMeasure n)) :
    ginibreFullConjugateAntiMode n hn k (c•f)=conj c•ginibreFullConjugateAntiMode n hn k f := by
  change hermiteAntiDegreeProjection n hn k (normalizedVandermondeL2 n hn (star (c•f))) = _
  rw [ginibreLp_star_complex_smul, map_smul, map_smul]
  rfl

private theorem conjugateAntiMode_phase {n r : ℕ} (hn : 0 < n) (k : ℕ)
    (f : Lp ℂ 2 (ginibreMeasure n))
    (hf : ∀ (u : ℂ) (hu : ‖u‖ = 1), ginibreGlobalPhaseL2 hn u hu f = u ^ r • f) :
    ∀ (u : ℂ) (hu : ‖u‖=1), gaussianGlobalPhaseL2 hn u hu (ginibreFullConjugateAntiMode n hn k f)=
      (u^(vandermondeDegree n)*(conj u)^r)•ginibreFullConjugateAntiMode n hn k f := by
  have hc : ∀ (u : ℂ) (hu : ‖u‖=1), ginibreGlobalPhaseL2 hn u hu (star f)=
      (u^0*(conj u)^r)•star f := by
    intro u hu
    simpa using ginibreGlobalPhaseL2_star_eigen hn f hf u hu
  have hg := gaussianGlobalPhaseL2_normalizedVandermonde_character hn (star f) hc
  intro u hu
  change gaussianGlobalPhaseL2 hn u hu
    (hermiteAntiDegreeProjection n hn k (normalizedVandermondeL2 n hn (star f))) = _
  rw [gaussianGlobalPhaseL2_comm_antiDegreeProjection, hg u hu, map_smul]
  simp only [Nat.add_zero]
  rfl

/-- Conjugate high-mode annihilation passes to each actual closed quotient degree
projection throughout the full positive graded closure. -/
theorem ginibreEquality_conjugate_mode_quotient_projection {n : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : h ∈ ginibrePositiveQuotientGradedClosedSpan n hn) (r k : ℕ)
    (hk : ginibreFullConjugateAntiMode n hn k h = 0) :
    ginibreFullConjugateAntiMode n hn k
      ((ginibreFiniteQuotientDegreeClosedSpan n r hn).starProjection h)=0 := by
  let P := (ginibreFiniteQuotientDegreeClosedSpan n r hn).starProjection
  let A := ginibreFullConjugateAntiMode n hn k
  let a := A (P h)
  let S : ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
    { toSubmodule :=
        { carrier := {f | inner ℂ a (A (f-P f))=0}
          zero_mem' := by simp
          add_mem' := by
            intro f g hf hg
            change inner ℂ a (A ((f+g)-P (f+g)))=0
            rw [map_add, show (f+g)-(P f+P g)=(f-P f)+(g-P g) by abel, map_add, inner_add_right,
              hf, hg, add_zero]
          smul_mem' := by
            intro c f hf
            change inner ℂ a (A (c•f-P (c•f)))=0
            rw [map_smul, ←smul_sub, conjugateAntiMode_complex_smul, inner_smul_right, hf,
              mul_zero] }
      isClosed' := isClosed_eq (continuous_const.inner
        (A.continuous.comp (continuous_id.sub P.continuous))) continuous_const }
  have hS : ginibrePositiveQuotientGradedClosedSpan n hn ≤ S := by
    apply iSup_le
    intro s f hf
    change inner ℂ a (A (f-P f))=0
    by_cases hsr : s.val=r
    · have hp : P f=f := Submodule.starProjection_eq_self_iff.mpr (by simpa [hsr] using hf)
      rw [hp, sub_self, map_zero, inner_zero_right]
    · have hp : P f=0 := by
        apply Submodule.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _)
        simpa only [sub_zero] using
          ((Submodule.isOrtho_iff_le.mp (ginibreFiniteQuotientDegreeClosedSpan_orthogonal hn hsr))
            hf)
      rw [hp, sub_zero]
      apply inner_eq_zero_of_gaussian_mixed_phase_degrees_ne
        (p:=vandermondeDegree n) (q:=r) (r:=vandermondeDegree n) (s:=s.val) hn a (A f) (by omega)
      · exact conjugateAntiMode_phase hn k (P h)
          (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn
            (Submodule.starProjection_apply_mem _ _))
      · exact conjugateAntiMode_phase hn k f
          (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n s.val hn hf)
  have hs : inner ℂ a (A (h-P h))=0 := hS hh
  rw [map_sub, hk, zero_sub, inner_neg_right] at hs
  have hi : inner ℂ a a=0 := neg_eq_zero.mp hs
  exact inner_self_eq_zero.mp hi

end GinibrePoincare
