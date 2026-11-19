/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberSpectrum.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorComplexHermiteMultiplier
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSelfAdjoint
public import Mathlib.Order.Filter.IsBounded
/-! # Spectrum of the maximal Gaussian number operator

The graph characterization from `CorrespondenceOperatorNumberDomain` turns the
operator into multiplication by `n * totalAntiDegree` in Hermite coordinates.
The proof here has two independent parts. Away from these levels, reciprocal
weights are bounded: the tail is bounded by one, and the remaining finitely many
weights are bounded separately. A bounded Hermite multiplier then supplies both
inverse identities on the maximal graph. At a level `n * k`, a single normalized
Hermite vector is a nonzero eigenvector, which rules out a two-sided inverse.

`correspondenceOperatorNumberHasResolvent` records the inverse identities
explicitly for this partially defined operator. The concluding equivalence uses
that graph-based notion of resolvent.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem correspondenceOperatorNumber_inverse_weights_bounded (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ, ‖(((n*k : ℕ) : ℂ)-z)⁻¹‖≤M := by
  obtain ⟨cutoff, hcutoff⟩ := exists_nat_gt (‖z‖+1)
  have htailBound : ∀ᶠ k : ℕ in atTop, ‖(((n*k : ℕ) : ℂ)-z)⁻¹‖≤1 := by
    filter_upwards [eventually_ge_atTop cutoff] with k hk
    have hmultiplier_ge_cutoff : cutoff≤n*k := le_trans hk (Nat.le_mul_of_pos_left k hn)
    have hlevel_large : ‖z‖+1<((n*k : ℕ) : ℝ) := lt_of_lt_of_le hcutoff (by exact_mod_cast
                                                                              hmultiplier_ge_cutoff)
    have hdistance_ge_one : 1≤‖((n*k : ℕ) : ℂ)-z‖ := by
      have hreverse_triangle := norm_sub_norm_le (((n*k : ℕ) : ℂ)) z
      rw [Complex.norm_natCast] at hreverse_triangle
      linarith
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0<‖((n*k : ℕ) : ℂ)-z‖)).mpr hdistance_ge_one
  obtain ⟨bound, hbound⟩ := (isBoundedUnder_of_eventually_le htailBound).bddAbove_range
  refine ⟨max 1 bound, lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro k
  exact le_trans (hbound (mem_range_self k)) (le_max_right _ _)

/-- The genuine unbounded resolvent condition: a bounded map is a two-sided
inverse to the literal maximal differential graph shifted by z. -/
def correspondenceOperatorNumberHasResolvent (n : ℕ) (hn : 0 < n) (z : ℂ) : Prop :=
  ∃inverse : Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n),
    (∀f, (inverse f, f+z • inverse f)∈(correspondenceOperatorNumber n hn).graph) ∧
    (∀u v, (u, v)∈(correspondenceOperatorNumber n hn).graph→inverse (v-z • u)=u)

/-- Every complex number outside the literal nℕ eigenvalues has a genuine
bounded two-sided resolvent on the full maximal operator domain. -/
theorem correspondenceOperatorNumber_resolvent_outside (n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : ∀ k : ℕ, z≠((n*k : ℕ) : ℂ)) : correspondenceOperatorNumberHasResolvent n hn z := by
  obtain ⟨bound, hbound, hweightBound⟩ := correspondenceOperatorNumber_inverse_weights_bounded n hn
      z
  -- Normalize reciprocal eigenvalue differences to use the contraction multiplier.
  let normalizedWeight : HermiteMultiIndex n→ℂ := fun pq => (((n*totalAntiDegree pq : ℕ) :
      ℂ)-z)⁻¹/(bound : ℂ)
  have hnormalizedWeight : ∀ pq, ‖normalizedWeight pq‖≤1 := by
    intro pq
    dsimp [normalizedWeight]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbound]
    exact (div_le_one hbound).mpr (hweightBound _)
  let inverse := (bound : ℂ) • correspondenceOperatorComplexHermiteMultiplier hn normalizedWeight
      hnormalizedWeight
  have hresolventCoefficient (f : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
      gaussianHermiteCoefficient hn (inverse f) pq=
        (((n*totalAntiDegree pq : ℕ) : ℂ)-z)⁻¹*gaussianHermiteCoefficient hn f pq := by
    change gaussianHermiteCoefficient hn ((bound : ℂ) •
        correspondenceOperatorComplexHermiteMultiplier hn normalizedWeight hnormalizedWeight f) pq=_
    rw [gaussianHermiteCoefficient_eq_inner, inner_smul_right,← gaussianHermiteCoefficient_eq_inner]
    change (bound : ℂ)*gaussianHermiteCoefficient hn
        (correspondenceOperatorComplexHermiteMultiplierValue hn normalizedWeight hnormalizedWeight
            f) pq=_
    rw [correspondenceOperatorComplexHermiteMultiplier_coefficient]
    dsimp [normalizedWeight]
    have hbound_ne_zero : (bound : ℂ)≠0 := by exact_mod_cast hbound.ne'
    field_simp
  -- The coefficient formula proves the two inverse laws separately.
  refine ⟨inverse,?_,?_⟩
  · intro f
    rw [correspondenceOperatorNumber_graph]
    intro pq
    have he : (((n*totalAntiDegree pq : ℕ) : ℂ)-z)≠0 := sub_ne_zero.mpr (Ne.symm (hz _))
    simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right, inner_smul_right]
    simp only [← gaussianHermiteCoefficient_eq_inner]
    rw [hresolventCoefficient]
    field_simp; ring
  · intro u v huv
    rw [correspondenceOperatorNumber_graph] at huv
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [hresolventCoefficient]
    have he : (((n*totalAntiDegree pq : ℕ) : ℂ)-z)≠0 := sub_ne_zero.mpr (Ne.symm (hz _))
    simp only [gaussianHermiteCoefficient_eq_inner, inner_sub_right, inner_smul_right]
    simp only [← gaussianHermiteCoefficient_eq_inner]
    rw [huv pq]
    field_simp

/-- Every n-times-integer level is a literal eigenvalue of the actual operator. -/
theorem correspondenceOperatorNumber_level_eigenvector (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ∃u : Lp ℂ 2 (complexGaussianMeasure n), u≠0 ∧
      (u, ((n*k : ℕ) : ℂ) • u)∈(correspondenceOperatorNumber n hn).graph := by
  classical
  -- Place all antiholomorphic degree in one coordinate to realize the level.
  let j : Fin n := ⟨0, hn⟩
  let pq : HermiteMultiIndex n := (0, Pi.single j k)
  have hantiDegree : totalAntiDegree pq=k := by
    simp [pq, totalAntiDegree]
  refine ⟨(gaussianHermiteHilbertBasis n hn) pq,
    (gaussianHermiteHilbertBasis n hn).orthonormal.ne_zero pq,?_⟩
  rw [correspondenceOperatorNumber_graph]
  intro ab
  have heigenvectorCoefficient : gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn)
      pq) ab=
      if ab=pq then 1 else 0 := by
    change (gaussianHermiteHilbertBasis n hn).repr ((gaussianHermiteHilbertBasis n hn) pq) ab=_
    rw [HilbertBasis.repr_self, lp.single_apply]
    simp [Pi.single_apply]
  rw [gaussianHermiteCoefficient_eq_inner, inner_smul_right,← gaussianHermiteCoefficient_eq_inner,
      heigenvectorCoefficient]
  by_cases h : ab=pq
  · subst ab
    simp [hantiDegree]
  · simp [h]

/-- Exact complex spectrum of the maximal differential number operator,
expressed by failure of a bounded two-sided inverse on its literal graph. -/
theorem correspondenceOperatorNumber_spectrum_iff (n : ℕ) (hn : 0 < n) (z : ℂ) :
    ¬correspondenceOperatorNumberHasResolvent n hn z ↔ ∃k : ℕ, z=((n*k : ℕ) : ℂ) := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    exact hz (correspondenceOperatorNumber_resolvent_outside n hn z h)
  · rintro ⟨k, rfl⟩ ⟨inverse, hR, hL⟩
    obtain ⟨u, heigenvector_ne_zero, heigenvectorGraph⟩ :=
        correspondenceOperatorNumber_level_eigenvector n hn k
    have he := hL u (((n*k : ℕ) : ℂ) • u) heigenvectorGraph
    simp only [sub_self, map_zero] at he
    exact heigenvector_ne_zero he.symm
end
end GinibrePoincare
