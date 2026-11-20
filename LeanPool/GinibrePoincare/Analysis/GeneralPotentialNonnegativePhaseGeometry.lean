/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialNonnegativePhaseGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# General potential nonnegative phase geometry

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialNonnegativePhase_mem_positive_of_orthogonal_constant`,
`potentialConstantL2_mem_nonnegativePhaseClosedSpan`,
`potentialPositivePhaseClosedSpan_le_nonnegative`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The one-dimensional subspace of constants in `L²(potentialMeasure n V)`, spanned by the
constant function `1`. -/
def potentialConstantSpace (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    Submodule ℂ (Lp ℂ 2 (potentialMeasure n V)) :=
  Submodule.span ℂ {potentialConstantL2 n hn hV hfin 1}

/-- The actual closed nonnegative-character space: constants plus the full
closed positive-character space. -/
def potentialNonnegativePhaseClosedSpan (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    ClosedSubmodule ℂ (Lp ℂ 2 (potentialMeasure n V)) where
  toSubmodule := potentialConstantSpace n hn hV hfin ⊔ (potentialPositivePhaseClosedSpan n hV
      hrot).toSubmodule
  isClosed' := by
    unfold potentialConstantSpace
    rw [sup_comm]
    exact Submodule.isClosed_sup_finiteDimensional _ _ (potentialPositivePhaseClosedSpan n hV
        hrot).isClosed

theorem potentialConstantL2_eq_smul_one (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    potentialConstantL2 n hn hV hfin c = c • potentialConstantL2 n hn hV hfin 1 := by
  apply Lp.ext
  filter_upwards [potentialConstantL2_coeFn n hn hV hfin c,
    potentialConstantL2_coeFn n hn hV hfin 1,
    Lp.coeFn_smul c (potentialConstantL2 n hn hV hfin 1)] with z hc h1 hs
  rw [hc, hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_one]

theorem potentialConstantL2_inner_one_one (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    inner ℂ (potentialConstantL2 n hn hV hfin 1) (potentialConstantL2 n hn hV hfin 1) = 1 := by
  let := potentialMeasure_isProbabilityMeasure n hn hV hfin
  rw [MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (show (fun z => inner ℂ (potentialConstantL2 n hn hV hfin 1 z)
      (potentialConstantL2 n hn hV hfin 1 z)) =ᵐ[potentialMeasure n V] (fun _ => (1 : ℂ)) by
    filter_upwards [potentialConstantL2_coeFn n hn hV hfin 1] with z hz
    rw [hz]
    simp)]
  simp

/-- Orthogonality to constants removes precisely the constant component of the
actual closed nonnegative-character space. -/
theorem potentialNonnegativePhase_mem_positive_of_orthogonal_constant
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (x : Lp ℂ 2 (potentialMeasure n V))
    (hx : x ∈ potentialNonnegativePhaseClosedSpan n hn hV hrot hfin)
    (ho : inner ℂ (potentialConstantL2 n hn hV hfin 1) x = 0) :
    x ∈ potentialPositivePhaseClosedSpan n hV hrot := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  have he : x = c • potentialConstantL2 n hn hV hfin 1 + b := by rw [hc]; exact hab.symm
  have hz : c = 0 := by
    rw [he, inner_add_right, inner_smul_right, potentialConstantL2_inner_one_one,
      potentialConstantL2_orthogonal_positivePhaseClosedSpan n hn hV hrot hfin 1 b hb,
      mul_one, add_zero] at ho
    exact ho
  rw [he, hz, zero_smul, zero_add]
  exact hb

theorem potentialConstantL2_mem_nonnegativePhaseClosedSpan
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    potentialConstantL2 n hn hV hfin c ∈ potentialNonnegativePhaseClosedSpan n hn hV hrot hfin := by
  rw [potentialConstantL2_eq_smul_one]
  apply Submodule.smul_mem
  exact Submodule.mem_sup_left (Submodule.subset_span (by simp))

theorem potentialPositivePhaseClosedSpan_le_nonnegative
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    (potentialPositivePhaseClosedSpan n hV hrot).toSubmodule ≤
      (potentialNonnegativePhaseClosedSpan n hn hV hrot hfin).toSubmodule :=
  le_sup_right

end
end GinibrePoincare
