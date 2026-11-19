/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialPositivePhaseClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialPositivePhaseGeometry
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialCenteredMean

/-!
# General potential positive phase closure

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialPositivePhaseClosedSpan_inner_star_zero`,
`potentialConstantL2_orthogonal_positivePhaseClosedSpan`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The genuine closed positive-character space of the nonquadratic law. -/
def potentialPositivePhaseClosedSpan (n : ℕ) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) : ClosedSubmodule ℂ (Lp ℂ 2 (potentialMeasure n V)) :=
  { toSubmodule := (Submodule.span ℂ (potentialPositivePhaseVectors n hV hrot)).topologicalClosure
    isClosed' := (Submodule.span ℂ (potentialPositivePhaseVectors n hV
        hrot)).isClosed_topologicalClosure }

/-- Orthogonality to value conjugates extends through both actual closed spans. -/
theorem potentialPositivePhaseClosedSpan_inner_star_zero {n : ℕ} {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V)
    (x y : Lp ℂ 2 (potentialMeasure n V))
    (hx : x ∈ potentialPositivePhaseClosedSpan n hV hrot)
    (hy : y ∈ potentialPositivePhaseClosedSpan n hV hrot) :
    inner ℂ x (star y) = 0 := by
  let S := potentialPositivePhaseVectors n hV hrot
  have hz : star (0 : Lp ℂ 2 (potentialMeasure n V)) = 0 := by
    apply norm_eq_zero.mp
    rw [complexLp_norm_star, norm_zero]
  have hbase (a b : Lp ℂ 2 (potentialMeasure n V)) (ha : a ∈ S) (hb : b ∈ S) :
      inner ℂ a (star b) = 0 := by
    obtain ⟨d, hd, ha⟩ := ha
    obtain ⟨e, he, hb⟩ := hb
    exact potentialPositivePhase_inner_star_zero hV hrot hd he a b ha hb
  have hl (b : Lp ℂ 2 (potentialMeasure n V)) (hb : b ∈ S) :
      ∀ a ∈ Submodule.span ℂ S, inner ℂ a (star b) = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hbase a b ha hb
    | zero => simp
    | add a b ha hb hia hib => rw [inner_add_left, hia, hib, add_zero]
    | smul c a ha hia => rw [inner_smul_left, hia, mul_zero]
  have hlc (b : Lp ℂ 2 (potentialMeasure n V)) (hb : b ∈ S) :
      inner ℂ x (star b) = 0 := by
    have hc : IsClosed {a : Lp ℂ 2 (potentialMeasure n V) | inner ℂ a (star b) = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    exact closure_minimal (fun a ha => hl b hb a ha) hc hx
  have hr : ∀ b ∈ Submodule.span ℂ S, inner ℂ x (star b) = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb => exact hlc b hb
    | zero => simp [hz]
    | add a b ha hb hia hib => rw [complexLp_star_add, inner_add_right, hia, hib, add_zero]
    | smul c a ha hia => rw [complexLp_star_complex_smul, inner_smul_right, hia, mul_zero]
  have hc : IsClosed {b : Lp ℂ 2 (potentialMeasure n V) | inner ℂ x (star b) = 0} :=
    isClosed_eq (continuous_const.inner (complexLpConjugationIsometry (potentialMeasure n
        V)).continuous)
      continuous_const
  exact closure_minimal (fun b hb => hr b hb) hc hy

theorem potentialConstantL2_phase_fixed (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (c a : ℂ) (ha : ‖a‖ = 1) :
    potentialGlobalPhaseL2 n hV hrot a ha (potentialConstantL2 n hn hV hfin c) =
      potentialConstantL2 n hn hV hfin c := by
  change Lp.compMeasurePreserving (globalPhase a)
    (measurePreserving_globalPhase_potentialMeasure n hV hrot a ha)
    (potentialConstantL2 n hn hV hfin c) = _
  apply Lp.ext
  have hp := (measurePreserving_globalPhase_potentialMeasure n hV hrot a
      ha).quasiMeasurePreserving.ae_eq_comp
    (potentialConstantL2_coeFn n hn hV hfin c)
  filter_upwards [Lp.coeFn_compMeasurePreserving (potentialConstantL2 n hn hV hfin c)
    (measurePreserving_globalPhase_potentialMeasure n hV hrot a ha), hp,
    potentialConstantL2_coeFn n hn hV hfin c] with z hz hp hc
  exact hz.trans (hp.trans hc.symm)

theorem potentialConstantL2_orthogonal_positivePhaseClosedSpan
    (n : ℕ) (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (c : ℂ) (x : Lp ℂ 2 (potentialMeasure n V))
    (hx : x ∈ potentialPositivePhaseClosedSpan n hV hrot) :
    inner ℂ (potentialConstantL2 n hn hV hfin c) x = 0 := by
  have hp : ∀ y ∈ potentialPositivePhaseVectors n hV hrot,
      inner ℂ (potentialConstantL2 n hn hV hfin c) y = 0 := by
    intro y hy
    obtain ⟨d, hd, hy⟩ := hy
    apply inner_eq_zero_of_potential_phase_degrees_ne (d := 0) (e := d) hV hrot (by omega)
    · intro a ha
      simpa only [pow_zero, one_smul] using potentialConstantL2_phase_fixed n hn hV hrot hfin c a ha
    · exact hy
  have hs : ∀ y ∈ Submodule.span ℂ (potentialPositivePhaseVectors n hV hrot),
      inner ℂ (potentialConstantL2 n hn hV hfin c) y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hp y hy
    | zero => simp
    | add y z hy hz hiy hiz => rw [inner_add_right, hiy, hiz, add_zero]
    | smul a y hy hiy => rw [inner_smul_right, hiy, mul_zero]
  have hc : IsClosed {y : Lp ℂ 2 (potentialMeasure n V) |
      inner ℂ (potentialConstantL2 n hn hV hfin c) y = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact closure_minimal (fun y hy => hs y hy) hc hx

end
end GinibrePoincare
