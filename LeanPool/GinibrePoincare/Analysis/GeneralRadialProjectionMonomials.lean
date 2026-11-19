/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralRadialProjectionMonomials.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionNegative

/-!
# General radial projection monomials

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarBergmanKernel_eq_weighted_monomial_closure`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem planarRotationCoefficient_unit_phase {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) (k : ℤ) (a : ℂ) (ha : ‖a‖ = 1) :
    planarLebesguePhase a ha (planarRotationCoefficient (T := T) u k) =
      a ^ k • planarRotationCoefficient (T := T) u k := by
  have hT : T ≠ 0 := (Fact.out : 0 < T).ne'
  let c : Circle := ⟨a, by change a ∈ Metric.sphere (0 : ℂ) 1; exact mem_sphere_zero_iff_norm.mpr
                             ha⟩
  obtain ⟨s, hs⟩ := (AddCircle.homeomorphCircle hT).surjective c
  have hs' : AddCircle.toCircle s = c := by
    rw [← AddCircle.homeomorphCircle_apply hT]
    exact hs
  have he := planarRotationCoefficient_eigen u k s
  simpa only [fourier_apply, AddCircle.toCircle_zsmul, hs', Circle.coe_zpow] using he

/-- The `L²` classes of the weighted monomials `z ↦ c * z ^ d * exp (-n V z / 2)` that are
square-integrable. -/
def planarWeightedMonomialVectors (n : ℕ) (V : ℂ → ℝ) : Set PlanarLebesgueL2 :=
  {u | ∃ d : ℕ, ∃ c : ℂ, ∃ hm : MemLp
      (fun z => c * z ^ d * planarPotentialHalfWeight n V z) 2 volume,
      hm.toLp _ = u}

/-- The actual scalar radial Bergman kernel is generated densely by its
integrable weighted monomials. No polynomial-density assumption is used. -/
theorem planarBergmanKernel_le_weighted_monomial_closure
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a * z) = V z) :
    planarBergmanKernel n V hV ≤
      (Submodule.span ℂ (planarWeightedMonomialVectors n V)).topologicalClosure := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  intro u hu
  have hspan : (Submodule.span ℂ (range (planarRotationCoefficient (T := 1) u))).topologicalClosure
      ≤
      (Submodule.span ℂ (planarWeightedMonomialVectors n V)).topologicalClosure := by
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro v ⟨k, rfl⟩
    have hm := planarRotationCoefficient_mem_bergman (T := 1) n V hV hr u hu k
    cases k with
    | ofNat d =>
      apply Submodule.subset_span
      obtain ⟨c, hi, he⟩ := planarBergman_phase_eigenvector_is_monomial n d V hV hr _ hm
        (fun a ha => by simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
          planarRotationCoefficient_unit_phase (T := 1) u (d : ℤ) a ha)
      exact ⟨d, c, hi, he⟩
    | negSucc d =>
      have he : planarRotationCoefficient (T := 1) u (Int.negSucc d) = 0 := by
        apply planarBergman_negative_phase_eq_zero n (d + 1) (by omega) V hV hr _ hm
        intro a ha
        simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one] using
          planarRotationCoefficient_unit_phase (T := 1) u (Int.negSucc d) a ha
      rw [he]
      exact Submodule.zero_mem _
  exact hspan (planarLebesgue_mem_closed_span_phase_fourier (T := 1) u)

theorem planarBergmanKernel_eq_weighted_monomial_closure
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a * z) = V z) :
    planarBergmanKernel n V hV =
      (Submodule.span ℂ (planarWeightedMonomialVectors n V)).topologicalClosure := by
  apply le_antisymm (planarBergmanKernel_le_weighted_monomial_closure n V hV hr)
  apply (Submodule.span ℂ (planarWeightedMonomialVectors n V)).topologicalClosure_minimal
    _ (planarBergmanKernelClosed n V hV).isClosed
  apply Submodule.span_le.mpr
  rintro u ⟨d, c, hm, rfl⟩
  exact weighted_holomorphic_mem_weak_dbar_kernel n V (hV.of_le (by norm_num))
    (fun z => c * z ^ d) (differentiable_const c |>.mul (differentiable_id.pow d)) hm

end
end GinibrePoincare
