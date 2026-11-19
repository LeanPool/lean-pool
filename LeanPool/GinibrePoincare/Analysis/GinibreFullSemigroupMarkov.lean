/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupMarkov.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupEulerCFC
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupWeakOrder
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConservation

/-! # Actual Markov positivity of the full symmetric diffusion -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Every backward Euler step preserves pointwise positivity of real parts. -/
theorem ginibreFullBackwardEuler_nonneg (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 < c)
    (x : ginibreSymmetricL2 n)
    (hx : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ ginibreFullComplexRe n x.val z) :
    ∀ᵐ z ∂ginibreMeasure n,
      0 ≤ ginibreFullComplexRe n (resolventBackwardEuler (ginibreFullComplexResolvent n hn) c x).val
          z := by
  let R := ginibreFullComplexResolvent n hn
  let U := resolventBackwardEuler R c x
  let V := resolventBackwardEulerImage R c x
  let u := ginibreFullSymmetricRe n U
  let v := ginibreFullSymmetricRe n V
  have hg : (U, V) ∈ (ginibreFullGenerator n hn).graph :=
    (ginibreFullGenerator_graph_iff n hn U V).mpr
      (resolventBackwardEuler_graph R (ginibreFullComplexResolvent_isSelfAdjoint n hn)
        (ginibreFullComplexResolvent_spectrum n hn) c hc x)
  have hr := ((ginibreFullGenerator_graph_iff_real_imag hn U V).mp hg).1
  have hgr : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    apply (ginibreFullGenerator_graph_iff_real_imag hn _ _).mpr
    constructor
    · simpa only [ginibreFullSymmetricRe_ofReal] using hr
    · simp
  have he := resolventBackwardEuler_equation R (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_spectrum n hn) c hc x
  have her : u - c • v = ginibreFullSymmetricRe n x := by
    have h := congrArg (ginibreFullSymmetricRe n) he
    rw [(ginibreFullSymmetricRe n).map_sub] at h
    rw [← h]
    congr 1
    exact ((ginibreFullSymmetricRe n).map_smul c V).symm
  exact ginibreFullGenerator_backward_nonneg n hn u v c hc hgr (by rw [her]; exact hx)

/-- Any number of backward Euler steps preserves positivity. -/
theorem ginibreFullBackwardEuler_pow_nonneg (n : ℕ) (hn : 0 < n) (c : ℝ) (hc : 0 < c)
    (x : ginibreSymmetricL2 n)
    (hx : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ ginibreFullComplexRe n x.val z) (k : ℕ) :
    ∀ᵐ z ∂ginibreMeasure n,
      0 ≤ ginibreFullComplexRe n (((resolventBackwardEuler (ginibreFullComplexResolvent n hn) c)^k)
          x).val z := by
  induction k with
  | zero => simpa using hx
  | succ k hk =>
    rw [pow_succ']
    exact ginibreFullBackwardEuler_nonneg n hn c hc _ hk

/-- The full diffusion preserves actual pointwise nonnegativity, rather than merely
positivity of its Hilbert quadratic form. -/
theorem ginibreFullEvolution_nonneg (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreSymmetricL2 n)
    (hx : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ ginibreFullComplexRe n x.val z) :
    ∀ᵐ z ∂ginibreMeasure n,
      0 ≤ ginibreFullComplexRe n (ginibreFullEvolution n hn t x).val z := by
  by_cases ht : t = 0
  · subst t
    simpa using hx
  have htp : 0 < (t : ℝ) := by exact_mod_cast (lt_of_le_of_ne (by positivity : (0 : ℝ≥0) ≤ t)
                                 (Ne.symm ht))
  let R := ginibreFullComplexResolvent n hn
  let p j := ((resolventBackwardEuler R ((t : ℝ) / (2 ^ j : ℕ)))^(2 ^ j : ℕ)) x
  have hp : Tendsto p atTop (𝓝 (ginibreFullEvolution n hn t x)) := by
    exact ((ContinuousLinearMap.apply ℂ (ginibreSymmetricL2 n) x).continuous.tendsto _).comp
      (resolventBackwardEuler_pow_tendsto R (ginibreFullComplexResolvent_isSelfAdjoint n hn)
        (ginibreFullComplexResolvent_spectrum n hn) t htp)
  have hpr : Tendsto (fun j => ginibreFullComplexRe n (p j).val) atTop
      (𝓝 (ginibreFullComplexRe n (ginibreFullEvolution n hn t x).val)) :=
    ((ginibreFullComplexRe n).continuous.tendsto _).comp
      (((ginibreSymmetricL2 n).subtypeL.continuous.tendsto _).comp hp)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hpr).exists_seq_tendsto_ae
  have hnz : ∀ᵐ z ∂ginibreMeasure n, ∀ j : ℕ, 0 ≤ ginibreFullComplexRe n (p (ns j)).val z := by
    apply ae_all_iff.mpr
    intro j
    exact ginibreFullBackwardEuler_pow_nonneg n hn _ (by positivity) x hx _
  filter_upwards [hae, hnz] with z hz hpos
  exact ge_of_tendsto hz (Eventually.of_forall hpos)

/-- Positivity on the actual real symmetric weighted L² space. -/
theorem ginibreFullRealEvolution_nonneg (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreFullSymmetricValues n)
    (hx : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ x.val z) :
    ∀ᵐ z ∂ginibreMeasure n, 0 ≤ (ginibreFullRealEvolution n hn t x).val z := by
  have h := ginibreFullEvolution_nonneg n hn t (ginibreFullSymmetricOfReal n x) (by
    simpa only [show (ginibreFullSymmetricOfReal n x).val = ginibreFullComplexOfReal n x.val from
        rfl,
      ginibreFullComplexRe_ofReal] using hx)
  exact h

/-- The actual real semigroup preserves almost-everywhere order. -/
theorem ginibreFullRealEvolution_mono (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x y : ginibreFullSymmetricValues n)
    (hxy : ∀ᵐ z ∂ginibreMeasure n, x.val z ≤ y.val z) :
    ∀ᵐ z ∂ginibreMeasure n,
      (ginibreFullRealEvolution n hn t x).val z ≤ (ginibreFullRealEvolution n hn t y).val z := by
  have hd : ∀ᵐ z ∂ginibreMeasure n, 0 ≤ (y - x).val z := by
    filter_upwards [hxy, Lp.coeFn_sub y.val x.val] with z hz he
    change 0 ≤ (y.val - x.val) z
    rw [he]
    exact sub_nonneg.mpr hz
  have hr := ginibreFullRealEvolution_nonneg n hn t (y - x) hd
  rw [map_sub] at hr
  filter_upwards [hr, Lp.coeFn_sub (ginibreFullRealEvolution n hn t y).val
    (ginibreFullRealEvolution n hn t x).val] with z hz he
  change 0 ≤ ((ginibreFullRealEvolution n hn t y).val -
    (ginibreFullRealEvolution n hn t x).val) z at hz
  rw [he] at hz
  exact sub_nonneg.mp hz

/-- Actual real constants, defined within the full real symmetric Hilbert space. -/
def ginibreFullRealConstant (n : ℕ) (hn : 0 < n) (c : ℝ) : ginibreFullSymmetricValues n :=
  ginibreFullSymmetricRe n (ginibreFullConstant n hn c)

theorem ginibreFullRealConstant_ae (n : ℕ) (hn : 0 < n) (c : ℝ) :
    ((ginibreFullRealConstant n hn c).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun _ => c :=
        by
  filter_upwards [ginibreFullComplexRe_ae n (ginibreFullConstant n hn c).val,
    ginibreFullConstant_ae n hn c] with z hr hc
  change ginibreFullComplexRe n (ginibreFullConstant n hn c).val z = c
  rw [hr, hc]
  simp

/-- Constants are fixed by the actual real diffusion. -/
theorem ginibreFullRealEvolution_constant (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (c : ℝ) :
    ginibreFullRealEvolution n hn t (ginibreFullRealConstant n hn c) =
      ginibreFullRealConstant n hn c := by
  have hc : ginibreFullSymmetricOfReal n (ginibreFullRealConstant n hn c) =
      ginibreFullConstant n hn c := by
    apply ginibreFullSymmetric_ext_parts
    · simp [ginibreFullRealConstant]
    · apply Subtype.ext
      simp [ginibreFullConstant_im]
  change ginibreFullSymmetricRe n
    (ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n (ginibreFullRealConstant n hn c))) =
        _
  rw [hc, ginibreFullEvolution_constant]
  rfl

/-- Bounded constant intervals are preserved on the complete real L² space. -/
theorem ginibreFullRealEvolution_interval (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (x : ginibreFullSymmetricValues n) (a b : ℝ)
    (hx : ∀ᵐ z ∂ginibreMeasure n, x.val z ∈ Set.Icc a b) :
    ∀ᵐ z ∂ginibreMeasure n, (ginibreFullRealEvolution n hn t x).val z ∈ Set.Icc a b := by
  have hl := ginibreFullRealEvolution_mono n hn t (ginibreFullRealConstant n hn a) x (by
    filter_upwards [hx, ginibreFullRealConstant_ae n hn a] with z hz he
    rw [he]
    exact hz.1)
  have hu := ginibreFullRealEvolution_mono n hn t x (ginibreFullRealConstant n hn b) (by
    filter_upwards [hx, ginibreFullRealConstant_ae n hn b] with z hz he
    rw [he]
    exact hz.2)
  rw [ginibreFullRealEvolution_constant] at hl hu
  filter_upwards [hl, hu, ginibreFullRealConstant_ae n hn a,
    ginibreFullRealConstant_ae n hn b] with z hz hz' ha hb
  rw [ha] at hz
  rw [hb] at hz'
  exact ⟨hz, hz'⟩

end
end GinibrePoincare
