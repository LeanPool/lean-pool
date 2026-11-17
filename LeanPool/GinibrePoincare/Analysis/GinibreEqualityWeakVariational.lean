/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityWeakVariational.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorWeakSpace
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare

/-!
# Ginibre Equality Weak Variational
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped Topology

/-- Centering on actual Ginibre L², bundled as a continuous real-linear map. -/
def ginibreFullCenter (n : ℕ) (hn : 0 < n) : GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  ContinuousLinearMap.id ℝ _ -
    (innerSL ℝ (ginibreRealConstantL2 n hn 1)).smulRight (ginibreRealConstantL2 n hn 1)

theorem ginibreFullCenter_apply (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    ginibreFullCenter n hn u = u - ginibreRealConstantL2 n hn (ginibreL2Mean n u) := by
  have hmean : inner ℝ (ginibreRealConstantL2 n hn 1) u = ginibreL2Mean n u := by
    rw [L2.inner_def]
    unfold ginibreL2Mean
    apply integral_congr_ae
    filter_upwards [ginibreRealConstantL2_ae n hn 1] with z hz
    simp [hz]
  have hc : ginibreL2Mean n u • ginibreRealConstantL2 n hn 1 =
      ginibreRealConstantL2 n hn (ginibreL2Mean n u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (ginibreL2Mean n u) (ginibreRealConstantL2 n hn 1),
      ginibreRealConstantL2_ae n hn 1,
      ginibreRealConstantL2_ae n hn (ginibreL2Mean n u)] with z hs hone hconst
    rw [hs]
    change ginibreL2Mean n u * (ginibreRealConstantL2 n hn 1) z = _
    rw [hone, hconst, mul_one]
  simp [ginibreFullCenter, hmean, hc]

theorem ginibreFullCenter_variance (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    ‖ginibreFullCenter n hn u‖ ^ 2 = ginibreL2Variance n hn u := by
  rw [ginibreFullCenter_apply]
  rfl

/-- The full-domain Poincaré deficit polarized on genuine weak pairs. -/
def ginibreWeakDeficitPairing (n : ℕ) (hn : 0 < n)
    (p q : ginibreFullWeakSpace n hn) : ℝ :=
  (1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2 -
    2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1)

theorem ginibreWeakDeficitPairing_self (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    ginibreWeakDeficitPairing n hn p p =
      ginibreWeakEnergy n p.val.2 - 2 * ginibreL2Variance n hn p.val.1 := by
  unfold ginibreWeakDeficitPairing ginibreWeakEnergy
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ginibreFullCenter_variance]

theorem ginibreWeakDeficitPairing_nonneg (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) : 0 ≤ ginibreWeakDeficitPairing n hn p p := by
  rw [ginibreWeakDeficitPairing_self]
  have h := ginibre_symmetric_weak_poincare hn p.val.1 p.val.2 p.property.1 p.property.2
  linarith


/-- Polarization of the full weak deficit along an actual weak-domain line. -/
theorem ginibreWeakDeficitPairing_quadratic (n : ℕ) (hn : 0 < n)
    (p q : ginibreFullWeakSpace n hn) (t : ℝ) :
    ginibreWeakDeficitPairing n hn (q + t • p) (q + t • p) =
      ginibreWeakDeficitPairing n hn q q +
        2 * t * ginibreWeakDeficitPairing n hn p q +
          t ^ 2 * ginibreWeakDeficitPairing n hn p p := by
  have hfst : (q + t • p).val.1 = q.val.1 + t • p.val.1 := rfl
  have hsnd : (q + t • p).val.2 = q.val.2 + t • p.val.2 := rfl
  unfold ginibreWeakDeficitPairing
  rw [hfst, hsnd]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm q.val.2 p.val.2,
    real_inner_comm (ginibreFullCenter n hn q.val.1) (ginibreFullCenter n hn p.val.1)]
  ring

/-- Full weak-domain equality is precisely the variational eigenfunction
identity against every genuine symmetric weak-H¹ test pair. -/
theorem ginibreEquality_weak_variational_iff (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    ginibreWeakEnergy n p.val.2 = 2 * ginibreL2Variance n hn p.val.1 ↔
      ∀ q : ginibreFullWeakSpace n hn,
        (1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2 =
          2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1) := by
  constructor
  · intro heq q
    have hzero : ginibreWeakDeficitPairing n hn p p = 0 := by
      rw [ginibreWeakDeficitPairing_self, heq, sub_self]
    have hb : ginibreWeakDeficitPairing n hn p q = 0 := by
      by_contra hne
      let a := ginibreWeakDeficitPairing n hn q q
      let b := ginibreWeakDeficitPairing n hn p q
      have ha : 0 ≤ a := ginibreWeakDeficitPairing_nonneg n hn q
      have hb : b ≠ 0 := hne
      let t := -(a + 1) / b
      have ht : t * b = -(a + 1) := div_mul_cancel₀ _ hb
      have hnonneg := ginibreWeakDeficitPairing_nonneg n hn (q + t • p)
      rw [ginibreWeakDeficitPairing_quadratic, hzero, mul_zero, add_zero] at hnonneg
      change 0 ≤ a + 2 * t * b at hnonneg
      nlinarith
    exact sub_eq_zero.mp hb
  · intro htest
    have hself := htest p
    have hzero : ginibreWeakDeficitPairing n hn p p = 0 := sub_eq_zero.mpr hself
    rw [ginibreWeakDeficitPairing_self] at hzero
    exact sub_eq_zero.mp hzero

end
end GinibrePoincare
