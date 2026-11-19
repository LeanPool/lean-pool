/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEqualityCore.lean.
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

public import LeanPool.GinibrePoincare.Endgame.ConcreteTheoremOneNine

/-! Exact spectral equality criteria on the concrete Theorem 1.9 core.
These criteria do not assert a classification on the full weak domain. -/


@[expose] public section


namespace GinibrePoincare
noncomputable section

/-- For a convergent nonnegative mode tail, vanishing is equivalent to
vanishing of every mode above the first positive mode. -/
theorem ginibreEquality_modeTail_eq_zero_iff (a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k) :
    modeTail a = 0 ↔ ∀ k, 0 < k → a k = 0 := by
  constructor
  · intro hz k hk
    have hle : (k : ℝ) * a k ≤ modeTail a :=
      ht.le_tsum k (fun j _ => mul_nonneg (Nat.cast_nonneg j) (ha j))
    rw [hz] at hle
    have hprod : (k : ℝ) * a k = 0 :=
      le_antisymm hle (mul_nonneg (Nat.cast_nonneg k) (ha k))
    exact (mul_eq_zero.mp hprod).resolve_left (by exact_mod_cast hk.ne')
  · intro hz
    unfold modeTail
    have hf : (fun k : ℕ => (k : ℝ) * a k) = fun _ => 0 := by
      funext k
      by_cases hk : k = 0
      · simp [hk]
      · rw [hz k (Nat.pos_of_ne_zero hk), mul_zero]
    rw [hf, tsum_zero]

/-- The weighted concrete tail converges, independently of equality. -/
theorem ginibreEquality_concrete_tail_summable {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Summable fun k : ℕ => (k : ℝ) * concretePositiveHermiteModeMass hn f hf k := by
  have h := (concrete_weightedModeEnergy hn f hf).summable.sub
    (summable_transformedCentered_positiveModeMass hn f hf)
  apply h.congr
  intro k
  dsimp [concretePositiveHermiteModeMass]
  push_cast
  ring

/-- Exact equality in sharp core Poincaré is equivalent to zero holomorphic
remainder and zero mass in all antiholomorphic degrees at least two. -/
theorem ginibreEquality_core_poincare_iff {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf)
    let r := centeredObservableL2 hn f hf - h - star h
    smoothGinibreEnergy n f = 2 * smoothGinibreVariance n f ↔
      r = 0 ∧ ∀ k, 0 < k → concretePositiveHermiteModeMass hn f hf k = 0 := by
  dsimp only
  let r := centeredObservableL2 hn f hf -
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf) - star
      ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf))
  let a := concretePositiveHermiteModeMass hn f hf
  have ha : ∀ k, 0 ≤ a k := fun k => sq_nonneg _
  have htail := modeTail_nonneg a ha
  have hid := (concrete_theoremOneNine hn f hf).1
  change smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f =
    2 * ‖r‖ ^ 2 + 4 * modeTail a at hid
  have hiff := ginibreEquality_modeTail_eq_zero_iff a ha
    (ginibreEquality_concrete_tail_summable hn f hf)
  constructor
  · intro heq
    have hr : ‖r‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖r‖]
    have hr0 : r = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg r])
    have ht : modeTail a = 0 := by nlinarith
    exact ⟨hr0, hiff.mp ht⟩
  · rintro ⟨hr, hmode⟩
    have ht := hiff.mpr hmode
    change r = 0 at hr
    rw [hr, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ht] at hid
    linarith


/-- Each weighted higher mode is controlled by the actual Poincaré deficit. -/
theorem ginibreEquality_core_mode_bound {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) (k : ℕ) :
    4 * (k : ℝ) * concretePositiveHermiteModeMass hn f hf k ≤
      smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f := by
  let a := concretePositiveHermiteModeMass hn f hf
  have ha : ∀ j, 0 ≤ a j := fun j => sq_nonneg _
  have hle : (k : ℝ) * a k ≤ modeTail a :=
    (ginibreEquality_concrete_tail_summable hn f hf).le_tsum k
      (fun j _ => mul_nonneg (Nat.cast_nonneg j) (ha j))
  have hid := (concrete_theoremOneNine hn f hf).1
  nlinarith [sq_nonneg (‖centeredObservableL2 hn f hf -
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf) - star
      ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf))‖)]

/-- Equality in the integrated generator inequality is exactly equality in
Poincaré together with vanishing of the shifted centered generator. -/
theorem ginibreEquality_core_generator_iff {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreGeneratorNormSq n f = 2 * smoothGinibreEnergy n f ↔
      shiftedGinibreGeneratorNormSq n (centeredObservable n f) = 0 ∧
        smoothGinibreEnergy n f = 2 * smoothGinibreVariance n f := by
  have hshift : 0 ≤ shiftedGinibreGeneratorNormSq n (centeredObservable n f) :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  have htail := modeTail_nonneg (concretePositiveHermiteModeMass hn f hf)
    (fun k => sq_nonneg _)
  have hid := concrete_theoremOneNine hn f hf
  dsimp only at hid
  have hsquare := sq_nonneg (‖centeredObservableL2 hn f hf -
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf) - star
      ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf))‖)
  constructor
  · intro heq
    constructor <;> nlinarith [hid.1, hid.2]
  · rintro ⟨hshift0, henergy⟩
    nlinarith [hid.1, hid.2]

end
end GinibrePoincare
