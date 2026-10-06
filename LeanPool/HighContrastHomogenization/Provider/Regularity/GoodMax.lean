/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail

/-!
# High-contrast homogenization: Provider.Regularity.GoodMax

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

open scoped BigOperators

/-!
# Uniform weak-error bounds on finite scale intervals

This module records the pointwise maximum-row event for the scalar identity
comparison on centered cubes and its elementary relation to the summable
finite-tail event.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- Every scalar identity weak error on the integer interval `[n,m]` is at
most `δ`. -/
@[expose]
def ScalarIdentityGoodMaxOnInterval {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (s δ : ℝ) (n m : ℤ) : Prop :=
  ∀ k ∈ Finset.Icc n m, scalarIdentityWeakError a s k ≤ δ

/-- Extract the pointwise weak-error bound from a finite good-max row. -/
theorem ScalarIdentityGoodMaxOnInterval.weakError_le
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n m k : ℤ}
    (h : ScalarIdentityGoodMaxOnInterval a s δ n m)
    (hk : k ∈ Finset.Icc n m) :
    scalarIdentityWeakError a s k ≤ δ :=
  h k hk

/-- Increasing the tolerance preserves a finite good-max row. -/
theorem ScalarIdentityGoodMaxOnInterval.mono
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ δ' : ℝ} {n m : ℤ}
    (h : ScalarIdentityGoodMaxOnInterval a s δ n m) (δh : δ ≤ δ') :
    ScalarIdentityGoodMaxOnInterval a s δ' n m := by
  intro k hk
  exact (h.weakError_le hk).trans δh

/-- Restricting the scale interval preserves a finite good-max row. -/
theorem ScalarIdentityGoodMaxOnInterval.mono_interval
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n n' m' m : ℤ}
    (h : ScalarIdentityGoodMaxOnInterval a s δ n m)
    (hn : n ≤ n') (hm : m' ≤ m) :
    ScalarIdentityGoodMaxOnInterval a s δ n' m' := by
  intro k hk
  exact h.weakError_le (Finset.Icc_subset_Icc hn hm hk)

/-- A summable finite weak-error row controls the pointwise maximum row at
the same tolerance. -/
theorem ScalarIdentityGoodTailOnInterval.toGoodMax
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n m : ℤ}
    (h : ScalarIdentityGoodTailOnInterval a s δ n m) :
    ScalarIdentityGoodMaxOnInterval a s δ n m := by
  intro k hk
  have hsingle :
      scalarIdentityWeakError a s k ≤
        ∑ j ∈ Finset.Icc n m, scalarIdentityWeakError a s j := by
    exact Finset.single_le_sum
      (fun j _ ↦ scalarIdentityWeakError_nonneg a s j) hk
  exact hsingle.trans h

/-- An infinite summable tail controls the finite good-max row on every
admissible terminal interval. -/
theorem ScalarIdentityGoodTail.goodMaxOnInterval
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s δ : ℝ} {n m : ℤ}
    (h : ScalarIdentityGoodTail a s δ n) (hnm : n ≤ m) :
    ScalarIdentityGoodMaxOnInterval a s δ n m :=
  (h.interval hnm).toGoodMax

end

end HighContrast
end HCPolySupport
