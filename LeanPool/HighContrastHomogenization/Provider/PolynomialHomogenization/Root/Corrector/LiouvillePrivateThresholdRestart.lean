/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorLiouvilleForward
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorTelescope
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleReverseClassification

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.LiouvillePrivateThresholdRestart

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Private restart for Liouville thresholds

A summable weak-error row may be restarted after a finite prefix with any
prescribed positive tolerance.  Consequently the threshold selected by the
deterministic Liouville terminal remains private to the exposed growth order.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

noncomputable section

/-- A summable scalar good tail can be restarted with any positive tolerance.
The coefficient family and fractional order are unchanged. -/
theorem ScalarIdentityGoodTail.exists_restart_at_tolerance
    {d : ℕ}
    {a : Book.Ch02.TriadicCoeffFamily d} {s delta : ℝ} {n : ℤ}
    (hgood : ScalarIdentityGoodTail a s delta n)
    {target : ℝ} (htarget : 0 < target) :
    ∃ n' : ℤ, n ≤ n' ∧ ScalarIdentityGoodTail a s target n' := by
  let f : ℕ → ℝ := fun j ↦
    scalarIdentityWeakError a s (n + (j : ℤ))
  have hsummable : Summable f := by
    simpa only [f] using hgood.summable_nat_shift
  have htendsto : Tendsto (fun k : ℕ ↦ ∑' j : ℕ, f (j + k))
      atTop (nhds 0) :=
    tendsto_sum_nat_add f
  have heventually : ∀ᶠ k : ℕ in atTop,
      (∑' j : ℕ, f (j + k)) < target :=
    (tendsto_order.1 htendsto).2 target htarget
  obtain ⟨k₀, hk₀⟩ := (eventually_atTop.1 heventually)
  let n' : ℤ := n + (k₀ : ℤ)
  refine ⟨n', by simp only [n']; omega, ?_⟩
  intro m hnm
  unfold ScalarIdentityGoodTailOnInterval
  have hsumIdentity :
      (∑ j ∈ Finset.Icc n' m, scalarIdentityWeakError a s j) =
        ∑ r ∈ Finset.range ((m - n').toNat + 1), f (r + k₀) := by
    classical
    refine Finset.sum_bij (fun j _ ↦ (j - n').toNat) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      omega
    · intro j₁ hj₁ j₂ hj₂ heq
      simp only [Finset.mem_Icc] at hj₁ hj₂
      have h₁ : 0 ≤ j₁ - n' := by omega
      have h₂ : 0 ≤ j₂ - n' := by omega
      have hcast : ((j₁ - n').toNat : ℤ) = ((j₂ - n').toNat : ℤ) :=
        congrArg (fun r : ℕ ↦ (r : ℤ)) heq
      rw [Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂] at hcast
      omega
    · intro r hr
      simp only [Finset.mem_range] at hr
      refine ⟨n' + (r : ℤ), ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · apply Int.ofNat_inj.mp
        have hnonneg : 0 ≤ n' + (r : ℤ) - n' := by omega
        rw [Int.toNat_of_nonneg hnonneg]
        omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [f, n']
      congr 2
      omega
  rw [hsumIdentity]
  have hshiftSummable : Summable (fun r : ℕ ↦ f (r + k₀)) :=
    (summable_nat_add_iff k₀).2 hsummable
  exact (hshiftSummable.sum_le_tsum
    (Finset.range ((m - n').toNat + 1))
    (fun r _ ↦ scalarIdentityWeakError_nonneg a s
      (n + ((r + k₀ : ℕ) : ℤ)))).trans
      (le_of_lt (hk₀ k₀ le_rfl))

end

end Root
end HighContrast
end HCPolySupport
