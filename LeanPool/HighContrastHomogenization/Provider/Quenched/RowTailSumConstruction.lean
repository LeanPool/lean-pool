/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.CountableWeakOrliczAE
public import LeanPool.HighContrastHomogenization.Provider.Quenched.QuenchedRowSeries

/-!
# High-contrast homogenization: Provider.Quenched.RowTailSumConstruction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A measurable representative of the weighted row series

The weighted tail series of `e.random.adapted.sum` need not
converge off the support of the law, so the endgame carries it as a measurable
function agreeing almost everywhere with the raw series.  This file constructs
that representative from measurability of the rows and almost-everywhere
summability alone.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An almost-everywhere summable weighted row family has a measurable tail-sum
representative at every generation. -/
theorem exists_measurable_weighted_rowTailSum
    {P : Measure Ω} {B : ℕ → Ω → ℝ} {kappa : ℝ}
    (hB : ∀ m, Measurable (B m))
    (hsummable : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Summable fun j : ℕ => (3 : ℝ) ^ (kappa * (j : ℝ)) * B (k + j) ω) :
    ∃ F : ℕ → Ω → ℝ,
      (∀ k, Measurable (F k)) ∧
      (∀ᵐ ω ∂P, ∀ k : ℕ,
        HasSum (fun j : ℕ => (3 : ℝ) ^ (kappa * (j : ℝ)) * B (k + j) ω)
          (F k ω)) := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂P,
      Summable fun j : ℕ => (3 : ℝ) ^ (kappa * (j : ℝ)) * B (k + j) ω := by
    intro k
    filter_upwards [hsummable] with ω hω
    exact hω k
  have hae : ∀ k : ℕ,
      AEMeasurable
        (fun ω => ∑' j : ℕ, (3 : ℝ) ^ (kappa * (j : ℝ)) * B (k + j) ω) P :=
    fun k => IndependentSums.aemeasurable_tsum_of_ae_summable
      (fun j => (hB (k + j)).const_mul _) (hk k)
  refine ⟨fun k => (hae k).mk _, fun k => (hae k).measurable_mk, ?_⟩
  rw [ae_all_iff]
  intro k
  filter_upwards [hk k, (hae k).ae_eq_mk] with ω hsum heq
  rw [← heq]
  exact hsum.hasSum

end

end Quenched
end HighContrast
end HCPolySupport
