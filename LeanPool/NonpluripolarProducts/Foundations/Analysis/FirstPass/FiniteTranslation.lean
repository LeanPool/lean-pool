/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PotentialL1
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# Translation by finite constants

Adding the same finite real constant to two extended-real potentials preserves
their canonical absolute difference, including at their common pole.  Hence it
also preserves the chartwise extended `L¹` distance and chart-local `L¹`
convergence.  The same operation preserves the genuine theta-PSH potential
predicate.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A common finite translation preserves the canonical extended absolute
difference, including every combination of infinite values. -/
@[simp] theorem canonicalERealAbsDiff_add_coe (a b : EReal) (c : ℝ) :
    canonicalERealAbsDiff (a + (c : EReal)) (b + (c : EReal)) =
      canonicalERealAbsDiff a b := by
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff,
      ← EReal.coe_add, ← EReal.coe_sub]

/-- Translating both potentials by the same finite constant preserves their
chartwise extended `L¹` distance. -/
@[simp] theorem chartL1EDistance_add_coe (u v : M → EReal) (c : ℝ)
    (e : ComplexChart n M) (K : Set (ComplexModel n)) :
    chartL1EDistance (fun x => u x + (c : EReal))
        (fun x => v x + (c : EReal)) e K =
      chartL1EDistance u v e K := by
  apply lintegral_congr
  intro z
  exact canonicalERealAbsDiff_add_coe _ _ c

/-- Chart-local `L¹` convergence is invariant under a common fixed finite
translation of the family and its limit. -/
theorem ManifoldL1LocallyTendsto.add_const {α : Type*}
    {u : α → M → EReal} {l : Filter α} {v : M → EReal}
    (hu : ManifoldL1LocallyTendsto (n := n) u l v) (c : ℝ) :
    ManifoldL1LocallyTendsto (n := n)
      (fun i x => u i x + (c : EReal)) l
      (fun x => v x + (c : EReal)) := by
  intro e K hK hKe
  simpa only [chartL1EDistance_add_coe] using hu e K hK hKe

variable [IsComplexManifold n M]

/-- Adding a finite real constant preserves the same theta-PSH potential
class, including local nondegeneracy at poles. -/
theorem IsThetaPshPotential.add_const {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : IsThetaPshPotential θ u) (c : ℝ) :
    IsThetaPshPotential θ (fun x => u x + (c : EReal)) := by
  constructor
  · have hraw :=
      PositiveClasses.thetaPlurisubharmonic_sub_const hu.1 (-c)
    simpa [sub_eq_add_neg] using hraw
  · intro x U hU hx
    obtain ⟨y, hy, hfin⟩ := hu.2 x U hU hx
    exact ⟨y, hy, EReal.add_ne_bot_iff.mpr ⟨hfin, EReal.coe_ne_bot c⟩⟩

end

end SGPT.Foundations.Analysis.FirstPass
