/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73WalkSubstitution
public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2ConnectedRegionArc
import LeanPool.GraphMinor.GM12.Section2CirclePeriod
import LeanPool.GraphMinor.GM12.Section2TraceParameters
import LeanPool.GraphMinor.GM11.Regions

/-!+# Counting visits to a region hub

The representativity step of XII (7.3), page 261, uses a normal
circle whose intersection with each region is connected. Such a
circle visits the hub of any fixed region at most once in its
radial trace. A second visit would give a second parameter interval
for that region, contradicting connectedness of the intersection.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem traceSteps_count_zero
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S}
    {f : ℝ → S} {r : Set S} (hr : r ∈ Γ.R) {v : S} (hv : v ∈ r)
    {a b : ℝ} {x y : S} (W : GraphWalk K.toGraph x y)
    (hW : TraceSteps Γ K f a b W)
    (havoid : ∀ s ∈ Ioo a b, f s ∉ r) : walkVertexCount v W = 0 := by
  classical
  cases hcase : W with
  | nil h => rfl
  | @cons _ w _ e h₁ rest =>
    rw [hcase] at hW
    cases hrest : rest with
    | nil h => rw [hrest] at hW; exact hW.elim
    | @cons _ z _ e' h₂ tail =>
      rw [hrest] at hW
      obtain ⟨c, hac, _, hx, _, _, q, hq, hwq, hfr, _, _, ht⟩ := hW
      have hcb := (traceSteps_parameters tail ht).1
      have hxv : x ≠ v := fun heq => region_subset hr (heq ▸ hv) (Γ.V_subset_U hx)
      have hwv : w ≠ v := by
        intro heq
        have hqr := region_eq_of_mem hq hr hwq (heq ▸ hv)
        have hm : (a + c) / 2 ∈ Ioo a c := ⟨by linarith, by linarith⟩
        exact havoid _ ⟨hm.1, hm.2.trans_le hcb⟩ (hqr ▸ hfr _ hm)
      have htzero := traceSteps_count_zero hr hv tail ht
        (fun s hs => havoid s ⟨hac.trans hs.1, hs.2⟩)
      simp only [walkVertexCount, ite_eq_right hxv, ite_eq_right hwv, htzero, Nat.zero_add]
termination_by W.length
decreasing_by
  rw [hcase, hrest]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- An embedded circle with connected intersection with a region
visits its hub at most once in a one-period radial trace. This
bounds the extra two edges in the representativity step of XII
(7.3), page 261. -/
theorem traceSteps_hub_count_le_one
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ K : Drawing S}
    {φ : C(Circle, S)} (hφ : IsEmbedding φ)
    {r : Set S} (hr : r ∈ Γ.R) (hconn : IsPreconnected (range φ ∩ r))
    {v : S} (hv : v ∈ r) {l a b : ℝ} (hla : l ≤ a) (hbl : b ≤ l + 1)
    {x y : S} (W : GraphWalk K.toGraph x y)
    (hW : TraceSteps Γ K (periodicCurve φ) a b W) :
    walkVertexCount v W ≤ 1 := by
  classical
  cases hcase : W with
  | nil h => exact Nat.zero_le _
  | @cons _ w _ e h₁ rest =>
    rw [hcase] at hW
    cases hrest : rest with
    | nil h => rw [hrest] at hW; exact hW.elim
    | @cons _ z _ e' h₂ tail =>
      rw [hrest] at hW
      obtain ⟨c, hac, hfa, hx, hfc, _, q, hq, hwq, hfr, _, _, ht⟩ := hW
      have hp := traceSteps_parameters tail ht
      have hxv : x ≠ v := fun heq => region_subset hr (heq ▸ hv) (Γ.V_subset_U hx)
      by_cases hwv : w = v
      · have hqr := region_eq_of_mem hq hr hwq (hwv ▸ hv)
        have hfr' : ∀ s ∈ Ioo a c, periodicCurve φ s ∈ r := fun s hs => hqr ▸ hfr s hs
        have havoid : ∀ s ∈ Ioo c b, periodicCurve φ s ∉ r := by
          intro s hs hsr
          obtain ⟨t, ht, hts⟩ := preimage_region_subset_parameter_arc hφ hr hconn hac
            (hfa.symm ▸ hx) (hfc.symm ▸ hp.2.2.1) hfr' hsr
          have hts' := circle_parameter_injOn l
            (show t ∈ Ico l (l + 1) from ⟨hla.trans ht.1.le, ht.2.trans_le (hp.1.trans hbl)⟩)
            (show s ∈ Ico l (l + 1) from ⟨hla.trans (hac.trans hs.1).le, hs.2.trans_le hbl⟩) hts
          exact (not_lt_of_ge hs.1.le) (hts' ▸ ht.2)
        have htzero := traceSteps_count_zero hr hv tail ht havoid
        simp only [walkVertexCount, ite_eq_right hxv, ite_eq_left hwv, htzero, Nat.zero_add,
          Nat.add_zero, le_refl]
      · have htail := traceSteps_hub_count_le_one hφ hr hconn hv (hla.trans hac.le) hbl tail ht
        simpa only [walkVertexCount, ite_eq_right hxv, ite_eq_right hwv, Nat.zero_add] using htail
termination_by W.length
decreasing_by
  rw [hcase, hrest]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

end GraphMinor.GM12
