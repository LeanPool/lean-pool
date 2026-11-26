/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryAtPathInSubspace
public import LeanPool.GraphMinor.GM12.Section2RegionVisitHomotopy
import LeanPool.GraphMinor.Surface.Disc

/-!
# Deforming a real region interval with fixed ends

For XII (2.1), Case 1, page 244, split a region visit at its midpoint.
The entry and reversed exit comparisons start at that midpoint.
Read both in the region with both boundary vertices restored. The
single-visit path algebra replaces the visit by its two spokes while
fixing its ends. All spoke parameterizations retain their exact edge
closures and interiors.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- An actual real region interval deforms to the two spokes supplied
by its exit and entry conditions, inside any subspace containing the
region and its two ends. -/
theorem region_path_homotopic_to_spokes
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {r Z e e' : Set S} (hcell : IsOpenDisc r) {u v w : S}
    (hrZ : r ⊆ Z) (huZ : u ∈ Z) (hvZ : v ∈ Z) (hw : w ∈ r)
    (huE : u ∉ e) (hwE : w ∉ e) (huw : u ≠ w)
    (hvE : v ∉ e') (hwE' : w ∉ e') (hvw : v ≠ w)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c)
    (hfa : f a = u) (hfc : f c = v) (hfr : ∀ t ∈ Ioo a c, f t ∈ r)
    (hleave : LeavesLike f a c e r u w) (henter : EntersLike f a c e' r v w)
    (P : Path (⟨u, huZ⟩ : Z) ⟨v, hvZ⟩)
    (hP : ∀ t, (P t).val = f (a + t.val * (c - a))) :
    ∃ (α : Path (⟨u, huZ⟩ : Z) ⟨w, hrZ hw⟩)
      (β : Path (⟨v, hvZ⟩ : Z) ⟨w, hrZ hw⟩),
      Function.Injective (fun t => (α t).val) ∧ Function.Injective (fun t => (β t).val) ∧
      range (fun t => (α t).val) = closure e ∧ range (fun t => (β t).val) = closure e' ∧
      (fun t => (α t).val) '' Ioo (0 : unitInterval) 1 = e ∧
      (fun t => (β t).val) '' Ioo (0 : unitInterval) 1 = e' ∧
      P.Homotopic (α.trans β.symm) := by
  let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let m := (a + c) / 2
  have hm : m ∈ Ioo a c := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  let L : Path (⟨u, huZ⟩ : Z) (P half) := (P.subpath 0 half).cast P.source.symm rfl
  let F : Path (P half) (⟨v, hvZ⟩ : Z) := (P.subpath half 1).cast rfl P.target.symm
  let G := L.symm
  have hF : ∀ t, (F t).val = f (m + t.val * (c - m)) := by
    intro t
    change (P (Icc.convexComb half 1 t)).val = _
    rw [hP]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_one]
    dsimp only [half, m]
    ring
  have hG : ∀ t, (G t).val = f (m + t.val * (a - m)) := by
    intro t
    change (P (Icc.convexComb 0 half (unitInterval.symm t))).val = _
    rw [hP]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_zero, mul_zero, zero_add]
    change a + (1 - t.val) * (1 / 2) * (c - a) = _
    dsimp only [m]
    ring
  have hFsmall : ∀ t, (F t).val ∈ r ∪ {v} := by
    intro t
    by_cases ht : t = 1
    · subst t; rw [F.target]; exact Or.inr rfl
    · left
      rw [hF]
      have ht1 : t.val < 1 := unitInterval.lt_one_iff_ne_one.mpr ht
      apply hfr
      constructor <;> nlinarith [t.property.1, hm.1, hm.2]
  have hGsmall : ∀ t, (G t).val ∈ r ∪ {u} := by
    intro t
    by_cases ht : t = 1
    · subst t; rw [G.target]; exact Or.inr rfl
    · left
      rw [hG]
      have ht1 : t.val < 1 := unitInterval.lt_one_iff_ne_one.mpr ht
      apply hfr
      constructor <;> nlinarith [t.property.1, hm.1, hm.2]
  have hZr : r ∪ {v} ⊆ Z := union_subset hrZ (singleton_subset_iff.mpr hvZ)
  have hZl : r ∪ {u} ⊆ Z := union_subset hrZ (singleton_subset_iff.mpr huZ)
  obtain ⟨β, ρ, hβi, hβrange, hβe, hρ, hβhom⟩ :=
    entry_comparison_at_path_start_in_subspace hcell hw hZr hvE hwE' hvw hf hm
      hfc hfr henter F hFsmall hF
  have hfm : -m ∈ Ioo (-c) (-a) := ⟨neg_lt_neg hm.2, neg_lt_neg hm.1⟩
  have hGneg : ∀ t, (G t).val = (fun z => f (-z)) (-m + t.val * (-a - -m)) := by
    intro t
    rw [hG]
    congr 1
    ring
  obtain ⟨α, σ, hαi, hαrange, hαe, hσ, hαhom⟩ :=
    entry_comparison_at_path_start_in_subspace hcell hw hZl huE hwE huw
      (hf.comp continuous_neg) hfm (by simpa only [Function.comp_apply, neg_neg] using hfa)
      (fun t ht => hfr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      hleave G hGsmall hGneg
  have hR := openDisc_in_subspace hcell hrZ
  have hvisit := region_visit_homotopic_to_spokes hR.isSimplyConnectedSet
    G F α β σ ρ hσ hρ hαhom hβhom
  have hsplit : (L.trans F).Homotopic P :=
    split_path_homotopic P half L F (fun _ => rfl) (fun _ => rfl)
  have hGL : G.symm = L := Path.symm_symm L
  rw [hGL] at hvisit
  exact ⟨α, β, hαi, hβi, hαrange, hβrange, hαe, hβe, hsplit.symm.trans hvisit⟩

end GraphMinor.GM12
