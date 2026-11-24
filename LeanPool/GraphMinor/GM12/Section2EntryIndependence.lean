/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2EntryComparison
import LeanPool.GraphMinor.GM12.Section2EntryConstruction
import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import LeanPool.GraphMinor.Surface.Disc

/-!
# The entry edge does not depend on its starting point

XII, page 243, omits the proof that the entry choice is independent of
where the approach is started. Normalize one entry witness on a common
approach. Comparisons inside the open-disc region can be moved to any
other starting time. Concatenating the normalized approach with the same
spoke then gives the required entry witness at that time.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Starting-point independence in XII's entry-edge definition, page 243.
Once an entry edge has a witness, every starting point in the approach
interval has a witness for that same edge. -/
theorem entersLike_witness_at {S : Type*} [TopologicalSpace S] [T2Space S]
    {r e : Set S} {v w : S} (hcell : IsOpenDisc r) (hw : w ∈ r)
    (hvE : v ∉ e) (hwE : w ∉ e) (hvw : v ≠ w)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hfc : f c = v)
    (hfr : ∀ t ∈ Ioo a c, f t ∈ r) (hentry : EntersLike f a c e r v w)
    {hNew : ℝ} (hNewIn : hNew ∈ Ioo a c) :
    ∃ ξ ρ : Curve S, IsEntryCurve f hNew c e w ξ ∧ range ρ ⊆ r ∧
      CurvesHomotopicIn (r ∪ {v}) ξ ρ := by
  classical
  obtain ⟨h, hh, ξ, ρ, hξ, hρ, hhom⟩ := hentry
  let h₀ : ℝ := min h hNew
  have h₀a : a < h₀ := lt_min hh.1 hNewIn.1
  have h₀c : h₀ < c := lt_of_le_of_lt (min_le_left _ _) hh.2
  have hpos : 0 < c - h₀ := sub_pos.mpr h₀c
  have hFinside : ∀ t : unitInterval, t < 1 → f (h₀ + t.val * (c - h₀)) ∈ r := by
    intro t ht
    apply hfr
    refine ⟨?_, ?_⟩
    · exact h₀a.trans_le (le_add_of_nonneg_right (mul_nonneg t.property.1 hpos.le))
    · have ht' : (t : ℝ) < 1 := ht
      nlinarith
  have hFmem : ∀ t : unitInterval, f (h₀ + t.val * (c - h₀)) ∈ r ∪ {v} := by
    intro t
    by_cases ht : t = 1
    · subst t
      right
      change f (h₀ + 1 * (c - h₀)) = v
      convert hfc using 1
      congr 1
      ring
    · exact Or.inl (hFinside t (lt_of_le_of_ne t.property.2 ht))
  let F : Path (⟨f h₀, Or.inl (hfr h₀ ⟨h₀a, h₀c⟩)⟩ : (r ∪ {v} : Set S))
      ⟨v, Or.inr (mem_singleton v)⟩ := {
    toFun := fun t => ⟨f (h₀ + t.val * (c - h₀)), hFmem t⟩
    continuous_toFun := (hf.comp (by fun_prop)).subtype_mk _
    source' := Subtype.ext (by simp only [Icc.coe_zero, zero_mul, add_zero])
    target' := Subtype.ext (by
      change f (h₀ + 1 * (c - h₀)) = v
      convert hfc using 1
      congr 1
      ring) }
  have hFval : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀)) := fun _ => rfl
  let s : unitInterval := ⟨(h - h₀) / (c - h₀),
    div_nonneg (sub_nonneg.mpr (min_le_left _ _)) hpos.le,
    (div_le_one hpos).mpr (by linarith [hh.2])⟩
  let s' : unitInterval := ⟨(hNew - h₀) / (c - h₀),
    div_nonneg (sub_nonneg.mpr (min_le_right _ _)) hpos.le,
    (div_le_one hpos).mpr (by linarith [hNewIn.2])⟩
  have hs : s < 1 := (div_lt_one hpos).mpr (by linarith [hh.2])
  have hs' : s' < 1 := (div_lt_one hpos).mpr (by linarith [hNewIn.2])
  have hstart : h = h₀ + s.val * (c - h₀) := by
    change h = h₀ + (h - h₀) / (c - h₀) * (c - h₀)
    field_simp [ne_of_gt hpos]
    ring
  have hstart' : hNew = h₀ + s'.val * (c - h₀) := by
    change hNew = h₀ + (hNew - h₀) / (c - h₀) * (c - h₀)
    field_simp [ne_of_gt hpos]
    ring
  obtain ⟨β, σ, hβinj, _, hβint, hσr, hβhom⟩ := compare_entry_to_approach
    hw F hFval hstart hfc hvE hwE hvw hξ hρ hhom
  let R : Set (r ∪ {v} : Set S) := (Subtype.val : (r ∪ {v} : Set S) → S) ⁻¹' r
  have hR : IsSimplyConnectedSet R :=
    (openDisc_in_subspace hcell (show r ⊆ r ∪ {v} from subset_union_left)).isSimplyConnectedSet
  obtain ⟨σNew, hσNew, hβNew⟩ := terminal_entry_from_any_time hR F
    (fun t ht => hFinside t ht) hw β hs hs' σ hσr hβhom
  let j : (r ∪ {v} : Set S) → S := Subtype.val
  let p := (F.subpath s' 1).map (show Continuous j from continuous_subtype_val)
  let q := β.map (show Continuous j from continuous_subtype_val)
  have hp : ∀ t : unitInterval, p t = f (hNew + t.val * (c - hNew)) := by
    intro t
    change (F (Icc.convexComb s' 1 t)).val = _
    rw [hFval]
    congr 1
    simp only [Icc.coe_convexComb, Icc.coe_one]
    rw [hstart']
    ring
  have hentryNew := isEntryCurve_trans p q hp hβinj hβint
  let ξNew : Curve S := (((F.subpath s' 1).trans β).map
    (show Continuous j from continuous_subtype_val)).toContinuousMap
  let ρNew : Curve S := (σNew.map (show Continuous j from continuous_subtype_val)).toContinuousMap
  refine ⟨ξNew, ρNew, ?_, ?_, ?_⟩
  · dsimp only [ξNew]
    rw [Path.map_trans]
    exact hentryNew
  · rintro x ⟨t, rfl⟩
    exact hσNew t
  · exact curvesHomotopicIn_of_paths_homotopic hβNew

/-- Entry is unchanged after discarding an initial portion of the
region interval. This is the interval form of the starting-point
independence asserted on XII page 243. -/
theorem entersLike_iff_tail_interval
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {r e : Set S} {v w : S} (hcell : IsOpenDisc r) (hw : w ∈ r)
    (hvE : v ∉ e) (hwE : w ∉ e) (hvw : v ≠ w)
    {f : ℝ → S} (hf : Continuous f) {a a' c : ℝ} (haa' : a ≤ a') (ha'c : a' < c)
    (hfc : f c = v) (hfr : ∀ t ∈ Ioo a c, f t ∈ r) :
    EntersLike f a c e r v w ↔ EntersLike f a' c e r v w := by
  constructor
  · intro he
    let h := (a' + c) / 2
    have hh : h ∈ Ioo a' c := ⟨by dsimp [h]; linarith, by dsimp [h]; linarith⟩
    have hhOld : h ∈ Ioo a c := ⟨haa'.trans_lt hh.1, hh.2⟩
    obtain ⟨ξ, ρ, hξ, hρ, hhom⟩ := entersLike_witness_at hcell hw hvE hwE hvw
      hf hfc hfr he hhOld
    exact ⟨h, hh, ξ, ρ, hξ, hρ, hhom⟩
  · rintro ⟨h, hh, ξ, ρ, hξ, hρ, hhom⟩
    exact ⟨h, ⟨haa'.trans_lt hh.1, hh.2⟩, ξ, ρ, hξ, hρ, hhom⟩

end GraphMinor.GM12
