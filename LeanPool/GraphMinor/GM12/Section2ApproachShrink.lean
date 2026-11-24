/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SectorEntry
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM12.Section2SpokePaths

/-!
# Shortening an approach before comparing its entry

For the entry definition on XII page 243, one may choose the starting
point as close to the vertex as needed. Continuity puts a terminal
segment of the approach inside the sector neighbourhood used for the
entry comparison. No injectivity of the approach is required.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface unitInterval

/-- An approach through a sector and a spoke germ in the same sector
have an entry comparison after shortening the approach. -/
theorem entry_comparison_from_sector_approach {S : Type*} [TopologicalSpace S]
    {D W r Z : Set S} {a v b : Z} (F : Path a v) (β : Path (F 1) b)
    (hD : IsClosedDisc D) (hv : v.val ∈ discBd D)
    (hW : IsOpen W) (hvW : v.val ∈ W)
    (hlocal : ((D \ discBd D) ∩ W) ∪ {v.val} ⊆ Z)
    (hregion : (D \ discBd D) ∩ W ⊆ r)
    (hvr : v.val ∉ r)
    (hF : ∀ t, t < 1 → (F t).val ∈ r ∩ (D \ discBd D))
    (hβr : ∀ t, 0 < t → (β t).val ∈ r)
    (hgerm : ∃ ε : I, 0 < ε ∧
      ∀ t, 0 < t → t ≤ ε → (β t).val ∈ D \ discBd D) :
    ∃ t : I, t < 1 ∧ ∃ ρ : Path (F t) b,
      (∀ s, (ρ s).val ∈ r) ∧ ((F.subpath t 1).trans β).Homotopic ρ := by
  have hv' : (F 1).val ∈ discBd D := by rw [F.target]; exact hv
  have hvW' : (F 1).val ∈ W := by rw [F.target]; exact hvW
  have hlocal' : ((D \ discBd D) ∩ W) ∪ {(F 1).val} ⊆ Z := by rw [F.target]; exact hlocal
  obtain ⟨N, hN, hvN, hcompare⟩ :=
    exists_sector_entry_neighbourhood hD hv' hW hvW' hlocal' hregion
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨δ, hδ, hδhalf, hδN⟩ := GM11.exists_pos_le
    (continuous_subtype_val.comp F.symm.continuous) hN (by simpa only [Function.comp_apply,
      Path.symm_apply, unitInterval.symm_zero] using hvN)
    (show (0 : I) < half by change (0 : ℝ) < 1 / 2; norm_num)
  let t : I := σ δ
  have ht : t < 1 := by
    change (1 - δ.val : ℝ) < 1
    exact sub_lt_self _ hδ
  have hne : F t ≠ F 1 := by
    intro h
    have hm := (hF t ht).1
    rw [h, F.target] at hm
    exact hvr hm
  have hp : ∀ s, ((F.subpath t 1) s).val ∈ ((N ∩ D) \ discBd D) ∪ {(F 1).val} := by
    intro s
    let u : I := Icc.convexComb t 1 s
    by_cases hu : u = 1
    · right
      change (F u).val ∈ {(F 1).val}
      rw [hu]
      exact mem_singleton _
    · left
      have hu1 : u < 1 := lt_of_le_of_ne u.property.2 hu
      have htu : t ≤ u := by
        change t.val ≤ (1 - s.val) * t.val + s.val * 1
        nlinarith [s.property.1, t.property.2]
      have hback : σ u ≤ δ := by
        change 1 - u.val ≤ δ.val
        have htu' : 1 - δ.val ≤ u.val := htu
        linarith
      have hNmem : (F u).val ∈ N := by
        have hm := hδN (σ u) hback
        simpa only [Function.comp_apply, Path.symm_apply, unitInterval.symm_symm] using hm
      exact ⟨⟨hNmem, (hF u hu1).2.1⟩, (hF u hu1).2.2⟩
  obtain ⟨ρ, hρ, hhom⟩ := hcompare (F.subpath t 1) β hne hp hβr hgerm
  exact ⟨t, ht, ρ, hρ, hhom⟩

/-- A surface path with a germ in the entering sector gives the path
comparison in the region with its vertex added. -/
theorem entry_comparison_from_surface_germ {S : Type*} [TopologicalSpace S]
    {D W r : Set S} {v c : S} (hc : c ∈ r)
    {a : (r ∪ {v} : Set S)}
    (F : Path a (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S))) (β : Path v c)
    (hD : IsClosedDisc D) (hv : v ∈ discBd D)
    (hW : IsOpen W) (hvW : v ∈ W)
    (hregion : (D \ discBd D) ∩ W ⊆ r) (hvr : v ∉ r)
    (hF : ∀ t, t < 1 → (F t).val ∈ r ∩ (D \ discBd D))
    (hβr : ∀ t, 0 < t → β t ∈ r)
    (hgerm : ∃ ε : I, 0 < ε ∧ ∀ t, 0 < t → t ≤ ε → β t ∈ D \ discBd D) :
    ∃ q : Path (F 1) (⟨c, Or.inl hc⟩ : (r ∪ {v} : Set S)),
      (∀ t, (q t).val = β t) ∧ ∃ t : I, t < 1 ∧
        ∃ ρ : Path (F t) (⟨c, Or.inl hc⟩ : (r ∪ {v} : Set S)),
          (∀ s, (ρ s).val ∈ r) ∧ ((F.subpath t 1).trans q).Homotopic ρ := by
  obtain ⟨q₀, hq₀⟩ := exists_path_in_region_vertex hc β hβr
  let q := q₀.cast F.target rfl
  have hq : ∀ t, (q t).val = β t := hq₀
  have hlocal : ((D \ discBd D) ∩ W) ∪ {v} ⊆ r ∪ {v} := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hregion hx)
    · exact Or.inr hx
  obtain ⟨t, ht, ρ, hρ, hhom⟩ := entry_comparison_from_sector_approach F q hD hv hW hvW
    hlocal hregion hvr hF (fun t ht => hq t ▸ hβr t ht) (by
      obtain ⟨ε, hε, hεβ⟩ := hgerm
      exact ⟨ε, hε, fun t ht htε => hq t ▸ hεβ t ht htε⟩)
  exact ⟨q, hq, t, ht, ρ, hρ, hhom⟩

end GraphMinor.GM12
