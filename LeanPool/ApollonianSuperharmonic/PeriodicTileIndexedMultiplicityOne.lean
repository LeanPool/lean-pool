/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCoverage
public import LeanPool.ApollonianSuperharmonic.PeriodicTileComplex

-- [TABLET NODE: PeriodicTileIndexedMultiplicityOne]

/-!
# PeriodicTileIndexedMultiplicityOne

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PeriodicTileIndexedMultiplicityOne {ι : Type} (P : PeriodicTileComplex ι) :
    ∀ x : LatticeCell, ∃! a : ι, x ∈ (P.tile a).cells := by
-- BODY
  classical
  let representative : GaussianInt → GaussianInt := fun x =>
    Classical.choose (P.lattice_full_rank x)
  have representative_spec (x : GaussianInt) :
      representative x ∈ P.latticeReps ∧
        x - representative x ∈ P.lattice :=
    (Classical.choose_spec (P.lattice_full_rank x)).1
  let incidences : Finset (Σ a : ι, LatticeCell) :=
    P.vertexOrbitReps.sigma (fun a => (P.tile a).cells)
  let target : Finset GaussianInt := P.latticeReps
  let incidence_map : (Σ a : ι, LatticeCell) → GaussianInt :=
    fun q => representative q.2
  have map_to_target : Set.MapsTo incidence_map incidences target := by
    intro q hq
    exact (representative_spec q.2).1
  have target_to_image : Set.MapsTo
      (fun x : GaussianInt => x) (target : Set GaussianInt)
      (incidence_map '' (incidences : Set (Σ a : ι, LatticeCell))) := by
    intro x hx
    obtain ⟨a, ha⟩ := PeriodicTileCoverage P.toPeriodicTileCore x
    obtain ⟨r, hr, u, hau⟩ := (P.vertex_orbit_representatives a).exists
    have htile : P.tile a = TileTranslation (P.tile r) u := by
      calc
        P.tile a = P.tile (P.shift u r) := congrArg P.tile hau
        _ = TileTranslation (P.tile r) u := P.tile_periodic u r
    have hmem : x ∈ (TileTranslation (P.tile r) u).cells := by
      rw [← htile]
      exact ha
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
    change y + (u : GaussianInt) = x at hxy
    have hyr : y - x ∈ P.lattice := by
      have hu : (u : GaussianInt) ∈ P.lattice := u.property
      have hneg := P.lattice.neg_mem hu
      have : y - x = -u := by
        rw [← hxy]
        abel
      rw [this]
      exact hneg
    have hrep : representative y = x := by
      apply (P.lattice_full_rank y).unique
      · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
      · exact ⟨hx, by simpa [sub_eq_add_neg, add_comm] using hyr⟩
    refine ⟨⟨r, y⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨hr, hy⟩
    · exact hrep
  have image_eq : Finset.image incidence_map incidences = target := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact map_to_target hq
    · apply Finset.card_le_card_of_injOn (fun x : GaussianInt => x)
        (by
          intro x hx
          obtain ⟨q, hq, hqx⟩ := target_to_image hx
          refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
          simpa using hqx)
      intro x hx y hy hxy
      exact hxy
  have map_injective : Set.InjOn incidence_map
      (incidences : Set (Σ a : ι, LatticeCell)) := by
    apply (Finset.card_image_iff).mp
    rw [image_eq]
    calc
      target.card = ∑ a ∈ P.vertexOrbitReps, (P.tile a).cells.card := by
        simpa [target, TileArea] using P.area_balance.symm
      _ = incidences.card := by
        simp [incidences, Finset.card_sigma]
  intro x
  obtain ⟨a, ha⟩ := PeriodicTileCoverage P.toPeriodicTileCore x
  refine ⟨a, ha, ?_⟩
  intro b hb
  obtain ⟨ra, hra, u, hau⟩ := (P.vertex_orbit_representatives a).exists
  obtain ⟨rb, hrb, v, hbv⟩ := (P.vertex_orbit_representatives b).exists
  have ha' : x ∈ (TileTranslation (P.tile ra) u).cells := by
    have htile : P.tile a = TileTranslation (P.tile ra) u := by
      calc
        P.tile a = P.tile (P.shift u ra) := congrArg P.tile hau
        _ = TileTranslation (P.tile ra) u := P.tile_periodic u ra
    rw [← htile]
    exact ha
  have hb' : x ∈ (TileTranslation (P.tile rb) v).cells := by
    have htile : P.tile b = TileTranslation (P.tile rb) v := by
      calc
        P.tile b = P.tile (P.shift v rb) := congrArg P.tile hbv
        _ = TileTranslation (P.tile rb) v := P.tile_periodic v rb
    rw [← htile]
    exact hb
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp ha'
  obtain ⟨z, hz, hxz⟩ := Finset.mem_image.mp hb'
  change y + (u : GaussianInt) = x at hxy
  change z + (v : GaussianInt) = x at hxz
  have hmap : incidence_map ⟨ra, y⟩ = incidence_map ⟨rb, z⟩ := by
    have hrep : representative y = representative z := by
      have hyx : y - representative y ∈ P.lattice := (representative_spec y).2
      have hzx : z - representative z ∈ P.lattice := (representative_spec z).2
      have hu : (u : GaussianInt) ∈ P.lattice := u.property
      have hv : (v : GaussianInt) ∈ P.lattice := v.property
      have hyzmem : y - z ∈ P.lattice := by
        have hsub : y - z = (v : GaussianInt) - u := by
          calc
            y - z = (y + (u : GaussianInt)) - (z + (v : GaussianInt)) +
                (v : GaussianInt) - u := by abel
            _ = (v : GaussianInt) - u := by rw [hxy, hxz]; abel
        rw [hsub]
        exact P.lattice.sub_mem hv hu
      have hycand : y - representative z ∈ P.lattice := by
        have := P.lattice.add_mem hyzmem hzx
        convert this using 1; abel
      exact (P.lattice_full_rank y).unique
        ⟨(representative_spec y).1, hyx⟩
        ⟨(representative_spec z).1, hycand⟩
    exact hrep
  have hinc : (⟨ra, y⟩ : Σ a : ι, LatticeCell) = ⟨rb, z⟩ :=
    map_injective (Finset.mem_sigma.mpr ⟨hra, hy⟩)
      (Finset.mem_sigma.mpr ⟨hrb, hz⟩) hmap
  have hyz : y = z := congrArg Sigma.snd hinc
  have huv : (u : GaussianInt) = v := by
    apply add_left_cancel (a := y)
    simpa [hyz] using hxy.trans hxz.symm
  have hrr : ra = rb := congrArg Sigma.fst hinc
  have huv' : u = v := Subtype.ext huv
  simp [hau, hbv, huv', hrr]

end ApollonianSuperharmonic

end
