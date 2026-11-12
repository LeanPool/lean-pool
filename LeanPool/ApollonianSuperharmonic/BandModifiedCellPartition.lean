/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.LatticeFundamentalSet
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: BandModifiedCellPartition]

/-!
# BandModifiedCellPartition

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ModifiedCellPartitionConstruction

private noncomputable abbrev base (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) :
    SixSubtileLabel → Finset GaussianInt := by
  classical
  exact fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells

private noncomputable abbrev incidences (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) : Finset
    (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ (base P O) j}) := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  change (Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}))
  exact Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)

private noncomputable abbrev representative (L : AddSubgroup GaussianInt) (R : Finset
    GaussianInt) (hfund : LatticeFundamentalSet L R) : GaussianInt → GaussianInt := by
  classical
  exact fun y =>
    Classical.choose (hfund y)

private theorem representative_spec (L : AddSubgroup GaussianInt) (R : Finset GaussianInt) (hfund
    : LatticeFundamentalSet L R) (y : GaussianInt) :
      (representative L R hfund) y ∈ R ∧ y - (representative L R hfund) y ∈ L := by
  classical
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  change (representative y ∈ R ∧ y - representative y ∈ L)
  exact (Classical.choose_spec (hfund y)).1

private theorem map_mem (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (L : AddSubgroup
    GaussianInt) (R : Finset GaussianInt) (hfund : LatticeFundamentalSet L R) (z : Σ j :
    SixSubtileLabel, {y : GaussianInt // y ∈ (base P O) j}) :
      (representative L R hfund) z.2 ∈ R := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  have representative_spec (y : GaussianInt) :
      representative y ∈ R ∧ y - representative y ∈ L := representative_spec L R hfund y
  change (representative z.2 ∈ R)
  exact (representative_spec z.2).1

private noncomputable abbrev mapped (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (L :
    AddSubgroup GaussianInt) (R : Finset GaussianInt) (hfund : LatticeFundamentalSet L R) : (Σ j
    : SixSubtileLabel, {y : GaussianInt // y ∈ (base P O) j}) → GaussianInt := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  change ((Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) → GaussianInt)
  exact fun z => representative z.2

private theorem hsurj (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (u : GaussianInt) (v :
    GaussianInt) (L : AddSubgroup GaussianInt) (R : Finset GaussianInt) (hu : u ∈ L) (hv : v ∈ L)
    (hfund : LatticeFundamentalSet L R) (hcover : forall x : LatticeCell, exists o :
    PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) : Set.SurjOn (mapped P O L R
          hfund) ((incidences P O) : Set _) (R : Set GaussianInt) := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  have representative_spec (y : GaussianInt) :
      representative y ∈ R ∧ y - representative y ∈ L := representative_spec L R hfund y
  let mapped : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) → GaussianInt :=
    fun z => representative z.2
  change (Set.SurjOn mapped (incidences : Set _) (R : Set GaussianInt))
  intro r hr
  obtain ⟨o, ho⟩ := hcover r
  cases o with
  | mk label first second =>
    cases label with
    | A =>
      change r ∈ (TileCellComplement (P 0 true) O).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .A := by simpa [base, TileCellComplement] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.A, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]
    | B =>
      change r ∈ (P 0 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .B := by simpa [base] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.B, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]
    | C =>
      change r ∈ (P 1 true).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .C := by simpa [base] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.C, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]
    | D =>
      change r ∈ (P 1 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .D := by simpa [base] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.D, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]
    | E =>
      change r ∈ (P 2 true).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .E := by simpa [base] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.E, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]
    | F =>
      change r ∈ (P 2 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at ho
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp ho
      have hyb : y ∈ base .F := by simpa [base] using hy
      have hyl : y - r ∈ L := by
        rw [← heq]
        dsimp [GaussianTranslation]
        have h1 : (first : GaussianInt) * u ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hu first
        have h2 : (second : GaussianInt) * v ∈ L := by
          rw [← zsmul_eq_mul]
          exact L.zsmul_mem hv second
        convert L.neg_mem (L.add_mem h1 h2) using 1; abel
      have hre : representative y = r := by
        apply (hfund y).unique
        · exact ⟨(representative_spec y).1, (representative_spec y).2⟩
        · exact ⟨hr, hyl⟩
      refine ⟨⟨.F, ⟨y, hyb⟩⟩, ?_, hre⟩
      simp [incidences]

private theorem hcard (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (R : Finset GaussianInt)
    (harea : TileArea (TileCellComplement (P 0 true) O) +
        TileArea (P 0 false) + TileArea (P 1 true) +
        TileArea (P 1 false) + TileArea (P 2 true) +
        TileArea (P 2 false) = R.card) : (incidences P O).card = R.card := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  change (incidences.card = R.card)
  simp [incidences, base, TileArea] at harea ⊢
  simp [TileCellComplement] at harea ⊢
  omega

private theorem himage (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (u : GaussianInt) (v :
    GaussianInt) (L : AddSubgroup GaussianInt) (R : Finset GaussianInt) (hu : u ∈ L) (hv : v ∈ L)
    (hfund : LatticeFundamentalSet L R) (hcover : forall x : LatticeCell, exists o :
    PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) : (incidences P O).image
          (mapped P O L R hfund) = R := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  have map_mem (z : Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :
      representative z.2 ∈ R := map_mem P O L R hfund z
  let mapped : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) → GaussianInt :=
    fun z => representative z.2
  have hsurj : Set.SurjOn mapped (incidences : Set _) (R : Set GaussianInt) := hsurj P O u v L R
      hu hv hfund hcover
  change (incidences.image mapped = R)
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact map_mem w
  · apply Finset.card_le_card
    intro z hz
    obtain ⟨w, hw, hwm⟩ := hsurj hz
    exact Finset.mem_image.mpr ⟨w, hw, hwm⟩

private theorem hinj (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (u : GaussianInt) (v :
    GaussianInt) (L : AddSubgroup GaussianInt) (R : Finset GaussianInt) (hu : u ∈ L) (hv : v ∈ L)
    (hfund : LatticeFundamentalSet L R) (hcover : forall x : LatticeCell, exists o :
    PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells) (harea : TileArea
          (TileCellComplement (P 0 true) O) +
        TileArea (P 0 false) + TileArea (P 1 true) +
        TileArea (P 1 false) + TileArea (P 2 true) +
        TileArea (P 2 false) = R.card) : Set.InjOn (mapped P O L R hfund) ((incidences P O) : Set
            _) := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  let mapped : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) → GaussianInt :=
    fun z => representative z.2
  have hcard : incidences.card = R.card := hcard P O R harea
  have himage : incidences.image mapped = R := himage P O u v L R hu hv hfund hcover
  change (Set.InjOn mapped (incidences : Set _))
  apply (Finset.card_image_iff).mp
  rw [himage, hcard]

private theorem decode (P : Fin 3 -> Bool -> ProtoTile) (O : ProtoTile) (u : GaussianInt) (v :
    GaussianInt) : ∀ (o : PeriodicSubtileIndex) (x : GaussianInt),
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells →
      ∃ z : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ (base P O) j}),
        z ∈ (incidences P O) ∧ z.1 = o.label ∧ x = z.2 + (o.first : GaussianInt) * u +
          (o.second : GaussianInt) * v := by
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  change (∀ (o : PeriodicSubtileIndex) (x : GaussianInt),
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells →
      ∃ z : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}),
        z ∈ incidences ∧ z.1 = o.label ∧ x = z.2 + (o.first : GaussianInt) * u +
          (o.second : GaussianInt) * v)
  intro o x hx
  cases o with
  | mk label first second =>
    cases label with
    | A =>
      change x ∈ (TileCellComplement (P 0 true) O).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.A, ⟨y, by simpa [base, TileCellComplement] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm
    | B =>
      change x ∈ (P 0 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.B, ⟨y, by simpa [base] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm
    | C =>
      change x ∈ (P 1 true).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.C, ⟨y, by simpa [base] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm
    | D =>
      change x ∈ (P 1 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.D, ⟨y, by simpa [base] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm
    | E =>
      change x ∈ (P 2 true).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.E, ⟨y, by simpa [base] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm
    | F =>
      change x ∈ (P 2 false).cells.image
        (GaussianTranslation ((first : GaussianInt) * u + (second : GaussianInt) * v)) at hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      refine ⟨⟨.F, ⟨y, by simpa [base] using hy⟩⟩, ?_, rfl, ?_⟩
      · simp [incidences]
      · dsimp [GaussianTranslation] at heq
        simpa [add_assoc] using heq.symm

end ModifiedCellPartitionConstruction

theorem BandModifiedCellPartition (P : Fin 3 -> Bool -> ProtoTile)
    (O : ProtoTile) (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (R : Finset GaussianInt)
    (hu : u ∈ L) (hv : v ∈ L)
    (hfund : LatticeFundamentalSet L R)
    (hcoords : ∀ w : L, ∃! mn : Int × Int,
      ((mn.1 : GaussianInt) * u + (mn.2 : GaussianInt) * v) =
        (w : GaussianInt))
    (hcover : forall x : LatticeCell, exists o : PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells)
    (harea : TileArea (TileCellComplement (P 0 true) O) +
        TileArea (P 0 false) + TileArea (P 1 true) +
        TileArea (P 1 false) + TileArea (P 2 true) +
        TileArea (P 2 false) = R.card) :
    ∀ x : LatticeCell, ∃! o : PeriodicSubtileIndex,
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells := by
-- BODY
  classical
  let base : SixSubtileLabel → Finset GaussianInt := fun j =>
    match j with
    | .A => (P 0 true).cells \ O.cells
    | .B => (P 0 false).cells
    | .C => (P 1 true).cells
    | .D => (P 1 false).cells
    | .E => (P 2 true).cells
    | .F => (P 2 false).cells
  let incidences : Finset (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :=
    Finset.sigma ({.A, .B, .C, .D, .E, .F} : Finset SixSubtileLabel)
      (fun j => (base j).attach)
  let representative : GaussianInt → GaussianInt := fun y =>
    Classical.choose (hfund y)
  have representative_spec (y : GaussianInt) :
      representative y ∈ R ∧ y - representative y ∈ L :=
          ModifiedCellPartitionConstruction.representative_spec L R hfund y
  have map_mem (z : Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) :
      representative z.2 ∈ R := ModifiedCellPartitionConstruction.map_mem P O L R hfund z
  let mapped : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}) → GaussianInt :=
    fun z => representative z.2
  have hsurj : Set.SurjOn mapped (incidences : Set _) (R : Set GaussianInt) :=
      ModifiedCellPartitionConstruction.hsurj P O u v L R hu hv hfund hcover
  have hcard : incidences.card = R.card := ModifiedCellPartitionConstruction.hcard P O R harea
  have himage : incidences.image mapped = R := ModifiedCellPartitionConstruction.himage P O u v L
      R hu hv hfund hcover
  have hinj : Set.InjOn mapped (incidences : Set _) := ModifiedCellPartitionConstruction.hinj P O
      u v L R hu hv hfund hcover harea
  have decode : ∀ (o : PeriodicSubtileIndex) (x : GaussianInt),
      x ∈ (ModifiedSubtileOccurrenceInterpretation P O u v o).cells →
      ∃ z : (Σ j : SixSubtileLabel, {y : GaussianInt // y ∈ base j}),
        z ∈ incidences ∧ z.1 = o.label ∧ x = z.2 + (o.first : GaussianInt) * u +
          (o.second : GaussianInt) * v := ModifiedCellPartitionConstruction.decode P O u v
  intro x
  obtain ⟨o, ho⟩ := hcover x
  refine ⟨o, ho, ?_⟩
  intro q hq
  obtain ⟨z, hz, hzl, heqz⟩ := decode o x ho
  obtain ⟨w, hw, hwl, heqw⟩ := decode q x hq
  have hshift : ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v) -
      ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v) ∈ L := by
    have ho1 : (o.first : GaussianInt) * u ∈ L := by
      rw [← zsmul_eq_mul]
      exact L.zsmul_mem hu o.first
    have ho2 : (o.second : GaussianInt) * v ∈ L := by
      rw [← zsmul_eq_mul]
      exact L.zsmul_mem hv o.second
    have hq1 : (q.first : GaussianInt) * u ∈ L := by
      rw [← zsmul_eq_mul]
      exact L.zsmul_mem hu q.first
    have hq2 : (q.second : GaussianInt) * v ∈ L := by
      rw [← zsmul_eq_mul]
      exact L.zsmul_mem hv q.second
    exact L.sub_mem (L.add_mem ho1 ho2) (L.add_mem hq1 hq2)
  have hycoset : (z.2 : GaussianInt) - (w.2 : GaussianInt) ∈ L := by
    have he : (z.2 : GaussianInt) +
        ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v) =
        (w.2 : GaussianInt) +
          ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v) :=
      by simpa [add_assoc] using heqz.symm.trans heqw
    have he' : (z.2 : GaussianInt) - (w.2 : GaussianInt) = -
        (((o.first : GaussianInt) * u + (o.second : GaussianInt) * v) -
          ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v)) := by
      have he2 : ((z.2 : GaussianInt) +
          ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)) -
          ((w.2 : GaussianInt) +
            ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v)) = 0 := by
        rw [he]
        abel
      calc
        (z.2 : GaussianInt) - (w.2 : GaussianInt) =
            ((z.2 : GaussianInt) + ((o.first : GaussianInt) * u + (o.second : GaussianInt) * v)) -
              ((w.2 : GaussianInt) + ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v)) -
                (((o.first : GaussianInt) * u + (o.second : GaussianInt) * v) -
                  ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v)) := by abel
        _ = -(((o.first : GaussianInt) * u + (o.second : GaussianInt) * v) -
          ((q.first : GaussianInt) * u + (q.second : GaussianInt) * v)) := by rw [he2]; abel
    rw [he']
    exact L.neg_mem hshift
  have hrep : mapped z = mapped w := by
    dsimp [mapped]
    apply (hfund z.2).unique
    · exact ⟨(representative_spec z.2).1, (representative_spec z.2).2⟩
    · have hwmem := (representative_spec w.2).2
      exact ⟨(representative_spec w.2).1, by
        have := L.add_mem hycoset hwmem
        convert this using 1; abel⟩
  have hzw : z = w := hinj hz hw hrep
  cases hzw
  have hl : o.label = q.label := hzl.symm.trans hwl
  cases o with
  | mk ol ofirst osecond =>
    cases q with
    | mk ql qfirst qsecond =>
      cases hl
      have hcoord : (ofirst, osecond) = (qfirst, qsecond) := by
        apply (hcoords ⟨x - (z.2 : GaussianInt), by
          have hs : (ofirst : GaussianInt) * u + (osecond : GaussianInt) * v ∈ L := by
            have h1 : (ofirst : GaussianInt) * u ∈ L := by
              rw [← zsmul_eq_mul]
              exact L.zsmul_mem hu ofirst
            have h2 : (osecond : GaussianInt) * v ∈ L := by
              rw [← zsmul_eq_mul]
              exact L.zsmul_mem hv osecond
            exact L.add_mem h1 h2
          have hxz : x - (z.2 : GaussianInt) =
              (ofirst : GaussianInt) * u + (osecond : GaussianInt) * v := by
            rw [heqz]
            abel
          rw [hxz]
          exact hs⟩).unique
        · have hxz : x - (z.2 : GaussianInt) =
              (ofirst : GaussianInt) * u + (osecond : GaussianInt) * v := by
            rw [heqz]
            abel
          exact hxz.symm
        · have hxq : x - (z.2 : GaussianInt) =
              (qfirst : GaussianInt) * u + (qsecond : GaussianInt) * v := by
            rw [heqw]
            abel
          exact hxq.symm
      cases hcoord
      rfl

end ApollonianSuperharmonic

end
