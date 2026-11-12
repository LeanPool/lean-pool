/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Algebra.Order.Interval.Set.Instances

public import LeanPool.ApollonianSuperharmonic.P3776T1SectorMaps
public import LeanPool.ApollonianSuperharmonic.P3832T1CollapsedConeDescent
public import LeanPool.ApollonianSuperharmonic.P3832T1ChamberOverlap
public import LeanPool.ApollonianSuperharmonic.P3832T1FiniteClosedCoverPasting
public import Mathlib.Algebra.BigOperators.Fin

-- [TABLET NODE: P3776T1SectorMapsExist]

/-!
# P3776T1SectorMapsExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SectorMapsProof

private theorem sectorCollapse_surjective :
    let sectorCollapse := P3832T1ConeCollapse
    Function.Surjective sectorCollapse := by
  classical
  intro sectorCollapse
  exact (P3832T1CollapsedConeDescent (Y := ℝ × ℝ)).1

private theorem sectorConeDescent :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (g : C(SectorInterval × SectorInterval, ℝ × ℝ)), ∀ (c : ℝ × ℝ), (∀ t : SectorInterval, g
        (⟨0, by norm_num [SectorInterval]⟩, t) = c) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z, G
        (sectorCollapse z) = g z) := by
  classical
  intro SectorInterval SectorCone sectorCollapse g c hzero
  exact (P3832T1CollapsedConeDescent (Y := ℝ × ℝ)).2 g c hzero

private theorem sectorSupportedHalfCone :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    (∀ (g : C(SectorInterval × SectorInterval, ℝ × ℝ)), ∀ (c : ℝ × ℝ), (∀ t : SectorInterval, g
        (⟨0, by norm_num [SectorInterval]⟩, t) = c) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z, G
        (sectorCollapse z) = g z)) → (∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval,
        G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))) := by
  classical
  intro SectorInterval SectorCone sectorCollapse sectorConeDescent ι P H E f a b hab ha hb
  have hp := E.half_spec f a b hab ha hb
  have hc : Continuous (fun z : SectorInterval × SectorInterval =>
      H.homotopy a z.1 (E.half f a b z.2)) :=
    (H.continuous a).comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (hp.1.comp continuous_snd))
      (fun z => ⟨z.1.2, (hp.2.2.2.1 z.2).1⟩)
  let g : C(SectorInterval × SectorInterval, ℝ × ℝ) :=
    ⟨fun z => H.homotopy a z.1 (E.half f a b z.2), hc⟩
  exact sectorConeDescent g (H.center a)
    (fun t => H.zero a _ (hp.2.2.2.1 t).1)

private theorem sectorOrderExists :
    ∀ x : Fin 3 → ℝ,
      ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x k ≤ x j ∧ x j ≤ x i := by
  classical
  intro x
  by_cases h01 : x 0 ≤ x 1
  · by_cases h12 : x 1 ≤ x 2
    · exact ⟨2,1,0,by decide,by decide,by decide,by linarith,by linarith⟩
    · by_cases h02 : x 0 ≤ x 2
      · exact ⟨1,2,0,by decide,by decide,by decide,by linarith,by linarith⟩
      · exact ⟨1,0,2,by decide,by decide,by decide,by linarith,by linarith⟩
  · by_cases h02 : x 0 ≤ x 2
    · exact ⟨2,0,1,by decide,by decide,by decide,by linarith,by linarith⟩
    · by_cases h12 : x 1 ≤ x 2
      · exact ⟨0,2,1,by decide,by decide,by decide,by linarith,by linarith⟩
      · exact ⟨0,1,2,by decide,by decide,by decide,by linarith,by linarith⟩

private theorem sectorChamber_closed :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    ∀ i j k : Fin 3, IsClosed (sectorChamber i j k) := by
  classical
  intro SectorSimplex sectorChamber i j k
  apply IsClosed.inter
  · exact isClosed_le ((continuous_apply j).comp continuous_subtype_val)
      ((continuous_apply i).comp continuous_subtype_val)
  · exact isClosed_le ((continuous_apply k).comp continuous_subtype_val)
      ((continuous_apply j).comp continuous_subtype_val)

private theorem sectorOrder_cover :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ x : Fin 3 → ℝ, ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x k ≤ x j ∧ x j ≤ x i) → (∀ s :
        SectorSimplex, ∃ o : SectorOrder, s ∈ sectorCh o) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderExists s
  obtain ⟨i,j,k,hij,hik,hjk,hkj,hji⟩ := sectorOrderExists s.1
  exact ⟨⟨(i,j,k),hij,hik,hjk⟩,hji,hkj⟩

private theorem sectorIndexCover :
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    ∀ (o : SectorOrder), ∀ (n : Fin 3), n = sectorI o ∨ n = sectorJ o ∨ n = sectorK o := by
  classical
  intro SectorOrder sectorI sectorJ sectorK o n
  let t : Finset (Fin 3) := {sectorI o, sectorJ o, sectorK o}
  have hcard : t.card = Fintype.card (Fin 3) := by
    simp [t, sectorI, sectorJ, sectorK, o.2.1, o.2.2.1, o.2.2.2]
  have huniv := Finset.eq_univ_of_card t hcard
  have hn : n ∈ t := by rw [huniv]; simp
  simpa [t] using hn

private theorem sectorOrderedSum :
    let SectorSimplex := StandardSimplex (Fin 3)
    ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j
        ≠ k) → (s.1 i + s.1 j + s.1 k = 1))) := by
  classical
  intro SectorSimplex s i j k hij hik hjk
  have hs : ∑ n : Fin 3, s.1 n = 1 := by
    simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2 |>.2
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals
    first
    | contradiction
    | simpa [Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm] using hs

private theorem sectorParam_values :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), (sectorParam o s hs).1.1
        = 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) ∧
      (sectorParam o s hs).1.2 = 2*(s.1 (sectorJ o)-s.1 (sectorK o)) := by
  classical
  intro SectorInterval SectorCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam o s hs
  constructor <;> rfl

private theorem sectorParam_continuous :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (o : SectorOrder), Continuous (fun s : {s : SectorSimplex // s ∈ sectorCh o} => sectorParam
        o s.1 s.2) := by
  classical
  intro SectorInterval SectorCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam o
  let A := {s : SectorSimplex // s ∈ sectorCh o}
  let y : A → ℝ := fun s => s.1.1 (sectorJ o)
  let z : A → ℝ := fun s => s.1.1 (sectorK o)
  have hy : Continuous y := (continuous_apply _).comp
    (continuous_subtype_val.comp continuous_subtype_val)
  have hz : Continuous z := (continuous_apply _).comp
    (continuous_subtype_val.comp continuous_subtype_val)
  have hr : Continuous (fun s : A => 2 * (y s-z s)+3*z s) := by fun_prop
  have hb : Continuous (fun s : A => 2*(y s-z s)) := by fun_prop
  change Continuous (fun s : A => sectorParam o s.1 s.2)
  unfold sectorParam
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact hr
  · apply Continuous.subtype_mk
    exact hb

private theorem sectorOrdersTie :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → (o = o' ∨ s.1 (sectorI o)=s.1 (sectorJ o) ∨ s.1 (sectorJ o)=s.1 (sectorK
        o))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho'
  exact (P3832T1ChamberOverlap s.1 o o' ho ho').1

private theorem sectorOrderedBetaTop :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorI o)=s.1 (sectorJ o)) → (2*(s.1 (sectorJ o)-s.1 (sectorK o))=
        2*(s.1 (sectorJ o')-s.1 (sectorK o'))))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.1 ht).2.1

private theorem sectorOrderedRBottom :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorJ o)=s.1 (sectorK o)) → (2*(s.1 (sectorJ o)-s.1 (sectorK
        o))+3*s.1 (sectorK o)=
        2*(s.1 (sectorJ o')-s.1 (sectorK o'))+3*s.1 (sectorK o')))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.2 ht).2.1

private theorem sectorTopTieParams :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    (∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), (sectorParam o s
        hs).1.1 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) ∧ (sectorParam o s
        hs).1.2 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))) → ((∀ (s : SectorSimplex), ∀ (o :
        SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → ((s.1
        (sectorI o)=s.1 (sectorJ o)) → (2*(s.1 (sectorJ o)-s.1 (sectorK o))= 2*(s.1 (sectorJ
        o')-s.1 (sectorK o')))))) → (∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' :
        SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh o'), (s.1 (sectorI o)=s.1
        (sectorJ o)) → ((sectorParam o s ho).1.1=1 ∧
        (sectorParam o s ho).1.2=(sectorParam o' s ho').1.2))) := by
  classical
  intro SectorInterval SectorCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam sectorParam_values sectorOrderedBetaTop s o o' ho ho' ht
  rcases sectorParam_values o s ho with ⟨hr,hb⟩
  rcases sectorParam_values o' s ho' with ⟨_,hb'⟩
  constructor
  · apply Subtype.ext
    rw [hr]
    have hsum := sectorOrderedSum s (sectorI o) (sectorJ o) (sectorK o)
      o.2.1 o.2.2.1 o.2.2.2
    rw [ht] at hsum
    calc
      2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o)=
        s.1 (sectorJ o)+s.1 (sectorJ o)+s.1 (sectorK o) := by ring
      _=1 := hsum
  · apply Subtype.ext
    rw [hb,hb']
    exact sectorOrderedBetaTop s o o' ho ho' ht

private theorem sectorBottomTieParams :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    (∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorJ o)=s.1 (sectorK o)) → (2*(s.1 (sectorJ o)-s.1 (sectorK
        o))+3*s.1 (sectorK o)= 2*(s.1 (sectorJ o')-s.1 (sectorK o'))+3*s.1 (sectorK o'))))) → (∀
        (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o),
        ∀ (ho' : s ∈ sectorCh o'), (s.1 (sectorJ o)=s.1 (sectorK o)) → ((sectorParam o s ho).1.2=0 ∧
        (sectorParam o s ho).1.1=(sectorParam o' s ho').1.1)) := by
  classical
  intro SectorInterval SectorCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam sectorOrderedRBottom s o o' ho ho' ht
  constructor
  · apply Subtype.ext
    change 2 * (s.1 (sectorJ o) - s.1 (sectorK o)) = 0
    rw [ht, sub_self, mul_zero]
  · apply Subtype.ext
    change 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) =
      2*(s.1 (sectorJ o')-s.1 (sectorK o'))+3*s.1 (sectorK o')
    exact sectorOrderedRBottom s o o' ho ho' ht

private theorem sectorBottomSameTop :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorJ o)=s.1 (sectorK o)) → (sectorI o=sectorI o' ∨
        (s.1 (sectorI o)=s.1 (sectorJ o) ∧ s.1 (sectorJ o)=s.1 (sectorK o))))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.2 ht).2.2

private theorem sectorTopTieOther :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorI o)=s.1 (sectorJ o)) → (s.1 (sectorI o')=s.1 (sectorJ o'))))
        := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.1 ht).1

private theorem sectorBottomTieOther :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorJ o)=s.1 (sectorK o)) → (s.1 (sectorJ o')=s.1 (sectorK o'))))
        := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.2 ht).1

private theorem sectorTopPairClassify :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈
        sectorCh o') → ((s.1 (sectorI o)=s.1 (sectorJ o)) → ((s.1 (sectorI o')=s.1 (sectorJ o'))
        → ((sectorI o=sectorI o' ∧ sectorJ o=sectorJ o' ∧ sectorK o=sectorK o') ∨
      (sectorI o=sectorJ o' ∧ sectorJ o=sectorI o' ∧ sectorK o=sectorK o') ∨
      (s.1 (sectorI o)=s.1 (sectorJ o) ∧ s.1 (sectorJ o)=s.1 (sectorK o)))))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh s o o' ho ho' ht
      ht'
  exact ((P3832T1ChamberOverlap s.1 o o' ho ho').2.1 ht).2.2

private theorem sectorChosenCone_spec :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) =
        H.homotopy (P.plane.faceVertex f (sectorI o)) z.1
          (E.half f (P.plane.faceVertex f (sectorI o))
            (P.plane.faceVertex f (sectorJ o)) z.2) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorOrder
      sectorI sectorJ sectorChosenCone f o z
  exact Classical.choose_spec (sectorSupportedHalfCone P H E f
    (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
    (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
    ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩) z

private theorem sectorChosenPiece_top :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)), (∀ (s : SectorSimplex),
        ∀ (o : SectorOrder), ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh
        o'), (s.1 (sectorI o)=s.1 (sectorJ o)) → ((sectorParam o s ho).1.1=1 ∧ (sectorParam o s
        ho).1.2=(sectorParam o' s ho').1.2)) → (
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        (s.1 (sectorI o)=s.1 (sectorJ o)) → (sectorChosenPiece f o ⟨s,hs⟩ =
        E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
          (sectorParam o s hs).1.2))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum sectorParam
      sectorParam_continuous sectorTopTieParams sectorPiece sectorChosenCone
      sectorChosenCone_spec sectorChosenPiece f o s hs ht
  let z := sectorParam o s hs
  have hr : (z.1.1 : ℝ) = 1 := by
    simpa [z] using (sectorTopTieParams s o o hs hs ht).1
  let t : SectorInterval := z.1.2
  have hz : z = sectorCollapse (⟨1,by norm_num [SectorInterval]⟩,t) := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; exact hr
    · apply Subtype.ext
      simp [sectorCollapse, P3832T1ConeCollapse,t]
  change sectorChosenCone f o z = _
  rw [hz,sectorChosenCone_spec]
  have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
    (P.plane.faceVertex f (sectorJ o))
    (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
    ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
  have hin := (hp.2.2.2.1 t).1
  simpa [t] using H.one (P.plane.faceVertex f (sectorI o))
    (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) t) hin

private theorem sectorChosenPiece_bottom :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)), (∀ (s : SectorSimplex),
        ∀ (o : SectorOrder), ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh
        o'), (s.1 (sectorJ o)=s.1 (sectorK o)) → ((sectorParam o s ho).1.2=0 ∧ (sectorParam o s
        ho).1.1=(sectorParam o' s ho').1.1)) → (
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        (s.1 (sectorJ o)=s.1 (sectorK o)) → (sectorChosenPiece f o ⟨s,hs⟩ =
        H.homotopy (P.plane.faceVertex f (sectorI o))
          (sectorParam o s hs).1.1 (GaussianRealPoint (P.rho f))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum sectorParam
      sectorParam_continuous sectorBottomTieParams sectorPiece sectorChosenCone
      sectorChosenCone_spec sectorChosenPiece f o s hs ht
  let z := sectorParam o s hs
  have hb : (z.1.2 : ℝ) = 0 := by
    simpa [z] using (sectorBottomTieParams s o o hs hs ht).1
  let t0 : SectorInterval := ⟨0,by norm_num [SectorInterval]⟩
  have hz : z = sectorCollapse (z.1.1,t0) := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [sectorCollapse, P3832T1ConeCollapse,hb,t0]
  change sectorChosenCone f o z = _
  rw [hz,sectorChosenCone_spec]
  have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
    (P.plane.faceVertex f (sectorJ o))
    (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
    ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
  rw [hp.2.1]

private theorem sectorParam_beta_zero :
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    (∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), (sectorParam o s
        hs).1.1 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) ∧ (sectorParam o s
        hs).1.2 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))) → (∀ (o : SectorOrder), ∀ (s :
        SectorSimplex), ∀ (hs : s ∈ sectorCh o), (s.1 (sectorJ o)=s.1 (sectorK o)) →
        ((sectorParam o s hs).1.2=⟨0,by norm_num [SectorInterval]⟩)) := by
  classical
  intro SectorInterval SectorCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam sectorParam_values o s hs ht
  apply Subtype.ext
  rcases sectorParam_values o s hs with ⟨_,hb⟩
  rw [hb,ht]
  norm_num

private theorem sectorChosenPieces_agree :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)), (∀ (s : SectorSimplex),
        ∀ (o : SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → (o =
        o' ∨ s.1 (sectorI o)=s.1 (sectorJ o) ∨ s.1 (sectorJ o)=s.1 (sectorK o)))) → ((∀ (s :
        SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀
        (ho' : s ∈ sectorCh o'), (s.1 (sectorI o)=s.1 (sectorJ o)) → ((sectorParam o s ho).1.1=1
        ∧ (sectorParam o s ho).1.2=(sectorParam o' s ho').1.2)) → ((∀ (s : SectorSimplex), ∀ (o :
        SectorOrder), ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh o'),
        (s.1 (sectorJ o)=s.1 (sectorK o)) → ((sectorParam o s ho).1.2=0 ∧ (sectorParam o s
        ho).1.1=(sectorParam o' s ho').1.1)) → ((∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀
        (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → ((s.1 (sectorJ o)=s.1
        (sectorK o)) → (sectorI o=sectorI o' ∨ (s.1 (sectorI o)=s.1 (sectorJ o) ∧ s.1 (sectorJ
        o)=s.1 (sectorK o)))))) → ((∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' :
        SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → ((s.1 (sectorI o)=s.1 (sectorJ o))
        → (s.1 (sectorI o')=s.1 (sectorJ o'))))) → ((∀ (s : SectorSimplex), ∀ (o : SectorOrder),
        ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → ((s.1 (sectorJ o)=s.1
        (sectorK o)) → (s.1 (sectorJ o')=s.1 (sectorK o'))))) → ((∀ (s : SectorSimplex), ∀ (o :
        SectorOrder), ∀ (o' : SectorOrder), (s ∈ sectorCh o) → ((s ∈ sectorCh o') → ((s.1
        (sectorI o)=s.1 (sectorJ o)) → ((s.1 (sectorI o')=s.1 (sectorJ o')) → ((sectorI o=sectorI
        o' ∧ sectorJ o=sectorJ o' ∧ sectorK o=sectorK o') ∨ (sectorI o=sectorJ o' ∧ sectorJ
        o=sectorI o' ∧ sectorK o=sectorK o') ∨ (s.1 (sectorI o)=s.1 (sectorJ o) ∧ s.1 (sectorJ
        o)=s.1 (sectorK o))))))) → (
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        (s.1 (sectorI o)=s.1 (sectorJ o)) → (sectorChosenPiece f o ⟨s,hs⟩ = E.half f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) (sectorParam o s
        hs).1.2)) → ((∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s
        ∈ sectorCh o), (s.1 (sectorJ o)=s.1 (sectorK o)) → (sectorChosenPiece f o ⟨s,hs⟩ =
        H.homotopy (P.plane.faceVertex f (sectorI o)) (sectorParam o s hs).1.1 (GaussianRealPoint
        (P.rho f)))) → ((∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        (s.1 (sectorJ o)=s.1 (sectorK o)) → ((sectorParam o s hs).1.2=⟨0,by norm_num
        [SectorInterval]⟩)) → (∀ (f : P.plane.Face), ∀ (s : SectorSimplex), ∀ (o : SectorOrder),
        ∀ (o' : SectorOrder), ∀ (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh o'),
        sectorChosenPiece f o ⟨s,ho⟩=sectorChosenPiece f o' ⟨s,ho'⟩)))))))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum sectorParam
      sectorParam_continuous sectorOrdersTie sectorTopTieParams sectorBottomTieParams
      sectorBottomSameTop sectorTopTieOther sectorBottomTieOther sectorTopPairClassify
      sectorPiece sectorChosenCone sectorChosenPiece sectorChosenPiece_top
      sectorChosenPiece_bottom sectorParam_beta_zero f s o o' ho ho'
  rcases sectorOrdersTie s o o' ho ho' with heq | htop | hbottom
  · subst o'; rfl
  · have htop' := sectorTopTieOther s o o' ho ho' htop
    have hclass := sectorTopPairClassify s o o' ho ho' htop htop'
    rw [sectorChosenPiece_top f o s ho htop,
      sectorChosenPiece_top f o' s ho' htop']
    rcases hclass with hpairs | hpairs | hall
    · rcases hpairs with ⟨hi,hj,hk⟩
      rw [← hi,← hj,← (sectorTopTieParams s o o' ho ho' htop).2]
    · rcases hpairs with ⟨hi,hj,hk⟩
      rw [← hi,← hj,← (sectorTopTieParams s o o' ho ho' htop).2]
      have hsym := E.half_spec f (P.plane.faceVertex f (sectorI o))
        (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
      simpa using hsym.2.2.2.2.1 ((sectorParam o s ho).1.2)
    · have hzero := sectorParam_beta_zero o s ho hall.2
      have hbottom' := sectorBottomTieOther s o o' ho ho' hall.2
      have hzero' := sectorParam_beta_zero o' s ho' hbottom'
      rw [hzero,hzero']
      have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
        (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
      have hp' := E.half_spec f (P.plane.faceVertex f (sectorI o'))
        (P.plane.faceVertex f (sectorJ o'))
        (P.plane.face_edges f (sectorI o') (sectorJ o') o'.2.1)
        ⟨sectorI o',rfl⟩ ⟨sectorJ o',rfl⟩
      exact hp.2.1.trans hp'.2.1.symm
  · have hbottom' := sectorBottomTieOther s o o' ho ho' hbottom
    have hclass := sectorBottomSameTop s o o' ho ho' hbottom
    rw [sectorChosenPiece_bottom f o s ho hbottom,
      sectorChosenPiece_bottom f o' s ho' hbottom']
    rcases hclass with hI | hall
    · rw [hI,(sectorBottomTieParams s o o' ho ho' hbottom).2]
    · have htop : s.1 (sectorI o)=s.1 (sectorJ o) := hall.1
      have htop' := sectorTopTieOther s o o' ho ho' htop
      have hr := (sectorTopTieParams s o o ho ho htop).1
      have hr' := (sectorTopTieParams s o' o' ho' ho' htop').1
      rw [hr,hr']
      have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
        (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
      have hp' := E.half_spec f (P.plane.faceVertex f (sectorI o'))
        (P.plane.faceVertex f (sectorJ o'))
        (P.plane.face_edges f (sectorI o') (sectorJ o') o'.2.1)
        ⟨sectorI o',rfl⟩ ⟨sectorJ o',rfl⟩
      let t0 : SectorInterval := ⟨0,by norm_num [SectorInterval]⟩
      have hm := (hp.2.2.2.1 t0).1
      have hm' := (hp'.2.2.2.1 t0).1
      have hmL : E.half f (P.plane.faceVertex f (sectorI o))
          (P.plane.faceVertex f (sectorJ o)) ⟨0,by norm_num [SectorInterval]⟩ ∈
          TileRealization (P.tile (P.plane.faceVertex f (sectorI o))) := by
        simpa [t0] using hm
      have hmL' : E.half f (P.plane.faceVertex f (sectorI o'))
          (P.plane.faceVertex f (sectorJ o')) ⟨0,by norm_num [SectorInterval]⟩ ∈
          TileRealization (P.tile (P.plane.faceVertex f (sectorI o'))) := by
        simpa [t0] using hm'
      have hm0 : GaussianRealPoint (P.rho f) ∈
          TileRealization (P.tile (P.plane.faceVertex f (sectorI o))) := by
        rw [hp.2.1] at hmL; exact hmL
      have hm0' : GaussianRealPoint (P.rho f) ∈
          TileRealization (P.tile (P.plane.faceVertex f (sectorI o'))) := by
        rw [hp'.2.1] at hmL'; exact hmL'
      have hone := H.one (P.plane.faceVertex f (sectorI o))
        (GaussianRealPoint (P.rho f)) hm0
      have hone' := H.one (P.plane.faceVertex f (sectorI o'))
        (GaussianRealPoint (P.rho f)) hm0'
      calc
        H.homotopy (P.plane.faceVertex f (sectorI o)) 1 _ =
            GaussianRealPoint (P.rho f) := by simpa using hone
        _ = H.homotopy (P.plane.faceVertex f (sectorI o')) 1 _ := by
          simpa using hone'.symm

private theorem sectorGlobalMap :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ s :
        SectorSimplex, ∃ o : SectorOrder, s ∈ sectorCh o) → (∀ (sectorOrderedSum : ∀ (s :
        SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j ≠
        k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    (∀ (f : P.plane.Face), ∀ (s : SectorSimplex), ∀ (o : SectorOrder), ∀ (o' : SectorOrder), ∀
        (ho : s ∈ sectorCh o), ∀ (ho' : s ∈ sectorCh o'), sectorChosenPiece f o
        ⟨s,ho⟩=sectorChosenPiece f o' ⟨s,ho'⟩) → (∀ (f : P.plane.Face), ∃ F :
        C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈ sectorCh o),
        F s=sectorChosenPiece f o ⟨s,hs⟩)) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrder_cover
      sectorOrderedSum sectorParam sectorParam_continuous sectorPiece sectorChosenCone
      sectorChosenPiece sectorChosenPieces_agree f
  let sectorChamber_closed : ∀ i j k : Fin 3, IsClosed (sectorChamber i j k) :=
    SectorMapsProof.sectorChamber_closed
  classical
  let S : SectorOrder → Set SectorSimplex := sectorCh
  let φ : ∀ o, C(S o,ℝ×ℝ) := sectorChosenPiece f
  have hclosed : ∀ o, IsClosed (S o) := by
    intro o
    exact sectorChamber_closed _ _ _
  have hcover : ∀ s : SectorSimplex, ∃ o, s ∈ S o := by
    intro s
    exact sectorOrder_cover s
  have hagree : ∀ o o' s (ho : s ∈ S o) (ho' : s ∈ S o'),
      φ o ⟨s,ho⟩=φ o' ⟨s,ho'⟩ := by
    intro o o' s ho ho'
    exact sectorChosenPieces_agree f s o o' ho ho'
  obtain ⟨F,hF⟩ := P3832T1FiniteClosedCoverPasting (S:=S) hclosed hcover φ hagree
  exact ⟨F,fun o s hs => hF o s hs⟩

private theorem sectorChosenPiece_support :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    (Function.Surjective sectorCollapse) → (∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P :
        PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀
        (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i,
        P.plane.faceVertex f i = a) → ((∃ i, P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ
        × ℝ), ∀ z : SectorInterval × SectorInterval, G (sectorCollapse z) = H.homotopy a z.1
        (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorChosenPiece f o ⟨s,hs⟩ ∈
        TileRealization (P.tile (P.plane.faceVertex f (sectorI o))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorCollapse_surjective
      sectorSupportedHalfCone SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK
      sectorCh sectorOrderedSum sectorParam sectorParam_continuous sectorPiece sectorChosenCone
      sectorChosenCone_spec sectorChosenPiece f o s hs
  let z := sectorParam o s hs
  let w := Classical.choose (sectorCollapse_surjective z)
  have hw : sectorCollapse w = z := Classical.choose_spec (sectorCollapse_surjective z)
  have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
    (P.plane.faceVertex f (sectorJ o))
    (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
    ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
  have hmember := (hp.2.2.2.1 w.2).1
  have hval : sectorChosenPiece f o ⟨s,hs⟩ =
      H.homotopy (P.plane.faceVertex f (sectorI o)) w.1
        (E.half f (P.plane.faceVertex f (sectorI o))
          (P.plane.faceVertex f (sectorJ o)) w.2) := by
    change sectorChosenCone f o z = _
    rw [← hw]
    exact sectorChosenCone_spec f o w
  rw [hval]
  exact H.support (P.plane.faceVertex f (sectorI o)) w.1 w.1.2
    (E.half f (P.plane.faceVertex f (sectorI o))
      (P.plane.faceVertex f (sectorJ o)) w.2) hmember

private theorem sectorTopPositive :
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j
        ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))) → (∀ (s : SectorSimplex), ∀ (o : SectorOrder), (s ∈
        sectorCh o) → (0 < s.1 (sectorI o))) := by
  classical
  intro SectorSimplex sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum
      s o hs
  have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
    simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
  have hsum := sectorOrderedSum s (sectorI o) (sectorJ o) (sectorK o)
    o.2.1 o.2.2.1 o.2.2.2
  have hj : s.1 (sectorJ o) ≤ s.1 (sectorI o) := hs.1
  have hk : s.1 (sectorK o) ≤ s.1 (sectorJ o) := hs.2
  have hj0 := hc.1 (sectorJ o)
  have hk0 := hc.1 (sectorK o)
  linarith

private theorem sectorChosenCone_periodic :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    (Function.Surjective sectorCollapse) → (∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P :
        PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀
        (f : P.plane.Face), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i,
        P.plane.faceVertex f i = a) → ((∃ i, P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ
        × ℝ), ∀ z : SectorInterval × SectorInterval, G (sectorCollapse z) = H.homotopy a z.1
        (E.half f a b z.2))))),
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (∀ (u : P.lattice), ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorCone),
        sectorChosenCone (P.faceShift u f) o z =
        sectorChosenCone f o z + GaussianRealPoint u)) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorCollapse_surjective
      sectorSupportedHalfCone SectorOrder sectorI sectorJ sectorChosenCone sectorChosenCone_spec
      u f o z
  let w := Classical.choose (sectorCollapse_surjective z)
  have hw : sectorCollapse w = z := Classical.choose_spec (sectorCollapse_surjective z)
  let a := P.plane.faceVertex f (sectorI o)
  let b := P.plane.faceVertex f (sectorJ o)
  have hadj := P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1
  have hpath := (E.half_spec f a b hadj ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩).2.2.2.1 w.2
  have hshift := E.half_periodic u f a b hadj ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩ w.2
  have hvI := P.face_vertices_periodic u f (sectorI o)
  have hvJ := P.face_vertices_periodic u f (sectorJ o)
  calc
    sectorChosenCone (P.faceShift u f) o z =
        sectorChosenCone (P.faceShift u f) o (sectorCollapse w) := by rw [hw]
    _ = H.homotopy (P.plane.faceVertex (P.faceShift u f) (sectorI o)) w.1
          (E.half (P.faceShift u f) (P.plane.faceVertex (P.faceShift u f) (sectorI o))
            (P.plane.faceVertex (P.faceShift u f) (sectorJ o)) w.2) :=
        sectorChosenCone_spec (P.faceShift u f) o w
    _ = H.homotopy (P.shift u a) w.1
          (E.half (P.faceShift u f) (P.shift u a) (P.shift u b) w.2) := by rw [hvI,hvJ]
    _ = H.homotopy a w.1 (E.half f a b w.2) + GaussianRealPoint u := by
      rw [hshift]
      exact H.homotopy_periodic u a w.1 (E.half f a b w.2) w.1.2 hpath.1
    _ = sectorChosenCone f o (sectorCollapse w) + GaussianRealPoint u := by
      rw [sectorChosenCone_spec f o w]
    _ = sectorChosenCone f o z + GaussianRealPoint u := by rw [hw]

private theorem sectorGlobalChosen_spec :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (sectorGlobalMap : ∀ (f : P.plane.Face), ∃ F : C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈
        sectorCh o), F s=sectorChosenPiece f o ⟨s,hs⟩),
    let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
      Classical.choose (sectorGlobalMap f)
    ∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorGlobalChosen f s = sectorChosenPiece f o ⟨s,hs⟩ := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum sectorParam
      sectorParam_continuous sectorPiece sectorChosenCone sectorChosenPiece sectorGlobalMap
      sectorGlobalChosen f o s hs
  exact Classical.choose_spec (sectorGlobalMap f) o s hs

private theorem sectorGlobalChosen_periodic :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ s : SectorSimplex, ∃ o : SectorOrder, s ∈ sectorCh o) → (∀ (sectorOrderedSum : ∀ (s :
        SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j ≠
        k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (sectorGlobalMap : ∀ (f : P.plane.Face), ∃ F : C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈
        sectorCh o), F s=sectorChosenPiece f o ⟨s,hs⟩), (∀ (u : P.lattice), ∀ (f : P.plane.Face),
        ∀ (o : SectorOrder), ∀ (z : SectorCone), sectorChosenCone (P.faceShift u f) o z =
        sectorChosenCone f o z + GaussianRealPoint u) → (
    let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
      Classical.choose (sectorGlobalMap f)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorGlobalChosen f s = sectorChosenPiece f o ⟨s,hs⟩) → (∀ (u : P.lattice), ∀ (f :
        P.plane.Face), ∀ (s : SectorSimplex), sectorGlobalChosen (P.faceShift u f) s =
        sectorGlobalChosen f s + GaussianRealPoint u))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrder_cover
      sectorOrderedSum sectorParam sectorParam_continuous sectorPiece sectorChosenCone
      sectorChosenPiece sectorGlobalMap sectorChosenCone_periodic sectorGlobalChosen
      sectorGlobalChosen_spec u f s
  obtain ⟨o,ho⟩ := sectorOrder_cover s
  rw [sectorGlobalChosen_spec (P.faceShift u f) o s ho,
    sectorGlobalChosen_spec f o s ho]
  change sectorChosenCone (P.faceShift u f) o (sectorParam o s ho) =
    sectorChosenCone f o (sectorParam o s ho) + GaussianRealPoint u
  exact sectorChosenCone_periodic u f o (sectorParam o s ho)

private theorem sectorGlobalChosen_support :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ s : SectorSimplex, ∃ o : SectorOrder, s ∈ sectorCh o) → (∀ (sectorOrderedSum : ∀ (s :
        SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j ≠
        k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    ∀ (sectorParam_continuous : ∀ (o : SectorOrder), Continuous (fun s :
        {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (sectorGlobalMap : ∀ (f : P.plane.Face), ∃ F : C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈
        sectorCh o), F s=sectorChosenPiece f o ⟨s,hs⟩), (∀ (f : P.plane.Face), ∀ (o :
        SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), sectorChosenPiece f o
        ⟨s,hs⟩ ∈ TileRealization (P.tile (P.plane.faceVertex f (sectorI o)))) → ((∀ (s :
        SectorSimplex), ∀ (o : SectorOrder), (s ∈ sectorCh o) → (0 < s.1 (sectorI o))) → (
    let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
      Classical.choose (sectorGlobalMap f)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorGlobalChosen f s = sectorChosenPiece f o ⟨s,hs⟩) → (∀ (f : P.plane.Face), ∀ (s :
        SectorSimplex), ∃ i, 0 < s.1 i ∧ sectorGlobalChosen f s ∈
        TileRealization (P.tile (P.plane.faceVertex f i)))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrder_cover
      sectorOrderedSum sectorParam sectorParam_continuous sectorPiece sectorChosenCone
      sectorChosenPiece sectorGlobalMap sectorChosenPiece_support sectorTopPositive
      sectorGlobalChosen sectorGlobalChosen_spec f s
  obtain ⟨o,ho⟩ := sectorOrder_cover s
  refine ⟨sectorI o, sectorTopPositive s o ho, ?_⟩
  rw [sectorGlobalChosen_spec f o s ho]
  exact sectorChosenPiece_support f o s ho

private theorem sectorGlobalChosen_vertex :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    (∀ s : SectorSimplex, ∃ o : SectorOrder, s ∈ sectorCh o) → ((∀ (o : SectorOrder), ∀ (n : Fin
        3), n = sectorI o ∨ n = sectorJ o ∨ n = sectorK o) → (∀ (sectorOrderedSum : ∀ (s :
        SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i ≠ j) → ((i ≠ k) → ((j ≠
        k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    (∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), (sectorParam o s
        hs).1.1 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) ∧ (sectorParam o s
        hs).1.2 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))) → (∀ (sectorParam_continuous : ∀ (o :
        SectorOrder), Continuous (fun s : {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o
        s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (sectorGlobalMap : ∀ (f : P.plane.Face), ∃ F : C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈
        sectorCh o), F s=sectorChosenPiece f o ⟨s,hs⟩),
    let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
      Classical.choose (sectorGlobalMap f)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorGlobalChosen f s = sectorChosenPiece f o ⟨s,hs⟩) → (∀ (f : P.plane.Face), ∀ (i :
        Fin 3), ∀ (s : SectorSimplex), (∀ j, s.1 j = if j = i then 1 else 0) →
        (sectorGlobalChosen f s = H.center (P.plane.faceVertex f i))))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrder_cover
      sectorIndexCover sectorOrderedSum sectorParam sectorParam_values sectorParam_continuous
      sectorPiece sectorChosenCone sectorChosenCone_spec sectorChosenPiece sectorGlobalMap
      sectorGlobalChosen sectorGlobalChosen_spec f i s hcoord
  obtain ⟨o,ho⟩ := sectorOrder_cover s
  have hI : sectorI o = i := by
    rcases sectorIndexCover o i with h | h | h
    · exact h.symm
    · have hJ : s.1 (sectorJ o) = 1 := by rw [← h]; simp [hcoord]
      have hIzero : s.1 (sectorI o) = 0 := by
        have hneq : sectorI o ≠ i := fun e => o.2.1 (e.trans h)
        simpa [hneq] using hcoord (sectorI o)
      linarith [ho.1]
    · have hK : s.1 (sectorK o) = 1 := by rw [← h]; simp [hcoord]
      have hJzero : s.1 (sectorJ o) = 0 := by
        have hneq : sectorJ o ≠ i := fun e => o.2.2.2 (e.trans h)
        simpa [hneq] using hcoord (sectorJ o)
      have hIzero : s.1 (sectorI o) = 0 := by
        have hneq : sectorI o ≠ i := fun e => o.2.2.1 (e.trans h)
        simpa [hneq] using hcoord (sectorI o)
      linarith [ho.1, ho.2]
  have hJ : s.1 (sectorJ o) = 0 := by
    have hij : sectorJ o ≠ i := by rw [← hI]; exact o.2.1.symm
    simpa [hij] using hcoord (sectorJ o)
  have hK : s.1 (sectorK o) = 0 := by
    have hik : sectorK o ≠ i := by rw [← hI]; exact o.2.2.1.symm
    simpa [hik] using hcoord (sectorK o)
  have hr : (sectorParam o s ho).1.1 = ⟨0, by norm_num [SectorInterval]⟩ := by
    apply Subtype.ext
    rcases sectorParam_values o s ho with ⟨hr,_⟩
    rw [hr,hJ,hK]
    norm_num [SectorInterval]
  have hb : (sectorParam o s ho).1.2 = ⟨0, by norm_num [SectorInterval]⟩ := by
    apply Subtype.ext
    rcases sectorParam_values o s ho with ⟨_,hb⟩
    rw [hb,hJ,hK]
    norm_num
  let t0 : SectorInterval := ⟨0, by norm_num [SectorInterval]⟩
  have hparam : sectorParam o s ho = sectorCollapse (t0,t0) := by
    apply Subtype.ext
    apply Prod.ext
    · exact hr
    · apply Subtype.ext
      simp [sectorCollapse, P3832T1ConeCollapse, t0, hb]
  rw [sectorGlobalChosen_spec f o s ho]
  change sectorChosenCone f o (sectorParam o s ho) = _
  rw [hparam, sectorChosenCone_spec]
  have hp := E.half_spec f (P.plane.faceVertex f (sectorI o))
    (P.plane.faceVertex f (sectorJ o))
    (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
    ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩
  have hm := (hp.2.2.2.1 t0).1
  have hm0 : GaussianRealPoint (P.rho f) ∈
      TileRealization (P.tile (P.plane.faceVertex f (sectorI o))) := by
    have hml : E.half f (P.plane.faceVertex f (sectorI o))
        (P.plane.faceVertex f (sectorJ o)) ⟨0,by norm_num [t0]⟩ ∈
        TileRealization (P.tile (P.plane.faceVertex f (sectorI o))) := by simpa [t0] using hm
    rw [hp.2.1] at hml
    exact hml
  rw [hp.2.1]
  rw [hI]
  rw [hI] at hm0
  exact H.zero (P.plane.faceVertex f i) (GaussianRealPoint (P.rho f)) hm0

private theorem sectorGlobalChosen_edge :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (H : P3776T1TileContractions P), ∀ (E :
        P3776T1DualEdges P),
    let SectorInterval := Set.Icc (0 : ℝ) 1
    let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
    let sectorCollapse := P3832T1ConeCollapse
    ∀ (sectorSupportedHalfCone : ∀ {ι : Type}, ∀ (P : PeriodicTileCore ι), ∀ (H :
        P3776T1TileContractions P), ∀ (E : P3776T1DualEdges P), ∀ (f : P.plane.Face), ∀ (a :
        ι), ∀ (b : ι), (P.plane.adjacent a b) → ((∃ i, P.plane.faceVertex f i = a) → ((∃ i,
        P.plane.faceVertex f i = b) → (∃ G : C(SectorCone, ℝ × ℝ), ∀ z : SectorInterval ×
        SectorInterval, G (sectorCollapse z) = H.homotopy a z.1 (E.half f a b z.2))))),
    let SectorSimplex := StandardSimplex (Fin 3)
    let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
      {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
    let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
    let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
    let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
    let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
    let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
    ∀ (sectorOrderedSum : ∀ (s : SectorSimplex), ∀ (i : Fin 3), ∀ (j : Fin 3), ∀ (k : Fin 3), (i
        ≠ j) → ((i ≠ k) → ((j ≠ k) → (s.1 i + s.1 j + s.1 k = 1)))),
    let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
      let i := sectorI o
      let j := sectorJ o
      let k := sectorK o
      have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
        simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
      have hsum : s.1 i + s.1 j + s.1 k = 1 :=
        sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
      have hxy := hs.1
      have hyz := hs.2
      have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        linarith [hc.1 j, hc.1 k]
      have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
        linarith [hc.1 i, hsum]
      have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
      have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
        nlinarith [hc.1 k]
      (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
        ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
    (∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o), (sectorParam o s
        hs).1.1 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))+3*s.1 (sectorK o) ∧ (sectorParam o s
        hs).1.2 = 2*(s.1 (sectorJ o)-s.1 (sectorK o))) → (∀ (sectorParam_continuous : ∀ (o :
        SectorOrder), Continuous (fun s : {s : SectorSimplex // s ∈ sectorCh o} => sectorParam o
        s.1 s.2)),
    let sectorPiece (o : SectorOrder)
        (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      ⟨fun s => G (sectorParam o s.1 s.2),
        G.continuous.comp (sectorParam_continuous o)⟩
    let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
      Classical.choose (sectorSupportedHalfCone P H E f
        (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
        (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
        ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (z : SectorInterval × SectorInterval),
        sectorChosenCone f o (sectorCollapse z) = H.homotopy (P.plane.faceVertex f (sectorI o))
        z.1 (E.half f (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o)) z.2))
        → (
    let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
        C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
      sectorPiece o (sectorChosenCone f o)
    ∀ (sectorGlobalMap : ∀ (f : P.plane.Face), ∃ F : C(SectorSimplex,ℝ×ℝ), ∀ o s (hs : s ∈
        sectorCh o), F s=sectorChosenPiece f o ⟨s,hs⟩),
    let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
      Classical.choose (sectorGlobalMap f)
    (∀ (f : P.plane.Face), ∀ (o : SectorOrder), ∀ (s : SectorSimplex), ∀ (hs : s ∈ sectorCh o),
        sectorGlobalChosen f s = sectorChosenPiece f o ⟨s,hs⟩) → (∀ (f : P.plane.Face), ∀ (i :
        Fin 3), ∀ (j : Fin 3), (i ≠ j) → (∀ (r : SectorInterval), ∀ (s : SectorSimplex), (∀ k,
        s.1 k = if k = i then (r : ℝ) else if k = j then 1-r else 0) → (sectorGlobalChosen f s =
        if (r : ℝ) ≤ 1/2 then
          H.homotopy (P.plane.faceVertex f j) (2 * (r : ℝ))
            (E.port (P.plane.faceVertex f i) (P.plane.faceVertex f j))
        else
          H.homotopy (P.plane.faceVertex f i) (2 * (1 - (r : ℝ)))
            (E.port (P.plane.faceVertex f i) (P.plane.faceVertex f j))))))) := by
  classical
  intro ι P H E SectorInterval SectorCone sectorCollapse sectorSupportedHalfCone SectorSimplex
      sectorChamber SectorOrder sectorI sectorJ sectorK sectorCh sectorOrderedSum sectorParam
      sectorParam_values sectorParam_continuous sectorPiece sectorChosenCone
      sectorChosenCone_spec sectorChosenPiece sectorGlobalMap sectorGlobalChosen
      sectorGlobalChosen_spec f i j hij r s hcoord
  have hexists : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by decide
  obtain ⟨k,hik,hjk⟩ := hexists i j hij
  have hi : s.1 i = (r : ℝ) := by simpa [hij] using hcoord i
  have hj : s.1 j = 1-r := by simpa [Ne.symm hij] using hcoord j
  have hk : s.1 k = 0 := by simpa [Ne.symm hik, Ne.symm hjk] using hcoord k
  by_cases hr : (r : ℝ) ≤ 1/2
  · let o : SectorOrder := ⟨(j,i,k), hij.symm, hjk, hik⟩
    have ho : s ∈ sectorCh o := by
      change s.1 i ≤ s.1 j ∧ s.1 k ≤ s.1 i
      rw [hi,hj,hk]
      constructor <;> nlinarith [hr, r.2.1]
    have hrad0 : 0 ≤ 2 * (r : ℝ) := mul_nonneg (by norm_num) r.2.1
    have hrad1 : 2 * (r : ℝ) ≤ 1 := by nlinarith [hr]
    let rad : SectorInterval := ⟨2*(r:ℝ), hrad0, hrad1⟩
    let one : SectorInterval := ⟨1, by exact ⟨by norm_num, le_rfl⟩⟩
    have hrad : (sectorParam o s ho).1.1 = rad := by
      apply Subtype.ext
      have vals := sectorParam_values o s ho
      simp only [ne_eq, o, sectorJ, sectorK] at vals
      calc
        (sectorParam o s ho).1.1 = 2*(s.1 i-s.1 k)+3*s.1 k := vals.1
        _ = 2*(r:ℝ) := by rw [hi,hk]; ring
        _ = (rad : ℝ) := rfl
    have hbeta : (sectorParam o s ho).1.2 = rad := by
      apply Subtype.ext
      have vals := sectorParam_values o s ho
      simp only [ne_eq, o, sectorJ, sectorK] at vals
      calc
        (sectorParam o s ho).1.2 = 2*(s.1 i-s.1 k) := vals.2
        _ = 2*(r:ℝ) := by rw [hi,hk]; ring
        _ = (rad : ℝ) := rfl
    have hparam : sectorParam o s ho = sectorCollapse (rad,one) := by
      apply Subtype.ext
      apply Prod.ext
      · exact hrad
      · apply Subtype.ext
        calc
          (sectorParam o s ho).1.2 = (rad : ℝ) := congrArg Subtype.val hbeta
          _ = (rad : ℝ) * (one : ℝ) := by simp [one]
    rw [sectorGlobalChosen_spec f o s ho]
    change sectorChosenCone f o (sectorParam o s ho) = _
    rw [hparam, sectorChosenCone_spec]
    change H.homotopy (P.plane.faceVertex f j) (rad : ℝ)
      (E.half f (P.plane.faceVertex f j) (P.plane.faceVertex f i) one) = _
    have hp := E.half_spec f (P.plane.faceVertex f j) (P.plane.faceVertex f i)
      (P.plane.face_edges f j i hij.symm) ⟨j,rfl⟩ ⟨i,rfl⟩
    have hone : one = ⟨1, by norm_num [SectorInterval]⟩ := by apply Subtype.ext; rfl
    rw [hone, hp.2.2.1]
    have hport := E.port_symmetric (P.plane.faceVertex f i) (P.plane.faceVertex f j)
      (P.plane.face_edges f i j hij)
    rw [← hport]
    rw [ite_eq_left hr]
  · let o : SectorOrder := ⟨(i,j,k), hij, hik, hjk⟩
    have ho : s ∈ sectorCh o := by
      change s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j
      rw [hi,hj,hk]
      constructor <;> nlinarith [r.2.1,r.2.2,hr]
    have hq0 : 0 ≤ 2*(1-(r:ℝ)) := by linarith [r.2.2]
    have hq1 : 2*(1-(r:ℝ)) ≤ 1 := by linarith
    let rad : SectorInterval := ⟨2*(1-(r:ℝ)),hq0,hq1⟩
    let one : SectorInterval := ⟨1, by exact ⟨by norm_num, le_rfl⟩⟩
    have hrad : (sectorParam o s ho).1.1 = rad := by
      apply Subtype.ext
      have vals := sectorParam_values o s ho
      simp only [ne_eq, o, sectorJ, sectorK] at vals
      calc
        (sectorParam o s ho).1.1 = 2*(s.1 j-s.1 k)+3*s.1 k := vals.1
        _ = 2*(1-(r:ℝ)) := by rw [hj,hk]; ring
        _ = (rad : ℝ) := rfl
    have hbeta : (sectorParam o s ho).1.2 = rad := by
      apply Subtype.ext
      have vals := sectorParam_values o s ho
      simp only [ne_eq, o, sectorJ, sectorK] at vals
      calc
        (sectorParam o s ho).1.2 = 2*(s.1 j-s.1 k) := vals.2
        _ = 2*(1-(r:ℝ)) := by rw [hj,hk]; ring
        _ = (rad : ℝ) := rfl
    have hparam : sectorParam o s ho = sectorCollapse (rad,one) := by
      apply Subtype.ext
      apply Prod.ext
      · exact hrad
      · apply Subtype.ext
        calc
          (sectorParam o s ho).1.2 = (rad : ℝ) := congrArg Subtype.val hbeta
          _ = (rad : ℝ) * (one : ℝ) := by simp [one]
    rw [sectorGlobalChosen_spec f o s ho]
    change sectorChosenCone f o (sectorParam o s ho) = _
    rw [hparam, sectorChosenCone_spec]
    change H.homotopy (P.plane.faceVertex f i) (rad : ℝ)
      (E.half f (P.plane.faceVertex f i) (P.plane.faceVertex f j) one) = _
    have hp := E.half_spec f (P.plane.faceVertex f i) (P.plane.faceVertex f j)
      (P.plane.face_edges f i j hij) ⟨i,rfl⟩ ⟨j,rfl⟩
    have hone : one = ⟨1, by norm_num [SectorInterval]⟩ := by apply Subtype.ext; rfl
    rw [hone, hp.2.2.1]
    rw [ite_eq_right hr]

end SectorMapsProof

theorem P3776T1SectorMapsExist {ι : Type} (P : PeriodicTileCore ι)
    (H : P3776T1TileContractions P) (E : P3776T1DualEdges P) :
    Nonempty (P3776T1SectorMaps P H E) := by
-- BODY
  classical
  let SectorInterval := Set.Icc (0 : ℝ) 1
  let SectorCone := {z : SectorInterval × SectorInterval // (z.2 : ℝ) ≤ z.1}
  let sectorCollapse := P3832T1ConeCollapse
  have sectorCollapse_surjective := SectorMapsProof.sectorCollapse_surjective
  have sectorConeDescent (g : C(SectorInterval × SectorInterval, ℝ × ℝ)) (c : ℝ × ℝ)
      (hzero : ∀ t : SectorInterval, g (⟨0, by norm_num [SectorInterval]⟩, t) = c) :=
          SectorMapsProof.sectorConeDescent g c hzero
  have sectorSupportedHalfCone {ι : Type} (P : PeriodicTileCore ι)
      (H : P3776T1TileContractions P) (E : P3776T1DualEdges P)
      (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b)
      (ha : ∃ i, P.plane.faceVertex f i = a)
      (hb : ∃ i, P.plane.faceVertex f i = b) := SectorMapsProof.sectorSupportedHalfCone
          sectorConeDescent (ι := ι) P H E f a b hab ha hb
  let SectorSimplex := StandardSimplex (Fin 3)
  let sectorChamber : Fin 3 → Fin 3 → Fin 3 → Set SectorSimplex := fun i j k =>
    {s | s.1 j ≤ s.1 i ∧ s.1 k ≤ s.1 j}
  let SectorOrder := {t : Fin 3 × Fin 3 × Fin 3 //
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}
  let sectorI : SectorOrder → Fin 3 := fun o => o.1.1
  let sectorJ : SectorOrder → Fin 3 := fun o => o.1.2.1
  let sectorK : SectorOrder → Fin 3 := fun o => o.1.2.2
  let sectorCh := fun o : SectorOrder => sectorChamber (sectorI o) (sectorJ o) (sectorK o)
  have sectorOrderExists := SectorMapsProof.sectorOrderExists
  have sectorChamber_closed := SectorMapsProof.sectorChamber_closed
  have sectorOrder_cover := SectorMapsProof.sectorOrder_cover sectorOrderExists
  have sectorIndexCover (o : SectorOrder) (n : Fin 3) := SectorMapsProof.sectorIndexCover o n
  have sectorOrderedSum (s : SectorSimplex) (i j k : Fin 3)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) := SectorMapsProof.sectorOrderedSum s i j k hij
          hik hjk
  let sectorParam := fun (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) =>
    let i := sectorI o
    let j := sectorJ o
    let k := sectorK o
    have hc : (∀ n, 0 ≤ s.1 n) ∧ ∑ n : Fin 3, s.1 n = 1 := by
      simpa only [SectorSimplex, StandardSimplex, Set.mem_ofPred_eq] using s.2
    have hsum : s.1 i + s.1 j + s.1 k = 1 :=
      sectorOrderedSum s i j k o.2.1 o.2.2.1 o.2.2.2
    have hxy := hs.1
    have hyz := hs.2
    have hr0 : 0 ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
      linarith [hc.1 j, hc.1 k]
    have hr1 : 2 * (s.1 j - s.1 k) + 3 * s.1 k ≤ 1 := by
      linarith [hc.1 i, hsum]
    have hb0 : 0 ≤ 2 * (s.1 j - s.1 k) := by linarith [hyz]
    have hbr : 2 * (s.1 j - s.1 k) ≤ 2 * (s.1 j - s.1 k) + 3 * s.1 k := by
      nlinarith [hc.1 k]
    (⟨⟨⟨2*(s.1 j-s.1 k)+3*s.1 k,hr0,hr1⟩,
      ⟨2*(s.1 j-s.1 k),hb0,le_trans hbr hr1⟩⟩,hbr⟩ : SectorCone)
  have sectorParam_values (o : SectorOrder) (s : SectorSimplex) (hs : s ∈ sectorCh o) :=
      SectorMapsProof.sectorParam_values sectorOrderedSum o s hs
  have sectorParam_continuous (o : SectorOrder) := SectorMapsProof.sectorParam_continuous
      sectorOrderedSum o
  have sectorOrdersTie (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o') := SectorMapsProof.sectorOrdersTie s o o' ho ho'
  have sectorOrderedBetaTop (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorI o)=s.1 (sectorJ o)) := SectorMapsProof.sectorOrderedBetaTop s o o' ho
            ho' ht
  have sectorOrderedRBottom (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorJ o)=s.1 (sectorK o)) := SectorMapsProof.sectorOrderedRBottom s o o' ho
          ho' ht
  have sectorTopTieParams (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorI o)=s.1 (sectorJ o)) := SectorMapsProof.sectorTopTieParams
            sectorOrderedSum sectorParam_values sectorOrderedBetaTop s o o' ho ho' ht
  have sectorBottomTieParams (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorJ o)=s.1 (sectorK o)) := SectorMapsProof.sectorBottomTieParams
          sectorOrderedSum sectorOrderedRBottom s o o' ho
            ho' ht
  have sectorBottomSameTop (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorJ o)=s.1 (sectorK o)) := SectorMapsProof.sectorBottomSameTop s o o' ho ho' ht
  have sectorTopTieOther (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorI o)=s.1 (sectorJ o)) := SectorMapsProof.sectorTopTieOther s o o' ho ho' ht
  have sectorBottomTieOther (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorJ o)=s.1 (sectorK o)) := SectorMapsProof.sectorBottomTieOther s o o' ho
          ho' ht
  have sectorTopPairClassify (s : SectorSimplex) (o o' : SectorOrder)
      (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o')
      (ht : s.1 (sectorI o)=s.1 (sectorJ o))
      (ht' : s.1 (sectorI o')=s.1 (sectorJ o')) := SectorMapsProof.sectorTopPairClassify s o o'
          ho ho' ht ht'
  let sectorPiece (o : SectorOrder)
      (G : C(SectorCone,ℝ×ℝ)) : C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
    ⟨fun s => G (sectorParam o s.1 s.2),
      G.continuous.comp (sectorParam_continuous o)⟩
  let sectorChosenCone (f : P.plane.Face) (o : SectorOrder) : C(SectorCone,ℝ×ℝ) :=
    Classical.choose (sectorSupportedHalfCone P H E f
      (P.plane.faceVertex f (sectorI o)) (P.plane.faceVertex f (sectorJ o))
      (P.plane.face_edges f (sectorI o) (sectorJ o) o.2.1)
      ⟨sectorI o,rfl⟩ ⟨sectorJ o,rfl⟩)
  have sectorChosenCone_spec (f : P.plane.Face) (o : SectorOrder)
      (z : SectorInterval × SectorInterval) := SectorMapsProof.sectorChosenCone_spec ι P
                H E sectorSupportedHalfCone f o z
  let sectorChosenPiece (f : P.plane.Face) (o : SectorOrder) :
      C({s : SectorSimplex // s ∈ sectorCh o},ℝ×ℝ) :=
    sectorPiece o (sectorChosenCone f o)
  have sectorChosenPiece_top (f : P.plane.Face) (o : SectorOrder) (s : SectorSimplex)
      (hs : s ∈ sectorCh o) (ht : s.1 (sectorI o)=s.1 (sectorJ o)) :=
          SectorMapsProof.sectorChosenPiece_top ι P H E
              sectorSupportedHalfCone sectorOrderedSum sectorParam_continuous sectorTopTieParams
              sectorChosenCone_spec f o s hs ht
  have sectorChosenPiece_bottom (f : P.plane.Face) (o : SectorOrder) (s : SectorSimplex)
      (hs : s ∈ sectorCh o) (ht : s.1 (sectorJ o)=s.1 (sectorK o)) :=
          SectorMapsProof.sectorChosenPiece_bottom ι P H E sectorSupportedHalfCone
              sectorOrderedSum sectorParam_continuous sectorBottomTieParams sectorChosenCone_spec
              f o s hs ht
  have sectorParam_beta_zero (o : SectorOrder) (s : SectorSimplex)
      (hs : s ∈ sectorCh o) (ht : s.1 (sectorJ o)=s.1 (sectorK o)) :=
          SectorMapsProof.sectorParam_beta_zero sectorOrderedSum sectorParam_values o s hs ht
  have sectorChosenPieces_agree (f : P.plane.Face) (s : SectorSimplex)
      (o o' : SectorOrder) (ho : s ∈ sectorCh o) (ho' : s ∈ sectorCh o') :=
          SectorMapsProof.sectorChosenPieces_agree ι P H E sectorSupportedHalfCone
          sectorOrderedSum sectorParam_continuous sectorOrdersTie sectorTopTieParams
          sectorBottomTieParams sectorBottomSameTop sectorTopTieOther sectorBottomTieOther
          sectorTopPairClassify sectorChosenPiece_top sectorChosenPiece_bottom
          sectorParam_beta_zero f s o o' ho ho'
  have sectorGlobalMap (f : P.plane.Face) := SectorMapsProof.sectorGlobalMap ι P H E
            sectorSupportedHalfCone
            sectorOrder_cover sectorOrderedSum sectorParam_continuous sectorChosenPieces_agree f
  have sectorChosenPiece_support (f : P.plane.Face) (o : SectorOrder)
      (s : SectorSimplex) (hs : s ∈ sectorCh o) := SectorMapsProof.sectorChosenPiece_support ι P
          H E sectorCollapse_surjective
            sectorSupportedHalfCone sectorOrderedSum sectorParam_continuous sectorChosenCone_spec
            f o s hs
  have sectorTopPositive (s : SectorSimplex) (o : SectorOrder)
      (hs : s ∈ sectorCh o) := SectorMapsProof.sectorTopPositive
          sectorOrderedSum s o hs
  have sectorChosenCone_periodic (u : P.lattice) (f : P.plane.Face)
      (o : SectorOrder) (z : SectorCone) := SectorMapsProof.sectorChosenCone_periodic
            ι P H E sectorCollapse_surjective sectorSupportedHalfCone sectorChosenCone_spec u f o z
  let sectorGlobalChosen (f : P.plane.Face) : C(SectorSimplex,ℝ×ℝ) :=
    Classical.choose (sectorGlobalMap f)
  have sectorGlobalChosen_spec (f : P.plane.Face) (o : SectorOrder)
      (s : SectorSimplex) (hs : s ∈ sectorCh o) := SectorMapsProof.sectorGlobalChosen_spec ι P H
          E sectorSupportedHalfCone
          sectorOrderedSum sectorParam_continuous sectorGlobalMap f o s hs
  have sectorGlobalChosen_periodic (u : P.lattice) (f : P.plane.Face)
      (s : SectorSimplex) := SectorMapsProof.sectorGlobalChosen_periodic ι P H E
          sectorSupportedHalfCone
            sectorOrder_cover sectorOrderedSum sectorParam_continuous sectorGlobalMap
            sectorChosenCone_periodic sectorGlobalChosen_spec u f s
  have sectorGlobalChosen_support (f : P.plane.Face) (s : SectorSimplex) :=
      SectorMapsProof.sectorGlobalChosen_support ι P H E sectorSupportedHalfCone
            sectorOrder_cover sectorOrderedSum sectorParam_continuous sectorGlobalMap
            sectorChosenPiece_support sectorTopPositive sectorGlobalChosen_spec f s
  have sectorGlobalChosen_vertex (f : P.plane.Face) (i : Fin 3) (s : SectorSimplex)
      (hcoord : ∀ j, s.1 j = if j = i then 1 else 0) := SectorMapsProof.sectorGlobalChosen_vertex
          ι P H E sectorSupportedHalfCone
          sectorOrder_cover sectorIndexCover sectorOrderedSum sectorParam_values
          sectorParam_continuous sectorChosenCone_spec sectorGlobalMap sectorGlobalChosen_spec f
          i s hcoord
  have sectorGlobalChosen_edge (f : P.plane.Face) (i j : Fin 3) (hij : i ≠ j)
      (r : SectorInterval) (s : SectorSimplex)
      (hcoord : ∀ k, s.1 k = if k = i then (r : ℝ) else if k = j then 1-r else 0) :=
          SectorMapsProof.sectorGlobalChosen_edge ι P H E sectorSupportedHalfCone
                sectorOrderedSum sectorParam_values sectorParam_continuous sectorChosenCone_spec
                sectorGlobalMap sectorGlobalChosen_spec f i j hij r s hcoord
  refine ⟨{
    faceMap := sectorGlobalChosen
    support := ?_
    vertex := ?_
    edge := ?_
    periodic := ?_
  }⟩
  · intro f s
    exact sectorGlobalChosen_support f s
  · intro f i s hcoord
    exact sectorGlobalChosen_vertex f i s hcoord
  · intro f i j hij r s hcoord
    exact sectorGlobalChosen_edge f i j hij r s hcoord
  · intro u f s
    exact sectorGlobalChosen_periodic u f s

end ApollonianSuperharmonic

end
