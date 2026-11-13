/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.GaussianRealPointProperties
public import LeanPool.ApollonianSuperharmonic.PeriodicEdgeContactSymmetry

public import LeanPool.ApollonianSuperharmonic.P3723T1ContactPorts
public import LeanPool.ApollonianSuperharmonic.P3723T1ContactStabilizer
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure

-- [TABLET NODE: P3723T1ContactPortsExist]

/-!
# P3723T1ContactPortsExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ContactPortGeometry

private theorem owner_unique :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (a : ι), ∀ (b : ι), ∀ (z : GaussianInt),
            (z ∈ (P.tile a).cells) → ((z ∈ (P.tile b).cells) → (a = b)) ) := by
  classical
  intro ι P a b z ha hb
  exact (PeriodicTileIndexedMultiplicityOne P z).unique ha hb

private theorem openSquare_closure :
    (by
      classical
      exact
        let openSquare (z : GaussianInt) : Set (Real × Real) :=
          Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
            Set.Ioo (z.im : Real) ((z.im : Real) + 1)
        ∀ (z : GaussianInt), closure (openSquare z) = ClosedSquareRealization z ) := by
  classical
  intro openSquare z
  dsimp [openSquare, ClosedSquareRealization]
  rw [closure_prod_eq, closure_Ioo (by linarith), closure_Ioo (by linarith),
    Set.Icc_prod_Icc]

private theorem coord_unique :
    (by
      classical
      exact
        ∀ (m : Int), ∀ (n : Int), ∀ (t : Real), ((m : Real) < t ∧ t < (m : Real) + 1) → (((n :
            Real) ≤ t ∧ t ≤ (n : Real) + 1) → (m = n)) ) := by
  classical
  intro m n t hm hn
  have hmn : (m : Real) < ((n + 1 : Int) : Real) := by
    push_cast
    linarith
  have hnm : (n : Real) < ((m + 1 : Int) : Real) := by
    push_cast
    linarith
  have hi : m < n + 1 := by exact_mod_cast hmn
  have hj : n < m + 1 := by exact_mod_cast hnm
  omega

private theorem square_unique :
    (by
      classical
      exact
        let openSquare (z : GaussianInt) : Set (Real × Real) :=
          Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
            Set.Ioo (z.im : Real) ((z.im : Real) + 1)
        (∀ (m : Int), ∀ (n : Int), ∀ (t : Real), ((m : Real) < t ∧ t < (m : Real) + 1) → (((n :
            Real) ≤ t ∧ t ≤ (n : Real) + 1) → (m = n))) → (∀ (x : GaussianInt), ∀ (y :
            GaussianInt), ∀ (p : Real × Real), (p ∈ openSquare x) → ((p ∈ ClosedSquareRealization
            y) → (x = y))) ) := by
  classical
  intro openSquare coord_unique x y p hx hy
  simp only [openSquare, Set.mem_prod, Set.mem_Ioo] at hx
  simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hy
  apply Zsqrtd.ext
  · exact coord_unique x.re y.re p.1 hx.1 ⟨hy.1.1, hy.2.1⟩
  · exact coord_unique x.im y.im p.2 hx.2 ⟨hy.1.2, hy.2.2⟩

private theorem interior_disjoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), ∀ (b : ι), ∀ (z : GaussianInt),
            (z ∈ (P.tile a).cells) → ((z ∈ (P.tile b).cells) → (a = b))) → (
        let openSquare (z : GaussianInt) : Set (Real × Real) :=
          Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
            Set.Ioo (z.im : Real) ((z.im : Real) + 1)
        (∀ (z : GaussianInt), closure (openSquare z) = ClosedSquareRealization z) → ((∀ (x :
            GaussianInt), ∀ (y : GaussianInt), ∀ (p : Real × Real), (p ∈ openSquare x) → ((p ∈
            ClosedSquareRealization y) → (x = y))) → (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (Disjoint
            (interior (TileRealization (P.tile a))) (TileRealization (P.tile b)))))) ) := by
  classical
  intro ι P owner_unique openSquare openSquare_closure square_unique a b hab
  apply Set.disjoint_left.mpr
  intro p hp hpb
  obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hpb
  have hd : Disjoint (TileRealization (P.tile a)) (openSquare z) := by
    apply Set.disjoint_left.mpr
    intro q hqa hqz
    obtain ⟨x, hx, hqx⟩ := Set.mem_iUnion₂.mp hqa
    have hxz := square_unique z x q hqz hqx
    exact hab (owner_unique a b z (hxz.symm ▸ hx) hz)
  have hc := (hd.mono_left interior_subset).closure_right isOpen_interior
  rw [openSquare_closure] at hc
  exact Set.disjoint_left.mp hc hp hpz

private theorem center_interior :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let openSquare (z : GaussianInt) : Set (Real × Real) :=
          Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
            Set.Ioo (z.im : Real) ((z.im : Real) + 1)
        (∀ (z : GaussianInt), IsOpen (openSquare z)) → ((∀ (z : GaussianInt), closure (openSquare
            z) = ClosedSquareRealization z) → (∀ (a : ι), ∀ (z : GaussianInt), (z ∈ (P.tile
            a).cells) → (GaussianRealPoint z + ((1 / 2 : Real), (1 / 2 : Real)) ∈ interior
            (TileRealization (P.tile a))))) ) := by
  classical
  intro ι P openSquare openSquare_open openSquare_closure a z hz
  apply interior_mono (s := openSquare z)
  · exact (subset_closure.trans (by
      rw [openSquare_closure]
      exact fun _ h => Set.mem_iUnion₂.mpr ⟨z, hz, h⟩))
  · rw [(openSquare_open z).interior_eq]
    simp only [openSquare, GaussianRealPoint, Set.mem_prod, Set.mem_Ioo,
      Prod.fst_add, Prod.snd_add]
    constructor <;> constructor <;> linarith

private theorem horizontal_midpoint :
    (by
      classical
      exact
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        ∀ (z : GaussianInt), midpoint {z, z + 1} = ((z.re : Real) + 1 / 2, (z.im : Real)) ) := by
  classical
  intro midpoint z
  have hn : z ≠ z + 1 := by
    intro h
    have hh := congrArg Zsqrtd.re h
    simp at hh
  simp [midpoint, Finset.sum_pair hn]
  ring

private theorem vertical_midpoint :
    (by
      classical
      exact
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        ∀ (z : GaussianInt), midpoint {z, z + ⟨0, 1⟩} = ((z.re : Real), (z.im : Real) + 1 / 2) )
            := by
  classical
  intro midpoint z
  have hn : z ≠ z + ⟨0, 1⟩ := by
    intro h
    have hh := congrArg Zsqrtd.im h
    simp at hh
  simp [midpoint, Finset.sum_pair hn]
  ring

private theorem edge_normal :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ z :
            GaussianInt, e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩}) ) := by
  classical
  intro T e he
  obtain ⟨x, hx, he⟩ := he
  rcases he with he | he | he | he
  · exact ⟨x, Or.inl he⟩
  · exact ⟨x, Or.inr he⟩
  · exact ⟨x + 1, Or.inr he⟩
  · refine ⟨x + ⟨0, 1⟩, Or.inl ?_⟩
    simpa only [add_assoc, add_comm, add_left_comm] using he

private theorem midpoint_cell :
    (by
      classical
      exact
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (z : GaussianInt), midpoint {z, z + 1} = ((z.re : Real) + 1 / 2, (z.im : Real))) → ((∀
            (z : GaussianInt), midpoint {z, z + ⟨0, 1⟩} = ((z.re : Real), (z.im : Real) + 1 / 2))
            → (∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ z ∈
            T.cells, midpoint e ∈ ClosedSquareRealization z))) ) := by
  classical
  intro midpoint horizontal_midpoint vertical_midpoint T e he
  obtain ⟨x, hx, he⟩ := he
  refine ⟨x, hx, ?_⟩
  rcases he with he | he | he | he
  · rw [he, horizontal_midpoint]
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    constructor <;> constructor <;> linarith
  · rw [he, vertical_midpoint]
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def]
    constructor <;> constructor <;> linarith
  · rw [he, vertical_midpoint]
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> linarith
  · have he' : e = {x + ⟨0, 1⟩, (x + ⟨0, 1⟩) + 1} := by
      simpa only [add_assoc, add_comm, add_left_comm] using he
    rw [he', horizontal_midpoint]
    simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def,
      Zsqrtd.re_add, Zsqrtd.im_add, Int.cast_add, Int.cast_one, Int.cast_zero]
    constructor <;> constructor <;> norm_num

private theorem midpoint_two_cells :
    (by
      classical
      exact
        (∀ (m : Int), ∀ (n : Int), ∀ (t : Real), ((m : Real) < t ∧ t < (m : Real) + 1) → (((n :
            Real) ≤ t ∧ t ≤ (n : Real) + 1) → (m = n))) → (
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (z : GaussianInt), midpoint {z, z + 1} = ((z.re : Real) + 1 / 2, (z.im : Real))) → ((∀
            (z : GaussianInt), midpoint {z, z + ⟨0, 1⟩} = ((z.re : Real), (z.im : Real) + 1 / 2))
            → ((∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ z :
            GaussianInt, e = {z, z + 1} ∨ e = {z, z + ⟨0, 1⟩})) → (∀ (T : ProtoTile), ∀ (e :
            Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ x y : GaussianInt, x ≠ y ∧ ∀ z,
            midpoint e ∈ ClosedSquareRealization z → z = x ∨ z = y))))) ) := by
  classical
  intro coord_unique midpoint horizontal_midpoint vertical_midpoint edge_normal T e he
  obtain ⟨x, rfl | rfl⟩ := edge_normal T e he
  · refine ⟨x, x - ⟨0, 1⟩, ?_, ?_⟩
    · intro h
      have hi := congrArg Zsqrtd.im h
      simp at hi
      omega
    · intro z hz
      rw [horizontal_midpoint] at hz
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hz
      have hre : x.re = z.re := coord_unique x.re z.re ((x.re : Real) + 1 / 2)
        ⟨by linarith, by linarith⟩ ⟨hz.1.1, hz.2.1⟩
      have hlo : z.im ≤ x.im := by exact_mod_cast hz.1.2
      have hup : x.im ≤ z.im + 1 := by exact_mod_cast hz.2.2
      have him : z.im = x.im ∨ z.im = x.im - 1 := by omega
      rcases him with him | him
      · left
        exact Zsqrtd.ext hre.symm him
      · right
        apply Zsqrtd.ext
        · simpa using hre.symm
        · simpa using him
  · refine ⟨x, x - 1, ?_, ?_⟩
    · intro h
      have hr := congrArg Zsqrtd.re h
      simp at hr
      omega
    · intro z hz
      rw [vertical_midpoint] at hz
      simp only [ClosedSquareRealization, Set.mem_Icc, Prod.le_def] at hz
      have him : x.im = z.im := coord_unique x.im z.im ((x.im : Real) + 1 / 2)
        ⟨by linarith, by linarith⟩ ⟨hz.1.2, hz.2.2⟩
      have hlo : z.re ≤ x.re := by exact_mod_cast hz.1.1
      have hup : x.re ≤ z.re + 1 := by exact_mod_cast hz.2.1
      have hre : z.re = x.re ∨ z.re = x.re - 1 := by omega
      rcases hre with hre | hre
      · left
        exact Zsqrtd.ext hre him.symm
      · right
        apply Zsqrtd.ext
        · simpa using hre
        · simpa using him.symm

private theorem common_midpoint :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), ∀ (b : ι), ∀ (z : GaussianInt),
            (z ∈ (P.tile a).cells) → ((z ∈ (P.tile b).cells) → (a = b))) → (
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ z ∈ T.cells,
            midpoint e ∈ ClosedSquareRealization z)) → ((∀ (T : ProtoTile), ∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges T) → (∃ x y : GaussianInt, x ≠ y ∧ ∀ z, midpoint e
            ∈ ClosedSquareRealization z → z = x ∨ z = y)) → (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀
            (e : Finset GaussianInt), (e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b))
            → (midpoint e ∈ TileRealization (P.tile a) ∩ TileRealization (P.tile b) ∧ ∀ c,
            midpoint e ∈ TileRealization (P.tile c) → c = a ∨ c = b))))) ) := by
  classical
  intro ι P owner_unique midpoint midpoint_cell midpoint_two_cells a b hab e he
  obtain ⟨x, hx, hpx⟩ := midpoint_cell (P.tile a) e he.1
  obtain ⟨y, hy, hpy⟩ := midpoint_cell (P.tile b) e he.2
  have hxy : x ≠ y := by
    intro h
    exact hab (owner_unique a b x hx (h.symm ▸ hy))
  refine ⟨⟨Set.mem_iUnion₂.mpr ⟨x, hx, hpx⟩,
    Set.mem_iUnion₂.mpr ⟨y, hy, hpy⟩⟩, ?_⟩
  intro c hc
  obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hc
  obtain ⟨s, t, hst, hall⟩ := midpoint_two_cells (P.tile a) e he.1
  have hxst := hall x hpx
  have hyst := hall y hpy
  have hzst := hall z hpz
  have hzx : z = x ∨ z = y := by
    rcases hxst with rfl | rfl <;> rcases hyst with rfl | rfl
    · exact (hxy rfl).elim
    · exact hzst
    · exact hzst.symm
    · exact (hxy rfl).elim
  rcases hzx with rfl | rfl
  · exact Or.inl (owner_unique c a z hz hx)
  · exact Or.inr (owner_unique c b z hz hy)

private theorem common_frontier :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (T : ProtoTile), IsClosed
            (TileRealization T)) → ((∀ (a : ι), ∀ (b : ι), (a ≠ b) → (Disjoint (interior
            (TileRealization (P.tile a))) (TileRealization (P.tile b)))) → (
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges (P.tile
            a) ∩ FootprintEdges (P.tile b)) → (midpoint e ∈ TileRealization (P.tile a) ∩
            TileRealization (P.tile b) ∧ ∀ c, midpoint e ∈ TileRealization (P.tile c) → c = a ∨ c
            = b))) → (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) → (midpoint e ∈ frontier
            (TileRealization (P.tile a)) ∩ frontier (TileRealization (P.tile b))))))) ) := by
  classical
  intro ι P realization_closed interior_disjoint midpoint common_midpoint a b hab e he
  have hm := (common_midpoint a b hab e he).1
  constructor
  · rw [(realization_closed (P.tile a)).frontier_eq]
    exact ⟨hm.1, fun h => Set.disjoint_left.mp (interior_disjoint a b hab) h hm.2⟩
  · rw [(realization_closed (P.tile b)).frontier_eq]
    exact ⟨hm.2, fun h => Set.disjoint_left.mp (interior_disjoint b a hab.symm) h hm.1⟩

private theorem footprint_finite :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (FootprintEdges T).Finite ) := by
  classical
  intro T
  let es : Finset (Finset GaussianInt) := T.cells.biUnion fun x =>
    {{x, x + 1}, {x, x + ⟨0, 1⟩}, {x + 1, x + 1 + ⟨0, 1⟩},
      {x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩}}
  apply es.finite_toSet.subset
  rintro e ⟨x, hx, he⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨x, hx, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton] using he

private theorem finite_degree :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (∃ z ∈ T.cells,
            midpoint e ∈ ClosedSquareRealization z)) → ((∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (e :
            Finset GaussianInt), (e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) →
            (midpoint e ∈ TileRealization (P.tile a) ∩ TileRealization (P.tile b) ∧ ∀ c, midpoint
            e ∈ TileRealization (P.tile c) → c = a ∨ c = b))) → ((∀ (T : ProtoTile),
            (FootprintEdges T).Finite) → (∀ (a : ι), Set.Finite {b | P3723T1EdgeContact P a
            b}))) ) := by
  classical
  intro ι P midpoint midpoint_cell common_midpoint footprint_finite a
  have hf (e : Finset GaussianInt) (he : e ∈ FootprintEdges (P.tile a)) :
      Set.Finite {b | b ≠ a ∧ e ∈ FootprintEdges (P.tile b)} := by
    apply Set.Subsingleton.finite
    intro b hb c hc
    obtain ⟨z, hz, hpz⟩ := midpoint_cell (P.tile c) e hc.2
    have hm := (common_midpoint a b hb.1.symm e ⟨he, hb.2⟩).2 c
      (Set.mem_iUnion₂.mpr ⟨z, hz, hpz⟩)
    exact hm.resolve_left hc.1 |>.symm
  apply ((footprint_finite (P.tile a)).biUnion hf).subset
  intro b hb
  obtain ⟨e, he⟩ := hb.2
  exact Set.mem_iUnion₂.mpr ⟨e, he.1, hb.1.symm, he.2⟩

private theorem rep_spec :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep a) ) := by
  classical
  intro ι P rep a
  exact Classical.choose_spec (P.vertex_orbit_representatives a).exists


private theorem shift_injective :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), ∀ (a : ι), P.shift (-u)
            (P.shift u a) = a) → (∀ (u : P.lattice), Function.Injective (P.shift u)) ) := by
  classical
  intro ι P shift_cancel u a b h
  simpa only [shift_cancel] using congrArg (P.shift (-u)) h

private theorem edges_periodic :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (u : P.lattice), ∀ (a : ι), FootprintEdges
            (P.tile (P.shift u a)) = (fun e : Finset GaussianInt => e.image (fun z => z + (u :
            GaussianInt))) '' FootprintEdges (P.tile a) ) := by
  classical
  intro ι P u a
  rw [P.tile_periodic]
  exact (TileTranslationFormulas (P.tile a) u).2.2.2.2.2.2.1

private theorem common_edge_transport :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), ∀ (a : ι),
            FootprintEdges (P.tile (P.shift u a)) = (fun e : Finset GaussianInt => e.image (fun z
            => z + (u : GaussianInt))) '' FootprintEdges (P.tile a)) → (∀ (u : P.lattice), ∀ (a :
            ι), ∀ (b : ι), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges (P.tile a) ∩
            FootprintEdges (P.tile b)) → (e.image (fun z => z + (u : GaussianInt)) ∈
            FootprintEdges (P.tile (P.shift u a)) ∩ FootprintEdges (P.tile (P.shift u b)))) ) := by
  classical
  intro ι P edges_periodic u a b e he
  rw [edges_periodic, edges_periodic]
  exact ⟨⟨e, he.1, rfl⟩, ⟨e, he.2, rfl⟩⟩

private theorem contact_forward :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), Function.Injective
            (P.shift u)) → ((∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι), ∀ (e : Finset GaussianInt),
            (e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) → (e.image (fun z => z +
            (u : GaussianInt)) ∈ FootprintEdges (P.tile (P.shift u a)) ∩ FootprintEdges (P.tile
            (P.shift u b)))) → (∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P
            a b) → (P3723T1EdgeContact P (P.shift u a) (P.shift u b)))) ) := by
  classical
  intro ι P shift_injective common_edge_transport u a b hab
  refine ⟨fun h => hab.1 (shift_injective u h), ?_⟩
  obtain ⟨e, he⟩ := hab.2
  exact ⟨_, common_edge_transport u a b e he⟩

private theorem contact_periodic :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), ∀ (a : ι), P.shift (-u)
            (P.shift u a) = a) → ((∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact
            P a b) → (P3723T1EdgeContact P (P.shift u a) (P.shift u b))) → (∀ (u : P.lattice),
            ∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P (P.shift u a) (P.shift u b) ↔
            P3723T1EdgeContact P a b)) ) := by
  classical
  intro ι P shift_cancel contact_forward u a b
  constructor
  · intro h
    simpa only [shift_cancel] using contact_forward (-u) _ _ h
  · exact contact_forward u a b

private theorem period_unique :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), ∀ (a : ι), P.shift (-u)
            (P.shift u a) = a) → (∀ (r : ι), ∀ (u : P.lattice), ∀ (v : P.lattice), (P.shift u r =
            P.shift v r) → (u = v)) ) := by
  classical
  intro ι P shift_cancel r u v h
  have hfix : P.shift (u - v) r = r := by
    rw [sub_eq_add_neg, add_comm, P.shift_add, h, shift_cancel]
  have hz : u - v = 0 := P3723T1ContactStabilizer P.toPeriodicTileCore (u - v) r r
    (by simp only [hfix])
  exact sub_eq_zero.mp hz

private theorem rep_shift :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (∀ (u : P.lattice), ∀ (a : ι), rep (P.shift
            u a) = rep a) ) := by
  classical
  intro ι P rep rep_spec period period_spec u a
  apply (P.vertex_orbit_representatives (P.shift u a)).unique
  · exact rep_spec (P.shift u a)
  · refine ⟨(rep_spec a).1, u + period a, ?_⟩
    rw [P.shift_add, ← period_spec]

private theorem period_shift :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → ((∀ (r : ι), ∀ (u : P.lattice), ∀ (v :
            P.lattice), (P.shift u r = P.shift v r) → (u = v)) → ((∀ (u : P.lattice), ∀ (a : ι),
            rep (P.shift u a) = rep a) → (∀ (u : P.lattice), ∀ (a : ι), period (P.shift u a) = u
            + period a))) ) := by
  classical
  intro ι P rep rep_spec period period_spec period_unique rep_shift u a
  apply period_unique (rep a)
  calc
    P.shift (period (P.shift u a)) (rep a) = P.shift u a := by
      rw [← rep_shift u a, ← period_spec]
    _ = P.shift (u + period a) (rep a) := by rw [P.shift_add, ← period_spec]

private abbrev real_add := ApollonianSuperharmonic.GaussianRealPointProperties.add

private theorem position_cell :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (cells_nonempty : ∀ (a : ι), (P.tile
            a).cells.Nonempty),
        let cell (a : ι) : GaussianInt := Classical.choose (cells_nonempty a)
        (∀ (a : ι), cell a ∈ (P.tile a).cells) → (
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → (
        let position (a : ι) : Real × Real :=
          GaussianRealPoint (cell (rep a) + (period a : GaussianInt)) + (1 / 2, 1 / 2)
        ∀ (a : ι), ∃ z ∈ (P.tile a).cells, position a = GaussianRealPoint z + ((1 / 2 : Real), (1
            / 2 : Real)))) ) := by
  classical
  intro ι P cells_nonempty cell cell_mem rep rep_spec period period_spec position a
  refine ⟨cell (rep a) + (period a : GaussianInt), ?_, rfl⟩
  have htile : P.tile a = TileTranslation (P.tile (rep a)) (period a) :=
    (congrArg P.tile (period_spec a)).trans (P.tile_periodic (period a) (rep a))
  rw [htile]
  exact Finset.mem_image.mpr ⟨cell (rep a), cell_mem (rep a), rfl⟩

private theorem position_interior :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), ∀ (z : GaussianInt), (z ∈
            (P.tile a).cells) → (GaussianRealPoint z + ((1 / 2 : Real), (1 / 2 : Real)) ∈
            interior (TileRealization (P.tile a)))) → (∀ (cells_nonempty : ∀ (a : ι), (P.tile
            a).cells.Nonempty),
        let cell (a : ι) : GaussianInt := Classical.choose (cells_nonempty a)
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        let position (a : ι) : Real × Real :=
          GaussianRealPoint (cell (rep a) + (period a : GaussianInt)) + (1 / 2, 1 / 2)
        (∀ (a : ι), ∃ z ∈ (P.tile a).cells, position a = GaussianRealPoint z + ((1 / 2 : Real),
            (1 / 2 : Real))) → (∀ (a : ι), position a ∈ interior (TileRealization (P.tile a)))) )
            := by
  classical
  intro ι P center_interior cells_nonempty cell rep rep_spec period position position_cell a
  obtain ⟨z, hz, heq⟩ := position_cell a
  rw [heq]
  exact center_interior a z hz

private theorem position_periodic :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (cells_nonempty : ∀ (a : ι), (P.tile
            a).cells.Nonempty),
        let cell (a : ι) : GaussianInt := Classical.choose (cells_nonempty a)
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        let position (a : ι) : Real × Real :=
          GaussianRealPoint (cell (rep a) + (period a : GaussianInt)) + (1 / 2, 1 / 2)
        (∀ (u : P.lattice), ∀ (a : ι), rep (P.shift u a) = rep a) → ((∀ (u : P.lattice), ∀ (a :
            ι), period (P.shift u a) = u + period a) → ((∀ (z : GaussianInt), ∀ (w :
            GaussianInt), GaussianRealPoint (z + w) = GaussianRealPoint z + GaussianRealPoint w)
            → (∀ (u : P.lattice), ∀ (a : ι), position (P.shift u a) = position a +
            GaussianRealPoint u))) ) := by
  classical
  intro ι P cells_nonempty cell rep rep_spec period position rep_shift period_shift real_add u a
  simp only [position, rep_shift, period_shift, AddSubgroup.coe_add, real_add]
  abel

private theorem representative_eq :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a),
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (p : ι × ι), ∀ (q : ι × ι), (S.r p q) → (representative p = representative q) ) := by
  classical
  intro ι P shift_cancel S representative p q h
  exact congrArg Quotient.out (Quotient.sound h)

private theorem transport_spec :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a),
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (representative_spec : ∀ (p : ι × ι), S.r (representative p) p),
        let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
        ∀ (p : ι × ι), ({P.shift (transport p) (representative p).1,
            P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2} ) := by
  classical
  intro ι P shift_cancel S representative representative_spec transport p
  exact Classical.choose_spec (representative_spec p)

private theorem transport_unique :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (u : P.lattice), ∀ (a : ι), P.shift (-u)
            (P.shift u a) = a) → (∀ (r : ι × ι), ∀ (p : ι × ι), ∀ (u : P.lattice), ∀ (v :
            P.lattice), (({P.shift u r.1, P.shift u r.2} : Set ι) = {p.1, p.2}) →
            ((({P.shift v r.1, P.shift v r.2} : Set ι) = {p.1, p.2}) → (u = v))) ) := by
  classical
  intro ι P shift_cancel r p u v hu hv
  have hh := congrArg (fun s : Set ι => P.shift (-v) '' s) (hu.trans hv.symm)
  have hfix : ({P.shift (-v + u) r.1, P.shift (-v + u) r.2} : Set ι) = {r.1, r.2} := by
    simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel,
      ← P.shift_add] using hh
  have hz := P3723T1ContactStabilizer P.toPeriodicTileCore (-v + u) r.1 r.2 hfix
  have hsub : u - v = 0 := by simpa only [sub_eq_add_neg, add_comm] using hz
  exact sub_eq_zero.mp hsub

private theorem transport_swap :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a),
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (representative_spec : ∀ (p : ι × ι), S.r (representative p) p),
        let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
        (∀ (p : ι × ι), ({P.shift (transport p) (representative p).1,
            P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2}) → ((∀ (r : ι × ι),
            ∀ (p : ι × ι), ∀ (u : P.lattice), ∀ (v : P.lattice), (({P.shift u r.1, P.shift u r.2}
            : Set ι) = {p.1, p.2}) → ((({P.shift v r.1, P.shift v r.2} : Set ι) = {p.1, p.2}) →
            (u = v))) → ((∀ (a : ι), ∀ (b : ι), representative (a, b) = representative (b, a)) →
            (∀ (a : ι), ∀ (b : ι), transport (a, b) = transport (b, a)))) ) := by
  classical
  intro ι P shift_cancel S representative representative_spec transport transport_spec
      transport_unique representative_swap a b
  apply transport_unique (representative (a, b)) (a, b)
  · exact transport_spec (a, b)
  · rw [representative_swap a b]
    exact (transport_spec (b, a)).trans (Set.pair_comm _ _)

private theorem representative_shift :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a),
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        (∀ (p : ι × ι), ∀ (q : ι × ι), (S.r p q) → (representative p = representative q)) → (∀ (u
            : P.lattice), ∀ (a : ι), ∀ (b : ι), representative (P.shift u a, P.shift u b) =
            representative (a, b)) ) := by
  classical
  intro ι P shift_cancel S representative representative_eq u a b
  apply (representative_eq (a, b) (P.shift u a, P.shift u b) ⟨u, rfl⟩).symm

private theorem transport_shift :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a),
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (representative_spec : ∀ (p : ι × ι), S.r (representative p) p),
        let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
        (∀ (p : ι × ι), ({P.shift (transport p) (representative p).1,
            P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2}) → ((∀ (r : ι × ι),
            ∀ (p : ι × ι), ∀ (u : P.lattice), ∀ (v : P.lattice), (({P.shift u r.1, P.shift u r.2}
            : Set ι) = {p.1, p.2}) → ((({P.shift v r.1, P.shift v r.2} : Set ι) = {p.1, p.2}) →
            (u = v))) → ((∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι), representative (P.shift u a,
            P.shift u b) = representative (a, b)) → (∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι),
            transport (P.shift u a, P.shift u b) = u + transport (a, b)))) ) := by
  classical
  intro ι P shift_cancel S representative representative_spec transport transport_spec
      transport_unique representative_shift u a b
  apply transport_unique (representative (a, b)) (P.shift u a, P.shift u b)
  · rw [← representative_shift u a b]
    exact transport_spec (P.shift u a, P.shift u b)
  · have hh := congrArg (fun s : Set ι => P.shift u '' s) (transport_spec (a, b))
    simpa only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] using hh

private theorem pair_contact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact
            P a b ↔ P3723T1EdgeContact P b a) → (∀ (a : ι), ∀ (b : ι), ∀ (c : ι), ∀ (d : ι),
            (({a, b} : Set ι) = {c, d}) → (P3723T1EdgeContact P a b ↔ P3723T1EdgeContact P c
            d)) ) := by
  classical
  intro ι P contact_symmetric a b c d h
  rcases Set.pair_eq_pair_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact contact_symmetric _ _

private theorem representative_contact :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a), (∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι),
            P3723T1EdgeContact P (P.shift u a) (P.shift u b) ↔
            P3723T1EdgeContact P a b) → (
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (representative_spec : ∀ (p : ι × ι), S.r (representative p) p),
        let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
        (∀ (p : ι × ι), ({P.shift (transport p) (representative p).1,
            P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2}) → ((∀ (a : ι), ∀
                (b : ι), ∀ (c : ι), ∀ (d : ι), (({a, b} : Set ι) = {c, d}) → (P3723T1EdgeContact P
            a b ↔ P3723T1EdgeContact P c d)) → (∀ (p : ι × ι), (P3723T1EdgeContact P p.1 p.2)
            → (P3723T1EdgeContact P (representative p).1 (representative p).2))))) := by
  classical
  intro ι P shift_cancel contact_periodic S representative representative_spec transport
      transport_spec pair_contact p hp
  apply (contact_periodic (transport p) _ _).mp
  exact (pair_contact _ _ _ _ (transport_spec p)).mpr hp

private theorem baseEdge_common :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let baseEdge (p : ι × ι) : Finset GaussianInt :=
          if hp : P3723T1EdgeContact P p.1 p.2 then Classical.choose hp.2 else ∅
        ∀ (p : ι × ι), (P3723T1EdgeContact P p.1 p.2) → (baseEdge p ∈ FootprintEdges (P.tile
            p.1) ∩ FootprintEdges (P.tile p.2)) ) := by
  classical
  intro ι P baseEdge p hp
  simp only [baseEdge, dite_eq_left hp]
  exact Classical.choose_spec hp.2

private theorem edge_common :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), ∀ (shift_cancel : ∀ (u : P.lattice), ∀ (a :
            ι), P.shift (-u) (P.shift u a) = a), (∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι), ∀ (e :
            Finset GaussianInt), (e ∈ FootprintEdges (P.tile a) ∩
            FootprintEdges (P.tile b)) → (e.image (fun z => z + (u : GaussianInt)) ∈
            FootprintEdges (P.tile (P.shift u a)) ∩ FootprintEdges (P.tile (P.shift u b)))) → (
        let S : Setoid (ι × ι) := {
          r := fun p q => ∃ u : P.lattice,
            ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
          iseqv := {
            refl := by
              intro p
              exact ⟨0, by simp only [P.shift_zero]⟩
            symm := by
              intro p q h
              obtain ⟨u, hu⟩ := h
              refine ⟨-u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
              simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
            trans := by
              intro p q r hpq hqr
              obtain ⟨u, hu⟩ := hpq
              obtain ⟨v, hv⟩ := hqr
              refine ⟨v + u, ?_⟩
              have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
              simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
              exact hh.trans hv
          }
        }
        let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
        ∀ (representative_spec : ∀ (p : ι × ι), S.r (representative p) p),
        let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
        (∀ (p : ι × ι), ({P.shift (transport p) (representative p).1,
            P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2}) → ((∀ (p : ι × ι),
                (P3723T1EdgeContact P p.1 p.2) → (P3723T1EdgeContact P (representative p).1
            (representative p).2)) → (
        let baseEdge (p : ι × ι) : Finset GaussianInt :=
          if hp : P3723T1EdgeContact P p.1 p.2 then Classical.choose hp.2 else ∅
        (∀ (p : ι × ι), (P3723T1EdgeContact P p.1 p.2) → (baseEdge p ∈ FootprintEdges (P.tile
            p.1) ∩ FootprintEdges (P.tile p.2))) → (
        let edge (a b : ι) : Finset GaussianInt :=
          if P3723T1EdgeContact P a b then
            (baseEdge (representative (a, b))).image
              (fun z => z + (transport (a, b) : GaussianInt))
          else ∅
        ∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (edge a b ∈ FootprintEdges (P.tile
            a) ∩ FootprintEdges (P.tile b))))))) := by
  classical
  intro ι P shift_cancel common_edge_transport S representative representative_spec transport
      transport_spec representative_contact baseEdge baseEdge_common edge a b hab
  have hh := common_edge_transport (transport (a, b))
    (representative (a, b)).1 (representative (a, b)).2 _
    (baseEdge_common _ (representative_contact (a, b) hab))
  simp only [edge, ite_eq_left hab]
  rcases Set.pair_eq_pair_iff.mp (transport_spec (a, b)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hh
    exact hh
  · rw [h1, h2] at hh
    exact ⟨hh.2, hh.1⟩

private theorem footprint_card :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (e.card = 2) ) := by
  classical
  intro T e he
  obtain ⟨x, hx, he⟩ := he
  have hone (z : GaussianInt) : z ≠ z + 1 := by
    intro h
    have hh := congrArg Zsqrtd.re h
    simp at hh
  have him (z : GaussianInt) : z ≠ z + ⟨0, 1⟩ := by
    intro h
    have hh := congrArg Zsqrtd.im h
    simp at hh
  rcases he with rfl | rfl | rfl | he
  · simp [hone]
  · simp [him]
  · simp [him]
  · have he' : e = {x + ⟨0, 1⟩, (x + ⟨0, 1⟩) + 1} := by
      simpa only [add_assoc, add_comm, add_left_comm] using he
    rw [he']
    simp [hone]

private theorem port_present :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        ∀ (edge : ι → ι → Finset GaussianInt),
        let port (a b : ι) : Option (Real × Real) :=
          if P3723T1EdgeContact P a b then some (midpoint (edge a b)) else none
        ∀ (a : ι), ∀ (b : ι), ∀ (p : Real × Real), (port a b = some p) → (P3723T1EdgeContact P
            a b ∧ midpoint (edge a b) = p) ) := by
  classical
  intro ι P midpoint edge port a b p hp
  by_cases h : P3723T1EdgeContact P a b
  · exact ⟨h, Option.some.inj (by simpa only [port, ite_eq_left h] using hp)⟩
  · simp only [port, ite_eq_right h] at hp
    cases hp

private theorem midpoint_periodic :
    (by
      classical
      exact
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        ∀ (e : Finset GaussianInt), ∀ (u : GaussianInt), (e.card = 2) → (midpoint (e.image (fun z
            => z + u)) = midpoint e + GaussianRealPoint u) ) := by
  classical
  intro midpoint e u he
  have hinj : Function.Injective (fun z : GaussianInt => z + u) :=
    fun _ _ h => add_right_cancel h
  dsimp [midpoint]
  rw [Finset.sum_image, Finset.sum_image]
  · simp only [Zsqrtd.re_add, Zsqrtd.im_add, Int.cast_add,
      Finset.sum_add_distrib, Finset.sum_const, he, nsmul_eq_mul,
      Nat.cast_ofNat, GaussianRealPoint]
    apply Prod.ext <;> dsimp <;> ring
  · exact hinj.injOn
  · exact hinj.injOn

private theorem hac :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι),
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → ((∀ (u : P.lattice), ∀ (a : ι), P.shift
            (-u) (P.shift u a) = a) → ((∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (P.shift u a) (P.shift u b)))
            → (∀ (a : ι), ∀ (b : ι), (P3723T1EdgeContact P a b) → (
        let c := P.shift (-period a) b
        P3723T1EdgeContact P (rep a) c)))) ) := by
  classical
  intro ι P rep rep_spec period period_spec shift_cancel contact_forward a b hab c
  have h := contact_forward (-period a) a b hab
  have ha : P.shift (-period a) a = rep a := by
    calc
      P.shift (-period a) a =
          P.shift (-period a) (P.shift (period a) (rep a)) :=
        congrArg (P.shift (-period a)) (period_spec a)
      _ = rep a := shift_cancel (period a) (rep a)
  rw [ha] at h
  exact h

end ContactPortGeometry


namespace ContactPortConstruction

private theorem finiteOrbitRepresentatives :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), Set.Finite {b |
            P3723T1EdgeContact P a b}) → (
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        (∀ (a : ι), a = P.shift (period a) (rep a)) → ((∀ (u : P.lattice), ∀ (a : ι), P.shift
            (-u) (P.shift u a) = a) → ((∀ (u : P.lattice), ∀ (a : ι), ∀ (b : ι),
            (P3723T1EdgeContact P a b) → (P3723T1EdgeContact P (P.shift u a) (P.shift u b)))
            → (∃ reps : Finset (ι × ι), (∀ e ∈ reps, P3723T1EdgeContact P e.1 e.2) ∧ (∀ a, ∀ b,
            P3723T1EdgeContact P a b → ∃ e ∈ reps, ∃ u : P.lattice, a = P.shift u e.1 ∧ b =
            P.shift u e.2))))) ) := by
  classical
  intro ι P finite_degree rep rep_spec period period_spec shift_cancel contact_forward
  -- Normalize the first index into the given finite vertex transversal.
  let reps : Finset (ι × ι) := P.vertexOrbitReps.biUnion fun r =>
    ((finite_degree r).toFinset).image (fun b => (r, b))
  refine ⟨reps, ?_, ?_⟩
  · intro e he
    obtain ⟨r, hr, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    exact (finite_degree r).mem_toFinset.mp hb
  · intro a b hab
    let c := P.shift (-period a) b
    have hac := ContactPortGeometry.hac ι P rep_spec period_spec shift_cancel contact_forward a
        b hab
    refine ⟨(rep a, c), Finset.mem_biUnion.mpr ⟨rep a, (rep_spec a).1,
      Finset.mem_image.mpr ⟨c, (finite_degree (rep a)).mem_toFinset.mpr hac, rfl⟩⟩,
      period a, period_spec a, ?_⟩
    dsimp [c]
    rw [← P.shift_add, add_neg_cancel, P.shift_zero]

private theorem portConstruction :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileComplex ι), (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (Disjoint
            (interior (TileRealization (P.tile a))) (TileRealization (P.tile b)))) → (
        let midpoint (e : Finset GaussianInt) : Real × Real :=
          ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
        (∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges (P.tile
            a) ∩ FootprintEdges (P.tile b)) → (midpoint e ∈ TileRealization (P.tile a) ∩
            TileRealization (P.tile b) ∧ ∀ c, midpoint e ∈ TileRealization (P.tile c) → c = a ∨ c
            = b))) → ((∀ (a : ι), ∀ (b : ι), (a ≠ b) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) → (midpoint e ∈ frontier
            (TileRealization (P.tile a)) ∩ frontier (TileRealization (P.tile b))))) → ((∀ (a :
            ι), Set.Finite {b | P3723T1EdgeContact P a b}) → (∀ (cells_nonempty : ∀ (a : ι),
            (P.tile a).cells.Nonempty),
        let cell (a : ι) : GaussianInt := Classical.choose (cells_nonempty a)
        let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
        ∀ (rep_spec : ∀ (a : ι), rep a ∈ P.vertexOrbitReps ∧ ∃ u : P.lattice, a = P.shift u (rep
            a)),
        let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
        let position (a : ι) : Real × Real :=
          GaussianRealPoint (cell (rep a) + (period a : GaussianInt)) + (1 / 2, 1 / 2)
        (∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P a b ↔ P3723T1EdgeContact P b a) → ((∀ (u
            : P.lattice), ∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P (P.shift u a) (P.shift u
            b) ↔ P3723T1EdgeContact P a b) → ((∀ (a : ι), ∃ z ∈ (P.tile a).cells, position a =
            GaussianRealPoint z + ((1 / 2 : Real), (1 / 2 : Real))) → ((∀ (a : ι), position a ∈
            interior (TileRealization (P.tile a))) → ((∀ (u : P.lattice), ∀ (a : ι), position
            (P.shift u a) = position a + GaussianRealPoint u) → (∀ (edge : ι → ι → Finset
            GaussianInt), (∀ (a : ι), ∀ (b : ι), P3723T1EdgeContact P a b → edge a b ∈
            FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) → ((∀ (a : ι), ∀ (b : ι),
            P3723T1EdgeContact P a b → (edge a b).card = (2 : ℕ)) → ((∀ (a : ι), ∀ (b : ι),
            edge a b = edge b a) → ((∀ (a : ι), ∀ (b : ι), ¬P3723T1EdgeContact P a b → edge a b
            = ∅) → ((∀ (u : ↥P.lattice), ∀ (a : ι), ∀ (b : ι), edge (P.shift u a) (P.shift u b) =
            Finset.image (fun (z : GaussianInt) => z + (↑u : GaussianInt)) (edge a b)) → (
        let port (a b : ι) : Option (Real × Real) :=
          if P3723T1EdgeContact P a b then some (midpoint (edge a b)) else none
        (∀ (a : ι), ∀ (b : ι), ∀ (p : Real × Real), (port a b = some p) → (P3723T1EdgeContact P
            a b ∧ midpoint (edge a b) = p)) → ((∀ (e : Finset GaussianInt), ∀ (u : GaussianInt),
            (e.card = 2) → (midpoint (e.image (fun z => z + u)) = midpoint e + GaussianRealPoint
            u)) → (∀ (reps : Finset (ι × ι)), (∀ e ∈ reps, P3723T1EdgeContact P e.1 e.2) → ((∀
            (a : ι), ∀ (b : ι), P3723T1EdgeContact P a b → ∃ e ∈ reps, ∃ (u : ↥P.lattice), a =
            P.shift u e.1 ∧ b = P.shift u e.2) → (Nonempty (P3723T1ContactPorts
            P))))))))))))))))))) ) := by
  classical
  intro ι P interior_disjoint midpoint common_midpoint common_frontier finite_degree
      cells_nonempty cell rep rep_spec period position contact_symmetric contact_periodic
      position_cell position_interior position_periodic edge edge_common edge_two edge_sym
      edge_absent edge_periodic port port_present midpoint_periodic reps reps_genuine reps_cover
  refine ⟨{
    position := position
    portEdge := edge
    port := port
    portEdge_symmetric := edge_sym
    port_symmetric := ?_
    portEdge_common := edge_common
    portEdge_two := edge_two
    port_midpoint := ?_
    port_eq_none_iff := ?_
    noncontact_has_no_portEdge := edge_absent
    position_cell := position_cell
    position_in_tile_interior := position_interior
    position_injective := ?_
    interior_disjoint_tiles := interior_disjoint
    port_frontier := ?_
    port_no_third := ?_
    port_owner_pair := ?_
    incident_ports_distinct := ?_
    finite_degree := finite_degree
    contactOrbitReps := reps
    contactOrbitReps_genuine := reps_genuine
    contact_orbit_representatives := reps_cover
    unordered_stabilizer := fun u a b h =>
      P3723T1ContactStabilizer P.toPeriodicTileCore u a b h
    contact_periodic := contact_periodic
    position_periodic := position_periodic
    portEdge_periodic := edge_periodic
    port_periodic := ?_
  }⟩
  · intro a b
    simp only [port, contact_symmetric a b, edge_sym a b]
  · intro a b hab
    simp only [port, ite_eq_left hab, midpoint]
  · intro a b
    simp only [port, ite_eq_right_iff, reduceCtorEq, imp_false]
  · intro a b heq
    by_contra hab
    exact Set.disjoint_left.mp (interior_disjoint a b hab) (position_interior a)
      (heq.symm ▸ interior_subset (position_interior b))
  · intro a b p hp
    obtain ⟨hab, rfl⟩ := port_present a b p hp
    exact common_frontier a b hab.1 (edge a b) (edge_common a b hab)
  · intro a b p hp c hca hcb hc
    obtain ⟨hab, hmid⟩ := port_present a b p hp
    rw [← hmid] at hc
    exact ((common_midpoint a b hab.1 (edge a b) (edge_common a b hab)).2 c hc).elim hca hcb
  · intro a b c d p hab hcd
    obtain ⟨h1, hm1⟩ := port_present a b p hab
    obtain ⟨h2, hm2⟩ := port_present c d p hcd
    have hp := (common_midpoint c d h2.1 (edge c d) (edge_common c d h2)).1
    rw [hm2, ← hm1] at hp
    have hc := (common_midpoint a b h1.1 (edge a b) (edge_common a b h1)).2 c hp.1
    have hd := (common_midpoint a b h1.1 (edge a b) (edge_common a b h1)).2 d hp.2
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact (h2.1 rfl).elim
    · rfl
    · exact Set.pair_comm _ _
    · exact (h2.1 rfl).elim
  · intro a b c p q hab hac hbc hpq
    obtain ⟨h1, hm1⟩ := port_present a b p hab
    obtain ⟨h2, hm2⟩ := port_present a c q hac
    have hc := (common_midpoint a c h2.1 (edge a c) (edge_common a c h2)).1.2
    rw [hm2, ← hpq, ← hm1] at hc
    have he := (common_midpoint a b h1.1 (edge a b) (edge_common a b h1)).2 c hc
    exact he.elim (fun h => h2.1 h.symm) (fun h => hbc h.symm)
  · intro u a b
    by_cases hab : P3723T1EdgeContact P a b
    · simp only [port, ite_eq_left hab, ite_eq_left ((contact_periodic u a b).mpr hab),
        edge_periodic, midpoint_periodic _ _ (edge_two a b hab), Option.map_some]
    · have hn : ¬ P3723T1EdgeContact P (P.shift u a) (P.shift u b) :=
        fun h => hab ((contact_periodic u a b).mp h)
      simp only [port, ite_eq_right hab, ite_eq_right hn, Option.map_none]

end ContactPortConstruction

theorem P3723T1ContactPortsExist {ι : Type} (P : PeriodicTileComplex ι) :
    Nonempty (P3723T1ContactPorts P) := by
-- BODY
  classical
  -- Unique cell ownership controls the square and midpoint geometry.
  have owner_unique := ContactPortGeometry.owner_unique ι P
  let openSquare (z : GaussianInt) : Set (Real × Real) :=
    Set.Ioo (z.re : Real) ((z.re : Real) + 1) ×ˢ
      Set.Ioo (z.im : Real) ((z.im : Real) + 1)
  have openSquare_open (z : GaussianInt) : IsOpen (openSquare z) :=
    isOpen_Ioo.prod isOpen_Ioo
  have openSquare_closure := ContactPortGeometry.openSquare_closure
  have coord_unique := ContactPortGeometry.coord_unique
  have square_unique := ContactPortGeometry.square_unique coord_unique
  have realization_closed (T : ProtoTile) : IsClosed (TileRealization T) :=
    isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  have interior_disjoint := ContactPortGeometry.interior_disjoint ι P owner_unique
      openSquare_closure square_unique
  have center_interior := ContactPortGeometry.center_interior ι P openSquare_open openSquare_closure
  let midpoint (e : Finset GaussianInt) : Real × Real :=
    ((∑ z ∈ e, (z.re : Real)) / 2, (∑ z ∈ e, (z.im : Real)) / 2)
  have horizontal_midpoint := ContactPortGeometry.horizontal_midpoint
  have vertical_midpoint := ContactPortGeometry.vertical_midpoint
  have edge_normal := ContactPortGeometry.edge_normal
  have midpoint_cell := ContactPortGeometry.midpoint_cell horizontal_midpoint vertical_midpoint
  have midpoint_two_cells := ContactPortGeometry.midpoint_two_cells coord_unique
      horizontal_midpoint vertical_midpoint edge_normal
  have common_midpoint := ContactPortGeometry.common_midpoint ι P owner_unique midpoint_cell
      midpoint_two_cells
  have common_frontier := ContactPortGeometry.common_frontier ι P realization_closed
      interior_disjoint common_midpoint
  have footprint_finite := ContactPortGeometry.footprint_finite
  have finite_degree := ContactPortGeometry.finite_degree ι P midpoint_cell common_midpoint
      footprint_finite
  have cells_nonempty (a : ι) : (P.tile a).cells.Nonempty :=
    (LatticeTileGridStructure (P.tile a) (P.tiles_are_disks a)).1.1
  let cell (a : ι) : GaussianInt := Classical.choose (cells_nonempty a)
  have cell_mem (a : ι) : cell a ∈ (P.tile a).cells :=
    Classical.choose_spec (cells_nonempty a)
  let rep (a : ι) : ι := Classical.choose (P.vertex_orbit_representatives a).exists
  have rep_spec (a : ι) : rep a ∈ P.vertexOrbitReps ∧
      ∃ u : P.lattice, a = P.shift u (rep a)  := ContactPortGeometry.rep_spec ι P a
  let period (a : ι) : P.lattice := Classical.choose (rep_spec a).2
  have period_spec (a : ι) : a = P.shift (period a) (rep a) :=
    Classical.choose_spec (rep_spec a).2
  let position (a : ι) : Real × Real :=
    GaussianRealPoint (cell (rep a) + (period a : GaussianInt)) + (1 / 2, 1 / 2)
  have contact_symmetric (a b : ι) :
      P3723T1EdgeContact P a b ↔ P3723T1EdgeContact P b a :=
          PeriodicEdgeContactSymmetry.symmetric ι P a b
  have shift_cancel (u : P.lattice) (a : ι) : P.shift (-u) (P.shift u a) = a := by
    rw [← P.shift_add, neg_add_cancel, P.shift_zero]
  have shift_injective := ContactPortGeometry.shift_injective ι P shift_cancel
  have edges_periodic := ContactPortGeometry.edges_periodic ι P
  have common_edge_transport (u : P.lattice) (a b : ι) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) :
      e.image (fun z => z + (u : GaussianInt)) ∈
        FootprintEdges (P.tile (P.shift u a)) ∩ FootprintEdges (P.tile (P.shift u b)) :=
            ContactPortGeometry.common_edge_transport ι P edges_periodic u a b e he
  have contact_forward := ContactPortGeometry.contact_forward ι P shift_injective
      common_edge_transport
  have contact_periodic (u : P.lattice) (a b : ι) :
      P3723T1EdgeContact P (P.shift u a) (P.shift u b) ↔
        P3723T1EdgeContact P a b := ContactPortGeometry.contact_periodic ι P shift_cancel
            contact_forward u a b
  have period_unique := ContactPortGeometry.period_unique ι P shift_cancel
  have rep_shift := ContactPortGeometry.rep_shift ι P rep_spec period_spec
  have period_shift := ContactPortGeometry.period_shift ι P rep_spec period_spec period_unique
      rep_shift
  have real_add := ContactPortGeometry.real_add
  have position_cell (a : ι) : ∃ z ∈ (P.tile a).cells,
      position a = GaussianRealPoint z + ((1 / 2 : Real), (1 / 2 : Real)) :=
          ContactPortGeometry.position_cell ι P cells_nonempty cell_mem rep_spec period_spec a
  have position_interior (a : ι) : position a ∈ interior (TileRealization (P.tile a)) :=
      ContactPortGeometry.position_interior ι P center_interior cells_nonempty rep_spec
      position_cell a
  have position_periodic := ContactPortGeometry.position_periodic ι P cells_nonempty rep_spec
      rep_shift period_shift real_add
  obtain ⟨edge, edge_common, edge_two, edge_sym, edge_absent, edge_periodic⟩ :
      ∃ edge : ι → ι → Finset GaussianInt,
        (∀ a b, P3723T1EdgeContact P a b →
          edge a b ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) ∧
        (∀ a b, P3723T1EdgeContact P a b → (edge a b).card = 2) ∧
        (∀ a b, edge a b = edge b a) ∧
        (∀ a b, ¬ P3723T1EdgeContact P a b → edge a b = ∅) ∧
        (∀ u : P.lattice, ∀ a b,
          edge (P.shift u a) (P.shift u b) =
            (edge a b).image (fun z => z + (u : GaussianInt))) := by
    -- Identify both orientations and all simultaneous translates before choosing an edge.
    let S : Setoid (ι × ι) := {
      r := fun p q => ∃ u : P.lattice,
        ({P.shift u p.1, P.shift u p.2} : Set ι) = {q.1, q.2}
      iseqv := {
        refl := by
          intro p
          exact ⟨0, by simp only [P.shift_zero]⟩
        symm := by
          intro p q h
          obtain ⟨u, hu⟩ := h
          refine ⟨-u, ?_⟩
          have hh := congrArg (fun s : Set ι => P.shift (-u) '' s) hu
          simpa only [Set.image_insert_eq, Set.image_singleton, shift_cancel] using hh.symm
        trans := by
          intro p q r hpq hqr
          obtain ⟨u, hu⟩ := hpq
          obtain ⟨v, hv⟩ := hqr
          refine ⟨v + u, ?_⟩
          have hh := congrArg (fun s : Set ι => P.shift v '' s) hu
          simp only [Set.image_insert_eq, Set.image_singleton, ← P.shift_add] at hh
          exact hh.trans hv
      }
    }
    let representative (p : ι × ι) : ι × ι := (Quotient.mk S p).out
    have representative_spec (p : ι × ι) : S.r (representative p) p :=
      @Quotient.mk_out _ S p
    have representative_eq (p q : ι × ι) (h : S.r p q) :
        representative p = representative q := ContactPortGeometry.representative_eq ι P
            shift_cancel p q h
    let transport (p : ι × ι) : P.lattice := Classical.choose (representative_spec p)
    have transport_spec (p : ι × ι) :
        ({P.shift (transport p) (representative p).1,
          P.shift (transport p) (representative p).2} : Set ι) = {p.1, p.2} :=
              ContactPortGeometry.transport_spec ι P shift_cancel representative_spec p
    have transport_unique := ContactPortGeometry.transport_unique ι P shift_cancel
    have representative_swap (a b : ι) : representative (a, b) = representative (b, a) :=
      representative_eq _ _ ⟨0, by simp only [P.shift_zero]; exact Set.pair_comm _ _⟩
    have transport_swap (a b : ι) : transport (a, b) = transport (b, a) :=
        ContactPortGeometry.transport_swap ι P shift_cancel representative_spec transport_spec
        transport_unique representative_swap a b
    have representative_shift (u : P.lattice) (a b : ι) :
        representative (P.shift u a, P.shift u b) = representative (a, b) :=
            ContactPortGeometry.representative_shift ι P shift_cancel representative_eq u a b
    have transport_shift (u : P.lattice) (a b : ι) :
        transport (P.shift u a, P.shift u b) = u + transport (a, b) :=
            ContactPortGeometry.transport_shift ι P shift_cancel representative_spec
            transport_spec transport_unique representative_shift u a b
    have pair_contact := ContactPortGeometry.pair_contact ι P contact_symmetric
    have representative_contact (p : ι × ι) (hp : P3723T1EdgeContact P p.1 p.2) :
        P3723T1EdgeContact P (representative p).1 (representative p).2 :=
            ContactPortGeometry.representative_contact ι P shift_cancel contact_periodic
            representative_spec transport_spec pair_contact p hp
    let baseEdge (p : ι × ι) : Finset GaussianInt :=
      if hp : P3723T1EdgeContact P p.1 p.2 then Classical.choose hp.2 else ∅
    have baseEdge_common (p : ι × ι) (hp : P3723T1EdgeContact P p.1 p.2) :
        baseEdge p ∈ FootprintEdges (P.tile p.1) ∩ FootprintEdges (P.tile p.2)  :=
            ContactPortGeometry.baseEdge_common ι P p hp
    let edge (a b : ι) : Finset GaussianInt :=
      if P3723T1EdgeContact P a b then
        (baseEdge (representative (a, b))).image
          (fun z => z + (transport (a, b) : GaussianInt))
      else ∅
    have edge_common := ContactPortGeometry.edge_common ι P shift_cancel common_edge_transport
        representative_spec transport_spec representative_contact baseEdge_common
    have footprint_card := ContactPortGeometry.footprint_card
    refine ⟨edge, edge_common, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact footprint_card (P.tile a) (edge a b) (edge_common a b hab).1
    · intro a b
      by_cases hab : P3723T1EdgeContact P a b
      · have hba := (contact_symmetric a b).mp hab
        simp only [edge, ite_eq_left hab, ite_eq_left hba, representative_swap a b,
            transport_swap a b]
      · have hba : ¬ P3723T1EdgeContact P b a := fun h => hab ((contact_symmetric a b).mpr h)
        simp only [edge, ite_eq_right hab, ite_eq_right hba]
    · intro a b hab
      simp only [edge, ite_eq_right hab]
    · intro u a b
      by_cases hab : P3723T1EdgeContact P a b
      · simp only [edge, ite_eq_left hab, ite_eq_left ((contact_periodic u a b).mpr hab),
          representative_shift, transport_shift, Finset.image_image, AddSubgroup.coe_add]
        congr 1
        funext z
        dsimp only [Function.comp_def]
        abel
      · have hn : ¬ P3723T1EdgeContact P (P.shift u a) (P.shift u b) :=
          fun h => hab ((contact_periodic u a b).mp h)
        simp only [edge, ite_eq_right hab, ite_eq_right hn, Finset.image_empty]
  let port (a b : ι) : Option (Real × Real) :=
    if P3723T1EdgeContact P a b then some (midpoint (edge a b)) else none
  have port_present := ContactPortGeometry.port_present ι P edge
  have midpoint_periodic (e : Finset GaussianInt) (u : GaussianInt) (he : e.card = 2) :
      midpoint (e.image (fun z => z + u)) = midpoint e + GaussianRealPoint u :=
          ContactPortGeometry.midpoint_periodic e u he
  have finiteOrbitRepresentatives : ∃ reps : Finset (ι × ι),
      (∀ e ∈ reps, P3723T1EdgeContact P e.1 e.2) ∧
      (∀ a b, P3723T1EdgeContact P a b →
        ∃ e ∈ reps, ∃ u : P.lattice, a = P.shift u e.1 ∧ b = P.shift u e.2) :=
            ContactPortConstruction.finiteOrbitRepresentatives ι P finite_degree rep_spec
            period_spec shift_cancel contact_forward
  obtain ⟨reps, reps_genuine, reps_cover⟩ := finiteOrbitRepresentatives
  have portConstruction :
    Nonempty (P3723T1ContactPorts P) := ContactPortConstruction.portConstruction ι P
        interior_disjoint common_midpoint common_frontier finite_degree cells_nonempty rep_spec
        contact_symmetric contact_periodic position_cell position_interior position_periodic edge
        edge_common edge_two edge_sym edge_absent edge_periodic port_present midpoint_periodic
        reps reps_genuine reps_cover
  exact portConstruction


end ApollonianSuperharmonic

end
