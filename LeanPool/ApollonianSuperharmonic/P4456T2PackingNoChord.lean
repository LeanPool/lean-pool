/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileReflectionFormulas
public import LeanPool.ApollonianSuperharmonic.OpenLatticeEdge
public import LeanPool.ApollonianSuperharmonic.FourNeighborAdjacent
public import Mathlib.Topology.Algebra.Ring.Real

-- [TABLET NODE: P4456T2PackingNoChord]

/-!
# P4456T2PackingNoChord

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PackingChordConstruction

private noncomputable abbrev NoChord (T : ProtoTile) : Prop := by
  classical
  exact ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)

private noncomputable abbrev q : Real × Real → Real × Real := by
  classical
  exact fun p => (-p.2, p.1)

private noncomputable abbrev r : Real × Real → Real × Real := by
  classical
  exact fun p => (p.1, -p.2)

private noncomputable abbrev qh : (Real × Real) ≃ₜ (Real × Real) := by
  classical
  let q : Real × Real → Real × Real := fun p => (-p.2, p.1)
  exact {
    toEquiv := {
      toFun := q
      invFun := fun p => (p.2, -p.1)
      left_inv := by intro p; simp [q]
      right_inv := by intro p; simp [q]
    }
    continuous_toFun := by
      exact Continuous.prodMk (continuous_neg.comp continuous_snd) continuous_fst
    continuous_invFun := by
      exact Continuous.prodMk continuous_snd (continuous_neg.comp continuous_fst)
  }

private noncomputable abbrev rh : (Real × Real) ≃ₜ (Real × Real) := by
  classical
  let r : Real × Real → Real × Real := fun p => (p.1, -p.2)
  exact {
    toEquiv := {
      toFun := r
      invFun := r
      left_inv := by intro p; simp [r]
      right_inv := by intro p; simp [r]
    }
    continuous_toFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
    continuous_invFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
  }

private theorem transport (T U : ProtoTile) (f : GaussianInt → GaussianInt)
      (H : (Real × Real) ≃ₜ (Real × Real))
      (hb : BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T)
      (ha : ∀ x y, FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (f x) (f y))
      (he : ∀ x y, OpenLatticeEdge (f x) (f y) =
        H '' OpenLatticeEdge x y)
      (hr : TileRealization U = H '' TileRealization T) :
      (NoChord) T ↔ (NoChord) U := by
  classical
  let NoChord (T : ProtoTile) : Prop :=
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)
  change (NoChord T ↔ NoChord U)
  have hc (x y : GaussianInt) :
      (OpenLatticeEdge x y ⊆ interior (TileRealization T)) ↔
      (OpenLatticeEdge (f x) (f y) ⊆ interior (TileRealization U)) := by
    rw [he, hr, (H.image_interior _).symm]
    constructor
    · intro h p hp
      obtain ⟨z, hz, rfl⟩ := (Set.mem_image H (OpenLatticeEdge x y) p).1 hp
      exact Set.mem_image_of_mem H (h hz)
    · intro h p hp
      obtain ⟨q, hq, hpq⟩ := h (Set.mem_image_of_mem H hp)
      have : q = p := H.injective hpq
      simpa [this] using hq
  constructor
  · intro h x y hxy hx hy hchord
    obtain ⟨x₀, hx₀, hxEq⟩ := (Set.mem_image f (BoundaryFootprintVertices T) x).1 (hb ▸ hx)
    obtain ⟨y₀, hy₀, hyEq⟩ := (Set.mem_image f (BoundaryFootprintVertices T) y).1 (hb ▸ hy)
    have hxy0 : FourNeighborAdjacent (f x₀) (f y₀) := by
      simpa [hxEq, hyEq] using hxy
    have hchord0 : OpenLatticeEdge (f x₀) (f y₀) ⊆
        interior (TileRealization U) := by
      simpa [hxEq, hyEq] using hchord
    exact h x₀ y₀ ((ha x₀ y₀).2 hxy0) hx₀ hy₀ ((hc x₀ y₀).2 hchord0)
  · intro h x y hxy hx hy hchord
    apply h (f x) (f y) ((ha x y).1 hxy)
    · rw [hb]
      exact ⟨x, hx, rfl⟩
    · rw [hb]
      exact ⟨y, hy, rfl⟩
    · exact (hc x y).1 hchord

private theorem qadj (x y : GaussianInt) :
      FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (GaussianQuarterTurn x) (GaussianQuarterTurn y) := by
  classical
  have q1 (z : GaussianInt) : GaussianQuarterTurn (z + 1) = GaussianQuarterTurn z + ⟨0, 1⟩ := by
    ext <;> simp [GaussianQuarterTurn]
  have qm1 (z : GaussianInt) : GaussianQuarterTurn (z - 1) = GaussianQuarterTurn z - ⟨0, 1⟩ := by
    ext <;> simp [GaussianQuarterTurn]
  have qi (z : GaussianInt) : GaussianQuarterTurn (z + ⟨0, 1⟩) = GaussianQuarterTurn z - 1 := by
    ext <;> simp [GaussianQuarterTurn]; ring
  have qmi (z : GaussianInt) : GaussianQuarterTurn (z - ⟨0, 1⟩) = GaussianQuarterTurn z + 1 := by
    ext <;> simp [GaussianQuarterTurn]; ring
  have qsq (z : GaussianInt) : GaussianQuarterTurn (GaussianQuarterTurn z) = -z := by
    ext <;> simp [GaussianQuarterTurn]
  have negAdj : FourNeighborAdjacent (-x) (-y) ↔ FourNeighborAdjacent x y := by
    constructor
    · intro h
      rcases h with h | h | h | h
      · right; left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · right; right; right; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · right; right; left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
    · intro h
      rcases h with h | h | h | h
      · right; left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · right; right; right; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
      · right; right; left; have := congrArg Neg.neg h; simpa [add_comm, sub_eq_add_neg] using this
  have fwd (a b : GaussianInt) : FourNeighborAdjacent a b →
      FourNeighborAdjacent (GaussianQuarterTurn a) (GaussianQuarterTurn b) := by
    intro h
    rcases h with h | h | h | h
    · rw [h, q1]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [h, qm1]
      exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h, qi]
      exact Or.inr (Or.inl rfl)
    · rw [h, qmi]
      exact Or.inl rfl
  refine ⟨fwd x y, ?_⟩
  intro h
  have h₂ := fwd (GaussianQuarterTurn x) (GaussianQuarterTurn y) h
  exact negAdj.mp (by simpa [qsq] using h₂)

private theorem radj (x y : GaussianInt) :
      FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (GaussianReflection x) (GaussianReflection y) := by
  classical
  have r1 (z : GaussianInt) : GaussianReflection (z + 1) = GaussianReflection z + 1 := by
    ext <;> simp [GaussianReflection]
  have rm1 (z : GaussianInt) : GaussianReflection (z - 1) = GaussianReflection z - 1 := by
    ext <;> simp [GaussianReflection]
  have ri (z : GaussianInt) : GaussianReflection (z + ⟨0, 1⟩) = GaussianReflection z - ⟨0, 1⟩ := by
    ext <;> simp [GaussianReflection]; ring
  have rmi (z : GaussianInt) : GaussianReflection (z - ⟨0, 1⟩) = GaussianReflection z + ⟨0, 1⟩ := by
    ext <;> simp [GaussianReflection]; ring
  have rinv (z : GaussianInt) : GaussianReflection (GaussianReflection z) = z := by
    ext <;> simp [GaussianReflection]
  have fwd (a b : GaussianInt) : FourNeighborAdjacent a b →
      FourNeighborAdjacent (GaussianReflection a) (GaussianReflection b) := by
    intro h
    rcases h with h | h | h | h
    · rw [h, r1]; exact Or.inl rfl
    · rw [h, rm1]; exact Or.inr (Or.inl rfl)
    · rw [h, ri]; exact Or.inr (Or.inr (Or.inr rfl))
    · rw [h, rmi]; exact Or.inr (Or.inr (Or.inl rfl))
  refine ⟨fwd x y, ?_⟩
  intro h
  have h₂ := fwd (GaussianReflection x) (GaussianReflection y) h
  simpa [rinv] using h₂

private theorem qedge (x y : GaussianInt) :
      OpenLatticeEdge (GaussianQuarterTurn x) (GaussianQuarterTurn y) =
        (qh) '' OpenLatticeEdge x y := by
  classical
  let q : Real × Real → Real × Real := fun p => (-p.2, p.1)
  let qh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := q
      invFun := fun p => (p.2, -p.1)
      left_inv := by intro p; simp [q]
      right_inv := by intro p; simp [q]
    }
    continuous_toFun := by
      exact Continuous.prodMk (continuous_neg.comp continuous_snd) continuous_fst
    continuous_invFun := by
      exact Continuous.prodMk continuous_snd (continuous_neg.comp continuous_fst)
  }
  change (OpenLatticeEdge (GaussianQuarterTurn x) (GaussianQuarterTurn y) =
        qh '' OpenLatticeEdge x y)
  ext p
  simp only [OpenLatticeEdge, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨t, ht, ht1, hp⟩
    refine ⟨(1 - t) • GaussianRealPoint x + t • GaussianRealPoint y,
      ⟨t, ht, ht1, rfl⟩, ?_⟩
    rw [hp]
    simp [qh, q, GaussianRealPoint, GaussianQuarterTurn]; ring
  · rintro ⟨z, ⟨t, ht, ht1, hp⟩, hpz⟩
    refine ⟨t, ht, ht1, ?_⟩
    have hz : z = (1 - t) • GaussianRealPoint x + t • GaussianRealPoint y := hp
    subst z
    rw [← hpz]
    simp [qh, q, GaussianRealPoint, GaussianQuarterTurn]; ring

private theorem redge (x y : GaussianInt) :
      OpenLatticeEdge (GaussianReflection x) (GaussianReflection y) =
        (rh) '' OpenLatticeEdge x y := by
  classical
  let r : Real × Real → Real × Real := fun p => (p.1, -p.2)
  let rh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := r
      invFun := r
      left_inv := by intro p; simp [r]
      right_inv := by intro p; simp [r]
    }
    continuous_toFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
    continuous_invFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
  }
  change (OpenLatticeEdge (GaussianReflection x) (GaussianReflection y) =
        rh '' OpenLatticeEdge x y)
  ext p
  simp only [OpenLatticeEdge, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨t, ht, ht1, hp⟩
    refine ⟨(1 - t) • GaussianRealPoint x + t • GaussianRealPoint y,
      ⟨t, ht, ht1, rfl⟩, ?_⟩
    rw [hp]
    simp [rh, r, GaussianRealPoint, GaussianReflection]; ring
  · rintro ⟨z, ⟨t, ht, ht1, hp⟩, hpz⟩
    refine ⟨t, ht, ht1, ?_⟩
    have hz : z = (1 - t) • GaussianRealPoint x + t • GaussianRealPoint y := hp
    subst z
    rw [← hpz]
    simp [rh, r, GaussianRealPoint, GaussianReflection]; ring

private theorem qturn (transport : ∀ (T U : ProtoTile) (f : GaussianInt → GaussianInt) (H : ℝ × ℝ
    ≃ₜ ℝ × ℝ),
  BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T →
    (∀ (x y : LatticeCell), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (f x) (f y)) →
      (∀ (x y : GaussianInt), OpenLatticeEdge (f x) (f y) = ⇑H '' OpenLatticeEdge x y) →
        TileRealization U = ⇑H '' TileRealization T → ((NoChord) T ↔ (NoChord) U)) (qadj : ∀ (x y
            : GaussianInt), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (GaussianQuarterTurn
            x) (GaussianQuarterTurn y)) (qedge : ∀ (x y : GaussianInt), OpenLatticeEdge
            (GaussianQuarterTurn x) (GaussianQuarterTurn y) = ⇑(qh) '' OpenLatticeEdge x y) (T :
            ProtoTile) :
      (NoChord) T ↔ (NoChord) (TileQuarterTurn T) := by
  classical
  let NoChord (T : ProtoTile) : Prop :=
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)
  let q : Real × Real → Real × Real := fun p => (-p.2, p.1)
  let qh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := q
      invFun := fun p => (p.2, -p.1)
      left_inv := by intro p; simp [q]
      right_inv := by intro p; simp [q]
    }
    continuous_toFun := by
      exact Continuous.prodMk (continuous_neg.comp continuous_snd) continuous_fst
    continuous_invFun := by
      exact Continuous.prodMk continuous_snd (continuous_neg.comp continuous_fst)
  }
  change (∀ (T U : ProtoTile) (f : GaussianInt → GaussianInt) (H : ℝ × ℝ ≃ₜ ℝ × ℝ),
  BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T →
    (∀ (x y : LatticeCell), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (f x) (f y)) →
      (∀ (x y : GaussianInt), OpenLatticeEdge (f x) (f y) = ⇑H '' OpenLatticeEdge x y) →
        TileRealization U = ⇑H '' TileRealization T → (NoChord T ↔ NoChord U)) at transport
  change (∀ (x y : GaussianInt), OpenLatticeEdge (GaussianQuarterTurn x) (GaussianQuarterTurn y)
      = ⇑qh '' OpenLatticeEdge x y) at qedge
  change (NoChord T ↔ NoChord (TileQuarterTurn T))
  apply transport T (TileQuarterTurn T) GaussianQuarterTurn qh
  · exact (TileQuarterTurnFormulas T).2.2.2.2.2.2.2.1
  · exact qadj
  · exact qedge
  · exact (TileQuarterTurnFormulas T).2.2.2.1

private theorem rturn (transport : ∀ (T U : ProtoTile) (f : GaussianInt → GaussianInt) (H : ℝ × ℝ
    ≃ₜ ℝ × ℝ),
  BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T →
    (∀ (x y : LatticeCell), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (f x) (f y)) →
      (∀ (x y : GaussianInt), OpenLatticeEdge (f x) (f y) = ⇑H '' OpenLatticeEdge x y) →
        TileRealization U = ⇑H '' TileRealization T → ((NoChord) T ↔ (NoChord) U)) (radj : ∀ (x y
            : GaussianInt), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (GaussianReflection
            x) (GaussianReflection y)) (redge : ∀ (x y : GaussianInt), OpenLatticeEdge
            (GaussianReflection x) (GaussianReflection y) = ⇑(rh) '' OpenLatticeEdge x y) (T :
            ProtoTile) :
      (NoChord) T ↔ (NoChord) (TileReflection T) := by
  classical
  let NoChord (T : ProtoTile) : Prop :=
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)
  let r : Real × Real → Real × Real := fun p => (p.1, -p.2)
  let rh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := r
      invFun := r
      left_inv := by intro p; simp [r]
      right_inv := by intro p; simp [r]
    }
    continuous_toFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
    continuous_invFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
  }
  change (∀ (T U : ProtoTile) (f : GaussianInt → GaussianInt) (H : ℝ × ℝ ≃ₜ ℝ × ℝ),
  BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T →
    (∀ (x y : LatticeCell), FourNeighborAdjacent x y ↔ FourNeighborAdjacent (f x) (f y)) →
      (∀ (x y : GaussianInt), OpenLatticeEdge (f x) (f y) = ⇑H '' OpenLatticeEdge x y) →
        TileRealization U = ⇑H '' TileRealization T → (NoChord T ↔ NoChord U)) at transport
  change (∀ (x y : GaussianInt), OpenLatticeEdge (GaussianReflection x) (GaussianReflection y) =
      ⇑rh '' OpenLatticeEdge x y) at redge
  change (NoChord T ↔ NoChord (TileReflection T))
  apply transport T (TileReflection T) GaussianReflection rh
  · exact (TileReflectionFormulas T).2.2.2.2.2.2.2.1
  · exact radj
  · exact redge
  · exact (TileReflectionFormulas T).2.2.2.1

end PackingChordConstruction

theorem P4456T2PackingNoChord (g : BandPackingSymmetry) (T : ProtoTile) :
    (∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)) ↔
    (∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices (BandPackingSymmetryTileAction g T) →
      y ∈ BoundaryFootprintVertices (BandPackingSymmetryTileAction g T) →
      ¬ OpenLatticeEdge x y ⊆
        interior (TileRealization (BandPackingSymmetryTileAction g T))) := by
-- BODY
  let NoChord (T : ProtoTile) : Prop :=
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T)
  let q : Real × Real → Real × Real := fun p => (-p.2, p.1)
  let r : Real × Real → Real × Real := fun p => (p.1, -p.2)
  let qh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := q
      invFun := fun p => (p.2, -p.1)
      left_inv := by intro p; simp [q]
      right_inv := by intro p; simp [q]
    }
    continuous_toFun := by
      exact Continuous.prodMk (continuous_neg.comp continuous_snd) continuous_fst
    continuous_invFun := by
      exact Continuous.prodMk continuous_snd (continuous_neg.comp continuous_fst)
  }
  let rh : (Real × Real) ≃ₜ (Real × Real) := {
    toEquiv := {
      toFun := r
      invFun := r
      left_inv := by intro p; simp [r]
      right_inv := by intro p; simp [r]
    }
    continuous_toFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
    continuous_invFun := by
      exact Continuous.prodMk continuous_fst (continuous_neg.comp continuous_snd)
  }
  have transport (T U : ProtoTile) (f : GaussianInt → GaussianInt)
      (H : (Real × Real) ≃ₜ (Real × Real))
      (hb : BoundaryFootprintVertices U = f '' BoundaryFootprintVertices T)
      (ha : ∀ x y, FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (f x) (f y))
      (he : ∀ x y, OpenLatticeEdge (f x) (f y) =
        H '' OpenLatticeEdge x y)
      (hr : TileRealization U = H '' TileRealization T) :
      NoChord T ↔ NoChord U := PackingChordConstruction.transport T U f H hb ha he hr
  have qadj (x y : GaussianInt) :
      FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (GaussianQuarterTurn x) (GaussianQuarterTurn y) :=
            PackingChordConstruction.qadj x y
  have radj (x y : GaussianInt) :
      FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (GaussianReflection x) (GaussianReflection y) :=
            PackingChordConstruction.radj x y
  have qedge (x y : GaussianInt) :
      OpenLatticeEdge (GaussianQuarterTurn x) (GaussianQuarterTurn y) =
        qh '' OpenLatticeEdge x y := PackingChordConstruction.qedge x y
  have redge (x y : GaussianInt) :
      OpenLatticeEdge (GaussianReflection x) (GaussianReflection y) =
        rh '' OpenLatticeEdge x y := PackingChordConstruction.redge x y
  have qturn (T : ProtoTile) :
      NoChord T ↔ NoChord (TileQuarterTurn T) := PackingChordConstruction.qturn transport qadj
          qedge T
  have rturn (T : ProtoTile) :
      NoChord T ↔ NoChord (TileReflection T) := PackingChordConstruction.rturn transport radj
          redge T
  change NoChord T ↔ NoChord (BandPackingSymmetryTileAction g T)
  induction g generalizing T with
  | identity => simp [BandPackingSymmetryTileAction]
  | shift w => simp [BandPackingSymmetryTileAction]
  | negate => exact qturn T
  | conjugate =>
      change NoChord T ↔ NoChord
        (TileQuarterTurn (TileQuarterTurn (TileReflection T)))
      exact (rturn T).trans ((qturn (TileReflection T)).trans
        (qturn (TileQuarterTurn (TileReflection T))))
  | comp g h ihg ihh =>
      change NoChord T ↔ NoChord
        (BandPackingSymmetryTileAction g (BandPackingSymmetryTileAction h T))
      exact (ihh T).trans (ihg (BandPackingSymmetryTileAction h T))

end ApollonianSuperharmonic

end
