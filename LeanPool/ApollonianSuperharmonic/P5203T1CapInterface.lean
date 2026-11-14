/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.DiamondFootprintCoordinates

public import LeanPool.ApollonianSuperharmonic.P5124T1BoundaryGeometry
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P5203T1CapInterface]

/-!
# P5203T1CapInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CapInterfaceProof


private theorem bounds :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → ((∀ (z : GaussianInt), z ∈ FootprintVertices (DiamondTile k)
            ↔ 0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ -(k : Int) ≤ z.re ∧ z.re ≤ k ∧ -(z.im + 1) ≤ z.re
            ∧ z.re ≤ z.im + 1 ∧ -(2 * (k : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im
            + 1) → (
        let D := DiamondTile k
        (∀ (w : GaussianInt), ∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation
            D w) ↔ z - w ∈ BoundaryFootprintVertices D) → (∀ (w : GaussianInt), ∀ (z :
            GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation D w) → (0 : ℤ) ≤ (z -
            w).im ∧ (z - w).im ≤ (2 : ℤ) * (↑k : ℤ) ∧ -(↑k : ℤ) ≤ (z - w).re ∧ (z - w).re ≤ (↑k :
            ℤ) ∧ -((z - w).im + (1 : ℤ)) ≤ (z - w).re ∧ (z - w).re ≤ (z - w).im + (1 : ℤ) ∧ -((2
            : ℤ) * (↑k : ℤ) - (z - w).im + (1 : ℤ)) ≤ (z - w).re ∧ (z - w).re ≤ (2 : ℤ) * (↑k :
            ℤ) - (z - w).im + (1 : ℤ))))
    ) := by
  classical
  intro k hk footprint D boundary_local w z hz
  apply (footprint (z - w)).mp
  apply (P4194T1DiamondVertexIncidence k hk (z - w)).1.mpr
  exact ((P4194T1DiamondVertexIncidence k hk (z - w)).2.mp
    ((boundary_local w z).mp hz)).1

private theorem hv :
    (by
      classical
      exact
        ∀ (k : Nat), ∀ (u : GaussianInt),
        let D := DiamondTile k
        let d : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let T := TileTranslation D u
        let U := TileTranslation D (u + d)
        let V : Set GaussianInt := {z | (z - u).im = 2 * (k : Int) ∧
          -1 ≤ (z - u).re ∧ (z - u).re ≤ 1}
        (∀ (w : GaussianInt), ∀ (z : GaussianInt), (z ∈ BoundaryFootprintVertices
            (TileTranslation D w)) → (0 ≤ (z - w).im ∧ (z - w).im ≤ 2 * (k : Int) ∧ -(k : Int) ≤
            (z - w).re ∧ (z - w).re ≤ k ∧ -((z - w).im + 1) ≤ (z - w).re ∧ (z - w).re ≤ (z -
            w).im + 1 ∧ -(2 * (k : Int) - (z - w).im + 1) ≤ (z - w).re ∧ (z - w).re ≤ 2 * (k :
            Int) - (z - w).im + 1)) → ((∀ (a : Int), (-1 ≤ a) → ((a < 1) → (({u + ⟨a,
            2 * (k : Int)⟩, u + ⟨a + 1, 2 * (k : Int)⟩} : Finset GaussianInt) ∈
            BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U))) → ((∀ (e : Finset
            GaussianInt), (e ∈ BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) → (∀ (z :
            GaussianInt), (z ∈ e) → (z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices
            U))) → ((∀ (z : GaussianInt), ((z - u).im = 2 * (k : Int)) → (z = u + ⟨(z - u).re, 2
            * (k : Int)⟩)) → (BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V))))
    ) := by
  classical
  intro k u D d T U V bounds common endpoint place
  ext z
  constructor
  · intro hz
    have hT := bounds u z hz.1
    have hU := bounds (u + d) z hz.2
    change (z - u).im = 2 * (k : Int) ∧ -1 ≤ (z - u).re ∧ (z - u).re ≤ 1
    simp only [Zsqrtd.im_sub, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.re_add,
      d] at hT hU ⊢
    omega
  · intro hz
    have hz' : (z - u).im = 2 * (k : Int) ∧
        -1 ≤ (z - u).re ∧ (z - u).re ≤ 1 := hz
    have eqz := place z hz'.1
    rcases (show (z - u).re = -1 ∨ (z - u).re = 0 ∨ (z - u).re = 1 by omega) with
      hx | hx | hx
    · apply endpoint _ (common (-1) (by omega) (by omega)) z
      exact Finset.mem_insert.mpr (Or.inl (by simpa only [hx] using eqz))
    · apply endpoint _ (common 0 (by omega) (by omega)) z
      exact Finset.mem_insert.mpr (Or.inl (by simpa only [hx] using eqz))
    · apply endpoint _ (common 0 (by omega) (by omega)) z
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (by simpa only [hx, zero_add] using eqz)))

private theorem he :
    (by
      classical
      exact
        ∀ (k : Nat), ∀ (u : GaussianInt),
        let D := DiamondTile k
        let d : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let T := TileTranslation D u
        let U := TileTranslation D (u + d)
        let V : Set GaussianInt := {z | (z - u).im = 2 * (k : Int) ∧
          -1 ≤ (z - u).re ∧ (z - u).re ≤ 1}
        let E : Set (Finset GaussianInt) := {e | ∃ a : Int, -1 ≤ a ∧ a < 1 ∧
          e = {u + ⟨a, 2 * (k : Int)⟩, u + ⟨a + 1, 2 * (k : Int)⟩}}
        (∀ (a : Int), (-1 ≤ a) → ((a < 1) → (({u + ⟨a, 2 * (k : Int)⟩, u + ⟨a + 1,
            2 * (k : Int)⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∩
            BoundaryFootprintEdges U))) → ((∀ (e : Finset GaussianInt), (e ∈
            BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U) → (∀ (z : GaussianInt), (z ∈ e)
            → (z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U))) → ((∀ (z :
            GaussianInt), ((z - u).im = 2 * (k : Int)) → (z = u + ⟨(z - u).re, 2 * (k : Int)⟩)) →
            ((BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V) →
            (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E))))
    ) := by
  classical
  intro k u D d T U V E common endpoint place hv
  ext e
  constructor
  · intro hh
    have ep (z : GaussianInt) (hz : z ∈ e) :
        (z - u).im = 2 * (k : Int) ∧ -1 ≤ (z - u).re ∧ (z - u).re ≤ 1 := by
      have := endpoint e hh z hz
      rw [hv] at this
      exact this
    obtain ⟨z, hz⟩ := hh.1
    rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have h0 := ep z (by simp)
      have h1 := ep (z + 1) (by simp)
      refine ⟨(z - u).re, h0.2.1, ?_, ?_⟩
      · simp only [Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_one] at h0 h1 ⊢
        omega
      · have eqz := place z h0.1
        have eqz' : z + 1 = u + ⟨(z - u).re + 1, 2 * (k : Int)⟩ := by
          convert place (z + 1) h1.1 using 1;
            simp [Zsqrtd.re_sub, Zsqrtd.re_add]; ring
        exact congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) eqz eqz'
    · have h0 := ep z (by simp)
      have h1 := ep (z + ⟨0, 1⟩) (by simp)
      simp only [Zsqrtd.im_sub, Zsqrtd.im_add] at h0 h1
      omega
  · rintro ⟨a, ha, ha', rfl⟩
    exact common a ha ha'

private theorem vert :
    (by
      classical
      exact
        ∀ (k : Nat), ∀ (u : GaussianInt),
        let V : Set GaussianInt := {z | (z - u).im = 2 * (k : Int) ∧
          -1 ≤ (z - u).re ∧ (z - u).re ≤ 1}
        (∀ (z : GaussianInt), ((z - u).im = 2 * (k : Int)) → (z = u + ⟨(z - u).re, 2 * (k :
            Int)⟩)) → (
        let p0 : GaussianInt := u + ⟨-1, 2 * (k : Int)⟩
        let p1 : GaussianInt := u + ⟨0, 2 * (k : Int)⟩
        let p2 : GaussianInt := u + ⟨1, 2 * (k : Int)⟩
        V = ({p0, p1, p2} : Set GaussianInt))
    ) := by
  classical
  intro k u V place p0 p1 p2
  ext z
  simp only [V, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hz
    have eqz := place z hz.1
    rcases (show (z - u).re = -1 ∨ (z - u).re = 0 ∨ (z - u).re = 1 by omega) with
      hx | hx | hx
    · exact Or.inl (by simpa only [hx] using eqz)
    · exact Or.inr (Or.inl (by simpa only [hx] using eqz))
    · exact Or.inr (Or.inr (by simpa only [hx] using eqz))
  · rintro (rfl | rfl | rfl) <;> simp [p0, p1, p2]

end CapInterfaceProof

theorem P5203T1CapInterface (k : Nat) (hk : 0 < k) (u : GaussianInt) :
    let T := TileTranslation (DiamondTile k) u
    let U := TileTranslation (DiamondTile k) (u + ⟨0, 2 * (k : Int)⟩)
    let V : Set GaussianInt := {z | (z - u).im = 2 * (k : Int) ∧
      -1 ≤ (z - u).re ∧ (z - u).re ≤ 1}
    let E : Set (Finset GaussianInt) := {e | ∃ a : Int, -1 ≤ a ∧ a < 1 ∧
      e = {u + ⟨a, 2 * (k : Int)⟩, u + ⟨a + 1, 2 * (k : Int)⟩}}
    T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
      BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V ∧
      BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E ∧
      SimpleGridPath V E := by
-- BODY
  classical
  have footprint (z : GaussianInt) :
      z ∈ FootprintVertices (DiamondTile k) ↔
        0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧
        -(k : Int) ≤ z.re ∧ z.re ≤ k ∧
        -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
        -(2 * (k : Int) - z.im + 1) ≤ z.re ∧
          z.re ≤ 2 * (k : Int) - z.im + 1 := DiamondFootprintCoordinates.coordinates k hk z
  let D := DiamondTile k
  let d : GaussianInt := ⟨0, 2 * (k : Int)⟩
  let T := TileTranslation D u
  let U := TileTranslation D (u + d)
  let V : Set GaussianInt := {z | (z - u).im = 2 * (k : Int) ∧
    -1 ≤ (z - u).re ∧ (z - u).re ≤ 1}
  let E : Set (Finset GaussianInt) := {e | ∃ a : Int, -1 ≤ a ∧ a < 1 ∧
    e = {u + ⟨a, 2 * (k : Int)⟩, u + ⟨a + 1, 2 * (k : Int)⟩}}
  change T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
    BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V ∧
    BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E ∧ SimpleGridPath V E
  have cell (w z : GaussianInt) :
      z ∈ (TileTranslation D w).cells ↔ z - w ∈ DiamondCellDomain k :=
    TileTranslationProperties.mem_cells (DiamondTile k) w z
  have ne (w : GaussianInt) : (TileTranslation D w).cells.Nonempty := by
    refine ⟨w, (cell w w).mpr ?_⟩
    rw [sub_self]
    exact (P4194T1DiamondCellRows k 0).1.mpr (by norm_num; omega)
  have disj : Disjoint T.cells U.cells := by
    apply Finset.disjoint_left.mpr
    intro z hT hU
    have hT := (P4194T1DiamondCellRows k (z - u)).1.mp ((cell u z).mp hT)
    have hU := (P4194T1DiamondCellRows k (z - (u + d))).1.mp
      ((cell (u + d) z).mp hU)
    simp only [Zsqrtd.im_sub, Zsqrtd.im_add, d] at hT hU
    omega
  have boundary_local (w z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation D w) ↔
        z - w ∈ BoundaryFootprintVertices D := by
    rw [(TileTranslationFormulas D w).2.2.2.2.2.2.2.1]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [GaussianTranslation] using hx
    · intro hz
      exact ⟨z - w, hz, by simp [GaussianTranslation]⟩
  have bounds (w z : GaussianInt)
      (hz : z ∈ BoundaryFootprintVertices (TileTranslation D w)) :
      0 ≤ (z - w).im ∧ (z - w).im ≤ 2 * (k : Int) ∧
      -(k : Int) ≤ (z - w).re ∧ (z - w).re ≤ k ∧
      -((z - w).im + 1) ≤ (z - w).re ∧ (z - w).re ≤ (z - w).im + 1 ∧
      -(2 * (k : Int) - (z - w).im + 1) ≤ (z - w).re ∧
        (z - w).re ≤ 2 * (k : Int) - (z - w).im + 1 := CapInterfaceProof.bounds k hk footprint
            boundary_local w z hz
  have horizontal (w : GaussianInt) (a b : Int) (ha : -1 ≤ a) (ha' : a < 1)
      (hb : b = 0 ∨ b = 2 * (k : Int)) :
      ({w + ⟨a, b⟩, w + ⟨a + 1, b⟩} : Finset GaussianInt) ∈
        BoundaryFootprintEdges (TileTranslation D w) := by
    rw [(TileTranslationFormulas D w).2.2.2.2.2.2.2.2]
    refine ⟨{⟨a, b⟩, ⟨a + 1, b⟩}, ?_, ?_⟩
    · rw [(P5124T1BoundaryGeometry k hk).1]
      exact ⟨a, b, Or.inl ⟨Or.inl ⟨hb, ha, ha'⟩, rfl⟩⟩
    · simp [GaussianTranslation, add_comm]
  have common (a : Int) (ha : -1 ≤ a) (ha' : a < 1) :
      ({u + ⟨a, 2 * (k : Int)⟩, u + ⟨a + 1, 2 * (k : Int)⟩} :
        Finset GaussianInt) ∈ BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U := by
    refine ⟨horizontal u a _ ha ha' (Or.inr rfl), ?_⟩
    have hz (x : Int) : (u + d) + (⟨x, 0⟩ : GaussianInt) =
        u + ⟨x, 2 * (k : Int)⟩ := by ext <;> simp [d]
    simpa only [hz] using horizontal (u + d) a 0 ha ha' (Or.inl rfl)
  have endpoint (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U)
      (z : GaussianInt) (hz : z ∈ e) :
      z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U := by
    exact ⟨by rw [BoundaryFootprintVertices, ite_eq_left (ne u)]; exact ⟨e, he.1, hz⟩,
      by rw [BoundaryFootprintVertices, ite_eq_left (ne (u + d))]; exact ⟨e, he.2, hz⟩⟩
  have place (z : GaussianInt) (hy : (z - u).im = 2 * (k : Int)) :
      z = u + ⟨(z - u).re, 2 * (k : Int)⟩ := by
    apply Zsqrtd.ext
    · simp
    · change z.im = u.im + 2 * (k : Int)
      change z.im - u.im = 2 * (k : Int) at hy
      omega
  have hv : BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V := CapInterfaceProof.hv
      k u bounds common endpoint place
  have he : BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E := CapInterfaceProof.he k u
      common endpoint place hv
  let p0 : GaussianInt := u + ⟨-1, 2 * (k : Int)⟩
  let p1 : GaussianInt := u + ⟨0, 2 * (k : Int)⟩
  let p2 : GaussianInt := u + ⟨1, 2 * (k : Int)⟩
  have hp0 : p1 = p0 + 1 := by ext <;> simp [p0, p1]
  have hp1 : p2 = p1 + 1 := by ext <;> simp [p1, p2]
  have vert : V = ({p0, p1, p2} : Set GaussianInt) := CapInterfaceProof.vert k u place
  have edge (e : Finset GaussianInt) : e ∈ E ↔ e = {p0, p1} ∨ e = {p1, p2} := by
    constructor
    · rintro ⟨a, ha, ha', rfl⟩
      rcases (show a = -1 ∨ a = 0 by omega) with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨-1, by omega, by omega, rfl⟩
      · exact ⟨0, by omega, by omega, rfl⟩
  have chain : [p0, p1, p2].IsChain (fun x y =>
      (x = p0 ∧ y = p1) ∨ (x = p1 ∧ y = p2)) := by
    simp
  refine ⟨ne u, ne (u + d), disj, hv, he, [p0, p1, p2], ?_, by simp, ?_, ?_, ?_⟩
  · simp [p0, p1, p2, Zsqrtd.ext_iff]
  · rw [vert]
    ext z
    simp
  · intro x y l r h
    rcases List.isChain_iff_forall_rel_of_append_cons_cons.mp chain h with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hp0
    · exact Or.inl hp1
  · intro e
    rw [edge]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨p0, p1, [], [p2], rfl, rfl⟩
      · exact ⟨p1, p2, [p0], [], rfl, rfl⟩
    · rintro ⟨x, y, l, r, h, rfl⟩
      rcases List.isChain_iff_forall_rel_of_append_cons_cons.mp chain h with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl

end ApollonianSuperharmonic

end
