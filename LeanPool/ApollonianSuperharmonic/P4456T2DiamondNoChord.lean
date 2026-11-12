/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4456T2EdgeInterior
public import LeanPool.ApollonianSuperharmonic.DiamondCellDomain
public import LeanPool.ApollonianSuperharmonic.P4456T2VertexInterior
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCellRows
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4456T2DiamondNoChord]

/-!
# P4456T2DiamondNoChord

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondNoChordProof

private theorem hcell :
    ∀ (k : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), (T.cells = (TileTranslation (DiamondTile
        k) w).cells) → (((TileTranslation (DiamondTile k) w).cells = (DiamondCellDomain k).image
        (GaussianTranslation w)) → (∀ (c : GaussianInt), c ∈ T.cells ↔ c - w ∈ DiamondCellDomain
        k)) := by
  classical
  intro k w T hcells htrans c
  rw [hcells, htrans]
  change c ∈ (DiamondCellDomain k).image (GaussianTranslation w) ↔ _
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨a, ha, heq⟩
    have : a = c - w := by
      have := congrArg (fun z : GaussianInt => z - w) heq
      simpa [GaussianTranslation, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using this
    simpa [this] using ha
  · intro hc
    apply Finset.mem_image.mpr
    refine ⟨c - w, hc, ?_⟩
    simp [GaussianTranslation, sub_eq_add_neg, add_comm]

private theorem hstar :
    ∀ (k : Nat), ∀ (w : GaussianInt), ∀ (T : ProtoTile), ∀ (x : LatticeCell), ∀ (y :
        LatticeCell), (x ∈ BoundaryFootprintVertices T) → ((y ∈ BoundaryFootprintVertices T) →
        ((∀ (c : GaussianInt), c ∈ T.cells ↔ c - w ∈ DiamondCellDomain k) → ((T.cells.Nonempty) →
        ((∀ (v : GaussianInt), (v ∈ BoundaryFootprintVertices T) → (v ∈ FootprintVertices T)) →
        (∀ (p : GaussianInt), p = x ∨ p = y → (∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (p
        - w) j ∈ DiamondCellDomain k) → p ∉ BoundaryFootprintVertices T))))) := by
  classical
  intro k w T x y hx hy hcell hnonempty hvertex p hp hs
  have hsT : ∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ T.cells := by
    intro j
    have heq : LatticeVertexIncidentCell (p - w) j + w =
        LatticeVertexIncidentCell p j := by
      fin_cases j <;> simp [LatticeVertexIncidentCell, sub_eq_add_neg,
        add_assoc, add_comm] <;> abel
    rw [← heq, hcell]
    simpa [sub_sub] using hs j
  have hpfoot : p ∈ FootprintVertices T := by
    rcases hp with h | h
    · rw [h]
      exact hvertex x hx
    · rw [h]
      exact hvertex y hy
  exact (P4456T2VertexInterior T hnonempty p hpfoot).2.mpr hsT

private theorem growUp :
    ∀ (k : Nat), (∀ q ∈ DiamondCellDomain k, (0 : ℤ) ≤ q.im ∧ q.im < (2 : ℤ) * (↑k : ℤ) ∧ -(q.im
        + (1 : ℤ)) ≤ q.re ∧ q.re < q.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑k : ℤ) - q.im) ≤ q.re ∧ q.re <
        (2 : ℤ) * (↑k : ℤ) - q.im) → (∀ q ∈ DiamondCellDomain k, q + (1 : GaussianInt) ∈
        DiamondCellDomain k → q.im < (↑k : ℤ) → ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (q
        + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) j ∈ DiamondCellDomain k) := by
  classical
  intro k rowFacts q hq hq1 hb
  have hr := rowFacts q hq
  have hr1 := rowFacts (q + 1) (by simpa using hq1)
  have hup : q + ⟨0,1⟩ ∈ DiamondCellDomain k := by
    apply (P4194T1DiamondCellRows k (q + ⟨0,1⟩)).1.mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one,
      ] at hr hr1 ⊢
    omega
  have hup1 : q + 1 + ⟨0,1⟩ ∈ DiamondCellDomain k := by
    apply (P4194T1DiamondCellRows k (q + 1 + ⟨0,1⟩)).1.mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one,
      ] at hr hr1 ⊢
    omega
  intro j
  fin_cases j
  · simpa [LatticeVertexIncidentCell] using hup1
  · have heq : q + 1 + ⟨0,1⟩ - 1 = q + ⟨0,1⟩ := by abel
    simpa [LatticeVertexIncidentCell, heq] using hup
  · have heq : q + 1 + ⟨0,1⟩ - 1 - ⟨0,1⟩ = q := by abel
    simpa [LatticeVertexIncidentCell, heq] using hq
  · have heq : q + 1 + ⟨0,1⟩ - ⟨0,1⟩ = q + 1 := by abel
    simpa [LatticeVertexIncidentCell, heq] using hq1

private theorem growDown :
    ∀ (k : Nat), (∀ q ∈ DiamondCellDomain k, (0 : ℤ) ≤ q.im ∧ q.im < (2 : ℤ) * (↑k : ℤ) ∧ -(q.im
        + (1 : ℤ)) ≤ q.re ∧ q.re < q.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑k : ℤ) - q.im) ≤ q.re ∧ q.re <
        (2 : ℤ) * (↑k : ℤ) - q.im) → (∀ q ∈ DiamondCellDomain k, q + (1 : GaussianInt) ∈
        DiamondCellDomain k → (↑k : ℤ) ≤ q.im → ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell (q
        + (1 : GaussianInt)) j ∈ DiamondCellDomain k) := by
  classical
  intro k rowFacts q hq hq1 hb
  have hr := rowFacts q hq
  have hr1 := rowFacts (q + 1) (by simpa using hq1)
  have hdown : q - ⟨0,1⟩ ∈ DiamondCellDomain k := by
    apply (P4194T1DiamondCellRows k (q - ⟨0,1⟩)).1.mpr
    simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
      Zsqrtd.im_add, Zsqrtd.re_one, Zsqrtd.im_one,
      ] at hr hr1 ⊢
    omega
  have hdown1 : q + 1 - ⟨0,1⟩ ∈ DiamondCellDomain k := by
    apply (P4194T1DiamondCellRows k (q + 1 - ⟨0,1⟩)).1.mpr
    simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
      Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
      ] at hr hr1 ⊢
    omega
  intro j
  fin_cases j
  · simpa [LatticeVertexIncidentCell] using hq1
  · have heq : q + 1 - 1 = q := by abel
    simpa [LatticeVertexIncidentCell, heq] using hq
  · have heq : q + 1 - 1 - ⟨0,1⟩ = q - ⟨0,1⟩ := by abel
    simpa [LatticeVertexIncidentCell, heq] using hdown
  · have heq : q + 1 - ⟨0,1⟩ = q + 1 - ⟨0,1⟩ := rfl
    simpa [LatticeVertexIncidentCell, heq] using hdown1

private theorem horizontalStar :
    ∀ (k : Nat), (∀ q ∈ DiamondCellDomain k, (0 : ℤ) ≤ q.im ∧ q.im < (2 : ℤ) * (↑k : ℤ) ∧ -(q.im
        + (1 : ℤ)) ≤ q.re ∧ q.re < q.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑k : ℤ) - q.im) ≤ q.re ∧ q.re <
        (2 : ℤ) * (↑k : ℤ) - q.im) → (∀ q ∈ DiamondCellDomain k, q + ⟨(0 : ℤ), (1 : ℤ)⟩ ∈
        DiamondCellDomain k → ∃ (p : GaussianInt), (p = q + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ p = q + (1 :
        GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ ∀ (j : Fin (4 : ℕ)), LatticeVertexIncidentCell p j ∈
        DiamondCellDomain k) := by
  classical
  intro k rowFacts q hq hqi
  have hr := rowFacts q hq
  have hr1 := rowFacts (q + ⟨0,1⟩) (by simpa using hqi)
  simp only [Zsqrtd.re_add, Zsqrtd.im_add,
    ] at hr hr1
  rcases hr with ⟨hb0, hbN, hlo1, hhi1, hlo2, hhi2⟩
  rcases hr1 with ⟨hb10, hb1N, hlo11, hhi11, hlo12, hhi12⟩
  let m : Int := if q.im < (k : Int) then q.im + 1 else 2 * (k : Int) - q.im - 1
  have hmrange : -m ≤ q.re ∧ q.re < m := by
    dsimp [m]
    by_cases hb : q.im < (k : Int) <;> simp [hb] at * <;> omega
  have hmpos : 0 < m := by
    dsimp [m]
    by_cases hb : q.im < (k : Int) <;> simp [hb] at * <;> omega
  have hright (ha : q.re = -m) :
      ∀ j : Fin 4, LatticeVertexIncidentCell (q + 1 + ⟨0,1⟩) j ∈
        DiamondCellDomain k := by
    have hq1 : q + 1 ∈ DiamondCellDomain k := by
      apply (P4194T1DiamondCellRows k (q + 1)).1.mpr
      simp only [Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_one, Zsqrtd.im_one,
        ]
      by_cases hb : q.im < (k : Int)
      · have hm : m = q.im + 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
      · have hm : m = 2 * (k : Int) - q.im - 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
    have hqi1 : q + ⟨0,1⟩ + 1 ∈ DiamondCellDomain k := by
      apply (P4194T1DiamondCellRows k (q + ⟨0,1⟩ + 1)).1.mpr
      simp only [Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_one, Zsqrtd.im_one,
        ]
      by_cases hb : q.im < (k : Int)
      · have hm : m = q.im + 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
      · have hm : m = 2 * (k : Int) - q.im - 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
    intro j
    fin_cases j
    · simpa [LatticeVertexIncidentCell, add_assoc, add_comm, add_left_comm] using hqi1
    · have heq : q + 1 + ⟨0,1⟩ - 1 = q + ⟨0,1⟩ := by abel
      simpa [LatticeVertexIncidentCell, heq] using hqi
    · have heq : q + 1 + ⟨0,1⟩ - 1 - ⟨0,1⟩ = q := by abel
      simpa [LatticeVertexIncidentCell, heq] using hq
    · have heq : q + 1 + ⟨0,1⟩ - ⟨0,1⟩ = q + 1 := by abel
      simpa [LatticeVertexIncidentCell, heq] using hq1
  have hleft (ha : -m < q.re) :
      ∀ j : Fin 4, LatticeVertexIncidentCell (q + ⟨0,1⟩) j ∈
        DiamondCellDomain k := by
    have hqm : q - 1 ∈ DiamondCellDomain k := by
      apply (P4194T1DiamondCellRows k (q - 1)).1.mpr
      simp only [Zsqrtd.re_sub,
        Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
        ]
      by_cases hb : q.im < (k : Int)
      · have hm : m = q.im + 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
      · have hm : m = 2 * (k : Int) - q.im - 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
    have hqim : q + ⟨0,1⟩ - 1 ∈ DiamondCellDomain k := by
      apply (P4194T1DiamondCellRows k (q + ⟨0,1⟩ - 1)).1.mpr
      simp only [Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub,
        Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
        ]
      by_cases hb : q.im < (k : Int)
      · have hm : m = q.im + 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
      · have hm : m = 2 * (k : Int) - q.im - 1 := by simp [m, hb]
        rw [hm] at ha hmrange
        omega
    intro j
    fin_cases j
    · simpa [LatticeVertexIncidentCell] using hqi
    · have heq : q + ⟨0,1⟩ - 1 = q - 1 + ⟨0,1⟩ := by abel
      simpa [LatticeVertexIncidentCell, heq] using hqim
    · have heq : q + ⟨0,1⟩ - 1 - ⟨0,1⟩ = q - 1 := by abel
      simpa [LatticeVertexIncidentCell, heq] using hqm
    · have heq : q + ⟨0,1⟩ - ⟨0,1⟩ = q := by abel
      simpa [LatticeVertexIncidentCell, heq] using hq
  by_cases ha : q.re = -m
  · exact ⟨q + 1 + ⟨0,1⟩, Or.inr rfl, hright ha⟩
  · have ha' : -m < q.re := by omega
    exact ⟨q + ⟨0,1⟩, Or.inl rfl, hleft ha'⟩

private theorem hpcoordsAt386 :
    ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (r : GaussianInt),
    let p : GaussianInt := r + w
    r = z - w + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ r = z - w + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ → p = z +
        ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ p = z + (1 : GaussianInt) + ⟨(0 : ℤ), (1 : ℤ)⟩ := by
  classical
  intro w z r p hr'
  dsimp [p]
  rcases hr' with h | h
  · left
    rw [h]
    abel
  · right
    rw [h]
    abel

end DiamondNoChordProof

theorem P4456T2DiamondNoChord (k : Nat) (hk : 0 < k)
    (w : GaussianInt) (T : ProtoTile)
    (hcells : T.cells = (TileTranslation (DiamondTile k) w).cells) :
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T) := by
-- BODY
  classical
  intro x y hxy hx hy hinside
  have htrans : (TileTranslation (DiamondTile k) w).cells =
      (DiamondCellDomain k).image (GaussianTranslation w) := by
    exact (TileTranslationFormulas (DiamondTile k) w).1
  have hcell (c : GaussianInt) : c ∈ T.cells ↔ c - w ∈ DiamondCellDomain k :=
      DiamondNoChordProof.hcell k w T hcells htrans c
  have hnonempty : T.cells.Nonempty := by
    rw [hcells, htrans]
    apply Finset.image_nonempty.mpr
    refine ⟨0, ?_⟩
    have hzero : (0 : GaussianInt) ∈ DiamondCellDomain k := by
      rw [(P4194T1DiamondCellRows k 0).1]
      norm_num
      omega
    exact hzero
  have hvertex (v : GaussianInt) (hv : v ∈ BoundaryFootprintVertices T) :
      v ∈ FootprintVertices T := by
    unfold BoundaryFootprintVertices at hv
    rw [ite_eq_left hnonempty] at hv
    rcases hv with ⟨e, he, hv⟩
    unfold BoundaryFootprintEdges at he
    rcases he with ⟨z, hz⟩
    rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      simp [FootprintVertices, hnonempty] <;> aesop
  obtain ⟨z, v, hform⟩ := P4397T1UnitEdgeCells.1 x y hxy
  let A : ProtoTile := ⟨{z}, z⟩
  let B : ProtoTile := ⟨{v}, v⟩
  have hzv : z ≠ v := by
    intro heq
    rcases hform with ⟨_, hvform⟩ | ⟨_, hvform⟩
    · rw [hvform] at heq
      have := congrArg Zsqrtd.re heq
      norm_num at this
    · rw [hvform] at heq
      have := congrArg Zsqrtd.im heq
      norm_num at this
  have hA : ({x,y} : Finset GaussianInt) ∈ FootprintEdges A := by
    exact (P4397T1UnitEdgeCells.2 x y z v hform A).1.mpr (by simp [A])
  have hB : ({x,y} : Finset GaussianInt) ∈ FootprintEdges B := by
    exact (P4397T1UnitEdgeCells.2 x y z v hform B).1.mpr (by simp [B])
  have hinc : z ∈ T.cells ∧ v ∈ T.cells :=
    (P4456T2EdgeInterior T x y z v hxy hzv hA hB).1 hinside
  have hza := hinc.1
  have hva := hinc.2
  have hstar (p : GaussianInt) (hp : p = x ∨ p = y)
      (hs : ∀ j : Fin 4, LatticeVertexIncidentCell (p - w) j ∈ DiamondCellDomain k) :
      p ∉ BoundaryFootprintVertices T := DiamondNoChordProof.hstar k w T x y hx hy hcell
          hnonempty hvertex p hp hs
  have rowFacts (q : GaussianInt) (hq : q ∈ DiamondCellDomain k) :=
    (P4194T1DiamondCellRows k q).1.mp hq
  have growUp (q : GaussianInt) (hq : q ∈ DiamondCellDomain k)
      (hq1 : q + 1 ∈ DiamondCellDomain k) (hb : q.im < (k : Int)) :
      ∀ j : Fin 4, LatticeVertexIncidentCell (q + 1 + ⟨0,1⟩) j ∈
        DiamondCellDomain k := DiamondNoChordProof.growUp k rowFacts q hq hq1 hb
  have growDown (q : GaussianInt) (hq : q ∈ DiamondCellDomain k)
      (hq1 : q + 1 ∈ DiamondCellDomain k) (hb : (k : Int) ≤ q.im) :
      ∀ j : Fin 4, LatticeVertexIncidentCell (q + 1) j ∈
        DiamondCellDomain k := DiamondNoChordProof.growDown k rowFacts q hq hq1 hb
  have horizontalStar (q : GaussianInt) (hq : q ∈ DiamondCellDomain k)
      (hqi : q + ⟨0,1⟩ ∈ DiamondCellDomain k) :
      ∃ p, (p = q + ⟨0,1⟩ ∨ p = q + 1 + ⟨0,1⟩) ∧
        ∀ j : Fin 4, LatticeVertexIncidentCell p j ∈ DiamondCellDomain k :=
            DiamondNoChordProof.horizontalStar k rowFacts q hq hqi
  rcases hform with ⟨hor, hvform⟩ | ⟨hor, hvform⟩
  · have hq : z - w ∈ DiamondCellDomain k := hcell z |>.mp hza
    have hq1 : (z - w) + 1 ∈ DiamondCellDomain k := by
      have heq : v - w = (z - w) + 1 := by rw [hvform]; abel
      rw [← heq]
      exact hcell v |>.mp hva
    by_cases hb : (z - w).im < (k : Int)
    · let p : GaussianInt := ((z - w) + 1 + ⟨0,1⟩) + w
      have hpcoords : (z - w) + 1 + ⟨0,1⟩ + w = z + 1 + ⟨0,1⟩ := by
        abel
      have hpends : p = x ∨ p = y := by
        dsimp [p]
        rw [hpcoords]
        rcases hor with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
        · exact Or.inr hy'.symm
        · exact Or.inl hx'.symm
      have hs := growUp (z - w) hq hq1 hb
      have hnot := hstar p hpends (by
        have hcalc : p - w = (z - w) + 1 + ⟨0,1⟩ := by dsimp [p]; abel
        simpa [hcalc] using hs)
      rcases hpends with hp | hp
      · exact hnot (by simpa [hp] using hx)
      · exact hnot (by simpa [hp] using hy)
    · let p : GaussianInt := ((z - w) + 1) + w
      have hpcoords : (z - w) + 1 + w = z + 1 := by abel
      have hpends : p = x ∨ p = y := by
        dsimp [p]
        rw [hpcoords]
        rcases hor with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
        · exact Or.inl hx'.symm
        · exact Or.inr hy'.symm
      have hs := growDown (z - w) hq hq1 (le_of_not_gt hb)
      have hnot := hstar p hpends (by
        have hcalc : p - w = (z - w) + 1 := by dsimp [p]; abel
        simpa [hcalc] using hs)
      rcases hpends with hp | hp
      · exact hnot (by simpa [hp] using hx)
      · exact hnot (by simpa [hp] using hy)
  · have hq : z - w ∈ DiamondCellDomain k := hcell z |>.mp hza
    have hqi : (z - w) + ⟨0,1⟩ ∈ DiamondCellDomain k := by
      have heq : v - w = (z - w) + ⟨0,1⟩ := by rw [hvform]; abel
      rw [← heq]
      exact hcell v |>.mp hva
    obtain ⟨r, hr, hstarR⟩ := horizontalStar (z - w) hq hqi
    let p : GaussianInt := r + w
    have hpcoords (hr' : r = (z - w) + ⟨0,1⟩ ∨
        r = (z - w) + 1 + ⟨0,1⟩) :
        p = z + ⟨0,1⟩ ∨ p = z + 1 + ⟨0,1⟩ := DiamondNoChordProof.hpcoordsAt386 w z r hr'
    have hpends : p = x ∨ p = y := by
      have hcoord := hpcoords hr
      rcases hor with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
      · rcases hcoord with h | h
        · exact Or.inr (h.trans hy'.symm)
        · exact Or.inl (h.trans hx'.symm)
      · rcases hcoord with h | h
        · exact Or.inl (h.trans hx'.symm)
        · exact Or.inr (h.trans hy'.symm)
    have hnot := hstar p hpends (by
      have hcalc : p - w = r := by dsimp [p]; abel
      simpa [hcalc] using hstarR)
    rcases hpends with hp | hp
    · exact hnot (by simpa [hp] using hx)
    · exact hnot (by simpa [hp] using hy)

end ApollonianSuperharmonic

end
