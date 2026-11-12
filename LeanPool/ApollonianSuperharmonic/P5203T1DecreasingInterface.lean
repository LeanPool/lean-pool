/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondVertexIncidence
public import LeanPool.ApollonianSuperharmonic.P5124T1BoundaryGeometry
public import LeanPool.ApollonianSuperharmonic.P5157T1AlternatingStaircase
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathEquivariance

-- [TABLET NODE: P5203T1DecreasingInterface]

/-!
# P5203T1DecreasingInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DecreasingInterfaceProof

private theorem footprint :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (z : GaussianInt), z ∈ FootprintVertices (DiamondTile k)
            ↔ (0 : ℤ) ≤ z.im ∧ z.im ≤ (2 : ℤ) * (↑k : ℤ) ∧ -(↑k : ℤ) ≤ z.re ∧ z.re ≤ (↑k : ℤ) ∧
            -(z.im + (1 : ℤ)) ≤ z.re ∧ z.re ≤ z.im + (1 : ℤ) ∧ -((2 : ℤ) * (↑k : ℤ) - z.im + (1 :
            ℤ)) ≤ z.re ∧ z.re ≤ (2 : ℤ) * (↑k : ℤ) - z.im + (1 : ℤ))
    ) := by
  classical
  intro k hk z
  rw [(P4194T1DiamondVertexIncidence k hk z).1]
  simp only [Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_succ,
    Fin.exists_fin_succ]
  rw [show LatticeVertexIncidentCell z 0 = z by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0) = z - 1 by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0).succ = z - 1 - ⟨0, 1⟩ by rfl,
    show LatticeVertexIncidentCell z (Fin.succ 0).succ.succ = z - ⟨0, 1⟩ by rfl]
  rw [(P4194T1DiamondCellRows k z).1,
    (P4194T1DiamondCellRows k (z - 1)).1,
    (P4194T1DiamondCellRows k (z - 1 - ⟨0, 1⟩)).1,
    (P4194T1DiamondCellRows k (z - ⟨0, 1⟩)).1]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one,
    ]
  simp []
  omega

private theorem boundary :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → ((∀ (z : GaussianInt), z ∈ FootprintVertices (DiamondTile k)
            ↔ 0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ -(k : Int) ≤ z.re ∧ z.re ≤ k ∧ -(z.im + 1) ≤ z.re
            ∧ z.re ≤ z.im + 1 ∧ -(2 * (k : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im
            + 1) → (
        let D := DiamondTile k
        let F := fun z : GaussianInt =>
          0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ -(k : Int) ≤ z.re ∧ z.re ≤ k ∧
          -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
          -(2 * (k : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im + 1
        let I := fun z : GaussianInt =>
          1 ≤ z.im ∧ z.im ≤ 2 * (k : Int) - 1 ∧
          -(z.im - 1) ≤ z.re ∧ z.re ≤ z.im - 1 ∧
          -(2 * (k : Int) - z.im - 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im - 1
        ∀ (w : GaussianInt), ∀ (z : GaussianInt), z ∈ BoundaryFootprintVertices (TileTranslation
            D w) ↔ F (z - w) ∧ ¬I (z - w)))
    ) := by
  classical
  intro k hk footprint D F I w z
  have local_formula (x : GaussianInt) : x ∈ BoundaryFootprintVertices D ↔ F x ∧ ¬I x := by
    rw [(P4194T1DiamondVertexIncidence k hk x).2]
    apply and_congr
    · exact ((P4194T1DiamondVertexIncidence k hk x).1).symm.trans
        (footprint x)
    · rw [← not_forall]
      exact not_congr (P4194T1DiamondCellRows k x).2
  rw [(TileTranslationFormulas D w).2.2.2.2.2.2.2.1]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [GaussianTranslation] using (local_formula x).mp hx
  · intro hz
    exact ⟨z - w, (local_formula (z - w)).mpr hz, by simp [GaussianTranslation]⟩

private theorem vp :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt),
        let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
          (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
        let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
          2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
          (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1}
        V = {z | ∃ j ≤ 2 * k - 1, z = p j})
    ) := by
  classical
  intro k hk u p V
  ext z
  constructor
  · intro hz
    have hz : 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
        2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
        (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1 := hz
    let j := ((z - u).im - (z - u).re).toNat
    have hj : (j : Int) = (z - u).im - (z - u).re :=
      Int.toNat_of_nonneg (by omega)
    refine ⟨j, by omega, ?_⟩
    apply Zsqrtd.ext <;>
      simp only [p, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.im_sub] at * <;>
      omega
  · rintro ⟨j, hj, rfl⟩
    simp only [V, Set.mem_ofPred_eq, p, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_sub, Zsqrtd.im_sub]
    omega

private theorem path :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt),
        let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
          (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
        let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
          2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
          (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1}
        let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
        (V = {z | ∃ j ≤ 2 * k - 1, z = p j}) → (SimpleGridPath V E))
    ) := by
  classical
  intro k hk u p V E vp
  let q := P5157T1StaircasePoint ⟨(k : Int), -(k : Int)⟩ true 1
  let V0 : Set GaussianInt := {z | ∃ j ≤ 2 * k - 1, z = q j}
  let E0 : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {q j, q (j + 1)}}
  have hq : SimpleGridPath V0 E0 :=
    (P5157T1AlternatingStaircase ⟨(k : Int), -(k : Int)⟩ true 1
      (Or.inl rfl) (2 * k - 1) (by omega)).2
  have peq (j : Nat) : GaussianTranslation u (GaussianQuarterTurn (q j)) = p j := by
    ext <;> simp [q, P5157T1StaircasePoint, GaussianQuarterTurn,
      GaussianTranslation, p] <;> ring
  have vertices : GaussianTranslation u '' (GaussianQuarterTurn '' V0) =
      {z | ∃ j ≤ 2 * k - 1, z = p j} := by
    ext z
    constructor
    · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j, hj, peq j⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨GaussianQuarterTurn (q j), ⟨q j, ⟨j, hj, rfl⟩, rfl⟩, peq j⟩
  have edges : (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
      ((fun e : Finset GaussianInt => e.image GaussianQuarterTurn) '' E0) = E := by
    ext e
    constructor
    · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j, hj, by simp only [Finset.image_insert, Finset.image_singleton, peq]⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨({q j, q (j + 1)} : Finset GaussianInt).image GaussianQuarterTurn,
        ⟨{q j, q (j + 1)}, ⟨j, hj, rfl⟩, rfl⟩, ?_⟩
      simp only [Finset.image_insert, Finset.image_singleton, peq]
  have hr := (SimpleGridPathEquivariance V0 E0 u).2.1.mp hq
  have ht := (SimpleGridPathEquivariance _ _ u).1.mp hr
  rw [vertices, edges, ← vp] at ht
  exact ht

private theorem vertical :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt),
        let D := DiamondTile k
        let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        let T := TileTranslation D u
        let U := TileTranslation D (u + a)
        let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
          (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
        (∀ (w : GaussianInt), ∀ (z : GaussianInt), z ∈ (TileTranslation D w).cells ↔ z - w ∈
            DiamondCellDomain k) → ((∀ (t : Nat), p (2 * t) = u + (⟨(k : Int) - (t : Int), (k :
            Int) + (t : Int)⟩ : GaussianInt)) → ((∀ (t : Nat), p (2 * t + 1) = u + (⟨(k : Int) -
            (t : Int), (k : Int) + (t : Int) + 1⟩ : GaussianInt)) → (∀ t < k, {p ((2 : ℕ) * t),
            p ((2 : ℕ) * t + (1 : ℕ))} ∈ BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U))))
    ) := by
  classical
  intro k hk u D a T U p cell even odd t ht
  have step : p (2 * t + 1) = p (2 * t) + ⟨0, 1⟩ := by
    rw [even, odd]
    ext <;> simp; ring
  rw [step]
  constructor
  · refine ⟨p (2 * t), Or.inr ⟨rfl, Or.inr ?_⟩⟩
    simp only [T, cell, (P4194T1DiamondCellRows _ _).1, even,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one]
    omega
  · refine ⟨p (2 * t), Or.inr ⟨rfl, Or.inl ?_⟩⟩
    simp only [U, cell, (P4194T1DiamondCellRows _ _).1, even,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one, a]
    omega

private theorem horizontal :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt),
        let D := DiamondTile k
        let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        let T := TileTranslation D u
        let U := TileTranslation D (u + a)
        let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
          (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
        (∀ (w : GaussianInt), ∀ (z : GaussianInt), z ∈ (TileTranslation D w).cells ↔ z - w ∈
            DiamondCellDomain k) → ((∀ (t : Nat), p (2 * t) = u + (⟨(k : Int) - (t : Int), (k :
            Int) + (t : Int)⟩ : GaussianInt)) → ((∀ (t : Nat), p (2 * t + 1) = u + (⟨(k : Int) -
            (t : Int), (k : Int) + (t : Int) + 1⟩ : GaussianInt)) → (∀ (t : ℕ), t + (1 : ℕ) < k →
            {p ((2 : ℕ) * t + (1 : ℕ)), p ((2 : ℕ) * (t + (1 : ℕ)))} ∈ BoundaryFootprintEdges T ∩
            BoundaryFootprintEdges U))))
    ) := by
  classical
  intro k hk u D a T U p cell even odd t ht
  have step : p (2 * t + 1) = p (2 * (t + 1)) + 1 := by
    rw [even, odd]
    ext <;> simp <;> ring
  rw [step, Finset.pair_comm]
  constructor
  · refine ⟨p (2 * (t + 1)), Or.inl ⟨rfl, Or.inr ?_⟩⟩
    simp only [T, cell, (P4194T1DiamondCellRows _ _).1, even,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  · refine ⟨p (2 * (t + 1)), Or.inl ⟨rfl, Or.inl ?_⟩⟩
    simp only [U, cell, (P4194T1DiamondCellRows _ _).1, even,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add, a]
    omega

private theorem he :
    (by
      classical
      exact
        ∀ (k : Nat), ((0 : ℕ) < k) → (∀ (u : GaussianInt),
        let D := DiamondTile k
        let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
        let T := TileTranslation D u
        let U := TileTranslation D (u + a)
        let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
          (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
        let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
          2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
          (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1}
        let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
        (∀ (w : GaussianInt), (TileTranslation D w).cells.Nonempty) → ((BoundaryFootprintVertices
            T ∩ BoundaryFootprintVertices U = V) → ((V = {z | ∃ j ≤ 2 * k - 1, z = p j}) → ((∀ (t
            : Nat), (t < k) → (({p (2 * t), p (2 * t + 1)} : Finset GaussianInt) ∈
            BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U)) → ((∀ (t : Nat), (t + 1 < k) →
            (({p (2 * t + 1), p (2 * (t + 1))} : Finset GaussianInt) ∈ BoundaryFootprintEdges T ∩
            BoundaryFootprintEdges U)) → ((∀ (j : Nat), (p j - u).im - (p j - u).re = (j : Int))
            → (BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E)))))))
    ) := by
  classical
  intro k hk u D a T U p V E ne hv vp vertical horizontal rank
  ext e
  constructor
  · intro hh
    have ep (z : GaussianInt) (hz : z ∈ e) : ∃ j ≤ 2 * k - 1, z = p j := by
      have hb : z ∈ BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U :=
        ⟨by rw [BoundaryFootprintVertices, ite_eq_left (ne u)]; exact ⟨e, hh.1, hz⟩,
         by rw [BoundaryFootprintVertices, ite_eq_left (ne (u + a))]; exact ⟨e, hh.2, hz⟩⟩
      rw [hv, vp] at hb
      exact hb
    obtain ⟨z, hz⟩ := hh.1
    rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · obtain ⟨i, hi, h0⟩ := ep z (by simp)
      obtain ⟨j, hj, h1⟩ := ep (z + 1) (by simp)
      have r0 := rank i
      have r1 := rank j
      rw [← h0] at r0
      rw [← h1] at r1
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_one, Zsqrtd.im_one] at r0 r1
      have ij : i = j + 1 := by omega
      exact ⟨j, by omega, by rw [h1, h0, ij, Finset.pair_comm]⟩
    · obtain ⟨i, hi, h0⟩ := ep z (by simp)
      obtain ⟨j, hj, h1⟩ := ep (z + ⟨0, 1⟩) (by simp)
      have r0 := rank i
      have r1 := rank j
      rw [← h0] at r0
      rw [← h1] at r1
      simp only [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add] at r0 r1
      have ij : j = i + 1 := by omega
      exact ⟨i, by omega, by rw [h1, h0, ij]⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨t, ht | ht⟩ : ∃ t : Nat, j = 2 * t ∨ j = 2 * t + 1 :=
      ⟨j / 2, by omega⟩
    · subst j
      exact vertical t (by omega)
    · subst j
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by omega]
      exact horizontal t (by omega)

end DecreasingInterfaceProof

theorem P5203T1DecreasingInterface (k : Nat) (hk : 0 < k) (u : GaussianInt) :
    let T := TileTranslation (DiamondTile k) u
    let U := TileTranslation (DiamondTile k) (u + ⟨(k : Int) + 1, (k : Int)⟩)
    let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
      (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
    let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
      2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
      (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1}
    let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
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
          z.re ≤ 2 * (k : Int) - z.im + 1 := DecreasingInterfaceProof.footprint k hk z
  let D := DiamondTile k
  let a : GaussianInt := ⟨(k : Int) + 1, (k : Int)⟩
  let T := TileTranslation D u
  let U := TileTranslation D (u + a)
  let p := fun j : Nat => u + (⟨(k : Int) - (j / 2 : Nat),
    (k : Int) + ((j + 1) / 2 : Nat)⟩ : GaussianInt)
  let V : Set GaussianInt := {z | 1 ≤ (z - u).re ∧ (z - u).re ≤ k ∧
    2 * (k : Int) ≤ (z - u).re + (z - u).im ∧
    (z - u).re + (z - u).im ≤ 2 * (k : Int) + 1}
  let E : Set (Finset GaussianInt) := {e | ∃ j < 2 * k - 1, e = {p j, p (j + 1)}}
  let F := fun z : GaussianInt =>
    0 ≤ z.im ∧ z.im ≤ 2 * (k : Int) ∧ -(k : Int) ≤ z.re ∧ z.re ≤ k ∧
    -(z.im + 1) ≤ z.re ∧ z.re ≤ z.im + 1 ∧
    -(2 * (k : Int) - z.im + 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im + 1
  let I := fun z : GaussianInt =>
    1 ≤ z.im ∧ z.im ≤ 2 * (k : Int) - 1 ∧
    -(z.im - 1) ≤ z.re ∧ z.re ≤ z.im - 1 ∧
    -(2 * (k : Int) - z.im - 1) ≤ z.re ∧ z.re ≤ 2 * (k : Int) - z.im - 1
  change T.cells.Nonempty ∧ U.cells.Nonempty ∧ Disjoint T.cells U.cells ∧
    BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V ∧
    BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E ∧ SimpleGridPath V E
  have cell (w z : GaussianInt) :
      z ∈ (TileTranslation D w).cells ↔ z - w ∈ DiamondCellDomain k := by
    change z ∈ (DiamondCellDomain k).image (GaussianTranslation w) ↔ _
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hx
    · intro hz
      exact Finset.mem_image.mpr ⟨z - w, hz, by simp [GaussianTranslation]⟩
  have ne (w : GaussianInt) : (TileTranslation D w).cells.Nonempty := by
    refine ⟨w, (cell w w).mpr ?_⟩
    rw [sub_self]
    exact (P4194T1DiamondCellRows k 0).1.mpr (by norm_num; omega)
  have disj : Disjoint T.cells U.cells := by
    apply Finset.disjoint_left.mpr
    intro z hT hU
    have hT := (P4194T1DiamondCellRows k (z - u)).1.mp ((cell u z).mp hT)
    have hU := (P4194T1DiamondCellRows k (z - (u + a))).1.mp
      ((cell (u + a) z).mp hU)
    simp only [Zsqrtd.im_sub, Zsqrtd.im_add, Zsqrtd.re_sub, Zsqrtd.re_add, a] at hT hU
    omega
  have boundary (w z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation D w) ↔ F (z - w) ∧ ¬I (z - w) :=
          DecreasingInterfaceProof.boundary k hk footprint w z
  have hv : BoundaryFootprintVertices T ∩ BoundaryFootprintVertices U = V := by
    ext z
    dsimp only [T, U]
    simp only [Set.mem_inter_iff, boundary]
    dsimp [V, F, I, a]
    omega
  have vp : V = {z | ∃ j ≤ 2 * k - 1, z = p j} := DecreasingInterfaceProof.vp k hk u
  have path : SimpleGridPath V E := DecreasingInterfaceProof.path k hk u vp
  have even (t : Nat) : p (2 * t) =
      u + (⟨(k : Int) - (t : Int), (k : Int) + (t : Int)⟩ : GaussianInt) := by
    ext <;> simp [p]; omega
  have odd (t : Nat) : p (2 * t + 1) =
      u + (⟨(k : Int) - (t : Int), (k : Int) + (t : Int) + 1⟩ : GaussianInt) := by
    ext <;> simp [p] <;> omega
  have vertical (t : Nat) (ht : t < k) :
      ({p (2 * t), p (2 * t + 1)} : Finset GaussianInt) ∈
        BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U := DecreasingInterfaceProof.vertical
            k hk u cell even odd t ht
  have horizontal (t : Nat) (ht : t + 1 < k) :
      ({p (2 * t + 1), p (2 * (t + 1))} : Finset GaussianInt) ∈
        BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U :=
            DecreasingInterfaceProof.horizontal k hk u cell even odd t ht
  have rank (j : Nat) : (p j - u).im - (p j - u).re = (j : Int) := by
    simp only [p, Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add, Zsqrtd.im_add]
    omega
  have he : BoundaryFootprintEdges T ∩ BoundaryFootprintEdges U = E :=
      DecreasingInterfaceProof.he k hk u ne hv vp vertical horizontal rank
  exact ⟨ne u, ne (u + a), disj, hv, he, path⟩

end ApollonianSuperharmonic

end
