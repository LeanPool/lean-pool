/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5110T1SquareInterface
public import LeanPool.ApollonianSuperharmonic.P3192T1SimplePathOrientation
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary

-- [TABLET NODE: P5682T1AlignedSquareRawInterfaces]

/-!
# P5682T1AlignedSquareRawInterfaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5682T1AlignedSquareRawInterfaces :
    let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
    (∀ (n : Nat), 0 < n → ∀ a z : GaussianInt,
      z ∈ FootprintVertices (sq n a) ↔
        a.re ≤ z.re ∧ z.re ≤ a.re + n ∧ a.im ≤ z.im ∧ z.im ≤ a.im + n) ∧
    (∀ (n m : Nat), 0 < n → 0 < m → ∀ (a b : GaussianInt) (v : Bool),
      (if v then b.re = a.re + n else b.im = a.im + n) →
      max (if v then a.im else a.re) (if v then b.im else b.re) <
        min ((if v then a.im else a.re) + n) ((if v then b.im else b.re) + m) →
      let l := max (if v then a.im else a.re) (if v then b.im else b.re)
      let u := min ((if v then a.im else a.re) + n) ((if v then b.im else b.re) + m)
      let x : GaussianInt := if v then ⟨b.re,l⟩ else ⟨l,b.im⟩
      let y : GaussianInt := if v then ⟨b.re,u⟩ else ⟨u,b.im⟩
      Disjoint (sq n a).cells (sq m b).cells ∧
        SimpleGridPathBetween
          (FootprintVertices (sq n a) ∩ FootprintVertices (sq m b))
          (FootprintEdges (sq n a) ∩ FootprintEdges (sq m b)) x y ∧
        SimpleGridPathBetween
          (FootprintVertices (sq n a) ∩ FootprintVertices (sq m b))
          (FootprintEdges (sq n a) ∩ FootprintEdges (sq m b)) y x) := by
-- BODY
  classical
  let sq := fun (n : Nat) (a : GaussianInt) => TileTranslation (FordTile n) a
  have vertex (n : Nat) (hn : 0 < n) (a z : GaussianInt) :
      z ∈ FootprintVertices (sq n a) ↔
        a.re ≤ z.re ∧ z.re ≤ a.re + n ∧ a.im ≤ z.im ∧ z.im ≤ a.im + n := by
    rw [(TileTranslationFormulas _ _).2.2.2.2.2.1,
      (P4062T1CanonicalSupport n hn).1]
    constructor
    · rintro ⟨w, hw, rfl⟩
      dsimp [FordVertexDomain, GaussianTranslation] at hw ⊢
      omega
    · intro hz
      refine ⟨z-a, ?_, by simp [GaussianTranslation]⟩
      dsimp [FordVertexDomain]
      omega
  refine ⟨vertex, ?_⟩
  intro n m hn hm a b v hside hover
  obtain ⟨_, _, hd, hV, hE, _, _, _, hp⟩ :=
    P5110T1SquareInterface n m hn hm a b v hside hover
  let l := max (if v then a.im else a.re) (if v then b.im else b.re)
  let u := min ((if v then a.im else a.re) + n) ((if v then b.im else b.re) + m)
  let x : GaussianInt := if v then ⟨b.re,l⟩ else ⟨l,b.im⟩
  let y : GaussianInt := if v then ⟨b.re,u⟩ else ⟨u,b.im⟩
  change Disjoint (sq n a).cells (sq m b).cells ∧
    SimpleGridPathBetween
      (FootprintVertices (sq n a) ∩ FootprintVertices (sq m b))
      (FootprintEdges (sq n a) ∩ FootprintEdges (sq m b)) x y ∧
    SimpleGridPathBetween
      (FootprintVertices (sq n a) ∩ FootprintVertices (sq m b))
      (FootprintEdges (sq n a) ∩ FootprintEdges (sq m b)) y x
  have hv : FootprintVertices (sq n a) ∩ FootprintVertices (sq m b) =
      BoundaryFootprintVertices (sq n a) ∩ BoundaryFootprintVertices (sq m b) := by
    rw [hV]
    ext z
    simp only [Set.mem_inter_iff, vertex n hn a, vertex m hm b, Set.mem_ofPred_eq]
    cases v <;> dsimp at hside ⊢ <;> omega
  have he := CellDisjointCommonEdgesBoundary (sq n a) (sq m b) hd
  have hx : x ∈ BoundaryFootprintVertices (sq n a) ∩ BoundaryFootprintVertices (sq m b) := by
    rw [hV]
    cases v <;> dsimp [x,l,u] at hover ⊢ <;> omega
  have hy : y ∈ BoundaryFootprintVertices (sq n a) ∩ BoundaryFootprintVertices (sq m b) := by
    rw [hV]
    cases v <;> dsimp [y,l,u] at hover ⊢ <;> omega
  have hxy : x ≠ y := by
    intro h
    cases v <;> simp only [x,y,l,u,Bool.false_eq_true,ite_false,ite_true,
      Zsqrtd.ext_iff] at h hover <;> omega
  have endpoint (z : GaussianInt) (hz : z = x ∨ z = y) :
      ∀ e f : Finset GaussianInt, z ∈ e → z ∈ f →
        e ∈ BoundaryFootprintEdges (sq n a) ∩ BoundaryFootprintEdges (sq m b) →
        f ∈ BoundaryFootprintEdges (sq n a) ∩ BoundaryFootprintEdges (sq m b) → e = f := by
    intro e f hze hzf he hf
    rw [hE] at he hf
    obtain ⟨t, htl, htu, rfl⟩ := he
    obtain ⟨t', ht'l, ht'u, rfl⟩ := hf
    have htt : t = t' := by
      cases v <;> rcases hz with rfl | rfl <;>
        simp only [x,y,l,u,Bool.false_eq_true, ite_false, ite_true, Finset.mem_insert,
          Finset.mem_singleton, Zsqrtd.ext_iff] at hze hzf htl htu ht'l ht'u <;> omega
    rw [htt]
  have forward := P3192T1SimplePathOrientation _ _ x y hp hx hy hxy
    (endpoint x (Or.inl rfl)) (endpoint y (Or.inr rfl))
  have backward := P3192T1SimplePathOrientation _ _ y x hp hy hx hxy.symm
    (endpoint y (Or.inr rfl)) (endpoint x (Or.inl rfl))
  exact ⟨hd, by simpa only [hv,he] using forward,
    by simpa only [hv,he] using backward⟩

end ApollonianSuperharmonic

end
