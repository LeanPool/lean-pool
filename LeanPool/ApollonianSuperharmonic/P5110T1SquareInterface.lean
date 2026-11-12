/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath

-- [TABLET NODE: P5110T1SquareInterface]

/-!
# P5110T1SquareInterface

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace SquareInterfaceConstruction

private theorem cell (h
    : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := by
  classical
  have translated : z ∈ (TileTranslation (FordTile h) c).cells ↔
      z - c ∈ (FordTile h).cells := by
    constructor
    · rintro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      simpa [GaussianTranslation] using hy
    · intro hz
      exact Finset.mem_image.mpr ⟨z - c, hz, by simp [GaussianTranslation]⟩
  rw [translated, (P4210T1FordCellRectangles h (z - c)).1]
  simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
  omega

private theorem vertex (h : Nat) (hh : 0 < h) (c z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation (FordTile h) c) ↔
        c.re ≤ z.re ∧ z.re ≤ c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im ≤ c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int) ∨
            z.im = c.im ∨ z.im = c.im + (h : Int)) := by
  classical
  rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.2.1,
    (P4062T1CanonicalSupport h hh).2]
  constructor
  · rintro ⟨y, hy, rfl⟩
    dsimp [GaussianTranslation] at *
    omega
  · intro hz
    refine ⟨z - c, ?_, by simp [GaussianTranslation]⟩
    dsimp
    omega

private theorem edge (h
    : Nat) (hh : 0 < h) (c : GaussianInt) (e : Finset GaussianInt) :
      e ∈ BoundaryFootprintEdges (TileTranslation (FordTile h) c) ↔
        (∃ z : GaussianInt, e = {z, z + 1} ∧
          c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          (z.im = c.im ∨ z.im = c.im + (h : Int))) ∨
        (∃ z : GaussianInt, e = {z, z + ⟨0, 1⟩} ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int))) := by
  classical
  have cell (h : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := cell h c z
  simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq, cell,
    Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one]
  constructor
  · rintro ⟨z, hz⟩
    rcases hz with ⟨he, hz⟩ | ⟨he, hz⟩
    · exact Or.inl ⟨z, he, by omega⟩
    · exact Or.inr ⟨z, he, by omega⟩
  · rintro (⟨z, he, hz⟩ | ⟨z, he, hz⟩)
    · exact ⟨z, Or.inl ⟨he, by omega⟩⟩
    · exact ⟨z, Or.inr ⟨he, by omega⟩⟩

private noncomputable abbrev A (n : Nat) (a : GaussianInt) := TileTranslation (FordTile n) a

private noncomputable abbrev B (m : Nat) (b : GaussianInt) := TileTranslation (FordTile m) b

private noncomputable abbrev l (a : GaussianInt) (b : GaussianInt) (vertical : Bool) := max (if
    vertical then a.im else a.re) (if vertical then b.im else b.re)

private noncomputable abbrev u (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical
    : Bool) := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))

private noncomputable abbrev f (a : GaussianInt) (b : GaussianInt) (vertical : Bool) := fun k :
    Nat => if vertical then (⟨b.re, (l a b vertical) + (k : Int)⟩ : GaussianInt)
    else (⟨(l a b vertical) + (k : Int), b.im⟩ : GaussianInt)

private noncomputable abbrev p (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical
    : Bool) := (List.range (((u n m a b vertical) - (l a b vertical)).toNat + 1)).map (f a b
    vertical)

private theorem na (n : Nat) (hn : 0 < n) (a : GaussianInt) : (A n a).cells.Nonempty := by
  classical
  have cell (h : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := cell h c z
  let A := TileTranslation (FordTile n) a
  change (A.cells.Nonempty)
  exact ⟨a, (cell n a a).mpr (by omega)⟩

private theorem nb (m : Nat) (hm : 0 < m) (b : GaussianInt) : (B m b).cells.Nonempty := by
  classical
  have cell (h : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := cell h c z
  let B := TileTranslation (FordTile m) b
  change (B.cells.Nonempty)
  exact ⟨b, (cell m b b).mpr (by omega)⟩

private theorem disj (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical : Bool)
    (hside : if vertical then b.re = a.re + (n : Int) else b.im = a.im + (n : Int)) (hoverlap :
    max (if vertical then a.im else a.re) (if vertical then b.im else b.re) < min ((if vertical
    then a.im else a.re) + (n : Int)) ((if vertical then b.im else b.re) + (m : Int))) : Disjoint
    (A n a).cells (B m b).cells := by
  classical
  have cell (h : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := cell h c z
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  change (Disjoint A.cells B.cells)
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  have ha := (cell n a z).mp hza
  have hb := (cell m b z).mp hzb
  cases vertical <;> dsimp at hside <;> omega

private theorem vertices (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : BoundaryFootprintVertices (A n a) ∩ BoundaryFootprintVertices (B m b) =
      {z | if vertical then z.re = b.re ∧ (l a b vertical) ≤ z.im ∧ z.im ≤ (u n m a b vertical)
        else z.im = b.im ∧ (l a b vertical) ≤ z.re ∧ z.re ≤ (u n m a b vertical)} := by
  classical
  have vertex (h : Nat) (hh : 0 < h) (c z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation (FordTile h) c) ↔
        c.re ≤ z.re ∧ z.re ≤ c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im ≤ c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int) ∨
            z.im = c.im ∨ z.im = c.im + (h : Int)) := vertex h hh c z
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  change (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u})
  ext z
  simp only [A, B, Set.mem_inter_iff, vertex n hn a z, vertex m hm b z,
    Set.mem_ofPred_eq]
  cases vertical <;> simp only [l, u, Bool.false_eq_true, ↓reduceIte] at hside ⊢
  all_goals omega

private theorem endpoints (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges (A n a) ∩ BoundaryFootprintEdges (B m b))
      (z : GaussianInt) (hz : z ∈ e) :
      z ∈ BoundaryFootprintVertices (A n a) ∩ BoundaryFootprintVertices (B m b) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  have na : A.cells.Nonempty := na n hn a
  have nb : B.cells.Nonempty := nb m hm b
  change (z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
  constructor
  · rw [BoundaryFootprintVertices, ite_eq_left na]
    exact ⟨e, he.1, hz⟩
  · rw [BoundaryFootprintVertices, ite_eq_left nb]
    exact ⟨e, he.2, hz⟩

private theorem edges (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : BoundaryFootprintEdges (A n a) ∩ BoundaryFootprintEdges (B m b) =
      {e | ∃ t : Int, (l a b vertical) ≤ t ∧ t < (u n m a b vertical) ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := by
  classical
  have edge (h : Nat) (hh : 0 < h) (c : GaussianInt) (e : Finset GaussianInt) :
      e ∈ BoundaryFootprintEdges (TileTranslation (FordTile h) c) ↔
        (∃ z : GaussianInt, e = {z, z + 1} ∧
          c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          (z.im = c.im ∨ z.im = c.im + (h : Int))) ∨
        (∃ z : GaussianInt, e = {z, z + ⟨0, 1⟩} ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int))) := edge h hh c e
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have endpoints (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B)
      (z : GaussianInt) (hz : z ∈ e) :
      z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B := endpoints n m hn hm a b e
          he z hz
  change (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}})
  ext e
  constructor
  · intro he
    have hea := (edge n hn a e).mp he.1
    rcases hea with ⟨z, rfl, _⟩ | ⟨z, rfl, _⟩
    · have h0 := endpoints _ he z (by simp)
      have h1 := endpoints _ he (z + 1) (by simp)
      rw [vertices] at h0 h1
      cases vertical
      · dsimp at h0 h1 ⊢
        refine ⟨z.re, h0.2.1, ?_, ?_⟩
        · omega
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> dsimp <;> omega
      · dsimp at h0 h1
        omega
    · have h0 := endpoints _ he z (by simp)
      have h1 := endpoints _ he (z + ⟨0, 1⟩) (by simp)
      rw [vertices] at h0 h1
      cases vertical
      · dsimp at h0 h1
        omega
      · dsimp at h0 h1 ⊢
        refine ⟨z.im, h0.2.1, ?_, ?_⟩
        · omega
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> dsimp <;> omega
  · rintro ⟨t, ht, htu, rfl⟩
    cases vertical
    · dsimp [l, u] at ht htu hside ⊢
      constructor
      · apply (edge n hn a _).mpr
        left
        refine ⟨⟨t, b.im⟩, ?_, ?_⟩
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> simp
        · dsimp; omega
      · apply (edge m hm b _).mpr
        left
        refine ⟨⟨t, b.im⟩, ?_, ?_⟩
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> simp
        · dsimp; omega
    · dsimp [l, u] at ht htu hside ⊢
      constructor
      · apply (edge n hn a _).mpr
        right
        refine ⟨⟨b.re, t⟩, ?_, ?_⟩
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> simp
        · dsimp; omega
      · apply (edge m hm b _).mpr
        right
        refine ⟨⟨b.re, t⟩, ?_, ?_⟩
        · apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
            apply Zsqrtd.ext <;> simp
        · dsimp; omega

private theorem hlu (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical : Bool)
    (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im else b.re) < min
    ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else b.re) + (m :
    Int))) : (l a b vertical) < (u n m a b vertical) := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  change (l < u)
  exact hoverlap

private theorem hdelta (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical : Bool)
    (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im else b.re) < min
    ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else b.re) + (m :
    Int))) : ((((u n m a b vertical) - (l a b vertical)).toNat : Nat) : Int) = (u n m a b
    vertical) - (l a b vertical) := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  change ((((u - l).toNat : Nat) : Int) = u - l)
  omega

private theorem positive_length (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical
    : Bool) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im else b.re) <
    min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else b.re) + (m :
    Int))) : 0 < ((u n m a b vertical) - (l a b vertical)).toNat := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  change (0 < (u - l).toNat)
  omega

private theorem finj (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : Function.Injective (f a b vertical) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  change (Function.Injective f)
  intro j k he
  cases vertical
  · have h := congrArg Zsqrtd.re he
    dsimp [f] at h
    omega
  · have h := congrArg Zsqrtd.im he
    dsimp [f] at h
    omega

private theorem pnd (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : (p n m a b vertical).Nodup := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  change (p.Nodup)
  exact List.nodup_range.map finj

private theorem plen (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical : Bool)
    (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im else b.re) < min
    ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else b.re) + (m :
    Int))) : 2 ≤ (p n m a b vertical).length := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  change (2 ≤ p.length)
  simp only [p, List.length_map, List.length_range]; omega

private theorem pvertices (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : BoundaryFootprintVertices (A n a) ∩ BoundaryFootprintVertices (B m b) =
      ((p n m a b vertical).toFinset : Set GaussianInt) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  have pnd : p.Nodup := pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := plen n m a b vertical hoverlap
  change (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt))
  ext z
  rw [vertices]
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, p, List.mem_map,
    List.mem_range]
  constructor
  · intro hz
    cases vertical
    · dsimp at hz
      refine ⟨(z.re - l).toNat, by omega, ?_⟩
      apply Zsqrtd.ext <;> dsimp [f] <;> omega
    · dsimp at hz
      refine ⟨(z.im - l).toNat, by omega, ?_⟩
      apply Zsqrtd.ext <;> dsimp [f] <;> omega
  · rintro ⟨k, hk, rfl⟩
    cases vertical <;> dsimp [f] <;> omega

private noncomputable abbrev adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩

private theorem fstep (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) (k : Nat) : adj ((f a b vertical) k) ((f a b vertical) (k + 1)) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  have pnd : p.Nodup := pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := plen n m a b vertical hoverlap
  have pvertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt) := pvertices n m hn hm a b vertical hside hoverlap
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  change (adj (f k) (f (k + 1)))
  cases vertical
  · left; apply Zsqrtd.ext <;> simp [f, add_assoc]
  · right; right; left; apply Zsqrtd.ext <;> simp [f, add_assoc]

private theorem chain (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : (p n m a b vertical).IsChain adj := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have fstep (k : Nat) : adj (f k) (f (k + 1)) := fstep n m hn hm a b vertical hside hoverlap k
  change (p.IsChain adj)
  apply (List.isChain_map f).mpr
  exact (List.isChain_range_succ _ (u - l).toNat).mpr (fun k _ => fstep k)

private theorem step (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : ∀ x y l₁ l₂, (p n m a b vertical) = l₁ ++ x :: y :: l₂ → adj x y := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have chain : p.IsChain adj := chain n m hn hm a b vertical hside hoverlap
  change (∀ x y l₁ l₂, p = l₁ ++ x :: y :: l₂ → adj x y)
  exact List.isChain_iff_forall_rel_of_append_cons_cons.mp chain

private theorem occurs (n : Nat) (m : Nat) (a : GaussianInt) (b : GaussianInt) (vertical : Bool)
    (k : Nat) (hk : k < ((u n m a b vertical) - (l a b vertical)).toNat) :
      ∃ l₁ l₂, (p n m a b vertical) = l₁ ++ (f a b vertical) k :: (f a b vertical) (k + 1) :: l₂
          := by
  classical
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  change k < (u - l).toNat at hk
  change (∃ l₁ l₂, p = l₁ ++ f k :: f (k + 1) :: l₂)
  have hk' : k < p.length := by simp only [p, List.length_map, List.length_range]; omega
  have hk'' : k + 1 < p.length := by simp only [p, List.length_map, List.length_range]; omega
  refine ⟨p.take k, p.drop (k + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop k p]
  rw [List.drop_eq_getElem_cons hk', List.drop_eq_getElem_cons hk'']
  simp [p]

private theorem edge_step (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) (k : Nat) (hk : k < ((u n m a b vertical) - (l a b vertical)).toNat) :
      {(f a b vertical) k, (f a b vertical) (k + 1)} ∈ BoundaryFootprintEdges (A n a) ∩
          BoundaryFootprintEdges (B m b) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  have pnd : p.Nodup := pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := plen n m a b vertical hoverlap
  have pvertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt) := pvertices n m hn hm a b vertical hside hoverlap
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have fstep (k : Nat) : adj (f k) (f (k + 1)) := fstep n m hn hm a b vertical hside hoverlap k
  have chain : p.IsChain adj := chain n m hn hm a b vertical hside hoverlap
  have step : ∀ x y l₁ l₂, p = l₁ ++ x :: y :: l₂ → adj x y := step n m hn hm a b vertical hside
      hoverlap
  have occurs (k : Nat) (hk : k < (u - l).toNat) :
      ∃ l₁ l₂, p = l₁ ++ f k :: f (k + 1) :: l₂ := occurs n m a b vertical k hk
  change k < (u - l).toNat at hk
  change ({f k, f (k + 1)} ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B)
  rw [edges]
  refine ⟨l + (k : Int), by omega, by omega, ?_⟩
  cases vertical <;> simp [f, add_assoc]

private theorem adjacent_indices (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt)
    (b : GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else
    b.im = a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then
    b.im else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im
    else b.re) + (m : Int))) (j k : Nat) (h : adj ((f a b vertical) j) ((f a b vertical) k)) :
      k = j + 1 ∨ j = k + 1 := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  have pnd : p.Nodup := pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := plen n m a b vertical hoverlap
  have pvertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt) := pvertices n m hn hm a b vertical hside hoverlap
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have fstep (k : Nat) : adj (f k) (f (k + 1)) := fstep n m hn hm a b vertical hside hoverlap k
  have chain : p.IsChain adj := chain n m hn hm a b vertical hside hoverlap
  have step : ∀ x y l₁ l₂, p = l₁ ++ x :: y :: l₂ → adj x y := step n m hn hm a b vertical hside
      hoverlap
  have occurs (k : Nat) (hk : k < (u - l).toNat) :
      ∃ l₁ l₂, p = l₁ ++ f k :: f (k + 1) :: l₂ := occurs n m a b vertical k hk
  have edge_step (k : Nat) (hk : k < (u - l).toNat) :
      {f k, f (k + 1)} ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B := edge_step n m hn
          hm a b vertical hside hoverlap k hk
  change adj (f j) (f k) at h
  cases vertical <;> simp [adj, f, Zsqrtd.ext_iff] at h <;> omega

private theorem path (n : Nat) (m : Nat) (hn : 0 < n) (hm : 0 < m) (a : GaussianInt) (b :
    GaussianInt) (vertical : Bool) (hside : if vertical then b.re = a.re + (n : Int) else b.im =
    a.im + (n : Int)) (hoverlap : max (if vertical then a.im else a.re) (if vertical then b.im
    else b.re) < min ((if vertical then a.im else a.re) + (n : Int)) ((if vertical then b.im else
    b.re) + (m : Int))) : SimpleGridPath (BoundaryFootprintVertices (A n a) ∩
    BoundaryFootprintVertices (B m b))
      (BoundaryFootprintEdges (A n a) ∩ BoundaryFootprintEdges (B m b)) := by
  classical
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := vertices n m hn hm a b vertical hside hoverlap
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := edges n m hn hm a b vertical hside
            hoverlap
  have hlu : l < u := hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := hdelta n m a b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := positive_length n m a b vertical hoverlap
  have finj : Function.Injective f := finj n m hn hm a b vertical hside hoverlap
  have pnd : p.Nodup := pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := plen n m a b vertical hoverlap
  have pvertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt) := pvertices n m hn hm a b vertical hside hoverlap
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have fstep (k : Nat) : adj (f k) (f (k + 1)) := fstep n m hn hm a b vertical hside hoverlap k
  have chain : p.IsChain adj := chain n m hn hm a b vertical hside hoverlap
  have step : ∀ x y l₁ l₂, p = l₁ ++ x :: y :: l₂ → adj x y := step n m hn hm a b vertical hside
      hoverlap
  have occurs (k : Nat) (hk : k < (u - l).toNat) :
      ∃ l₁ l₂, p = l₁ ++ f k :: f (k + 1) :: l₂ := occurs n m a b vertical k hk
  have edge_step (k : Nat) (hk : k < (u - l).toNat) :
      {f k, f (k + 1)} ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B := edge_step n m hn
          hm a b vertical hside hoverlap k hk
  have adjacent_indices (j k : Nat) (h : adj (f j) (f k)) :
      k = j + 1 ∨ j = k + 1 := adjacent_indices n m hn hm a b vertical hside hoverlap j k h
  change (SimpleGridPath (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
      (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B))
  refine ⟨p, pnd, plen, pvertices, step, ?_⟩
  intro e
  constructor
  · intro he
    rw [edges] at he
    obtain ⟨t, htl, htu, het⟩ := he
    let k := (t - l).toNat
    have hk : k < (u - l).toNat := by dsimp [k]; omega
    obtain ⟨l₁, l₂, hp⟩ := occurs k hk
    refine ⟨f k, f (k + 1), l₁, l₂, hp, ?_⟩
    rw [het]
    cases vertical <;>
      apply congrArg₂ (fun x y : GaussianInt => ({x, y} : Finset GaussianInt)) <;>
      apply Zsqrtd.ext <;> dsimp [f, k] <;> omega
  · rintro ⟨x, y, l₁, l₂, hp, rfl⟩
    have hx : x ∈ p := by rw [hp]; simp
    have hy : y ∈ p := by rw [hp]; simp
    obtain ⟨j, hj, rfl⟩ : ∃ j < (u - l).toNat + 1, f j = x := by
      simpa only [p, List.mem_map, List.mem_range] using hx
    obtain ⟨k, hk, rfl⟩ : ∃ k < (u - l).toNat + 1, f k = y := by
      simpa only [p, List.mem_map, List.mem_range] using hy
    rcases adjacent_indices j k (step _ _ _ _ hp) with h | h
    · subst k
      exact edge_step j (by omega)
    · subst j
      simpa only [Finset.pair_comm] using edge_step k (by omega)

end SquareInterfaceConstruction

theorem P5110T1SquareInterface (n m : Nat) (hn : 0 < n) (hm : 0 < m)
    (a b : GaussianInt) (vertical : Bool)
    (hside : if vertical then b.re = a.re + (n : Int)
      else b.im = a.im + (n : Int))
    (hoverlap :
      max (if vertical then a.im else a.re) (if vertical then b.im else b.re) <
        min ((if vertical then a.im else a.re) + (n : Int))
          ((if vertical then b.im else b.re) + (m : Int))) :
    let A := TileTranslation (FordTile n) a
    let B := TileTranslation (FordTile m) b
    let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
    let u := min ((if vertical then a.im else a.re) + (n : Int))
      ((if vertical then b.im else b.re) + (m : Int))
    let p := (List.range ((u - l).toNat + 1)).map (fun k : Nat =>
      if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
      else (⟨l + (k : Int), b.im⟩ : GaussianInt))
    A.cells.Nonempty ∧ B.cells.Nonempty ∧ Disjoint A.cells B.cells ∧
      BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
        {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
          else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} ∧
      BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
        {e | ∃ t : Int, l ≤ t ∧ t < u ∧
          e = if vertical then
            {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
          else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} ∧
      p.Nodup ∧ 2 ≤ p.length ∧
      BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
        (p.toFinset : Set GaussianInt) ∧
      SimpleGridPath (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
        (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B) := by
-- BODY
  have cell (h : Nat) (c z : GaussianInt) :
      z ∈ (TileTranslation (FordTile h) c).cells ↔
        c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) := SquareInterfaceConstruction.cell h c z
  have vertex (h : Nat) (hh : 0 < h) (c z : GaussianInt) :
      z ∈ BoundaryFootprintVertices (TileTranslation (FordTile h) c) ↔
        c.re ≤ z.re ∧ z.re ≤ c.re + (h : Int) ∧
          c.im ≤ z.im ∧ z.im ≤ c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int) ∨
            z.im = c.im ∨ z.im = c.im + (h : Int)) := SquareInterfaceConstruction.vertex h hh c z
  have edge (h : Nat) (hh : 0 < h) (c : GaussianInt) (e : Finset GaussianInt) :
      e ∈ BoundaryFootprintEdges (TileTranslation (FordTile h) c) ↔
        (∃ z : GaussianInt, e = {z, z + 1} ∧
          c.re ≤ z.re ∧ z.re < c.re + (h : Int) ∧
          (z.im = c.im ∨ z.im = c.im + (h : Int))) ∨
        (∃ z : GaussianInt, e = {z, z + ⟨0, 1⟩} ∧
          c.im ≤ z.im ∧ z.im < c.im + (h : Int) ∧
          (z.re = c.re ∨ z.re = c.re + (h : Int))) := SquareInterfaceConstruction.edge h hh c e
  let A := TileTranslation (FordTile n) a
  let B := TileTranslation (FordTile m) b
  let l := max (if vertical then a.im else a.re) (if vertical then b.im else b.re)
  let u := min ((if vertical then a.im else a.re) + (n : Int))
    ((if vertical then b.im else b.re) + (m : Int))
  let f := fun k : Nat => if vertical then (⟨b.re, l + (k : Int)⟩ : GaussianInt)
    else (⟨l + (k : Int), b.im⟩ : GaussianInt)
  let p := (List.range ((u - l).toNat + 1)).map f
  have na : A.cells.Nonempty := SquareInterfaceConstruction.na n hn a
  have nb : B.cells.Nonempty := SquareInterfaceConstruction.nb m hm b
  have disj : Disjoint A.cells B.cells := SquareInterfaceConstruction.disj n m a b vertical hside
      hoverlap
  have vertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      {z | if vertical then z.re = b.re ∧ l ≤ z.im ∧ z.im ≤ u
        else z.im = b.im ∧ l ≤ z.re ∧ z.re ≤ u} := SquareInterfaceConstruction.vertices n m hn hm
            a b vertical hside hoverlap
  have endpoints (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B)
      (z : GaussianInt) (hz : z ∈ e) :
      z ∈ BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B :=
          SquareInterfaceConstruction.endpoints n m hn hm a b e he z hz
  have edges : BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B =
      {e | ∃ t : Int, l ≤ t ∧ t < u ∧ e = if vertical then
        {(⟨b.re, t⟩ : GaussianInt), ⟨b.re, t + 1⟩}
        else {(⟨t, b.im⟩ : GaussianInt), ⟨t + 1, b.im⟩}} := SquareInterfaceConstruction.edges n m
            hn hm a b vertical hside hoverlap
  have hlu : l < u := SquareInterfaceConstruction.hlu n m a b vertical hoverlap
  have hdelta : (((u - l).toNat : Nat) : Int) = u - l := SquareInterfaceConstruction.hdelta n m a
      b vertical hoverlap
  have positive_length : 0 < (u - l).toNat := SquareInterfaceConstruction.positive_length n m a b
      vertical hoverlap
  have finj : Function.Injective f := SquareInterfaceConstruction.finj n m hn hm a b vertical
      hside hoverlap
  have pnd : p.Nodup := SquareInterfaceConstruction.pnd n m hn hm a b vertical hside hoverlap
  have plen : 2 ≤ p.length := SquareInterfaceConstruction.plen n m a b vertical hoverlap
  have pvertices : BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B =
      (p.toFinset : Set GaussianInt) := SquareInterfaceConstruction.pvertices n m hn hm a b
          vertical hside hoverlap
  let adj := fun x y : GaussianInt => y = x + 1 ∨ y = x - 1 ∨
    y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩
  have fstep (k : Nat) : adj (f k) (f (k + 1)) := SquareInterfaceConstruction.fstep n m hn hm a b
      vertical hside hoverlap k
  have chain : p.IsChain adj := SquareInterfaceConstruction.chain n m hn hm a b vertical hside
      hoverlap
  have step : ∀ x y l₁ l₂, p = l₁ ++ x :: y :: l₂ → adj x y := SquareInterfaceConstruction.step n
      m hn hm a b vertical hside hoverlap
  have occurs (k : Nat) (hk : k < (u - l).toNat) :
      ∃ l₁ l₂, p = l₁ ++ f k :: f (k + 1) :: l₂ := SquareInterfaceConstruction.occurs n m a b
          vertical k hk
  have edge_step (k : Nat) (hk : k < (u - l).toNat) :
      {f k, f (k + 1)} ∈ BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B :=
          SquareInterfaceConstruction.edge_step n m hn hm a b vertical hside hoverlap k hk
  have adjacent_indices (j k : Nat) (h : adj (f j) (f k)) :
      k = j + 1 ∨ j = k + 1 := SquareInterfaceConstruction.adjacent_indices n m hn hm a b
          vertical hside hoverlap j k h
  have path : SimpleGridPath (BoundaryFootprintVertices A ∩ BoundaryFootprintVertices B)
      (BoundaryFootprintEdges A ∩ BoundaryFootprintEdges B) := SquareInterfaceConstruction.path n
          m hn hm a b vertical hside hoverlap
  exact ⟨na, nb, disj, vertices, edges, pnd, plen, pvertices, path⟩

end ApollonianSuperharmonic

end
