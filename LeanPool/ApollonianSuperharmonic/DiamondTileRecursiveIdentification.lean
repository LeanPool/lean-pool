/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.DiamondCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.DiamondTile
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCentroid

-- [TABLET NODE: DiamondTileRecursiveIdentification]

/-!
# DiamondTileRecursiveIdentification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondTileRecursiveIdentification (K : DiamondParameter) :
    BandPrototile ((DiamondRecursiveQuadruple K) 0) (DiamondTile K.1) ∧
      ∃ S : Fin 3 → Bool → ProtoTile,
        (∀ i s, BandSubtileOccurrence (DiamondRecursiveQuadruple K)
          (DiamondTile K.1) i s (S i s)) ∧
        (∀ x, x ∈ (DiamondTile K.1).cells ↔ ∃ i s, x ∈ (S i s).cells) ∧
        S 0 true =
          ⟨{⟨-(K.1 : Int), (K.1 : Int) - 1⟩},
            ⟨-(K.1 : Int), (K.1 : Int) - 1⟩⟩ ∧
        S 0 false =
          ⟨{⟨(K.1 : Int) - 1, (K.1 : Int)⟩},
            ⟨(K.1 : Int) - 1, (K.1 : Int)⟩⟩ ∧
        S 1 true =
          ⟨{⟨(K.1 : Int) - 1, (K.1 : Int) - 1⟩},
            ⟨(K.1 : Int) - 1, (K.1 : Int) - 1⟩⟩ ∧
        S 1 false =
          ⟨{⟨-(K.1 : Int), (K.1 : Int)⟩},
            ⟨-(K.1 : Int), (K.1 : Int)⟩⟩ ∧
        S 2 false = DiamondTile (K.1 - 1) ∧
        S 2 true = TileTranslation (DiamondTile (K.1 - 1)) ⟨0, 2⟩ := by
-- BODY
  classical
  have centroid (n : Nat) : TileCentroid (DiamondTile n) = (0, (n : Real)) := by
    by_cases hn : 0 < n
    · exact P4194T1DiamondCentroid n hn
    · have hn0 : n = 0 := by omega
      subst n
      simp [TileCentroid, DiamondTile, DiamondCellDomain]
  have singleton_centroid (x : GaussianInt) :
      TileCentroid (⟨{x}, x⟩ : ProtoTile) =
        ((x.re : Real) + 1 / 2, (x.im : Real) + 1 / 2) := by
    simp [TileCentroid]
  have translated_mem (n : Nat) (x : GaussianInt) :
      x ∈ (TileTranslation (DiamondTile n) ⟨0, 2⟩).cells ↔
        x - ⟨0, 2⟩ ∈ DiamondCellDomain n := by
    change x ∈ (DiamondCellDomain n).image (GaussianTranslation ⟨0, 2⟩) ↔ _
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      simpa [GaussianTranslation] using hy
    · intro hx
      exact Finset.mem_image.mpr
        ⟨x - ⟨0, 2⟩, hx, by simp [GaussianTranslation]⟩
  rcases K with ⟨k, hk⟩
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let q := DiamondRecursiveQuadruple ⟨k, hk⟩
    obtain ⟨_, hq, h10, h20, h30, _⟩ := DiamondCoordinateConfiguration ⟨k, hk⟩
    have hs := (VectorRecursionLaws q hq.1).1
    have h1 := (VectorRecursionLaws q hq.1).2.2.1
    have h3 : BandVectors.1 (q 3) (q 0) =
        BandVectors.1 (q 3) (q 2) -
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3) := by
      simpa using (VectorRecursionLaws _
        (SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hq.1))).2.2.1
    change BandVectors.1 (q 1) (q 0) = _ at h10
    change BandVectors.1 (q 3) (q 0) = _ at h30
    rw [h10] at h1
    rw [h30] at h3
    simp only [Zsqrtd.ext_iff, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_mul, Zsqrtd.im_mul,
      Zsqrtd.re_zero, Zsqrtd.im_zero] at hs h1 h3
    norm_num at hs h1 h3
    have h32 : BandVectors.1 (q 3) (q 2) =
        ⟨1 - (k : Int), -(k : Int)⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    have h13 : BandVectors.1 (q 1) (q 3) =
        ⟨(k : Int), (k : Int) - 1⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    have h21 : BandVectors.1 (q 2) (q 1) = ⟨-1, 1⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    let S : Fin 3 → Bool → ProtoTile :=
      ![fun s => if s then
          ⟨{⟨-(k : Int), (k : Int) - 1⟩}, ⟨-(k : Int), (k : Int) - 1⟩⟩ else
          ⟨{⟨(k : Int) - 1, (k : Int)⟩}, ⟨(k : Int) - 1, (k : Int)⟩⟩,
        fun s => if s then
          ⟨{⟨(k : Int) - 1, (k : Int) - 1⟩},
            ⟨(k : Int) - 1, (k : Int) - 1⟩⟩ else
          ⟨{⟨-(k : Int), (k : Int)⟩}, ⟨-(k : Int), (k : Int)⟩⟩,
        fun s => if s then TileTranslation (DiamondTile (k - 1)) ⟨0, 2⟩ else
          DiamondTile (k - 1)]
    have row_union (x : GaussianInt) : x ∈ DiamondCellDomain k ↔
        x = ⟨-(k : Int), (k : Int) - 1⟩ ∨
        x = ⟨(k : Int) - 1, (k : Int)⟩ ∨
        x = ⟨(k : Int) - 1, (k : Int) - 1⟩ ∨
        x = ⟨-(k : Int), (k : Int)⟩ ∨
        x ∈ DiamondCellDomain (k - 1) ∨
        x - ⟨0, 2⟩ ∈ DiamondCellDomain (k - 1) := by
      simp only [(P4194T1DiamondCellRows _ _).1, Zsqrtd.ext_iff]
      norm_num
      omega
    have hcells (x : GaussianInt) :
        x ∈ (DiamondTile k).cells ↔ ∃ i s, x ∈ (S i s).cells := by
      change x ∈ DiamondCellDomain k ↔ _
      rw [row_union]
      constructor
      · rintro (hx | hx | hx | hx | hx | hx)
        · exact ⟨0, true, by simpa [S] using hx⟩
        · exact ⟨0, false, by simpa [S] using hx⟩
        · exact ⟨1, true, by simpa [S] using hx⟩
        · exact ⟨1, false, by simpa [S] using hx⟩
        · exact ⟨2, false, hx⟩
        · exact ⟨2, true, (translated_mem (k - 1) x).mpr hx⟩
      · rintro ⟨i, s, hx⟩
        fin_cases i <;> cases s
        · exact Or.inr (Or.inl (by simpa [S] using hx))
        · exact Or.inl (by simpa [S] using hx)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [S] using hx))))
        · exact Or.inr (Or.inr (Or.inl (by simpa [S] using hx)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr ((translated_mem (k - 1) x).mp hx)))))
    have hsubset (i : Fin 3) (s : Bool) : (S i s).cells ⊆ (DiamondTile k).cells := by
      intro x hx
      exact (hcells x).mpr ⟨i, s, hx⟩
    have hzero : (0 : GaussianInt) ∈ (DiamondTile k).cells := by
      apply (P4194T1DiamondCellRows k 0).1.mpr
      norm_num
      omega
    have hnonempty : (DiamondTile k).cells.Nonempty := ⟨0, hzero⟩
    have zero_foot : (0 : GaussianInt) ∈ FootprintVertices (DiamondTile k) := by
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨0, hzero, Or.inl rfl⟩
    have two_foot : (⟨0, 2⟩ : GaussianInt) ∈ FootprintVertices (DiamondTile k) := by
      have hcell : (⟨0, 1⟩ : GaussianInt) ∈ (DiamondTile k).cells := by
        apply (P4194T1DiamondCellRows k ⟨0, 1⟩).1.mpr
        norm_num
        omega
      simp only [FootprintVertices, ite_eq_left hnonempty, Set.mem_ofPred_eq]
      exact ⟨⟨0, 1⟩, hcell, Or.inr (Or.inr (Or.inl rfl))⟩
    have hfoot (i : Fin 3) (s : Bool) :
        FootprintVertices (S i s) ⊆ FootprintVertices (DiamondTile k) := by
      intro v hv
      by_cases hne : (S i s).cells.Nonempty
      · simp only [FootprintVertices, ite_eq_left hne, ite_eq_left hnonempty,
          Set.mem_ofPred_eq] at hv ⊢
        obtain ⟨x, hx, hv⟩ := hv
        exact ⟨x, hsubset i s hx, hv⟩
      · simp only [FootprintVertices, ite_eq_right hne, Set.mem_singleton_iff] at hv
        subst v
        fin_cases i <;> cases s
        · simp [S] at hne
        · simp [S] at hne
        · simp [S] at hne
        · simp [S] at hne
        · simpa [S, DiamondTile] using zero_foot
        · simpa [S, TileTranslation, GaussianTranslation, DiamondTile] using two_foot
    have hprev : BandPrototile (q 3) (DiamondTile (k - 1)) := by
      by_cases hp : 0 < k - 1
      · have hpk : k - 1 < k := by omega
        have hpred := (ih (k - 1) hpk hp).1
        have hsucc : k - 1 + 1 = k := by omega
        have hsuccI : ((k - 1 : Nat) : Int) + 1 = (k : Int) := by omega
        simpa [q, DiamondRecursiveQuadruple, hsucc, hsuccI] using hpred
      · have hk1 : k = 1 := by omega
        subst k
        convert (BandPrototile.line (-1) 0 (Or.inr rfl)) using 1 <;>
          simp [q, DiamondRecursiveQuadruple, DiamondTile, DiamondCellDomain,
            Zsqrtd.ext_iff]
    have hparents (i : Fin 3) (s : Bool) : BandPrototile (q i.succ) (S i s) := by
      fin_cases i
      · cases s
        · convert (BandPrototile.unit (⟨0, 1⟩ : GaussianInt)
              ⟨(k : Int) - 1, (k : Int)⟩ ⟨(k : Int) - 1, (k : Int)⟩) using 1 <;>
            simp [q, DiamondRecursiveQuadruple, S, Zsqrtd.ext_iff]
        · convert (BandPrototile.unit (⟨0, 1⟩ : GaussianInt)
              ⟨-(k : Int), (k : Int) - 1⟩ ⟨-(k : Int), (k : Int) - 1⟩) using 1 <;>
            simp [q, DiamondRecursiveQuadruple, S, Zsqrtd.ext_iff]
      · cases s
        · simpa [q, DiamondRecursiveQuadruple, S] using
            (BandPrototile.unit 0
              ⟨-(k : Int), (k : Int)⟩ ⟨-(k : Int), (k : Int)⟩)
        · simpa [q, DiamondRecursiveQuadruple, S] using
            (BandPrototile.unit 0
              ⟨(k : Int) - 1, (k : Int) - 1⟩ ⟨(k : Int) - 1, (k : Int) - 1⟩)
      · cases s
        · exact hprev
        · exact BandPrototileTranslation (q 3) (DiamondTile (k - 1)) ⟨0, 2⟩ hprev
    have hcentroid (i : Fin 3) (s : Bool) :
        TileCentroid (S i s) - TileCentroid (DiamondTile k) =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ)) -
                (-((GaussianRealPoint
                  (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ))).2),
                  (GaussianRealPoint
                    (BandVectors.1 (q (i + 2).succ) (q (i + 1).succ))).1))) := by
      have hsucc : 1 ≤ k := by omega
      have htrans := (TileTranslationFormulas (DiamondTile (k - 1)) ⟨0, 2⟩).2.2.2.2.1
      fin_cases i <;> cases s <;>
        simp [S, singleton_centroid, centroid, htrans, h32, h13, h21,
          GaussianRealPoint, Prod.ext_iff, Nat.cast_sub hsucc] <;> ring <;> simp
    refine ⟨BandPrototile.decompose hq hparents hcells hfoot hcentroid,
      S, ?_, hcells, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro i s
    exact ⟨hparents i s, hfoot i s, hcentroid i s⟩

end ApollonianSuperharmonic

end
