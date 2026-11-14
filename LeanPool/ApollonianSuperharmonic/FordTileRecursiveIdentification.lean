/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordFareyParentsExist
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.FordTile
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.P4210T1FordCellRectangles
public import LeanPool.ApollonianSuperharmonic.P4210T1FordSquareCentroid
public import LeanPool.ApollonianSuperharmonic.P4062T1CanonicalSupport

-- [TABLET NODE: FordTileRecursiveIdentification]

/-!
# FordTileRecursiveIdentification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem fordDeterminantCoprime : ∀ (a : Int) (b d : Nat) (c : Int),
        a * (d : Int) - (b : Int) * c = 1 → Nat.Coprime b a.natAbs := by
  intro a b d c hd
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let g := Nat.gcd b a.natAbs
  have gb : g ∣ b := Nat.gcd_dvd_left _ _
  have ga : g ∣ a.natAbs := Nat.gcd_dvd_right _ _
  have gb' : (g : Int) ∣ (b : Int) := by exact_mod_cast gb
  have ga' : (g : Int) ∣ a := (Int.dvd_natAbs).mp (by exact_mod_cast ga)
  have gd : (g : Int) ∣ a * (d : Int) - (b : Int) * c :=
    dvd_sub (dvd_mul_of_dvd_left ga' _) (dvd_mul_of_dvd_left gb' _)
  have gd1 : (g : Int) ∣ 1 := by simpa [hd] using gd
  have ge : (g : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le g)) gd1
  have gn : g = 1 := by exact_mod_cast ge
  simp [g, gn]

theorem FordTileRecursiveIdentification (P : FordFareyParameter) :
    BandPrototile (FordCircleCoordinate P.p P.q) (FordTile P.q) ∧
      (P.q = 1 → FordTile P.q = ⟨{0}, 0⟩) ∧
      (1 < P.q →
        ProperBandQuadruple (FordRecursiveQuadruple P) ∧
        ∃ S : Fin 3 → Bool → ProtoTile,
          (∀ i s, BandSubtileOccurrence (FordRecursiveQuadruple P)
            (FordTile P.q) i s (S i s)) ∧
          (∀ x, x ∈ (FordTile P.q).cells ↔ ∃ i s, x ∈ (S i s).cells) ∧
          (S 0 true).cells = (FordTile P.q₁).cells ∧
          (S 0 false).cells =
            (TileTranslation (FordTile P.q₁)
              ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).cells ∧
          (S 1 true).cells =
            (TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩).cells ∧
          (S 1 false).cells =
            (TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩).cells ∧
          (S 2 true).cells = ∅ ∧
          (S 2 true).anchor = ⟨(P.q₂ : Int), (P.q : Int)⟩ ∧
          (S 2 false).cells = ∅ ∧
          (S 2 false).anchor = ⟨(P.q₁ : Int), 0⟩) := by
-- BODY
  classical
  generalize hn : P.q = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    subst n
    by_cases hu : P.q = 1
    · have htile : FordTile P.q = ⟨{0}, 0⟩ := by
        simp [hu, FordTile, FordCellDomain, Finset.range_one]
        rfl
      refine ⟨?_, fun _ => htile, ?_⟩
      · rw [htile]
        convert BandPrototile.unit ⟨0, P.p⟩ 0 0 using 1;
          simp only [FordCircleCoordinate, hu, mul_one, Nat.cast_one, Int.reduceNeg,
              Prod.mk.injEq, true_and]
        ext <;> simp
      · intro hgt
        omega
    have hgt : 1 < P.q := by have := P.q_pos; omega
    have q1pos : 0 < P.q₁ := by
      by_contra h
      have hz : P.q₁ = 0 := by omega
      have hd := P.det₁
      simp [hz] at hd
      have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
      have hqone : (P.q : Int) = 1 := Int.eq_one_of_dvd_one (by omega) hdv
      omega
    have q2lt : P.q₂ < P.q := by have := P.sum_q; omega
    have cross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := by
      have h1 : P.p₁ * ((P.q₁ + P.q₂ : Nat) : Int) -
          (P.q₁ : Int) * (P.p₁ + P.p₂) = 1 := by
        simpa [P.sum_q, P.sum_p] using P.det₁
      norm_num [Nat.cast_add] at h1
      nlinarith [h1]
    have determinantCoprime := fordDeterminantCoprime
    have red1 := determinantCoprime P.p₁ P.q₁ P.q₂ P.p₂ cross
    have red2 : Nat.Coprime P.q₂ P.p₂.natAbs := by
      have h := determinantCoprime (-P.p₂) P.q₂ P.q₁ (-P.p₁) (by nlinarith [cross])
      simpa using h
    obtain ⟨P1, ⟨hp1, hq1⟩, _⟩ := FordFareyParentsExist P.p₁ P.q₁ q1pos red1
    obtain ⟨P2, ⟨hp2, hq2⟩, _⟩ := FordFareyParentsExist P.p₂ P.q₂ P.q₂_pos red2
    have parent1 : BandPrototile (FordCircleCoordinate P.p₁ P.q₁) (FordTile P.q₁) := by
      have h := (ih P.q₁ P.q₁_lt P1 hq1).1
      simpa [hp1, hq1] using h
    have parent2 : BandPrototile (FordCircleCoordinate P.p₂ P.q₂) (FordTile P.q₂) := by
      have h := (ih P.q₂ q2lt P2 hq2).1
      simpa [hp2, hq2] using h
    let q := FordRecursiveQuadruple P
    obtain ⟨hq, h10, h20, h30, _⟩ := (FordCoordinateConfiguration P).2 hgt
    change ProperBandQuadruple q at hq
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
    have hsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
      exact_mod_cast P.sum_q
    have h32 : BandVectors.1 (q 3) (q 2) = ⟨0, -(P.q₂ : Int)⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    have h13 : BandVectors.1 (q 1) (q 3) = ⟨(P.q₁ : Int), 0⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    have h21 : BandVectors.1 (q 2) (q 1) = ⟨-(P.q₁ : Int), (P.q₂ : Int)⟩ := by
      apply Zsqrtd.ext <;> dsimp <;> omega
    let S : Fin 3 → Bool → ProtoTile :=
      ![fun s => if s then FordTile P.q₁ else
          TileTranslation (FordTile P.q₁) ⟨(P.q₂ : Int), (P.q₂ : Int)⟩,
        fun s => if s then
          TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩ else
          TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩,
        fun s => if s then ⟨∅, ⟨(P.q₂ : Int), (P.q : Int)⟩⟩ else
          ⟨∅, ⟨(P.q₁ : Int), 0⟩⟩]
    have hS (i : Fin 3) (s : Bool) : BandPrototile (q i.succ) (S i s) := by
      have hne : P.q₁ ≠ 0 := by omega
      fin_cases i <;> cases s
      · simpa [S, q, FordRecursiveQuadruple, hne] using
          BandPrototileTranslation _ _ ⟨(P.q₂ : Int), (P.q₂ : Int)⟩ parent1
      · simpa [S, q, FordRecursiveQuadruple, hne] using parent1
      · simpa [S, q, FordRecursiveQuadruple] using
          BandPrototileTranslation _ _ ⟨0, (P.q₁ : Int)⟩ parent2
      · simpa [S, q, FordRecursiveQuadruple] using
          BandPrototileTranslation _ _ ⟨(P.q₁ : Int), 0⟩ parent2
      · exact BandPrototile.line (-1) _ (Or.inr rfl)
      · exact BandPrototile.line (-1) _ (Or.inr rfl)
    have row_union (x : GaussianInt) : x ∈ (FordTile P.q).cells ↔
        x ∈ (FordTile P.q₁).cells ∨
        x ∈ (TileTranslation (FordTile P.q₁) ⟨(P.q₂ : Int), (P.q₂ : Int)⟩).cells ∨
        x ∈ (TileTranslation (FordTile P.q₂) ⟨(P.q₁ : Int), 0⟩).cells ∨
        x ∈ (TileTranslation (FordTile P.q₂) ⟨0, (P.q₁ : Int)⟩).cells := by
      exact (P4210T1FordCellRectangles P.q x).2 P.q₁ P.q₂ P.sum_q
    have hcells (x : GaussianInt) :
        x ∈ (FordTile P.q).cells ↔ ∃ i s, x ∈ (S i s).cells := by
      rw [row_union]
      constructor
      · rintro (hx | hx | hx | hx)
        · exact ⟨0, true, hx⟩
        · exact ⟨0, false, hx⟩
        · exact ⟨1, true, hx⟩
        · exact ⟨1, false, hx⟩
      · rintro ⟨i, s, hx⟩
        fin_cases i <;> cases s
        · exact Or.inr (Or.inl hx)
        · exact Or.inl hx
        · exact Or.inr (Or.inr (Or.inr hx))
        · exact Or.inr (Or.inr (Or.inl hx))
        · simp [S] at hx
        · simp [S] at hx
    have hsubset (i : Fin 3) (s : Bool) : (S i s).cells ⊆ (FordTile P.q).cells := by
      intro x hx
      exact (hcells x).mpr ⟨i, s, hx⟩
    have hfoot (i : Fin 3) (s : Bool) :
        FootprintVertices (S i s) ⊆ FootprintVertices (FordTile P.q) := by
      intro v hv
      have hroot : (FordTile P.q).cells.Nonempty := by
        refine ⟨0, (P4210T1FordCellRectangles _ _).1.mpr ?_⟩
        simpa using P.q_pos
      by_cases hne : (S i s).cells.Nonempty
      · simp only [FootprintVertices, ite_eq_left hne, ite_eq_left hroot,
          Set.mem_ofPred_eq] at hv ⊢
        obtain ⟨x, hx, hv⟩ := hv
        exact ⟨x, hsubset i s hx, hv⟩
      · simp only [FootprintVertices, ite_eq_right hne, Set.mem_singleton_iff] at hv
        subst v
        have ne1 : (FordTile P.q₁).cells.Nonempty := by
          refine ⟨0, (P4210T1FordCellRectangles _ _).1.mpr ?_⟩
          simpa using q1pos
        have ne2 : (FordTile P.q₂).cells.Nonempty := by
          refine ⟨0, (P4210T1FordCellRectangles _ _).1.mpr ?_⟩
          simpa using P.q₂_pos
        fin_cases i <;> cases s
        · exact False.elim (hne (ne1.image _))
        · exact False.elim (hne ne1)
        · exact False.elim (hne (ne2.image _))
        · exact False.elim (hne (ne2.image _))
        · rw [(P4062T1CanonicalSupport _ P.q_pos).1]
          change 0 ≤ (P.q₁ : Int) ∧ (P.q₁ : Int) ≤ (P.q : Int) ∧ 0 ≤ 0 ∧ 0 ≤ (P.q : Int)
          omega
        · rw [(P4062T1CanonicalSupport _ P.q_pos).1]
          change 0 ≤ (P.q₂ : Int) ∧ (P.q₂ : Int) ≤ (P.q : Int) ∧
            0 ≤ (P.q : Int) ∧ (P.q : Int) ≤ (P.q : Int)
          omega
    have hcentroid (i : Fin 3) (s : Bool) :
        TileCentroid (S i s) - TileCentroid (FordTile P.q) =
          (if s = true then (1 : Real) else -1) •
            ((1 / 2 : Real) •
              (GaussianRealPoint (BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))) -
                (-(GaussianRealPoint (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).2,
                  (GaussianRealPoint (BandVectors.1 (q ((i + 2).succ))
                    (q ((i + 1).succ)))).1))) := by
      have cr := P4210T1FordSquareCentroid _ P.q_pos
      have c1 := P4210T1FordSquareCentroid _ q1pos
      have c2 := P4210T1FordSquareCentroid _ P.q₂_pos
      have cs : (P.q : Real) = (P.q₁ : Real) + (P.q₂ : Real) := by
        exact_mod_cast P.sum_q
      have ctrans (r : Nat) (u : GaussianInt) :=
        (TileTranslationFormulas (FordTile r) u).2.2.2.2.1
      have cempty (a : GaussianInt) : TileCentroid (⟨∅, a⟩ : ProtoTile) =
          ((a.re : Real), (a.im : Real)) := by simp [TileCentroid]
      fin_cases i <;> cases s <;>
        simp only [Int.reduceNeg, Fin.mk_one, Fin.isValue, Matrix.cons_val',
            Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_fin_one, Matrix.cons_val_one,
            Matrix.cons_val_zero, ctrans, c2, Int.cast_zero, add_zero, Int.cast_natCast, cr,
            Prod.mk_sub_mk, one_div, GaussianRealPoint, Fin.reduceAdd, Fin.succ_zero_eq_one,
            Fin.reduceSucc, h13, neg_zero, sub_zero, zero_sub, Prod.smul_mk, smul_eq_mul,
            mul_neg, neg_smul, one_smul, Prod.neg_mk, neg_neg, Prod.ext_iff, S,
            Fin.reduceFinMk, Matrix.cons_val, cempty, Fin.succ_one_eq_two, h21, Int.cast_neg,
            sub_neg_eq_add, neg_inj, Fin.zero_eta, c1, zero_add, h32, and_self] <;>
        (try constructor) <;> linarith only [cs]
    refine ⟨?_, ?_, ?_⟩
    · exact BandPrototile.decompose hq hS hcells hfoot hcentroid
    · intro h
      omega
    · intro _
      exact ⟨hq, S, (fun i s => ⟨hS i s, hfoot i s, hcentroid i s⟩),
        hcells, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ApollonianSuperharmonic

end
