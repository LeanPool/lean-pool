/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordTileCellMembership

public import LeanPool.ApollonianSuperharmonic.FordTileOdometerRestriction
public import LeanPool.ApollonianSuperharmonic.TileOdometerTranslationUniqueness

-- [TABLET NODE: P4158T1MatchedFordPair]

/-!
# P4158T1MatchedFordPair

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace MatchedFordGeometry

private theorem hidx :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 → (1 : ℤ) < Ci.1.1.1 → i ≠ 2
    ) := by
  classical
  intro P Ci i hCi hlarge hi
  subst i
  have hc := congrArg (fun x : CircleCoordinates => x.1) hCi
  simp [FordRecursiveQuadruple] at hc
  linarith

private theorem hqgt :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                (1 : ℤ) < Ci.1.1.1 → i ≠ 2 → 1 < P.q
    ) := by
  classical
  intro P Ci i hCi hlarge hidx
  have hsumq : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
    exact_mod_cast P.sum_q
  have hc := congrArg (fun x : CircleCoordinates => x.1) hCi
  simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      Matrix.cons_val_succ] at hc
  have : 1 < P.q := by
    fin_cases i
    · simp only [Int.reduceNeg, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hc
      split at hc
      · norm_num at hc
        exact (by omega : False).elim
      · have hq : 1 < P.q₁ := by nlinarith [hlarge, hc]
        have hqNat : 1 < P.q₁ := by exact_mod_cast hq
        omega
    · simp only [Int.reduceNeg, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hc
      have hq : 1 < P.q₂ := by nlinarith [hlarge, hc]
      have hqNat : 1 < P.q₂ := by exact_mod_cast hq
      omega
    · exact (hidx rfl).elim
  exact this

private theorem hrpos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), 1 < P.q → 0 < P.q₁
    ) := by
  classical
  intro P hqgt
  by_contra hn
  have hz : P.q₁ = 0 := by omega
  have hd := P.det₁
  rw [hz] at hd
  simp at hd
  have hdvd : (P.q : Int) ∣ 1 := ⟨P.p₁, by nlinarith⟩
  have hone : (P.q : Int) = 1 := Int.eq_one_of_dvd_one (by omega) hdvd
  exact (by omega : False).elim

private theorem hneq :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                (1 : ℤ) < Ci.1.1.1 → i ≠ 2 → 0 < P.q₁ → 0 < P.q₂ → P.q₁ ≠ P.q₂
    ) := by
  classical
  intro P Ci i hCi hlarge hidx hrpos hspos heq
  have hcross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := by
    have h := P.det₁
    rw [P.sum_q, P.sum_p] at h
    push_cast at h
    nlinarith
  rw [heq] at hcross
  have hone : (P.q₁ : Int) ∣ 1 := ⟨P.p₁ - P.p₂, by nlinarith⟩
  have hqone : P.q₁ = 1 := by
    have hz := Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le P.q₁)) hone
    exact_mod_cast hz
  have hselected : 1 < P.q₁ := by
    fin_cases i
    · have hc := congrArg (fun x : CircleCoordinates => x.1) hCi
      simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
          Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one,
          Matrix.cons_val_zero] at hc
      split at hc
      · norm_num at hc
        exact (by omega : False).elim
      · have hh : 1 < P.q₁ := by nlinarith [hlarge, hc]
        exact hh
    · have hc := congrArg (fun x : CircleCoordinates => x.1) hCi
      simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
          Fin.mk_one, Fin.isValue, Fin.succ_one_eq_two, Matrix.cons_val] at hc
      have hh : 1 < P.q₂ := by nlinarith [hlarge, hc]
      omega
    · exact False.elim (hidx rfl)
  omega

private theorem hcurv :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q) → (0 < (FordCircleCoordinate P.p P.q).1) ) := by
  classical
  intro P hqpos
  change (0 : ℤ) < ((P.q * P.q : Nat) : ℤ)
  exact_mod_cast Nat.mul_pos hqpos hqpos

private theorem hHcircle :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ)) = C0.1.1) → (∀ (H : PartialOdometer), (TileOdometer (FordCircleCoordinate P.p
            P.q) (FordTile P.q) H) → (TileOdometer C0.1.1 (FordTile P.q) H)) ) := by
  classical
  intro P C0 hC0 H hHO
  rw [← hC0]
  exact hHO

private theorem hC0pos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ)) = C0.1.1) → ((0 < P.q) → (0 < C0.1.1.1)) ) := by
  classical
  intro P C0 hC0 hqpos
  have ht : 0 < (FordRecursiveQuadruple P 0).1 := by
    change (0 : ℤ) < ((P.q * P.q : Nat) : ℤ)
    exact_mod_cast Nat.mul_pos hqpos hqpos
  have := congrArg (fun x : CircleCoordinates => x.1) hC0
  simpa only [this] using ht

private theorem hFnon :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (0 < P.q) → ((FordTile P.q).cells.Nonempty) ) := by
  classical
  intro P hqpos
  refine ⟨⟨0, 0⟩, ?_⟩
  simp [FordTile, FordCellDomain, hqpos]

private theorem hTnon :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (H :
            PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile P.q)
            u).cells ∧ (T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧ ∃
            (a : GaussianInt) (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ H.domain) ∧ ∀
            x ∈ h.domain, h.value x = H.value (x - u) + a.re * x.re + a.im * x.im + b) →
            (((FordTile P.q).cells.Nonempty) → (T.cells.Nonempty)) ) := by
  classical
  intro P T h H u hu hFnon
  rw [hu.1]
  simpa [TileTranslation] using hFnon.image (GaussianTranslation u)

private abbrev hT'non := ApollonianSuperharmonic.MatchedFordGeometry.hTnon

private theorem hcentT :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (H :
            PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile P.q)
            u).cells ∧ (T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧ ∃
            (a : GaussianInt) (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ H.domain) ∧ ∀
            x ∈ h.domain, h.value x = H.value (x - u) + a.re * x.re + a.im * x.im + b) →
            (((FordTile P.q).cells.Nonempty) → ((T.cells.Nonempty) → (TileCentroid T =
            TileCentroid (TileTranslation (FordTile P.q) u)))) ) := by
  classical
  intro P T h H u hu hFnon hTnon
  have htn : (TileTranslation (FordTile P.q) u).cells.Nonempty := by
    simpa [TileTranslation] using hFnon.image (GaussianTranslation u)
  simp only [TileCentroid, ite_eq_left hTnon, ite_eq_left htn]
  rw [hu.1]

private abbrev hcentT' :=
  ApollonianSuperharmonic.MatchedFordGeometry.hcentT

private theorem hfordcent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          1 < P.q → 0 < P.q → TileCentroid (FordTile P.q) = ((P.q : ℝ) / 2, (P.q : ℝ) / 2)
    ) := by
  classical
  intro P hqgt hqpos
  let domain : Finset GaussianInt :=
    ((Finset.range P.q).product (Finset.range P.q)).image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
  have hneDomain : domain.Nonempty := by
    refine ⟨⟨0, 0⟩, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), by simp [hqpos], rfl⟩
  have hinj : Set.InjOn
      (fun a : ℕ × ℕ => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
      ↑((Finset.range P.q).product (Finset.range P.q)) := by
    intro a ha b hb hab
    apply Prod.ext
    · have h := congrArg Zsqrtd.re hab
      change (a.1 : Int) = (b.1 : Int) at h
      exact_mod_cast h
    · have h := congrArg Zsqrtd.im hab
      change (a.2 : Int) = (b.2 : Int) at h
      exact_mod_cast h
  have hcard : domain.card = P.q * P.q := by
    calc
      domain.card = ((Finset.range P.q).product (Finset.range P.q)).card := by
        dsimp [domain]
        exact Finset.card_image_iff.mpr hinj
      _ = P.q * P.q := by simp
  have hsum : domain.sum (fun z : GaussianInt => z.re) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 * (P.q : Int) := by
    have hrange : (Finset.range P.q).sum (fun n => (n : Int)) =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    conv_lhs => rw [← Finset.mul_sum (Finset.range P.q)
      (fun n => (n : Int)) (P.q : Int)]
    rw [hrange]
    ring
  have hsumIm : domain.sum (fun z : GaussianInt => z.im) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 * (P.q : Int) := by
    have hrange : (Finset.range P.q).sum (fun n => (n : Int)) =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, domain]
    rw [hrange]
    ring
  change (if domain.Nonempty then
    ((↑(domain.sum (fun z : GaussianInt => z.re) : Int) /
        ↑domain.card + (1 / 2 : Real)),
     (↑(domain.sum (fun z : GaussianInt => z.im) : Int) /
        ↑domain.card + (1 / 2 : Real))) else _) = _
  rw [ite_eq_left hneDomain, hcard, hsum, hsumIm]
  have hqcast : ((P.q - 1 : Nat) : Int) = (P.q : Int) - 1 := by omega
  rw [hqcast]
  norm_num
  field_simp
  have arithmetic := Finset.sum_range_id_mul_two P.q
  have rangeSum : (Finset.range P.q).sum (fun n => (n : Int)) =
      (P.q : Int) * ((P.q - 1 : Nat) : Int) / 2 := by
    rw [← Nat.cast_sum]
    simp [Finset.sum_range_id]
  have arithmeticCast :
      ((Finset.range P.q).sum (fun n => (n : Int))) * 2 =
        (P.q : Int) * ((P.q - 1 : Nat) : Int) := by
    rw [← Nat.cast_sum]
    exact_mod_cast arithmetic
  rw [rangeSum] at arithmeticCast
  rw [hqcast] at arithmeticCast
  have arithmeticReal :
      ((((P.q : Int) * ((P.q : Int) - 1) / 2 : Int) : ℝ) * 2) =
        (P.q : ℝ) * ((P.q : ℝ) - 1) := by
    exact_mod_cast arithmeticCast
  norm_num [Int.subNatNat, pow_two] at ⊢
  nlinarith [arithmeticReal]

private theorem hcentdiff :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀
            (v : GaussianInt), (TileCentroid T = TileCentroid (TileTranslation (FordTile P.q) u))
            → ((TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q) v)) →
            (TileCentroid T' - TileCentroid T = GaussianRealPoint (v - u))) ) := by
  classical
  intro P T T' u v hcentT hcentT'
  rw [hcentT, hcentT', (TileTranslationFormulas (FordTile P.q) u).2.2.2.2.1,
    (TileTranslationFormulas (FordTile P.q) v).2.2.2.2.1]
  simp [GaussianRealPoint]

private theorem hvec :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            ∀ (i : Fin 3),
              FordRecursiveQuadruple P i.succ = Ci.1.1 →
                i ≠ 2 →
                  BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
                        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) =
                      (⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩ : GaussianInt) →
                    BandVectors.1 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
                          (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) =
                        (⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩ : GaussianInt) →
                      BandVectors.1 (FordRecursiveQuadruple P i.succ)
                          (FordRecursiveQuadruple P 0) =
                        if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
                        else ⟨-(P.q : Int), (P.q₂ : Int)⟩
    ) := by
  classical
  intro P Ci i hCi hidx hvec0 hvec1
  fin_cases i
  · simpa using hvec0
  · simpa using hvec1
  · exact (hidx rfl).elim

private theorem hshift :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin 3), ∀ (T : ProtoTile), ∀ (T' : ProtoTile),
            (TileCentroid T' - TileCentroid T = GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) → (∀
            (u : GaussianInt), ∀ (v : GaussianInt), (TileCentroid T' - TileCentroid T =
            GaussianRealPoint (v - u)) → ((BandVectors.1 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P 0) = if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q
            : Int), (P.q₂ : Int)⟩) → (v - u = if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else
            ⟨-(P.q : Int), (P.q₂ : Int)⟩))) ) := by
  classical
  intro P i T T' hcent u v hcentdiff hvec
  have heq : GaussianRealPoint (v-u) =
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0)) := hcentdiff.symm.trans hcent
  rw [← hvec]
  apply Zsqrtd.ext
  · have hh := congrArg Prod.fst heq
    simpa [GaussianRealPoint] using (Int.cast_injective hh)
  · have hh := congrArg Prod.snd heq
    simpa [GaussianRealPoint] using (Int.cast_injective hh)

private theorem hshift' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin 3), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (v -
            u = if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩ else ⟨-(P.q : Int), (P.q₂ : Int)⟩) → (
        let d : GaussianInt :=
          if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
          else ⟨-(P.q : Int), (P.q₂ : Int)⟩
        v = u + d) ) := by
  classical
  intro P i u v hshift d
  calc
    v = (v-u)+u := by abel
    _ = d+u := by rw [hshift]
    _ = u+d := by abel

private theorem squareCell :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (z : GaussianInt),
            z ∈ (FordTile P.q).cells ↔
              0 ≤ z.re ∧ z.re < (P.q : Int) ∧ 0 ≤ z.im ∧ z.im < (P.q : Int)
    ) := by
  intro P z
  exact FordTileCellMembership P.q z

private theorem translatedCell :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (∀ (z : GaussianInt), z ∈ (FordTile P.q).cells ↔ 0 ≤ z.re ∧
            z.re < (P.q : Int) ∧ 0 ≤ z.im ∧ z.im < (P.q : Int)) → (∀ (w : GaussianInt), ∀ (z :
            GaussianInt), z ∈ (TileTranslation (FordTile P.q) w).cells ↔ 0 ≤ (z-w).re ∧ (z-w).re
            < (P.q : Int) ∧ 0 ≤ (z-w).im ∧ (z-w).im < (P.q : Int)) ) := by
  classical
  intro P squareCell w z
  rw [(TileTranslationFormulas (FordTile P.q) w).1]
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hz⟩
    have heq : a+w=z := by simpa [GaussianTranslation] using hz
    have hcoords : z-w=a := by rw [← heq]; abel
    rw [hcoords]
    exact (squareCell a).mp ha
  · intro hz
    refine ⟨z-w, (squareCell (z-w)).mpr ?_, ?_⟩
    · simpa using hz
    · simp [GaussianTranslation]

private theorem hdisj :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ∀ (T : ProtoTile),
              ∀ (T' : ProtoTile),
                ∀ (h : PartialOdometer),
                  ∀ (h' : PartialOdometer),
                    ∀ (H : PartialOdometer),
                      ∀ (u : GaussianInt),
                        (T.cells = (TileTranslation (FordTile P.q) u).cells ∧
                            (T.cells = ∅ →
                                T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧
                              ∃ (a : GaussianInt) (b : ℤ),
                                (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ H.domain) ∧
                                ∀ x ∈ h.domain,
                                h.value x =
                                H.value (x - u) + a.re * x.re + a.im * x.im + b) →
                          ∀ (v : GaussianInt),
                            (T'.cells = (TileTranslation (FordTile P.q) v).cells ∧
                                (T'.cells = ∅ →
                                T'.anchor = (TileTranslation (FordTile P.q) v).anchor) ∧
                                ∃ (a : GaussianInt) (b : ℤ),
                                (∀ (x : GaussianInt), x ∈ h'.domain ↔ x - v ∈ H.domain) ∧
                                ∀ x ∈ h'.domain,
                                h'.value x =
                                H.value (x - v) + a.re * x.re + a.im * x.im + b) →
                              let d : GaussianInt :=
                                if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
                              else ⟨-(P.q : Int), (P.q₂ : Int)⟩
                              v = u + d →
                                (∀ (w : GaussianInt),
                                ∀ (z : GaussianInt),
                                z ∈ (TileTranslation (FordTile P.q) w).cells ↔
                                0 ≤ (z - w).re ∧
                                (z - w).re < (P.q : Int) ∧
                                0 ≤ (z - w).im ∧ (z - w).im < (P.q : Int)) →
                                Disjoint T.cells T'.cells
    ) := by
  classical
  intro P i T T' h h' H u hu v hv d hshift' translatedCell
  rw [hu.1, hv.1]
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  have hleft := (translatedCell u x).mp hx
  have hright := (translatedCell v x).mp hx'
  have hrel : (x-v).re = (x-u).re-d.re := by
    rw [hshift']
    simp
    ring
  by_cases hi : i = 0
  · simp [d, hi] at hrel hleft hright
    omega
  · simp [d, hi] at hrel hleft hright
    omega

private theorem hsecond :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (i : Fin 3), ∀ (T' : ProtoTile), ∀ (h' : PartialOdometer),
            ∀ (H : PartialOdometer), ∀ (u : GaussianInt), ∀ (v : GaussianInt), (T'.cells =
            (TileTranslation (FordTile P.q) v).cells ∧ (T'.cells = ∅ → T'.anchor =
            (TileTranslation (FordTile P.q) v).anchor) ∧ ∃ (a : GaussianInt) (b : ℤ), (∀ (x :
            GaussianInt), x ∈ h'.domain ↔ x - v ∈ H.domain) ∧ ∀ x ∈ h'.domain, h'.value x =
            H.value (x - v) + a.re * x.re + a.im * x.im + b) → (
        let d : GaussianInt :=
          if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
          else ⟨-(P.q : Int), (P.q₂ : Int)⟩
        (v = u + d) → (T'.cells = (TileTranslation (FordTile P.q) (u+d)).cells)) ) := by
  classical
  intro P i T' h' H u v hv d hshift'
  calc
    T'.cells = (TileTranslation (FordTile P.q) v).cells := hv.1
    _ = (TileTranslation (FordTile P.q) (u+d)).cells := by rw [hshift']

private theorem translatedFootprint :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((FordTile P.q).cells.Nonempty) → ((FootprintVertices
            (FordTile P.q) = FordVertexDomain P.q) → (∀ (w : GaussianInt), FootprintVertices
            (TileTranslation (FordTile P.q) w) = GaussianTranslation w '' FordVertexDomain P.q))
            ) := by
  classical
  intro P hFnon hFfoot w
  have htn : (TileTranslation (FordTile P.q) w).cells.Nonempty := by
    simpa [TileTranslation] using hFnon.image (GaussianTranslation w)
  calc
    FootprintVertices (TileTranslation (FordTile P.q) w) =
        GaussianTranslation w '' FootprintVertices (FordTile P.q) :=
      (TileTranslationFormulas (FordTile P.q) w).2.2.2.2.2.1
    _ = GaussianTranslation w '' FordVertexDomain P.q := by rw [hFfoot]

private theorem footprintCoord :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (∀ (w : GaussianInt), FootprintVertices (TileTranslation
            (FordTile P.q) w) = GaussianTranslation w '' FordVertexDomain P.q) → (∀ (w :
            GaussianInt), ∀ (z : GaussianInt), z ∈ FootprintVertices (TileTranslation (FordTile
            P.q) w) ↔ 0 ≤ (z-w).re ∧ (z-w).re ≤ (P.q : Int) ∧ 0 ≤ (z-w).im ∧ (z-w).im ≤ (P.q :
            Int)) ) := by
  classical
  intro P translatedFootprint w z
  rw [translatedFootprint w]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    have heq' : y+w=z := by simpa [GaussianTranslation] using heq
    have hy' : y ∈ FordVertexDomain P.q := hy
    have hz : z-w=y := by rw [← heq']; abel
    rw [hz]
    simpa [FordVertexDomain] using hy'
  · intro hz
    refine ⟨z-w, ?_, ?_⟩
    · change 0 ≤ (z-w).re ∧ (z-w).re ≤ (P.q : Int) ∧
        0 ≤ (z-w).im ∧ (z-w).im ≤ (P.q : Int)
      exact hz
    · simp [GaussianTranslation]

private theorem footprintT :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (H :
            PartialOdometer), ∀ (u : GaussianInt), (T.cells = (TileTranslation (FordTile P.q)
            u).cells ∧ (T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor) ∧ ∃
            (a : GaussianInt) (b : ℤ), (∀ (x : GaussianInt), x ∈ h.domain ↔ x - u ∈ H.domain) ∧ ∀
            x ∈ h.domain, h.value x = H.value (x - u) + a.re * x.re + a.im * x.im + b) →
            (((FordTile P.q).cells.Nonempty) → ((T.cells.Nonempty) → (FootprintVertices T =
            FootprintVertices (TileTranslation (FordTile P.q) u)))) ) := by
  classical
  intro P T h H u hu hFnon hTnon
  simp only [FootprintVertices, ite_eq_left hTnon]
  have htn : (TileTranslation (FordTile P.q) u).cells.Nonempty := by
    simpa [TileTranslation] using hFnon.image (GaussianTranslation u)
  simp only [ite_eq_left htn]
  rw [hu.1]

private abbrev footprintT' :=
  ApollonianSuperharmonic.MatchedFordGeometry.footprintT

private theorem hinter :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (i : Fin 3),
            ∀ (T : ProtoTile),
              ∀ (T' : ProtoTile),
                1 < P.q →
                  0 < P.q₁ →
                    0 < P.q₂ →
                      ∀ (u : GaussianInt),
                        ∀ (v : GaussianInt),
                          let d : GaussianInt :=
                            if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
                            else ⟨-(P.q : Int), (P.q₂ : Int)⟩
                          v = u + d →
                            (∀ (w : GaussianInt),
                                ∀ (z : GaussianInt),
                                z ∈ FootprintVertices (TileTranslation (FordTile P.q) w) ↔
                                0 ≤ (z - w).re ∧
                                (z - w).re ≤ (P.q : Int) ∧
                                0 ≤ (z - w).im ∧ (z - w).im ≤ (P.q : Int)) →
                              FootprintVertices T =
                                FootprintVertices (TileTranslation (FordTile P.q) u) →
                                FootprintVertices T' =
                                FootprintVertices (TileTranslation (FordTile P.q) v) →
                                ∀ x,
                                x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
                                ((x - u).re = if i = 0 then (P.q : Int) else 0) ∧
                                (if i = 0 then (P.q₁ : Int) else (P.q₂ : Int)) ≤
                                (x - u).im ∧
                                (x - u).im ≤ (P.q : Int)
    ) := by
  classical
  intro P i T T' hqgt hrpos hspos u v d hshift' footprintCoord footprintT footprintT' x
  rw [Set.mem_inter_iff, footprintT, footprintT']
  rw [(footprintCoord u x), (footprintCoord v x)]
  have hrelRe : (x-v).re = (x-u).re-d.re := by rw [hshift']; simp; ring
  have hrelIm : (x-v).im = (x-u).im-d.im := by rw [hshift']; simp; ring
  by_cases hi : i = 0
  · simp [d, hi, hrelRe, hrelIm]
    omega
  · simp [d, hi, hrelRe, hrelIm]
    omega

end MatchedFordGeometry

theorem P4158T1MatchedFordPair
    (P : FordFareyParameter)
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : FordRecursiveQuadruple P 0 = C0.1.1)
    (hCi : FordRecursiveQuadruple P i.succ = Ci.1.1)
    (T T' : ProtoTile) (h h' : PartialOdometer)
    (hO : TileOdometer C0.1.1 T h) (hO' : TileOdometer C0.1.1 T' h')
    (hlarge : 1 < Ci.1.1.1)
    (hcent : TileCentroid T' - TileCentroid T =
      GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
        (FordRecursiveQuadruple P 0))) :
    i ≠ 2 ∧ 1 < P.q ∧ 0 < P.q₁ ∧ P.q₁ ≠ P.q₂ ∧
    ∃ u : GaussianInt,
      T.cells = (TileTranslation (FordTile P.q) u).cells ∧
      T'.cells = (TileTranslation (FordTile P.q)
        (u + if i = 0 then ⟨P.q, P.q₁⟩ else ⟨-(P.q : Int), P.q₂⟩)).cells ∧
      Disjoint T.cells T'.cells ∧
      (∀ x, x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
        (x - u).re = (if i = 0 then (P.q : Int) else 0) ∧
        (if i = 0 then (P.q₁ : Int) else P.q₂) ≤ (x - u).im ∧
        (x - u).im ≤ (P.q : Int)) := by
-- BODY
  classical
  have hidx : i ≠ 2 := MatchedFordGeometry.hidx P Ci i hCi hlarge
  have hqgt : 1 < P.q := MatchedFordGeometry.hqgt P Ci i hCi hlarge hidx
  have hqpos : 0 < P.q := by omega
  have hrpos : 0 < P.q₁ := MatchedFordGeometry.hrpos P hqgt
  have hspos : 0 < P.q₂ := P.q₂_pos
  have hneq : P.q₁ ≠ P.q₂ := MatchedFordGeometry.hneq P Ci i hCi hlarge hidx hrpos hspos
  have hcurv : 0 < (FordCircleCoordinate P.p P.q).1 := MatchedFordGeometry.hcurv P hqpos
  obtain ⟨H, hHO, hHD, hHV⟩ := FordTileOdometerRestriction P
  have hHcircle : TileOdometer C0.1.1 (FordTile P.q) H := MatchedFordGeometry.hHcircle P C0 hC0 H
      hHO
  have hC0pos : 0 < C0.1.1.1 := MatchedFordGeometry.hC0pos P C0 hC0 hqpos
  obtain ⟨u, hu, huuniq⟩ := TileOdometerTranslationUniqueness
    C0.1.1 T (FordTile P.q) h H hC0pos hO hHcircle
  obtain ⟨v, hv, hvuniq⟩ := TileOdometerTranslationUniqueness
    C0.1.1 T' (FordTile P.q) h' H hC0pos hO' hHcircle
  obtain ⟨a, b, hud, huv⟩ := hu.2.2
  obtain ⟨a', b', hvd, hvv⟩ := hv.2.2
  have hFnon : (FordTile P.q).cells.Nonempty := MatchedFordGeometry.hFnon P hqpos
  have hTnon : T.cells.Nonempty := MatchedFordGeometry.hTnon P T h H u hu hFnon
  have hT'non : T'.cells.Nonempty := MatchedFordGeometry.hT'non P T' h' H v hv hFnon
  have hcentT : TileCentroid T = TileCentroid (TileTranslation (FordTile P.q) u) :=
      MatchedFordGeometry.hcentT P T h H u hu hFnon hTnon
  have hcentT' : TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q) v) :=
      MatchedFordGeometry.hcentT' P T' h' H v hv hFnon hT'non
  have hfordcent : TileCentroid (FordTile P.q) =
      ((P.q : ℝ) / 2, (P.q : ℝ) / 2) := MatchedFordGeometry.hfordcent P hqgt hqpos
  have hcentdiff : TileCentroid T' - TileCentroid T =
      GaussianRealPoint (v - u) := MatchedFordGeometry.hcentdiff P T T' u v hcentT hcentT'
  obtain ⟨_, hconfig⟩ := FordCoordinateConfiguration P
  obtain ⟨_, hvec0, hvec1, _, _, _, _, _, _⟩ := hconfig hqgt
  have hvec : BandVectors.1 (FordRecursiveQuadruple P i.succ)
      (FordRecursiveQuadruple P 0) =
      if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
      else ⟨-(P.q : Int), (P.q₂ : Int)⟩ := MatchedFordGeometry.hvec P Ci i hCi hidx
          hvec0 hvec1
  have hshift : v - u =
      if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
      else ⟨-(P.q : Int), (P.q₂ : Int)⟩ := MatchedFordGeometry.hshift P i T T' hcent u v
          hcentdiff hvec
  let d : GaussianInt :=
    if i = 0 then ⟨(P.q : Int), (P.q₁ : Int)⟩
    else ⟨-(P.q : Int), (P.q₂ : Int)⟩
  have hshift' : v = u + d := MatchedFordGeometry.hshift' P i u v hshift
  have squareCell (z : GaussianInt) :
      z ∈ (FordTile P.q).cells ↔
        0 ≤ z.re ∧ z.re < (P.q : Int) ∧
          0 ≤ z.im ∧ z.im < (P.q : Int) := MatchedFordGeometry.squareCell P z
  have translatedCell (w z : GaussianInt) :
      z ∈ (TileTranslation (FordTile P.q) w).cells ↔
        0 ≤ (z-w).re ∧ (z-w).re < (P.q : Int) ∧
          0 ≤ (z-w).im ∧ (z-w).im < (P.q : Int) := MatchedFordGeometry.translatedCell P
              squareCell w z
  have hdisj : Disjoint T.cells T'.cells := MatchedFordGeometry.hdisj P i T T' h h' H u hu
      v hv hshift' translatedCell
  have hsecond : T'.cells = (TileTranslation (FordTile P.q) (u+d)).cells :=
      MatchedFordGeometry.hsecond P i T' h' H u v hv hshift'
  have hFfoot : FootprintVertices (FordTile P.q) = FordVertexDomain P.q :=
    (P4062T1CanonicalSupport P.q hqpos).1
  have translatedFootprint (w : GaussianInt) :
      FootprintVertices (TileTranslation (FordTile P.q) w) =
        GaussianTranslation w '' FordVertexDomain P.q := MatchedFordGeometry.translatedFootprint
            P hFnon hFfoot w
  have footprintCoord (w z : GaussianInt) :
      z ∈ FootprintVertices (TileTranslation (FordTile P.q) w) ↔
        0 ≤ (z-w).re ∧ (z-w).re ≤ (P.q : Int) ∧
          0 ≤ (z-w).im ∧ (z-w).im ≤ (P.q : Int) := MatchedFordGeometry.footprintCoord P
              translatedFootprint w z
  have footprintT : FootprintVertices T =
      FootprintVertices (TileTranslation (FordTile P.q) u) := MatchedFordGeometry.footprintT P T
          h H u hu hFnon hTnon
  have footprintT' : FootprintVertices T' =
      FootprintVertices (TileTranslation (FordTile P.q) v) := MatchedFordGeometry.footprintT' P
          T' h' H v hv hFnon hT'non
  have hinter : ∀ x, x ∈ FootprintVertices T ∩ FootprintVertices T' ↔
      (x-u).re = (if i = 0 then (P.q : Int) else 0) ∧
        (if i = 0 then (P.q₁ : Int) else (P.q₂ : Int)) ≤ (x-u).im ∧
        (x-u).im ≤ (P.q : Int) := MatchedFordGeometry.hinter P i T T' hqgt hrpos hspos u v
            hshift' footprintCoord footprintT footprintT'
  refine ⟨hidx, hqgt, hrpos, hneq, u, hu.1, ?_, hdisj, ?_⟩
  · simpa [d] using hsecond
  · exact hinter

end ApollonianSuperharmonic

end
