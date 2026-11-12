/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality

-- [TABLET NODE: P4158T1LargeFirstRestrictions]

/-!
# P4158T1LargeFirstRestrictions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LargeFirstRestrictions

private theorem hq1 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → (1 < P.q₁)) ) := by
  classical
  intro P Ci horder
  have hq2 := P.q₂_pos
  omega

private theorem hqgt :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((1 < P.q₁) → (1 < P.q)) ) := by
  classical
  intro P Ci hq1
  have hsum := P.sum_q
  have hq2 := P.q₂_pos
  omega

private theorem hroot :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (1 < P.q) → (1 < (FordRecursiveQuadruple P 0).1) ) := by
  classical
  intro P hqgt
  simp [FordRecursiveQuadruple, FordCircleCoordinate]
  nlinarith

private theorem hATU :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) =
            C0.1.1) → ((FordRecursiveQuadruple P (1 : Fin (4 : ℕ)) = Ci.1.1) → (∀ (T :
            ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (BandPrototile (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) T) →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S i s) ⊆ FootprintVertices T)
            → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T = (if s
            = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let U := S 0 false
        let g := gS 0 false
        (TileOdometer Ci.1.1 U g) → (AncestorTile Ci.1.1 C0.1.1 U T))))))) ) := by
  classical
  intro P hq C0 Ci hC0 hCi T S gS hbandT hfoot hcent U g hUg
  unfold AncestorTile
  apply Relation.ReflTransGen.single
  refine ⟨FordRecursiveQuadruple P, 0, false, hq, ?_, ?_, ?_, ?_, hfoot 0 false, ?_⟩
  · exact hC0
  · exact hCi
  · exact (by simpa only [← hC0] using hbandT)
  · exact TileOdometerBandPrototile _ _ _ hUg
  · exact hcent 0 false

private theorem hATV :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) =
            C0.1.1) → ((FordRecursiveQuadruple P (1 : Fin (4 : ℕ)) = Ci.1.1) → (∀ (T' :
            ProtoTile), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (kS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (BandPrototile (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) T') →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S' i s) ⊆ FootprintVertices
            T') → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S' i s) - TileCentroid T' =
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let V := S' 0 true
        let k := kS 0 true
        (TileOdometer Ci.1.1 V k) → (AncestorTile Ci.1.1 C0.1.1 V T'))))))) ) := by
  classical
  intro P hq C0 Ci hC0 hCi T' S' kS hbandT' hfoot' hcent' V k hVk
  unfold AncestorTile
  apply Relation.ReflTransGen.single
  refine ⟨FordRecursiveQuadruple P, 0, true, hq, ?_, ?_, ?_, ?_, hfoot' 0 true, ?_⟩
  · exact hC0
  · exact hCi
  · exact (by simpa only [← hC0] using hbandT')
  · exact TileOdometerBandPrototile _ _ _ hVk
  · exact hcent' 0 true

private theorem hAncU :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T : ProtoTile), ∀ (h :
            PartialOdometer), (TileOdometer C0.1.1 T h) → (∀ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (gS : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (x : GaussianInt), x ∈
            h.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (gS i s).domain) → ((∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ x ∈ (gS i s).domain, h.value x = (gS i s).value x) → (
        let U := S 0 false
        let g := gS 0 false
        (TileOdometer Ci.1.1 U g) → ((0 < Ci.1.1.1) → ((AncestorTile Ci.1.1 C0.1.1 U T) →
            (AncestorOdometer Ci.1.1 C0.1.1 U T g h))))))) ) := by
  classical
  intro P C0 Ci hC0 T h hO S gS hdom hvalue U g hUg hCiPos hATU
  refine ⟨by simpa only [← hC0] using hO, hATU, ?_, ?_, ?_⟩
  · exact PositiveCurvatureTileOdometerDomain Ci.1.1 U g hCiPos hUg
  · intro y hy
    exact (hdom y).mpr ⟨0, false, hy⟩
  · intro y hy
    exact (hvalue 0 false y hy).symm

private theorem hAncV :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), ∀ (Ci : BandCircle),
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) = C0.1.1) → (∀ (T' : ProtoTile), ∀ (h' :
            PartialOdometer), (TileOdometer C0.1.1 T' h') → (∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile), ∀ (kS : Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (x : GaussianInt), x ∈
            h'.domain ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (kS i s).domain) → ((∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ x ∈ (kS i s).domain, h'.value x = (kS i s).value x) → (
        let V := S' 0 true
        let k := kS 0 true
        (TileOdometer Ci.1.1 V k) → ((0 < Ci.1.1.1) → ((AncestorTile Ci.1.1 C0.1.1 V T') →
            (AncestorOdometer Ci.1.1 C0.1.1 V T' k h'))))))) ) := by
  classical
  intro P C0 Ci hC0 T' h' hO' S' kS hdom' hvalue' V k hVk hCiPos hATV
  refine ⟨by simpa only [← hC0] using hO', hATV, ?_, ?_, ?_⟩
  · exact PositiveCurvatureTileOdometerDomain Ci.1.1 V k hCiPos hVk
  · intro y hy
    exact (hdom' y).mpr ⟨0, true, hy⟩
  · intro y hy
    exact (hvalue' 0 true y hy).symm

private theorem hcross :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 ) := by
  classical
  intro P
  have h := P.det₁
  rw [P.sum_q, P.sum_p] at h
  push_cast at h
  nlinarith

private theorem hcop :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1) →
            (Nat.Coprime P.q₁ P.p₁.natAbs) ) := by
  classical
  intro P hcross
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let d := Nat.gcd P.q₁ P.p₁.natAbs
  have hdq : d ∣ P.q₁ := Nat.gcd_dvd_left _ _
  have hdp : d ∣ P.p₁.natAbs := Nat.gcd_dvd_right _ _
  have hdq' : (d : Int) ∣ (P.q₁ : Int) := by exact_mod_cast hdq
  have hdp' : (d : Int) ∣ P.p₁ :=
    (Int.dvd_natAbs).mp (by exact_mod_cast hdp)
  have hd : (d : Int) ∣ 1 := by
    have hm : (d : Int) ∣ P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ :=
      dvd_sub (dvd_mul_of_dvd_left hdp' _) (dvd_mul_of_dvd_left hdq' _)
    simpa [hcross] using hm
  have hd1 : (d : Int) = 1 := Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le d)) hd
  have hdNat : d = 1 := by exact_mod_cast hd1
  simpa [d] using hdNat

private theorem hQchild :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (1 :
            Fin (4 : ℕ)) = Ci.1.1) → (∀ (horder : P.q₂ < P.q₁), ∀ (hq1 : 1 < P.q₁), ∀ (hcross :
                P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1), ∀ (hcop : Nat.Coprime P.q₁
                P.p₁.natAbs),
        let Q : FordFareyParameter := {
          p := P.p₁
          q := P.q₁
          q_pos := by omega
          reduced := hcop
          p₁ := P.p₁ - P.p₂
          q₁ := P.q₁ - P.q₂
          p₂ := P.p₂
          q₂ := P.q₂
          sum_p := by omega
          sum_q := by omega
          det₁ := by
            rw [Nat.cast_sub (by omega)]
            nlinarith
          det₂ := by
            nlinarith
          q₁_lt := by
            exact Nat.sub_lt (by omega : 0 < P.q₁) P.q₂_pos
          q₂_pos := P.q₂_pos
          unit_case := by
            intro hu
            change P.q₁ = 1 at hu
            omega }
        FordRecursiveQuadruple Q 0 = Ci.1.1)) := by
  classical
  intro P Ci hCi horder hq1 hcross hcop Q
  rw [← hCi]
  have hq1nz : P.q₁ ≠ 0 := by omega
  simp [FordRecursiveQuadruple, Q, hq1nz]

private theorem hQbandCi :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (horder : P.q₂ < P.q₁), ∀ (hq1 : 1 <
            P.q₁), ∀ (hcross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1), ∀ (hcop :
            Nat.Coprime P.q₁ P.p₁.natAbs),
        let Q : FordFareyParameter := {
          p := P.p₁
          q := P.q₁
          q_pos := by omega
          reduced := hcop
          p₁ := P.p₁ - P.p₂
          q₁ := P.q₁ - P.q₂
          p₂ := P.p₂
          q₂ := P.q₂
          sum_p := by omega
          sum_q := by omega
          det₁ := by
            rw [Nat.cast_sub (by omega)]
            nlinarith
          det₂ := by
            nlinarith
          q₁_lt := by
            exact Nat.sub_lt (by omega : 0 < P.q₁) P.q₂_pos
          q₂_pos := P.q₂_pos
          unit_case := by
            intro hu
            change P.q₁ = 1 at hu
            omega }
        (FordRecursiveQuadruple Q 0 = Ci.1.1) → ((BandPrototile (FordCircleCoordinate Q.p Q.q)
            (FordTile Q.q)) → (BandPrototile Ci.1.1 (FordTile P.q₁))) ) := by
  classical
  intro P Ci horder hq1 hcross hcop Q hQchild hQband
  rw [← hQchild]
  exact hQband

private theorem hvfirst :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) →
            ((BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple
            P (0 : Fin (4 : ℕ))) = ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩) → (
        let x := BandVectors.1 (FordRecursiveQuadruple P 1)
          (FordRecursiveQuadruple P 3)
        let y := BandVectors.1 (FordRecursiveQuadruple P 2)
          (FordRecursiveQuadruple P 1)
        x - (⟨0, 1⟩ : GaussianInt) * y = ⟨P.q, P.q₁⟩)) ) := by
  classical
  intro P hq hv10 x y
  have hh := (VectorRecursionLaws (FordRecursiveQuadruple P) hq.1).2.2.1
  rw [hv10] at hh
  simpa [x, y] using hh.symm

private theorem hvsecond :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) →
            ((BandVectors.1 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple
            P (0 : Fin (4 : ℕ))) = ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩) → (
        let w := BandVectors.1 (FordRecursiveQuadruple P 3)
          (FordRecursiveQuadruple P 2)
        let y := BandVectors.1 (FordRecursiveQuadruple P 2)
          (FordRecursiveQuadruple P 1)
        y - (⟨0, 1⟩ : GaussianInt) * w = ⟨-(P.q : Int), P.q₂⟩)) ) := by
  classical
  intro P hq hv20 w y
  have rotated : SemiProperQuadruple
      (![FordRecursiveQuadruple P 0, FordRecursiveQuadruple P 2,
        FordRecursiveQuadruple P 3, FordRecursiveQuadruple P 1]) :=
    SemiProperQuadruple.rotate hq.1
  have hh := (VectorRecursionLaws
    (![FordRecursiveQuadruple P 0, FordRecursiveQuadruple P 2,
      FordRecursiveQuadruple P 3, FordRecursiveQuadruple P 1]) rotated).2.2.1
  have hh' := by simpa using hh
  rw [hv20] at hh'
  simpa [y, w] using hh'.symm

private theorem hvsol :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → ((1 < P.q₁) → ((P.p₁ * (P.q₂
            : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) → (
        let w := BandVectors.1 (FordRecursiveQuadruple P 3)
          (FordRecursiveQuadruple P 2)
        let x := BandVectors.1 (FordRecursiveQuadruple P 1)
          (FordRecursiveQuadruple P 3)
        let y := BandVectors.1 (FordRecursiveQuadruple P 2)
          (FordRecursiveQuadruple P 1)
        (w + x + y = 0) → ((x - (⟨0, 1⟩ : GaussianInt) * y = ⟨P.q, P.q₁⟩) → ((y - (⟨0, 1⟩ :
            GaussianInt) * w = ⟨-(P.q : Int), P.q₂⟩) → (w = ⟨0, -(P.q₂ : Int)⟩)))))))) ) := by
  classical
  intro P Ci horder hq1 hcross hcop w x y hvsum hvfirst hvsecond
  have solve : ∀ (r s : Int) (w a b : GaussianInt),
      w + a + b = 0 →
      a - (⟨0, 1⟩ : GaussianInt) * b = ⟨r + s, r⟩ →
      b - (⟨0, 1⟩ : GaussianInt) * w = ⟨-(r + s), s⟩ →
      w = ⟨0, -s⟩ := by
    intro r s w a b hsum hfirst hsecond
    have hsre := congrArg (fun z : GaussianInt => z.re) hsum
    have hsim := congrArg (fun z : GaussianInt => z.im) hsum
    have hfre := congrArg (fun z : GaussianInt => z.re) hfirst
    have hfim := congrArg (fun z : GaussianInt => z.im) hfirst
    have htre := congrArg (fun z : GaussianInt => z.re) hsecond
    have htim := congrArg (fun z : GaussianInt => z.im) hsecond
    simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at hsre hsim hfre hfim htre htim
    apply Zsqrtd.ext <;> dsimp <;> omega
  exact solve P.q₁ P.q₂ w x y hvsum (by
    simpa [P.sum_q] using hvfirst) (by
    simpa [P.sum_q] using hvsecond)

private theorem haslope32 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) = ⟨-P.p₂, (0 : ℤ)⟩) → (BandVectors.2
            (FordRecursiveQuadruple P 3) (FordRecursiveQuadruple P 2) = -(P.p₂ : GaussianInt)) )
            := by
  classical
  intro P ha32
  exact ha32

private theorem fordCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → ((1 < P.q₁) → ((P.p₁ * (P.q₂
            : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) → (∀ (n : ℕ), (0
            : ℕ) < n → TileCentroid (FordTile n) = ((↑n : ℝ) / (2 : ℝ), (↑n : ℝ) / (2 : ℝ)))))))
            ) := by
  classical
  intro P Ci horder hq1 hcross hcop n hn
  let D : Finset GaussianInt :=
    (Finset.range n).product (Finset.range n) |>.image
      (fun a => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
  have hne : D.Nonempty := by
    refine ⟨⟨0, 0⟩, ?_⟩
    simp [D, hn]
  have hinj : Set.InjOn
      (fun a : Nat × Nat => (⟨(a.1 : Int), (a.2 : Int)⟩ : GaussianInt))
      ↑((Finset.range n).product (Finset.range n)) := by
    intro a ha b hb hab
    apply Prod.ext
    · have hh := congrArg (fun z : GaussianInt => z.re) hab
      change (a.1 : Int) = b.1 at hh
      exact_mod_cast hh
    · have hh := congrArg (fun z : GaussianInt => z.im) hab
      change (a.2 : Int) = b.2 at hh
      exact_mod_cast hh
  have hcard : D.card = n * n := by
    calc
      D.card = ((Finset.range n).product (Finset.range n)).card := by
        dsimp [D]
        exact Finset.card_image_iff.mpr hinj
      _ = n * n := by simp
  have hsumR : D.sum (fun z : GaussianInt => z.re) =
      (n : Int) * ((n - 1 : Nat) : Int) / 2 * (n : Int) := by
    have hrange : (Finset.range n).sum (fun a => (a : Int)) =
        (n : Int) * ((n - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, D]
    conv_lhs => rw [← Finset.mul_sum (Finset.range n)
      (fun a => (a : Int)) (n : Int)]
    rw [hrange]
    ring
  have hsumI : D.sum (fun z : GaussianInt => z.im) =
      (n : Int) * ((n - 1 : Nat) : Int) / 2 * (n : Int) := by
    have hrange : (Finset.range n).sum (fun a => (a : Int)) =
        (n : Int) * ((n - 1 : Nat) : Int) / 2 := by
      rw [← Nat.cast_sum]
      simp [Finset.sum_range_id]
    simp only [Int.reduceNeg, Finset.product_eq_sprod, Finset.coe_product, Finset.coe_range,
        Zsqrtd.mk.injEq, Nat.cast_inj, Prod.forall, Prod.mk.injEq, implies_true,
        Set.injOn_of_eq_iff_eq, Finset.sum_image, Finset.sum_product, Finset.sum_const,
        Finset.card_range, Int.nsmul_eq_mul, D]
    rw [hrange]
    ring
  change (if D.Nonempty then
    (((D.sum (fun z : GaussianInt => z.re) : Int) : Real) / D.card + 1 / 2,
     ((D.sum (fun z : GaussianInt => z.im) : Int) : Real) / D.card + 1 / 2)
    else _) = _
  rw [ite_eq_left hne, hcard, hsumR, hsumI]
  have hncast : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
  rw [hncast]
  norm_num
  field_simp
  have rangeSum : (Finset.range n).sum (fun a => (a : Int)) =
      (n : Int) * ((n - 1 : Nat) : Int) / 2 := by
    rw [← Nat.cast_sum]
    simp [Finset.sum_range_id]
  have arithmeticCast :
      ((Finset.range n).sum (fun a => (a : Int))) * 2 =
        (n : Int) * ((n - 1 : Nat) : Int) := by
    rw [← Nat.cast_sum]
    exact_mod_cast Finset.sum_range_id_mul_two n
  rw [rangeSum] at arithmeticCast
  rw [hncast] at arithmeticCast
  have hreal :
      ((((n : Int) * ((n : Int) - 1) / 2 : Int) : Real) * 2) =
        (((n : Int) * ((n : Int) - 1) : Int) : Real) := by
    exact_mod_cast arithmeticCast
  rw [hreal]
  push_cast
  ring

private theorem rootNonempty :
    (by
      classical
      exact
        ∀ (n : ℕ), (0 : ℕ) < n → ∀ (z : GaussianInt), Finset.Nonempty (TileTranslation (FordTile
            n) z).cells ) := by
  classical
  intro n hn z
  refine ⟨z, ?_⟩
  rw [(TileTranslationFormulas (FordTile n) z).1]
  apply Finset.mem_image.mpr
  refine ⟨0, ?_, ?_⟩
  · change (0 : GaussianInt) ∈ FordCellDomain n
    unfold FordCellDomain
    apply Finset.mem_image.mpr
    refine ⟨(0, 0), Finset.mem_product.mpr ⟨by simp [hn], by simp [hn]⟩, ?_⟩
    ext <;> simp
  · simp [GaussianTranslation]

private theorem hrootCent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → ((∀ (n : Nat), (0 < n) → (∀ (z :
            GaussianInt), (TileTranslation (FordTile n) z).cells.Nonempty)) → (TileCentroid T =
            TileCentroid (TileTranslation (FordTile P.q) u))) ) := by
  classical
  intro P T u hc rootNonempty
  have hne := rootNonempty P.q P.q_pos u
  have hanch : T.cells = ∅ → T.anchor = (TileTranslation (FordTile P.q) u).anchor := by
    intro he
    have he' : (TileTranslation (FordTile P.q) u).cells = ∅ := by rw [← hc, he]
    exact False.elim (hne.ne_empty he')
  exact (ProtoTileObservableExtensionality T
    (TileTranslation (FordTile P.q) u) hc hanch).2.2.2.2

private theorem hrootCent' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), (T'.cells =
            (TileTranslation (FordTile P.q) (u + ⟨(↑P.q : ℤ), (↑P.q₁ : ℤ)⟩)).cells) → ((∀ (n :
            Nat), (0 < n) → (∀ (z : GaussianInt), (TileTranslation (FordTile n)
            z).cells.Nonempty)) → (TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q)
            (u + ⟨P.q, P.q₁⟩)))) ) := by
  classical
  intro P T' u hc' rootNonempty
  let z := u + ⟨P.q, P.q₁⟩
  have hne := rootNonempty P.q P.q_pos z
  have hanch : T'.cells = ∅ → T'.anchor =
      (TileTranslation (FordTile P.q) z).anchor := by
    intro he
    have he' : (TileTranslation (FordTile P.q) z).cells = ∅ := by rw [← hc', he]
    exact False.elim (hne.ne_empty he')
  simpa [z] using (ProtoTileObservableExtensionality T'
    (TileTranslation (FordTile P.q) z) hc' hanch).2.2.2.2

private theorem hw' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let w := BandVectors.1 (FordRecursiveQuadruple P 3)
          (FordRecursiveQuadruple P 2)
        (w = ⟨0, -(P.q₂ : Int)⟩) → (BandVectors.1 (FordRecursiveQuadruple P 3)
            (FordRecursiveQuadruple P 2) = ⟨0, -(P.q₂ : Int)⟩) ) := by
  classical
  intro P w hvsol
  simpa [w] using hvsol

private theorem hUoffset :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀
            (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S i s) - TileCentroid T = (if s = true
            then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let U := S 0 false
        let w := BandVectors.1 (FordRecursiveQuadruple P 3)
          (FordRecursiveQuadruple P 2)
        (w = ⟨0, -(P.q₂ : Int)⟩) → (TileCentroid U - TileCentroid T = ((P.q₂ : Real) / 2, (P.q₂ :
            Real) / 2))) ) := by
  classical
  intro P T S hcent U w hvsol
  have hh : TileCentroid U - TileCentroid T =
      (-1 : Real) • ((1 / 2 : Real) •
        (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) := by
    simpa [U, w] using hcent 0 false
  rw [hvsol] at hh
  norm_num [GaussianRealPoint] at hh
  apply Prod.ext
  · have hh := congrArg Prod.fst hh
    norm_num at hh ⊢
    linarith
  · have hh := congrArg Prod.snd hh
    norm_num at hh ⊢
    linarith

private theorem hVoffset :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S' i s) - TileCentroid T' = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let V := S' 0 true
        let w := BandVectors.1 (FordRecursiveQuadruple P 3)
          (FordRecursiveQuadruple P 2)
        (w = ⟨0, -(P.q₂ : Int)⟩) → (TileCentroid V - TileCentroid T' = (-((P.q₂ : Real) / 2),
            -((P.q₂ : Real) / 2)))) ) := by
  classical
  intro P T' S' hcent' V w hvsol
  have hh : TileCentroid V - TileCentroid T' =
      (1 : Real) • ((1 / 2 : Real) •
        (GaussianRealPoint w - (-(GaussianRealPoint w).2, (GaussianRealPoint w).1))) := by
    simpa [V, w] using hcent' 0 true
  rw [hvsol] at hh
  norm_num [GaussianRealPoint] at hh
  apply Prod.ext
  · have hh := congrArg Prod.fst hh
    norm_num at hh ⊢
    linarith
  · have hh := congrArg Prod.snd hh
    norm_num at hh ⊢
    linarith

private theorem hUCcent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → (∀ (T : ProtoTile), ∀ (u :
            GaussianInt), (1 < P.q₁) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 0 false
        (P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) → ((∀
            (n : Nat), (0 < n) → (TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → (
        let Uc := TileTranslation (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)
        (TileCentroid T = TileCentroid (TileTranslation (FordTile P.q) u)) → ((TileCentroid U -
            TileCentroid T = ((P.q₂ : Real) / 2, (P.q₂ : Real) / 2)) → (TileCentroid U =
            TileCentroid Uc)))))))) ) := by
  classical
  intro P Ci horder T u hq1 S U hcross hcop fordCentroid Uc hrootCent hUoffset
  calc
    TileCentroid U = (TileCentroid U - TileCentroid T) + TileCentroid T := by abel
    _ = ((P.q₂ : Real) / 2, (P.q₂ : Real) / 2) +
        TileCentroid (TileTranslation (FordTile P.q) u) := by rw [hUoffset, hrootCent]
    _ = TileCentroid Uc := by
      rw [(TileTranslationFormulas (FordTile P.q) u).2.2.2.2.1,
        (TileTranslationFormulas (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)).2.2.2.2.1,
        fordCentroid P.q P.q_pos, fordCentroid P.q₁ (by omega)]
      apply Prod.ext <;> simp [P.sum_q]  <;> ring

private theorem hVCcent :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → (∀ (T' : ProtoTile), ∀ (u :
            GaussianInt), (1 < P.q₁) → (∀ (S' : Fin (3 : ℕ) → Bool → ProtoTile),
        let V := S' 0 true
        (P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) → ((∀
            (n : Nat), (0 < n) → (TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → (
        let Vc := TileTranslation (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)
        (TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q) (u + ⟨P.q, P.q₁⟩))) →
            ((TileCentroid V - TileCentroid T' = (-((P.q₂ : Real) / 2), -((P.q₂ : Real) / 2))) →
            (TileCentroid V = TileCentroid Vc)))))))) ) := by
  classical
  intro P Ci horder T' u hq1 S' V hcross hcop fordCentroid Vc hrootCent' hVoffset
  calc
    TileCentroid V = (TileCentroid V - TileCentroid T') + TileCentroid T' := by abel
    _ = (-((P.q₂ : Real) / 2), -((P.q₂ : Real) / 2)) +
        TileCentroid (TileTranslation (FordTile P.q)
          (u + ⟨P.q, P.q₁⟩)) := by rw [hVoffset, hrootCent']
    _ = TileCentroid Vc := by
      rw [(TileTranslationFormulas (FordTile P.q) (u + ⟨P.q, P.q₁⟩)).2.2.2.2.1,
        (TileTranslationFormulas (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)).2.2.2.2.1,
        fordCentroid P.q P.q_pos, fordCentroid P.q₁ (by omega)]
      apply Prod.ext <;> simp [P.sum_q]  <;> ring

private theorem hcentUV :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → (∀ (u : GaussianInt), (1 <
            P.q₁) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (S' : Fin (3 : ℕ) → Bool →
            ProtoTile),
        let U := S 0 false
        let V := S' 0 true
        (P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) → ((∀
            (n : Nat), (0 < n) → (TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → (
        let Uc := TileTranslation (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)
        let Vc := TileTranslation (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)
        (TileCentroid U = TileCentroid Uc) → ((TileCentroid V = TileCentroid Vc) → (TileCentroid
            V - TileCentroid U = GaussianRealPoint ⟨P.q₁, (P.q₁ : Int) - P.q₂⟩)))))))) ) := by
  classical
  intro P Ci horder u hq1 S S' U V hcross hcop fordCentroid Uc Vc hUCcent hVCcent
  rw [hVCcent, hUCcent,
    (TileTranslationFormulas (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)).2.2.2.2.1,
    (TileTranslationFormulas (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)).2.2.2.2.1,
    fordCentroid P.q₁ (by omega)]
  apply Prod.ext <;> simp [GaussianRealPoint, P.sum_q]

private theorem hnonzero :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandCircle) → ((P.q₂ < P.q₁) → ((1 < P.q₁) → ((P.p₁ * (P.q₂
            : Int) - (P.q₁ : Int) * P.p₂ = 1) → ((Nat.Coprime P.q₁ P.p₁.natAbs) →
            ((FordRecursiveQuadruple P 1).1 ≠ 0))))) ) := by
  classical
  intro P Ci horder hq1 hcross hcop
  change (if P.q₁ = 0 then (0, 1) else
    FordCircleCoordinate P.p₁ P.q₁).1 ≠ 0
  rw [ite_eq_right (by omega)]
  simp [FordCircleCoordinate]
  omega

private theorem hslopeUdata :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (h : PartialOdometer), ∀ (gS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (FordRecursiveQuadruple P
            i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope h = some p ∧
            PartialOdometerSlope (gS i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (FordRecursiveQuadruple P (i + (2 :
            Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ)
            - (↑(BandVectors.2 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if
            s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (FordRecursiveQuadruple P (i +
            (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).re
            : ℝ))) → (((FordRecursiveQuadruple P 1).1 ≠ 0) → (∃ p₀ pU, PartialOdometerSlope h =
            some p₀ ∧ PartialOdometerSlope (gS 0 false) = some pU ∧ pU.1 - p₀.1 = (if false =
            true then (1 : ℝ) else -1) * (1 / 2) * (((BandVectors.2 (FordRecursiveQuadruple P 3)
            (FordRecursiveQuadruple P 2)).re : Int) - ((BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2)).im : Int)) ∧ pU.2 - p₀.2 = (if false = true then (1
            : ℝ) else -1) * (1 / 2) * (((BandVectors.2 (FordRecursiveQuadruple P 3)
            (FordRecursiveQuadruple P 2)).im : Int) + ((BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2)).re : Int)))) ) := by
  classical
  intro P h gS hslope hnonzero
  rcases hslope 0 false with hz | h
  · exact False.elim (hnonzero hz)
  · exact h

private theorem hdu1' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), (BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2) = -(P.p₂ : GaussianInt)) → (∀ (p₀ : ℝ × ℝ), ∀ (pU : ℝ
            × ℝ), (pU.1 - p₀.1 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2
            (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)))).im : ℝ))) → ((p₀ = p) → (
        let s := pU
        s.1 - p.1 = (P.p₂ : Real) / 2))) ) := by
  classical
  intro P p haslope32 p₀ pU hdu1 hp₀ s
  rw [hp₀] at hdu1
  rw [haslope32] at hdu1
  norm_num at hdu1
  dsimp [s]
  linarith [hdu1]

private theorem hdu2' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), (BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2) = -(P.p₂ : GaussianInt)) → (∀ (p₀ : ℝ × ℝ), ∀ (pU : ℝ
            × ℝ), (pU.2 - p₀.2 = (if false = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2
            (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)))).re : ℝ))) → ((p₀ = p) → (
        let s := pU
        s.2 - p.2 = (P.p₂ : Real) / 2))) ) := by
  classical
  intro P p haslope32 p₀ pU hdu2 hp₀ s
  rw [hp₀] at hdu2
  rw [haslope32] at hdu2
  norm_num at hdu2
  dsimp [s]
  linarith [hdu2]

private theorem hslopeVdata :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (h' : PartialOdometer), ∀ (kS : Fin (3 : ℕ) → Bool →
            PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), (FordRecursiveQuadruple P
            i.succ).1 = (0 : ℤ) ∨ ∃ (p : ℝ × ℝ) (p_i : ℝ × ℝ), PartialOdometerSlope h' = some p ∧
            PartialOdometerSlope (kS i s) = some p_i ∧ p_i.1 - p.1 = (if s = true then (1 : ℝ)
            else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2 (FordRecursiveQuadruple P (i + (2 :
            Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).re : ℝ)
            - (↑(BandVectors.2 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).im : ℝ)) ∧ p_i.2 - p.2 = (if
            s = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) * ((↑(BandVectors.2
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)).im : ℝ) + (↑(BandVectors.2 (FordRecursiveQuadruple P (i +
            (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)).re
            : ℝ))) → (((FordRecursiveQuadruple P 1).1 ≠ 0) → (∃ p₀' pV, PartialOdometerSlope h' =
            some p₀' ∧ PartialOdometerSlope (kS 0 true) = some pV ∧ pV.1 - p₀'.1 = (if true =
            true then (1 : ℝ) else -1) * (1 / 2) * (((BandVectors.2 (FordRecursiveQuadruple P 3)
            (FordRecursiveQuadruple P 2)).re : Int) - ((BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2)).im : Int)) ∧ pV.2 - p₀'.2 = (if true = true then (1
            : ℝ) else -1) * (1 / 2) * (((BandVectors.2 (FordRecursiveQuadruple P 3)
            (FordRecursiveQuadruple P 2)).im : Int) + ((BandVectors.2 (FordRecursiveQuadruple P
            3) (FordRecursiveQuadruple P 2)).re : Int)))) ) := by
  classical
  intro P h' kS hslope' hnonzero
  rcases hslope' 0 true with hz | h
  · exact False.elim (hnonzero hz)
  · exact h

private theorem hdk1' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p' : Real × Real), (BandVectors.2 (FordRecursiveQuadruple
            P 3) (FordRecursiveQuadruple P 2) = -(P.p₂ : GaussianInt)) → (∀ (p₀' : ℝ × ℝ), ∀ (pV
            : ℝ × ℝ), (pV.1 - p₀'.1 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))).re : ℝ) - (↑(BandVectors.2
            (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)))).im : ℝ))) → ((p₀' = p') → (
        let t := pV
        t.1 - p'.1 = -((P.p₂ : Real) / 2)))) ) := by
  classical
  intro P p' haslope32 p₀' pV hdk1 hp₀' t
  rw [hp₀'] at hdk1
  rw [haslope32] at hdk1
  norm_num at hdk1
  dsimp [t]
  linarith [hdk1]

private theorem hdk2' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p' : Real × Real), (BandVectors.2 (FordRecursiveQuadruple
            P 3) (FordRecursiveQuadruple P 2) = -(P.p₂ : GaussianInt)) → (∀ (p₀' : ℝ × ℝ), ∀ (pV
            : ℝ × ℝ), (pV.2 - p₀'.2 = (if true = true then (1 : ℝ) else (-1 : ℝ)) * (1 / 2 : ℝ) *
            ((↑(BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))).im : ℝ) + (↑(BandVectors.2
            (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)))).re : ℝ))) → ((p₀' = p') → (
        let t := pV
        t.2 - p'.2 = -((P.p₂ : Real) / 2)))) ) := by
  classical
  intro P p' haslope32 p₀' pV hdk2 hp₀' t
  rw [hp₀'] at hdk2
  rw [haslope32] at hdk2
  norm_num at hdk2
  dsimp [t]
  linarith [hdk2]

private theorem hsl' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), ∀ (p' : Real × Real), (p' - p =
            GaussianRealPoint (BandVectors.2 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) → ((BandVectors.2
            (FordRecursiveQuadruple P (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ))) = ⟨P.p₁, P.p⟩) → (p' - p = ((P.p₁ : Real), (P.p₁ : Real) + P.p₂))) ) := by
  classical
  intro P p p' hsl ha10
  rw [ha10] at hsl
  simpa [GaussianRealPoint, P.sum_p] using hsl

private theorem hSlopeDiff :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), ∀ (p' : Real × Real), ∀ (pU : ℝ × ℝ),
        let s := pU
        (s.1 - p.1 = (P.p₂ : Real) / 2) → ((s.2 - p.2 = (P.p₂ : Real) / 2) → (∀ (pV : ℝ × ℝ),
        let t := pV
        (t.1 - p'.1 = -((P.p₂ : Real) / 2)) → ((t.2 - p'.2 = -((P.p₂ : Real) / 2)) → ((p' - p =
            ((P.p₁ : Real), (P.p₁ : Real) + P.p₂)) → (t - s = GaussianRealPoint ⟨P.p₁ - P.p₂,
            P.p₁⟩))))) ) := by
  classical
  intro P p p' pU s hdu1' hdu2' pV t hdk1' hdk2' hsl'
  have hu1 := hdu1'
  have hu2 := hdu2'
  have hv1 := hdk1'
  have hv2 := hdk2'
  have hsl1 : p'.1 - p.1 = (P.p₁ : Real) := by
    have hh := congrArg Prod.fst hsl'
    simpa using hh
  have hsl2 : p'.2 - p.2 = (P.p₁ : Real) + P.p₂ := by
    have hh := congrArg Prod.snd hsl'
    simpa using hh
  dsimp [s] at hu1 hu2
  dsimp [t] at hv1 hv2
  have hd1 : pV.1 - pU.1 = (P.p₁ : Real) - P.p₂ := by
    linarith [hu1, hv1, hsl1]
  have hd2 : pV.2 - pU.2 = (P.p₁ : Real) := by
    linarith [hu2, hv2, hsl2]
  apply Prod.ext
  · simpa [GaussianRealPoint, Int.cast_sub] using hd1
  · simpa [GaussianRealPoint] using hd2

end LargeFirstRestrictions

theorem P4158T1LargeFirstRestrictions
    (P : FordFareyParameter) (hq : ProperBandQuadruple (FordRecursiveQuadruple P))
    (C0 Ci : BandCircle)
    (hC0 : FordRecursiveQuadruple P 0 = C0.1.1)
    (hCi : FordRecursiveQuadruple P 1 = Ci.1.1)
    (hlarge : 1 < Ci.1.1.1) (horder : P.q₂ < P.q₁)
    (T T' : ProtoTile) (h h' : PartialOdometer)
    (hO : TileOdometer C0.1.1 T h) (hO' : TileOdometer C0.1.1 T' h')
    (p p' : Real × Real)
    (hs : PartialOdometerSlope h = some p)
    (hs' : PartialOdometerSlope h' = some p')
    (hsl : p' - p = GaussianRealPoint
      (BandVectors.2 (FordRecursiveQuadruple P 1) (FordRecursiveQuadruple P 0)))
    (u : GaussianInt)
    (hc : T.cells = (TileTranslation (FordTile P.q) u).cells)
    (hc' : T'.cells = (TileTranslation (FordTile P.q) (u + ⟨P.q, P.q₁⟩)).cells) :
    ∃ (U V : ProtoTile) (g k : PartialOdometer) (s t : Real × Real)
      (Q : FordFareyParameter),
      AncestorOdometer Ci.1.1 C0.1.1 U T g h ∧
      AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧
      TileOdometer Ci.1.1 U g ∧ TileOdometer Ci.1.1 V k ∧
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      U.cells = (TileTranslation (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)).cells ∧
      V.cells = (TileTranslation (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)).cells ∧
      TileCentroid V - TileCentroid U = GaussianRealPoint ⟨P.q₁, (P.q₁ : Int) - P.q₂⟩ ∧
      t - s = GaussianRealPoint ⟨P.p₁ - P.p₂, P.p₁⟩ ∧
      Q.q = P.q₁ ∧ Q.q₁ = P.q₁ - P.q₂ ∧ Q.p = P.p₁ ∧ Q.p₁ = P.p₁ - P.p₂ ∧
      FordRecursiveQuadruple Q 0 = Ci.1.1 ∧ 1 < Q.q := by
-- BODY
  classical
  have hq1 : 1 < P.q₁ := LargeFirstRestrictions.hq1 P Ci horder
  have hqgt := LargeFirstRestrictions.hqgt P Ci hq1
  have hroot : 1 < (FordRecursiveQuadruple P 0).1 := LargeFirstRestrictions.hroot P hqgt
  have dec := TileOdometerReindexedDecomposition
    (FordRecursiveQuadruple P) hq T h hroot (by simpa [hC0] using hO)
  have dec' := TileOdometerReindexedDecomposition
    (FordRecursiveQuadruple P) hq T' h' hroot (by simpa [hC0] using hO')
  rcases dec with ⟨S, gS, hbandT, hsub, hcells, hfoot, hcent, hdom, hvalue,
    hcompat, hslope⟩
  rcases dec' with ⟨S', kS, hbandT', hsub', hcells', hfoot', hcent',
    hdom', hvalue', hcompat', hslope'⟩
  let U := S 0 false
  let V := S' 0 true
  let g := gS 0 false
  let k := kS 0 true
  have hUg : TileOdometer Ci.1.1 U g := by
    simpa [U, g, ← hCi] using hsub 0 false
  have hVk : TileOdometer Ci.1.1 V k := by
    simpa [V, k, ← hCi] using hsub' 0 true
  have hCiPos : 0 < Ci.1.1.1 := by omega
  have hATU := LargeFirstRestrictions.hATU P hq C0 Ci hC0 hCi T S gS hbandT hfoot hcent hUg
  have hATV := LargeFirstRestrictions.hATV P hq C0 Ci hC0 hCi T' S' kS hbandT' hfoot' hcent' hVk
  have hAncU := LargeFirstRestrictions.hAncU P C0 Ci hC0 T h hO S gS hdom hvalue hUg hCiPos hATU
  have hAncV := LargeFirstRestrictions.hAncV P C0 Ci hC0 T' h' hO' S' kS hdom' hvalue' hVk hCiPos
      hATV
  have hcross := LargeFirstRestrictions.hcross P
  have hcop := LargeFirstRestrictions.hcop P hcross
  let Q : FordFareyParameter := {
    p := P.p₁
    q := P.q₁
    q_pos := by omega
    reduced := hcop
    p₁ := P.p₁ - P.p₂
    q₁ := P.q₁ - P.q₂
    p₂ := P.p₂
    q₂ := P.q₂
    sum_p := by omega
    sum_q := by omega
    det₁ := by
      have hh := hcross
      rw [Nat.cast_sub (by omega)]
      nlinarith
    det₂ := by
      have hh := hcross
      nlinarith
    q₁_lt := by
      exact Nat.sub_lt (by omega : 0 < P.q₁) P.q₂_pos
    q₂_pos := P.q₂_pos
    unit_case := by
      intro hu
      change P.q₁ = 1 at hu
      omega }
  have hQchild := LargeFirstRestrictions.hQchild P Ci hCi horder hq1 hcross hcop
  have hQgt : 1 < Q.q := by simpa [Q] using hq1
  have hQband := (FordTileRecursiveIdentification Q).1
  have hQbandCi := LargeFirstRestrictions.hQbandCi P Ci horder hq1 hcross hcop hQchild hQband
  have fcfg := (FordCoordinateConfiguration P).2 hqgt
  rcases fcfg with ⟨_, hv10, hv20, _, ha10, _, _, ha32, _⟩
  let w := BandVectors.1 (FordRecursiveQuadruple P 3)
    (FordRecursiveQuadruple P 2)
  let x := BandVectors.1 (FordRecursiveQuadruple P 1)
    (FordRecursiveQuadruple P 3)
  let y := BandVectors.1 (FordRecursiveQuadruple P 2)
    (FordRecursiveQuadruple P 1)
  have hvsum : w + x + y = 0 := (VectorRecursionLaws
    (FordRecursiveQuadruple P) hq.1).1
  have hvfirst := LargeFirstRestrictions.hvfirst P hq hv10
  have hvsecond := LargeFirstRestrictions.hvsecond P hq hv20
  have hvsol := LargeFirstRestrictions.hvsol P Ci horder hq1 hcross hcop hvsum hvfirst hvsecond
  have haslope32 := LargeFirstRestrictions.haslope32 P ha32
  have fordCentroid (n : Nat) (hn : 0 < n) := LargeFirstRestrictions.fordCentroid P Ci horder hq1
      hcross hcop n hn
  let Uc := TileTranslation (FordTile P.q₁) (u + ⟨P.q₂, P.q₂⟩)
  let Vc := TileTranslation (FordTile P.q₁) (u + ⟨P.q, P.q₁⟩)
  have hUcBand : BandPrototile Ci.1.1 Uc :=
    BandPrototileTranslation Ci.1.1 (FordTile P.q₁)
      (u + ⟨P.q₂, P.q₂⟩) hQbandCi
  have hVcBand : BandPrototile Ci.1.1 Vc :=
    BandPrototileTranslation Ci.1.1 (FordTile P.q₁)
      (u + ⟨P.q, P.q₁⟩) hQbandCi
  have rootNonempty (n : Nat) (hn : 0 < n) (z : GaussianInt) :=
      LargeFirstRestrictions.rootNonempty n hn z
  have hrootCent := LargeFirstRestrictions.hrootCent P T u hc rootNonempty
  have hrootCent' := LargeFirstRestrictions.hrootCent' P T' u hc' rootNonempty
  have hw' := LargeFirstRestrictions.hw' P hvsol
  have hUoffset := LargeFirstRestrictions.hUoffset P T S hcent hvsol
  have hVoffset := LargeFirstRestrictions.hVoffset P T' S' hcent' hvsol
  have hUCcent := LargeFirstRestrictions.hUCcent P Ci horder T u hq1 S hcross hcop fordCentroid
      hrootCent hUoffset
  have hVCcent := LargeFirstRestrictions.hVCcent P Ci horder T' u hq1 S' hcross hcop fordCentroid
      hrootCent' hVoffset
  have hUcells : U.cells = Uc.cells :=
    (BandPrototileCentroidUnique Ci.1.1 U Uc
      (TileOdometerBandPrototile Ci.1.1 U g hUg) hUcBand hUCcent).1
  have hVcells : V.cells = Vc.cells :=
    (BandPrototileCentroidUnique Ci.1.1 V Vc
      (TileOdometerBandPrototile Ci.1.1 V k hVk) hVcBand hVCcent).1
  have hcentUV := LargeFirstRestrictions.hcentUV P Ci horder u hq1 S S' hcross hcop fordCentroid
      hUCcent hVCcent
  have hnonzero := LargeFirstRestrictions.hnonzero P Ci horder hq1 hcross hcop
  have hslopeUdata := LargeFirstRestrictions.hslopeUdata P h gS hslope hnonzero
  obtain ⟨p₀, pU, hsp, hspU, hdu1, hdu2⟩ := hslopeUdata
  have hp₀ : p₀ = p := Option.some.inj (hsp.symm.trans hs)
  let s := pU
  have hslopeU : PartialOdometerSlope g = some s := by
    simpa [g, s] using hspU
  have hdu1' := LargeFirstRestrictions.hdu1' P p haslope32 p₀ pU hdu1 hp₀
  have hdu2' := LargeFirstRestrictions.hdu2' P p haslope32 p₀ pU hdu2 hp₀
  have hslopeVdata := LargeFirstRestrictions.hslopeVdata P h' kS hslope' hnonzero
  obtain ⟨p₀', pV, hsp', hspV, hdk1, hdk2⟩ := hslopeVdata
  have hp₀' : p₀' = p' := Option.some.inj (hsp'.symm.trans hs')
  let t := pV
  have hslopeV : PartialOdometerSlope k = some t := by
    simpa [k, t] using hspV
  have hdk1' := LargeFirstRestrictions.hdk1' P p' haslope32 p₀' pV hdk1 hp₀'
  have hdk2' := LargeFirstRestrictions.hdk2' P p' haslope32 p₀' pV hdk2 hp₀'
  have hsl' := LargeFirstRestrictions.hsl' P p p' hsl ha10
  have hSlopeDiff := LargeFirstRestrictions.hSlopeDiff P p p' pU hdu1' hdu2' pV hdk1' hdk2' hsl'
  refine ⟨U, V, g, k, s, t, Q, hAncU, hAncV, hUg, hVk,
    hslopeU, hslopeV, ?_, ?_, hcentUV, hSlopeDiff, ?_, ?_, ?_, ?_, hQchild, hQgt⟩
  · simpa [Uc] using hUcells
  · simpa [Vc] using hVcells
  · rfl
  · rfl
  · rfl
  · rfl

end ApollonianSuperharmonic

end
