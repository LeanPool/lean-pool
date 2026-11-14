/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.P4210T1FordSquareCentroid
public import LeanPool.ApollonianSuperharmonic.FordFareySum

public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.FordTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P4158T1LargeSecondRestrictions]

/-!
# P4158T1LargeSecondRestrictions

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LargeSecondRestrictions

private theorem hcurv :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          ∀ (Ci : BandCircle),
            FordRecursiveQuadruple P (2 : Fin (4 : ℕ)) = Ci.1.1 →
              (1 : ℤ) < Ci.1.1.1 → P.q₁ < P.q₂ → 1 < P.q₂
    ) := by
  classical
  intro P Ci hCi hlarge horder
  have hlarge' : (1 : Int) < (P.q₂ * P.q₂ : Nat) := by
    rw [← hCi] at hlarge
    simpa [FordRecursiveQuadruple, FordCircleCoordinate] using hlarge
  have hnat : 1 < P.q₂ * P.q₂ := by exact_mod_cast hlarge'
  have hcast : (1 : Int) < (P.q₂ : Int) * P.q₂ := by exact_mod_cast hnat
  by_contra hn
  have hle : P.q₂ ≤ 1 := by omega
  interval_cases P.q₂ <;> norm_num at hnat

private theorem hqgt :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), 1 < P.q₂ → 1 < P.q
    ) := by
  classical
  intro P hcurv
  have hsum := P.sum_q
  omega

private theorem hq0 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (1 < P.q) → (1 < (FordRecursiveQuadruple P 0).1) ) := by
  classical
  intro P hqgt
  have hq0sq : (1 : Int) < (P.q * P.q : Nat) := by
    have hqcast : (1 : Int) < (P.q : Int) * P.q := by nlinarith
    exact_mod_cast hqcast
  simpa [FordRecursiveQuadruple, FordCircleCoordinate] using hq0sq

private theorem hUg :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)) = Ci.1.1) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gfamily : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer
            (FordRecursiveQuadruple P i.succ) (S i s) (gfamily i s)) → (
        let U := S 1 false
        let g := gfamily 1 false
        TileOdometer Ci.1.1 U g)) ) := by
  classical
  intro P Ci hCi S gfamily hchild U g
  rw [← hCi]
  exact hchild 1 false

private theorem hVk :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (2 : Fin (4 :
            ℕ)) = Ci.1.1) → (∀ (S₂ : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (kfamily : Fin (3 : ℕ) →
            Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileOdometer
            (FordRecursiveQuadruple P i.succ) (S₂ i s) (kfamily i s)) → (
        let V := S₂ 1 true
        let k := kfamily 1 true
        TileOdometer Ci.1.1 V k)) ) := by
  classical
  intro P Ci hCi S₂ kfamily hchild₂ V k
  rw [← hCi]
  exact hchild₂ 1 true

private abbrev hcross := ApollonianSuperharmonic.FordFareySum.determinant

private theorem hcross2 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (P.q₁ < P.q₂) → ((P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ =
            1) → ((P.p₂ - P.p₁) * (P.q₂ : Int) - ((P.q₂ - P.q₁ : Nat) : Int) * P.p₂ = -1)) ) := by
  classical
  intro P horder hcross
  have hcast : ((P.q₂ - P.q₁ : Nat) : Int) = P.q₂ - P.q₁ := by
    exact_mod_cast (Nat.cast_sub horder.le)
  rw [hcast]
  nlinarith [hcross]

private theorem hredchild :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1) →
            (Nat.Coprime P.q₂ P.p₂.natAbs) ) := by
  classical
  intro P hcross
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd P.q₂ P.p₂.natAbs
  have hdqN : d ∣ P.q₂ := by dsimp [d]; exact Nat.gcd_dvd_left _ _
  have hdpN : d ∣ P.p₂.natAbs := by dsimp [d]; exact Nat.gcd_dvd_right _ _
  have hdq : (d : Int) ∣ (P.q₂ : Int) := by exact_mod_cast hdqN
  have hdp' : (d : Int) ∣ P.p₂ := by
    apply (Int.dvd_natAbs).mp
    exact_mod_cast hdpN
  have hd1 : (d : Int) ∣ 1 := by
    have hh : (d : Int) ∣ P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ :=
      dvd_sub (dvd_mul_of_dvd_right hdq P.p₁)
        (dvd_mul_of_dvd_right hdp' (P.q₁ : Int))
    simpa [hcross] using hh
  have hdint : (d : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le d)) hd1
  have hdval : d = 1 := by exact_mod_cast hdint
  simp [d, hdval]

private theorem hv13 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
          let w := BandVectors.1 (FordRecursiveQuadruple P 3) (FordRecursiveQuadruple P 2)
          let a := BandVectors.1 (FordRecursiveQuadruple P 1) (FordRecursiveQuadruple P 3)
          let b := BandVectors.1 (FordRecursiveQuadruple P 2) (FordRecursiveQuadruple P 1)
          w + a + b = 0 →
            a - (⟨0, 1⟩ : GaussianInt) * b = ⟨(P.q : Int), (P.q₁ : Int)⟩ →
              b - (⟨0, 1⟩ : GaussianInt) * w = ⟨-(P.q : Int), (P.q₂ : Int)⟩ →
                (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) → a = ⟨(P.q₁ : Int), 0⟩
    ) := by
  classical
  intro P w a b hsum' hfirst hsecond hqsum
  have hre := congrArg (fun z : GaussianInt => z.re) hsum'
  have him := congrArg (fun z : GaussianInt => z.im) hsum'
  have hfre := congrArg (fun z : GaussianInt => z.re) hfirst
  have hfim := congrArg (fun z : GaussianInt => z.im) hfirst
  have htre := congrArg (fun z : GaussianInt => z.re) hsecond
  have htim := congrArg (fun z : GaussianInt => z.im) hsecond
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him hfre hfim htre htim
  have hreA : a.re = P.q₁ := by omega
  have himA : a.im = 0 := by omega
  apply Zsqrtd.ext <;> assumption

private theorem hoffU :
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
        let U := S 1 false
        let a := BandVectors.1 (FordRecursiveQuadruple P 1) (FordRecursiveQuadruple P 3)
        (a = ⟨(P.q₁ : Int), 0⟩) → (TileCentroid U - TileCentroid T = (-(P.q₁ : Real) / 2, (P.q₁ :
            Real) / 2))) ) := by
  classical
  intro P T S hcent U a hv13
  have h := hcent 1 false
  have hvect : BandVectors.1 (FordRecursiveQuadruple P ((1 : Fin 3) + 2).succ)
      (FordRecursiveQuadruple P ((1 : Fin 3) + 1).succ) = a := by
    change BandVectors.1 (FordRecursiveQuadruple P 1)
      (FordRecursiveQuadruple P 3) = a
    rfl
  rw [hvect, hv13] at h
  have hh : TileCentroid (S 1 false) - TileCentroid T =
      (-(2⁻¹ * (P.q₁ : Real)), 2⁻¹ * (P.q₁ : Real)) := by
    simpa [GaussianRealPoint] using h
  calc
    TileCentroid U - TileCentroid T =
        (-(2⁻¹ * (P.q₁ : Real)), 2⁻¹ * (P.q₁ : Real)) := by simpa [U] using hh
    _ = (-(P.q₁ : Real) / 2, (P.q₁ : Real) / 2) := by ext <;> ring

private theorem hoffV :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (S₂ : Fin (3 : ℕ) → Bool → ProtoTile),
            (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S₂ i s) - TileCentroid T' = (if s =
            true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (i
            + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let V := S₂ 1 true
        let a := BandVectors.1 (FordRecursiveQuadruple P 1) (FordRecursiveQuadruple P 3)
        (a = ⟨(P.q₁ : Int), 0⟩) → (TileCentroid V - TileCentroid T' = ((P.q₁ : Real) / 2, -(P.q₁
            : Real) / 2))) ) := by
  classical
  intro P T' S₂ hcent₂ V a hv13
  have h := hcent₂ 1 true
  have hvect : BandVectors.1 (FordRecursiveQuadruple P ((1 : Fin 3) + 2).succ)
      (FordRecursiveQuadruple P ((1 : Fin 3) + 1).succ) = a := by
    change BandVectors.1 (FordRecursiveQuadruple P 1)
      (FordRecursiveQuadruple P 3) = a
    rfl
  rw [hvect, hv13] at h
  have hh : TileCentroid (S₂ 1 true) - TileCentroid T' =
      (2⁻¹ * (P.q₁ : Real), -(2⁻¹ * (P.q₁ : Real))) := by
    simpa [GaussianRealPoint] using h
  calc
    TileCentroid V - TileCentroid T' =
        (2⁻¹ * (P.q₁ : Real), -(2⁻¹ * (P.q₁ : Real))) := by simpa [V] using hh
    _ = ((P.q₁ : Real) / 2, -(P.q₁ : Real) / 2) := by ext <;> ring

private abbrev fordCentroid := ApollonianSuperharmonic.P4210T1FordSquareCentroid

private theorem rootCentroidEq :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (T.cells =
            (TileTranslation (FordTile P.q) u).cells) → (TileCentroid T = TileCentroid
            (TileTranslation (FordTile P.q) u)) ) := by
  classical
  intro P T u hc
  have hzero : (0 : GaussianInt) ∈ (FordTile P.q).cells := by
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), Finset.mem_product.mpr ⟨by simpa using P.q_pos, by simpa using P.q_pos⟩, rfl⟩
  have hneT : T.cells.Nonempty := by
    rw [hc, (TileTranslationFormulas _ _).1]
    exact ⟨GaussianTranslation u 0, Finset.mem_image.mpr ⟨0, hzero, rfl⟩⟩
  unfold TileCentroid
  rw [ite_eq_left hneT, ite_eq_left (by rw [← hc]; exact hneT), hc]

private theorem rootCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), (∀ (n : Nat), (0 < n)
            → (TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → ((TileCentroid T
            = TileCentroid (TileTranslation (FordTile P.q) u)) → (TileCentroid T = ((u.re : Real)
            + (P.q : Real) / 2, (u.im : Real) + (P.q : Real) / 2))) ) := by
  classical
  intro P T u fordCentroid rootCentroidEq
  rw [rootCentroidEq, (TileTranslationFormulas _ _).2.2.2.2.1,
    fordCentroid P.q P.q_pos]
  ext <;> simp <;> ring

private theorem rootCentroidEq' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), (T'.cells =
            (TileTranslation (FordTile P.q) (u + ⟨-(↑P.q : ℤ), (↑P.q₂ : ℤ)⟩)).cells) → (
        let v : GaussianInt := u + ⟨-(P.q : Int), P.q₂⟩
        TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q) v)) ) := by
  classical
  intro P T' u hc' v
  have hzero : (0 : GaussianInt) ∈ (FordTile P.q).cells := by
    apply Finset.mem_image.mpr
    exact ⟨(0, 0), Finset.mem_product.mpr ⟨by simpa using P.q_pos, by simpa using P.q_pos⟩, rfl⟩
  have hneT : T'.cells.Nonempty := by
    rw [hc', (TileTranslationFormulas _ _).1]
    exact ⟨GaussianTranslation v 0, Finset.mem_image.mpr ⟨0, hzero, rfl⟩⟩
  unfold TileCentroid
  rw [ite_eq_left hneT, ite_eq_left (by rw [← hc']; exact hneT), hc']

private theorem rootCentroid' :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), (∀ (n : Nat), (0 <
            n) → (TileCentroid (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → (
        let v : GaussianInt := u + ⟨-(P.q : Int), P.q₂⟩
        (TileCentroid T' = TileCentroid (TileTranslation (FordTile P.q) v)) → (TileCentroid T' =
            ((u.re : Real) - (P.q : Real) / 2, (u.im : Real) + (P.q₂ : Real) + (P.q : Real) /
            2))) ) := by
  classical
  intro P T' u fordCentroid v rootCentroidEq'
  rw [rootCentroidEq', (TileTranslationFormulas _ _).2.2.2.2.1,
    fordCentroid P.q P.q_pos]
  simp [v, GaussianInt.intCast_re, GaussianInt.intCast_im,
    Int.cast_add, Int.cast_neg, sub_eq_add_neg]
  constructor <;> linarith

private theorem hUcenter :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (S : Fin (3 : ℕ) →
            Bool → ProtoTile),
        let U := S 1 false
        (TileCentroid U - TileCentroid T = (-(P.q₁ : Real) / 2, (P.q₁ : Real) / 2)) →
            ((TileCentroid T = ((u.re : Real) + (P.q : Real) / 2, (u.im : Real) + (P.q : Real) /
            2)) → (((P.q : Real) = (P.q₁ : Real) + P.q₂) → (TileCentroid U = ((u.re : Real) +
            (P.q₂ : Real) / 2, (u.im : Real) + (P.q₁ : Real) + (P.q₂ : Real) / 2)))) ) := by
  classical
  intro P T u S U hoffU rootCentroid hqreal
  have hu1 := congrArg Prod.fst hoffU
  have hu2 := congrArg Prod.snd hoffU
  have ht1 := congrArg Prod.fst rootCentroid
  have ht2 := congrArg Prod.snd rootCentroid
  apply Prod.ext
  · dsimp at hu1 ht1 ⊢
    linarith [hqreal]
  · dsimp at hu2 ht2 ⊢
    linarith [hqreal]

private theorem hVcenter :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T' : ProtoTile), ∀ (u : GaussianInt), ∀ (S₂ : Fin (3 : ℕ)
            → Bool → ProtoTile),
        let V := S₂ 1 true
        (TileCentroid V - TileCentroid T' = ((P.q₁ : Real) / 2, -(P.q₁ : Real) / 2)) →
            ((TileCentroid T' = ((u.re : Real) - (P.q : Real) / 2, (u.im : Real) + (P.q₂ : Real)
            + (P.q : Real) / 2)) → (((P.q : Real) = (P.q₁ : Real) + P.q₂) → (TileCentroid V =
            ((u.re : Real) - (P.q₂ : Real) / 2, (u.im : Real) + 3 * (P.q₂ : Real) / 2)))) ) := by
  classical
  intro P T' u S₂ V hoffV rootCentroid' hqreal
  have hv1 := congrArg Prod.fst hoffV
  have hv2 := congrArg Prod.snd hoffV
  have ht1 := congrArg Prod.fst rootCentroid'
  have ht2 := congrArg Prod.snd rootCentroid'
  apply Prod.ext
  · dsimp at hv1 ht1 ⊢
    linarith [hqreal]
  · dsimp at hv2 ht2 ⊢
    linarith [hqreal]

private theorem hUcCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (u : GaussianInt), (1 < P.q₂) → (∀ (S : Fin
            (3 : ℕ) → Bool → ProtoTile),
        let U := S 1 false;
        ((P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int)) → ((∀ (n : Nat), (0 < n) → (TileCentroid
            (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → ((TileCentroid U = ((u.re : Real)
            + (P.q₂ : Real) / 2, (u.im : Real) + (P.q₁ : Real) + (P.q₂ : Real) / 2)) → (
        let Uc := TileTranslation (FordTile P.q₂) (u + ⟨0, P.q₁⟩);
        TileCentroid Uc = TileCentroid U))))) ) := by
  classical
  intro P u hcurv S U hqsum fordCentroid hUcenter Uc
  rw [hUcenter]
  rw [(TileTranslationFormulas _ _).2.2.2.2.1, fordCentroid P.q₂ (by omega)]
  simp [GaussianInt.intCast_re, GaussianInt.intCast_im]
  constructor <;> linarith

private theorem hVcCentroid :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        (∀ (u : GaussianInt), (1 < P.q₂) → (∀ (S₂ :
            Fin (3 : ℕ) → Bool → ProtoTile),
        let V := S₂ 1 true;
        ((P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int)) → ((∀ (n : Nat), (0 < n) → (TileCentroid
            (FordTile n) = ((n : Real) / 2, (n : Real) / 2))) → ((TileCentroid V = ((u.re : Real)
            - (P.q₂ : Real) / 2, (u.im : Real) + 3 * (P.q₂ : Real) / 2)) → (
        let Vc := TileTranslation (FordTile P.q₂) (u + ⟨-(P.q₂ : Int), P.q₂⟩);
        TileCentroid Vc = TileCentroid V))))) ) := by
  classical
  intro P u hcurv S₂ V hqsum fordCentroid hVcenter Vc
  rw [hVcenter]
  rw [(TileTranslationFormulas _ _).2.2.2.2.1, fordCentroid P.q₂ (by omega)]
  simp [GaussianInt.intCast_re, GaussianInt.intCast_im]
  constructor <;> linarith

private theorem hQbase :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (horder : P.q₁ < P.q₂), ∀ (hcurv : 1 <
            P.q₂), ∀ (hcross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1), ∀ (hcross2 : (P.p₂
            - P.p₁) * (P.q₂ : Int) - ((P.q₂ - P.q₁ : Nat) : Int) * P.p₂ = -1), ∀ (hredchild :
            Nat.Coprime P.q₂ P.p₂.natAbs),
        let Q : FordFareyParameter := {
          p := P.p₂
          q := P.q₂
          q_pos := by omega
          reduced := hredchild
          p₁ := P.p₁
          q₁ := P.q₁
          p₂ := P.p₂ - P.p₁
          q₂ := P.q₂ - P.q₁
          sum_p := by ring
          sum_q := by omega
          det₁ := by simpa using hcross
          det₂ := hcross2
          q₁_lt := horder
          q₂_pos := by omega
          unit_case := by intro hu; omega
        }
        (BandPrototile (FordCircleCoordinate Q.p Q.q) (FordTile Q.q) ∧ (Q.q = (1 : ℕ) → FordTile
            Q.q = (⟨{(0 : LatticeCell)}, (0 : GaussianInt)⟩ : ProtoTile)) ∧ ((1 : ℕ) < Q.q
            → ProperBandQuadruple (FordRecursiveQuadruple Q) ∧ ∃ (S : Fin (3 : ℕ) → Bool →
            ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), BandSubtileOccurrence
            (FordRecursiveQuadruple Q) (FordTile Q.q) i s (S i s)) ∧ (∀ (x : LatticeCell), x ∈
            (FordTile Q.q).cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) ∧ (S (0 :
            Fin (3 : ℕ)) true).cells = (FordTile Q.q₁).cells ∧ (S (0 : Fin (3 : ℕ)) false).cells
            = (TileTranslation (FordTile Q.q₁) ⟨(↑Q.q₂ : ℤ), (↑Q.q₂ : ℤ)⟩).cells ∧ (S (1 : Fin (3
            : ℕ)) true).cells = (TileTranslation (FordTile Q.q₂) ⟨(↑Q.q₁ : ℤ), (0 : ℤ)⟩).cells ∧
            (S (1 : Fin (3 : ℕ)) false).cells = (TileTranslation (FordTile Q.q₂) ⟨(0 : ℤ), (↑Q.q₁
            : ℤ)⟩).cells ∧ (S (2 : Fin (3 : ℕ)) true).cells = ∅ ∧ (S (2 : Fin (3 : ℕ))
            true).anchor = ⟨(↑Q.q₂ : ℤ), (↑Q.q : ℤ)⟩ ∧ (S (2 : Fin (3 : ℕ)) false).cells = ∅ ∧ (S
            (2 : Fin (3 : ℕ)) false).anchor = ⟨(↑Q.q₁ : ℤ), (0 : ℤ)⟩)) → ((FordCircleCoordinate
            Q.p Q.q = Ci.1.1) → (BandPrototile Ci.1.1 (FordTile P.q₂))) ) := by
  classical
  intro P Ci horder hcurv hcross hcross2 hredchild Q hQrec hQcircle
  have hbase := hQrec.1
  rw [hQcircle] at hbase
  simpa [Q] using hbase

private theorem hUcBand :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt),
        let Uc := TileTranslation (FordTile P.q₂) (u + ⟨0, P.q₁⟩)
        (BandPrototile Ci.1.1 (FordTile P.q₂)) → (BandPrototile Ci.1.1 Uc) ) := by
  classical
  intro P Ci u Uc hQbase
  simpa [Uc] using BandPrototileTranslation Ci.1.1 (FordTile P.q₂)
    (u + ⟨0, P.q₁⟩) hQbase

private theorem hVcBand :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (Ci : BandCircle), ∀ (u : GaussianInt),
        let Vc := TileTranslation (FordTile P.q₂) (u + ⟨-(P.q₂ : Int), P.q₂⟩)
        (BandPrototile Ci.1.1 (FordTile P.q₂)) → (BandPrototile Ci.1.1 Vc) ) := by
  classical
  intro P Ci u Vc hQbase
  simpa [Vc] using BandPrototileTranslation Ci.1.1 (FordTile P.q₂)
    (u + ⟨-(P.q₂ : Int), P.q₂⟩) hQbase

private theorem hveca :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (BandVectors.2 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = ⟨(0 : ℤ), P.p₁⟩) → (BandVectors.2
            (FordRecursiveQuadruple P ((1 : Fin 3) + 2).succ) (FordRecursiveQuadruple P ((1 : Fin
            3) + 1).succ) = (⟨0, P.p₁⟩ : GaussianInt)) ) := by
  classical
  intro P ha13
  change BandVectors.2 (FordRecursiveQuadruple P 1)
    (FordRecursiveQuadruple P 3) = _
  exact ha13

private theorem hcurvNZ :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (FordRecursiveQuadruple P 2).1 ≠ 0
    ) := by
  classical
  intro P
  have hpNat : 0 < P.q₂ * P.q₂ := Nat.mul_pos P.q₂_pos P.q₂_pos
  have hpInt : (0 : Int) < (P.q₂ * P.q₂ : Nat) := by exact_mod_cast hpNat
  have hp : 0 < (FordRecursiveQuadruple P 2).1 := by
    simpa [FordRecursiveQuadruple, FordCircleCoordinate] using hpInt
  omega

private theorem hpRootU :
    (by
      classical
      exact
        ∀ (h : PartialOdometer), ∀ (p : Real × Real), (PartialOdometerSlope h = some p) → (∀
            (pRootU : ℝ × ℝ), (PartialOdometerSlope h = some pRootU) → (pRootU = p)) ) := by
  classical
  intro h p hs pRootU hrootU
  apply Option.some.inj
  exact hrootU.symm.trans hs

private theorem hUoffSlope :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), ∀ (pU : ℝ × ℝ), (pU.1 - p.1 = (1 / 2 :
            ℝ) * (↑P.p₁ : ℝ)) → ((pU.2 - p.2 = -((1 / 2 : ℝ) * (↑P.p₁ : ℝ))) → (pU.1 - p.1 =
            (P.p₁ : Real) / 2 ∧ pU.2 - p.2 = -(P.p₁ : Real) / 2)) ) := by
  classical
  intro P p pU hxU hyU
  constructor <;> linarith

private abbrev hpRootV := ApollonianSuperharmonic.LargeSecondRestrictions.hpRootU

private theorem hVoffSlope :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p' : Real × Real), ∀ (pV : ℝ × ℝ), (pV.1 - p'.1 = -((1 / 2
            : ℝ) * (↑P.p₁ : ℝ))) → ((pV.2 - p'.2 = (1 / 2 : ℝ) * (↑P.p₁ : ℝ)) → (pV.1 - p'.1 =
            -(P.p₁ : Real) / 2 ∧ pV.2 - p'.2 = (P.p₁ : Real) / 2)) ) := by
  classical
  intro P p' pV hxV hyV
  constructor <;> linarith

private theorem hslForm :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), ∀ (p' : Real × Real), (p' - p =
            GaussianRealPoint (BandVectors.2 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) → ((BandVectors.2
            (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ))) = ⟨P.p₂, -P.p⟩) → (p' - p = ((P.p₂ : Real), -(P.p : Real)))) ) := by
  classical
  intro P p p' hsl ha20
  rw [ha20] at hsl
  simpa [GaussianRealPoint] using hsl

private theorem hslopediff :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (p : Real × Real), ∀ (p' : Real × Real), ∀ (pU : ℝ × ℝ),
            (pU.1 - p.1 = (1 / 2 : ℝ) * (↑P.p₁ : ℝ)) → ((pU.2 - p.2 = -((1 / 2 : ℝ) * (↑P.p₁ :
            ℝ))) → ((pU.1 - p.1 = (P.p₁ : Real) / 2 ∧ pU.2 - p.2 = -(P.p₁ : Real) / 2) → (∀ (pV :
            ℝ × ℝ), (pV.1 - p'.1 = -((1 / 2 : ℝ) * (↑P.p₁ : ℝ))) → ((pV.2 - p'.2 = (1 / 2 : ℝ) *
            (↑P.p₁ : ℝ)) → ((pV.1 - p'.1 = -(P.p₁ : Real) / 2 ∧ pV.2 - p'.2 = (P.p₁ : Real) / 2)
            → ((p' - p = ((P.p₂ : Real), -(P.p : Real))) → (
        let s : Real × Real := pU
        let t : Real × Real := pV
        t - s = GaussianRealPoint ⟨P.p₂ - P.p₁, -P.p₂⟩))))))) ) := by
  classical
  intro P p p' pU hxU hyU hUoffSlope pV hxV hyV hVoffSlope hslForm s t
  apply Prod.ext
  · dsimp [s, t]
    have := hUoffSlope.1
    have := hVoffSlope.1
    have hp := congrArg Prod.fst hslForm
    dsimp at hp
    simp [GaussianRealPoint]
    linarith
  · dsimp [s, t]
    have := hUoffSlope.2
    have := hVoffSlope.2
    have hp := congrArg Prod.snd hslForm
    dsimp at hp
    simp [GaussianRealPoint]
    have hpsum : (P.p : Real) = (P.p₁ : Real) + (P.p₂ : Real) := by
      exact_mod_cast P.sum_p
    linarith

private theorem hcentdiff :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (u : GaussianInt), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
            ∀ (S₂ : Fin (3 : ℕ) → Bool → ProtoTile),
        let U := S 1 false
        let V := S₂ 1 true
        (TileCentroid U = ((u.re : Real) + (P.q₂ : Real) / 2, (u.im : Real) + (P.q₁ : Real) +
            (P.q₂ : Real) / 2)) → ((TileCentroid V = ((u.re : Real) - (P.q₂ : Real) / 2, (u.im :
            Real) + 3 * (P.q₂ : Real) / 2)) → (TileCentroid V - TileCentroid U =
            GaussianRealPoint ⟨-(P.q₂ : Int), (P.q₂ : Int) - P.q₁⟩)) ) := by
  classical
  intro P u S S₂ U V hUcenter hVcenter
  rw [hVcenter, hUcenter]
  simp [GaussianRealPoint]
  constructor  <;> ring

private theorem hrootpos :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (C0 : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ)) = C0.1.1) → (0 < C0.1.1.1) ) := by
  classical
  intro P C0 hC0
  rw [← hC0]
  have hp : (0 : Int) < (P.q * P.q : Nat) := by
    have hqn : 0 < P.q := P.q_pos
    exact_mod_cast (Nat.mul_pos hqn hqn)
  simpa [FordRecursiveQuadruple, FordCircleCoordinate] using hp

private theorem hATU :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) =
            C0.1.1) → ((FordRecursiveQuadruple P (2 : Fin (4 : ℕ)) = Ci.1.1) → (∀ (T :
            ProtoTile), ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gfamily : Fin (3 : ℕ) → Bool →
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
        let U := S 1 false
        let g := gfamily 1 false
        (TileOdometer Ci.1.1 U g) → (AncestorTile Ci.1.1 C0.1.1 U T))))))) ) := by
  classical
  intro P hq C0 Ci hC0 hCi T S gfamily hband hfoot hcent U g hUg
  change Relation.ReflTransGen _ (Ci.1.1, U) (C0.1.1, T)
  apply Relation.ReflTransGen.single
  refine ⟨FordRecursiveQuadruple P, 1, false, hq, ?_, ?_,
    (by simpa [hC0] using hband), TileOdometerBandPrototile Ci.1.1 U g hUg,
    hfoot 1 false, hcent 1 false⟩
  · exact hC0
  · exact hCi

private theorem hATV :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), (ProperBandQuadruple (FordRecursiveQuadruple P)) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)) =
            C0.1.1) → ((FordRecursiveQuadruple P (2 : Fin (4 : ℕ)) = Ci.1.1) → (∀ (T' :
            ProtoTile), ∀ (S₂ : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (kfamily : Fin (3 : ℕ) → Bool
            → PartialOdometer), (BandPrototile (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) T') →
            ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), FootprintVertices (S₂ i s) ⊆ FootprintVertices
            T') → ((∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), TileCentroid (S₂ i s) - TileCentroid T' =
            (if s = true then (1 : ℝ) else (-1 : ℝ)) • (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)) - (-(GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ))).2, (GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P (i + (2 : Fin (3 : ℕ))).succ)
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ))).1))) → (
        let V := S₂ 1 true
        let k := kfamily 1 true
        (TileOdometer Ci.1.1 V k) → (AncestorTile Ci.1.1 C0.1.1 V T'))))))) ) := by
  classical
  intro P hq C0 Ci hC0 hCi T' S₂ kfamily hband₂ hfoot₂ hcent₂ V k hVk
  change Relation.ReflTransGen _ (Ci.1.1, V) (C0.1.1, T')
  apply Relation.ReflTransGen.single
  refine ⟨FordRecursiveQuadruple P, 1, true, hq, ?_, ?_,
    (by simpa [hC0] using hband₂), TileOdometerBandPrototile Ci.1.1 V k hVk,
    hfoot₂ 1 true, hcent₂ 1 true⟩
  · exact hC0
  · exact hCi

private theorem hAncU :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer),
            (TileOdometer C0.1.1 T h) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (gfamily : Fin
            (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            FootprintVertices (S i s) ⊆ FootprintVertices T) → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), ∀ x ∈ (gfamily i s).domain, h.value x = (gfamily i s).value x) → (
        let U := S 1 false
        let g := gfamily 1 false
        ((h.domain : Set GaussianInt) = FootprintVertices T) → (((g.domain : Set GaussianInt) =
            FootprintVertices U) → ((AncestorTile Ci.1.1 C0.1.1 U T) → (AncestorOdometer Ci.1.1
            C0.1.1 U T g h)))))) ) := by
  classical
  intro C0 Ci T h hO S gfamily hfoot hvalues U g hrootDom hdomU hATU
  refine ⟨hO, hATU, hdomU, ?_, ?_⟩
  · calc
      (g.domain : Set GaussianInt) = FootprintVertices U := hdomU
      _ ⊆ FootprintVertices T := hfoot 1 false
      _ = (h.domain : Set GaussianInt) := hrootDom.symm
  · intro x hx
    exact (hvalues 1 false x hx).symm

private theorem hAncV :
    (by
      classical
      exact
        ∀ (C0 : BandCircle), ∀ (Ci : BandCircle), ∀ (T' : ProtoTile), ∀ (h' : PartialOdometer),
            (TileOdometer C0.1.1 T' h') → (∀ (S₂ : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (kfamily :
            Fin (3 : ℕ) → Bool → PartialOdometer), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            FootprintVertices (S₂ i s) ⊆ FootprintVertices T') → ((∀ (i : Fin (3 : ℕ)), ∀ (s :
            Bool), ∀ x ∈ (kfamily i s).domain, h'.value x = (kfamily i s).value x) → (
        let V := S₂ 1 true
        let k := kfamily 1 true
        ((h'.domain : Set GaussianInt) = FootprintVertices T') → (((k.domain : Set GaussianInt) =
            FootprintVertices V) → ((AncestorTile Ci.1.1 C0.1.1 V T') → (AncestorOdometer Ci.1.1
            C0.1.1 V T' k h')))))) ) := by
  classical
  intro C0 Ci T' h' hO' S₂ kfamily hfoot₂ hvalues₂ V k hrootDom' hdomV hATV
  refine ⟨hO', hATV, hdomV, ?_, ?_⟩
  · calc
      (k.domain : Set GaussianInt) = FootprintVertices V := hdomV
      _ ⊆ FootprintVertices T' := hfoot₂ 1 true
      _ = (h'.domain : Set GaussianInt) := hrootDom'.symm
  · intro x hx
    exact (hvalues₂ 1 true x hx).symm

end LargeSecondRestrictions

theorem P4158T1LargeSecondRestrictions
    (P : FordFareyParameter) (hq : ProperBandQuadruple (FordRecursiveQuadruple P))
    (C0 Ci : BandCircle)
    (hC0 : FordRecursiveQuadruple P 0 = C0.1.1)
    (hCi : FordRecursiveQuadruple P 2 = Ci.1.1)
    (hlarge : 1 < Ci.1.1.1) (horder : P.q₁ < P.q₂)
    (T T' : ProtoTile) (h h' : PartialOdometer)
    (hO : TileOdometer C0.1.1 T h) (hO' : TileOdometer C0.1.1 T' h')
    (p p' : Real × Real)
    (hs : PartialOdometerSlope h = some p)
    (hs' : PartialOdometerSlope h' = some p')
    (hsl : p' - p = GaussianRealPoint
      (BandVectors.2 (FordRecursiveQuadruple P 2) (FordRecursiveQuadruple P 0)))
    (u : GaussianInt)
    (hc : T.cells = (TileTranslation (FordTile P.q) u).cells)
    (hc' : T'.cells = (TileTranslation (FordTile P.q) (u + ⟨-(P.q : Int), P.q₂⟩)).cells) :
    ∃ (U V : ProtoTile) (g k : PartialOdometer) (s t : Real × Real)
      (Q : FordFareyParameter),
      AncestorOdometer Ci.1.1 C0.1.1 U T g h ∧
      AncestorOdometer Ci.1.1 C0.1.1 V T' k h' ∧
      TileOdometer Ci.1.1 U g ∧ TileOdometer Ci.1.1 V k ∧
      PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t ∧
      U.cells = (TileTranslation (FordTile P.q₂) (u + ⟨0, P.q₁⟩)).cells ∧
      V.cells = (TileTranslation (FordTile P.q₂) (u + ⟨-(P.q₂ : Int), P.q₂⟩)).cells ∧
      TileCentroid V - TileCentroid U = GaussianRealPoint ⟨-(P.q₂ : Int), (P.q₂ : Int) - P.q₁⟩ ∧
      t - s = GaussianRealPoint ⟨P.p₂ - P.p₁, -P.p₂⟩ ∧
      Q.q = P.q₂ ∧ Q.q₂ = P.q₂ - P.q₁ ∧ Q.p = P.p₂ ∧ Q.p₂ = P.p₂ - P.p₁ ∧
      FordRecursiveQuadruple Q 0 = Ci.1.1 ∧ 1 < Q.q := by
-- BODY
  classical
  have hcurv := LargeSecondRestrictions.hcurv P Ci hCi hlarge horder
  have hqgt := LargeSecondRestrictions.hqgt P hcurv
  have hq0 : 1 < (FordRecursiveQuadruple P 0).1 := LargeSecondRestrictions.hq0 P hqgt
  have hd := TileOdometerReindexedDecomposition
    (FordRecursiveQuadruple P) hq T h hq0 (by simpa [hC0] using hO)
  rcases hd with ⟨S, gfamily, hband, hchild, hcells, hfoot, hcent,
    hdomains, hvalues, hcompatible, hslope⟩
  have hd' := TileOdometerReindexedDecomposition
    (FordRecursiveQuadruple P) hq T' h' hq0 (by simpa [hC0] using hO')
  rcases hd' with ⟨S₂, kfamily, hband₂, hchild₂, hcells₂, hfoot₂, hcent₂,
    hdomains₂, hvalues₂, hcompatible₂, hslope₂⟩
  let U := S 1 false
  let V := S₂ 1 true
  let g := gfamily 1 false
  let k := kfamily 1 true
  have hUg := LargeSecondRestrictions.hUg P Ci hCi S gfamily hchild
  have hVk := LargeSecondRestrictions.hVk P Ci hCi S₂ kfamily hchild₂
  have hcross : P.p₁ * (P.q₂ : Int) - (P.q₁ : Int) * P.p₂ = 1 := LargeSecondRestrictions.hcross P
  have hcross2 := LargeSecondRestrictions.hcross2 P horder hcross
  have hredchild := LargeSecondRestrictions.hredchild P hcross
  let Q : FordFareyParameter := {
    p := P.p₂
    q := P.q₂
    q_pos := by omega
    reduced := hredchild
    p₁ := P.p₁
    q₁ := P.q₁
    p₂ := P.p₂ - P.p₁
    q₂ := P.q₂ - P.q₁
    sum_p := by ring
    sum_q := by omega
    det₁ := by simpa using hcross
    det₂ := hcross2
    q₁_lt := horder
    q₂_pos := by omega
    unit_case := by intro hu; omega
  }
  have hvconfig := (FordCoordinateConfiguration P).2 hqgt
  rcases hvconfig with ⟨hproper, h10, h20, h30, ha10, ha20, ha30, ha32, ha13⟩
  have vSystem : RecursiveVectorSystem BandVectors := by
    simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
  rcases vSystem with ⟨_, _, vstep, _⟩
  have vlaws := VectorRecursionLaws (FordRecursiveQuadruple P) hq.1
  rcases vlaws with ⟨hsum, _, hrec, _⟩
  let w := BandVectors.1 (FordRecursiveQuadruple P 3) (FordRecursiveQuadruple P 2)
  let a := BandVectors.1 (FordRecursiveQuadruple P 1) (FordRecursiveQuadruple P 3)
  let b := BandVectors.1 (FordRecursiveQuadruple P 2) (FordRecursiveQuadruple P 1)
  have hsum' : w + a + b = 0 := by simpa [w, a, b] using hsum
  have hfirst : a - (⟨0, 1⟩ : GaussianInt) * b = ⟨(P.q : Int), (P.q₁ : Int)⟩ :=
    hrec.symm.trans h10
  have hstep := vstep (FordRecursiveQuadruple P) hq.1
  have hsecond : b - (⟨0, 1⟩ : GaussianInt) * w = ⟨-(P.q : Int), (P.q₂ : Int)⟩ :=
    hstep.1.symm.trans h20
  have hqsum : (P.q : Int) = (P.q₁ : Int) + (P.q₂ : Int) := by
    exact_mod_cast P.sum_q
  have hv13 := LargeSecondRestrictions.hv13 P hsum' hfirst hsecond hqsum
  have hoffU := LargeSecondRestrictions.hoffU P T S hcent hv13
  have hoffV := LargeSecondRestrictions.hoffV P T' S₂ hcent₂ hv13
  have fordCentroid (n : Nat) (hn : 0 < n) := LargeSecondRestrictions.fordCentroid n hn
  have rootCentroidEq := LargeSecondRestrictions.rootCentroidEq P T u hc
  have rootCentroid := LargeSecondRestrictions.rootCentroid P T u fordCentroid rootCentroidEq
  have rootCentroidEq' := LargeSecondRestrictions.rootCentroidEq' P T' u hc'
  have rootCentroid' := LargeSecondRestrictions.rootCentroid' P T' u fordCentroid rootCentroidEq'
  have hqreal : (P.q : Real) = (P.q₁ : Real) + P.q₂ := by exact_mod_cast P.sum_q
  have hUcenter := LargeSecondRestrictions.hUcenter P T u S hoffU rootCentroid hqreal
  have hVcenter := LargeSecondRestrictions.hVcenter P T' u S₂ hoffV rootCentroid' hqreal
  let Uc := TileTranslation (FordTile P.q₂) (u + ⟨0, P.q₁⟩)
  let Vc := TileTranslation (FordTile P.q₂) (u + ⟨-(P.q₂ : Int), P.q₂⟩)
  have hUcCentroid := LargeSecondRestrictions.hUcCentroid P u hcurv S hqsum fordCentroid hUcenter
  have hVcCentroid := LargeSecondRestrictions.hVcCentroid P u hcurv S₂ hqsum fordCentroid
      hVcenter
  have hQrec := FordTileRecursiveIdentification Q
  have hQcircle : FordCircleCoordinate Q.p Q.q = Ci.1.1 := by
    simpa [FordRecursiveQuadruple, Q] using hCi
  have hQbase := LargeSecondRestrictions.hQbase P Ci horder hcurv hcross hcross2 hredchild hQrec
      hQcircle
  have hUcBand := LargeSecondRestrictions.hUcBand P Ci u hQbase
  have hVcBand := LargeSecondRestrictions.hVcBand P Ci u hQbase
  have hUcells : U.cells = Uc.cells :=
    (BandPrototileCentroidUnique Ci.1.1 U Uc
      (TileOdometerBandPrototile Ci.1.1 U g hUg) hUcBand hUcCentroid.symm).1
  have hVcells : V.cells = Vc.cells :=
    (BandPrototileCentroidUnique Ci.1.1 V Vc
      (TileOdometerBandPrototile Ci.1.1 V k hVk) hVcBand hVcCentroid.symm).1
  have hveca : BandVectors.2 (FordRecursiveQuadruple P ((1 : Fin 3) + 2).succ)
      (FordRecursiveQuadruple P ((1 : Fin 3) + 1).succ) =
      (⟨0, P.p₁⟩ : GaussianInt) := LargeSecondRestrictions.hveca P ha13
  have hcurvNZ := LargeSecondRestrictions.hcurvNZ P
  obtain hzU | ⟨pRootU, pU, hrootU, hsU, hxU, hyU⟩ := hslope 1 false
  · exact (hcurvNZ hzU).elim
  have hpRootU := LargeSecondRestrictions.hpRootU h p hs pRootU hrootU
  subst pRootU
  rw [hveca] at hxU hyU
  norm_num at hxU hyU
  have hUoffSlope := LargeSecondRestrictions.hUoffSlope P p pU hxU hyU
  obtain hzV | ⟨pRootV, pV, hrootV, hsV, hxV, hyV⟩ := hslope₂ 1 true
  · exact (hcurvNZ hzV).elim
  have hpRootV := LargeSecondRestrictions.hpRootV h' p' hs' pRootV hrootV
  subst pRootV
  rw [hveca] at hxV hyV
  norm_num at hxV hyV
  have hVoffSlope := LargeSecondRestrictions.hVoffSlope P p' pV hxV hyV
  have hslForm := LargeSecondRestrictions.hslForm P p p' hsl ha20
  let s : Real × Real := pU
  let t : Real × Real := pV
  have hslopes : PartialOdometerSlope g = some s ∧ PartialOdometerSlope k = some t := by
    exact ⟨by simpa [g, s] using hsU, by simpa [k, t] using hsV⟩
  have hslopediff := LargeSecondRestrictions.hslopediff P p p' pU hxU hyU hUoffSlope pV hxV hyV
      hVoffSlope hslForm
  have hcentdiff := LargeSecondRestrictions.hcentdiff P u S S₂ hUcenter hVcenter
  have hrootpos := LargeSecondRestrictions.hrootpos P C0 hC0
  have hrootpos' : 0 < C0.1.1.1 := hrootpos
  have hrootDom : (h.domain : Set GaussianInt) = FootprintVertices T :=
    PositiveCurvatureTileOdometerDomain C0.1.1 T h hrootpos hO
  have hrootDom' : (h'.domain : Set GaussianInt) = FootprintVertices T' :=
    PositiveCurvatureTileOdometerDomain C0.1.1 T' h' hrootpos' hO'
  have hchildpos : 0 < Ci.1.1.1 := by omega
  have hdomU : (g.domain : Set GaussianInt) = FootprintVertices U :=
    PositiveCurvatureTileOdometerDomain Ci.1.1 U g hchildpos hUg
  have hdomV : (k.domain : Set GaussianInt) = FootprintVertices V :=
    PositiveCurvatureTileOdometerDomain Ci.1.1 V k hchildpos hVk
  have hATU := LargeSecondRestrictions.hATU P hq C0 Ci hC0 hCi T S gfamily hband hfoot hcent hUg
  have hATV := LargeSecondRestrictions.hATV P hq C0 Ci hC0 hCi T' S₂ kfamily hband₂ hfoot₂ hcent₂
      hVk
  have hAncU := LargeSecondRestrictions.hAncU C0 Ci T h hO S gfamily hfoot hvalues hrootDom hdomU
      hATU
  have hAncV := LargeSecondRestrictions.hAncV C0 Ci T' h' hO' S₂ kfamily hfoot₂ hvalues₂
      hrootDom' hdomV hATV
  refine ⟨U, V, g, k, s, t, Q, hAncU, hAncV, hUg, hVk,
    hslopes.1, hslopes.2, ?_, ?_, hcentdiff, hslopediff,
    rfl, rfl, rfl, rfl, hQcircle, ?_⟩
  · simpa [Uc] using hUcells
  · simpa [Vc] using hVcells
  · exact hcurv

end ApollonianSuperharmonic

end
