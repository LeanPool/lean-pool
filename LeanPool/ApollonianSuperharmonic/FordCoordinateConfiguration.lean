/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.FordFareySum

public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandVectors
public import LeanPool.ApollonianSuperharmonic.FordRecursiveQuadruple
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: FordCoordinateConfiguration]

/-!
# FordCoordinateConfiguration

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordConfigurationProof

private theorem determinantCoprime :
    ∀ (a : Int), ∀ (b : Nat), ∀ (d : Nat), ∀ (c : Int), a * (d : Int) - (b : Int) * c = 1 →
        Nat.Coprime b a.natAbs := by
  classical
  intro a b d c hd
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  let g := Nat.gcd b a.natAbs
  have gb : g ∣ b := Nat.gcd_dvd_left _ _
  have ga : g ∣ a.natAbs := Nat.gcd_dvd_right _ _
  have gb' : (g : Int) ∣ (b : Int) := by exact_mod_cast gb
  have ga' : (g : Int) ∣ a :=
    (Int.dvd_natAbs).mp (by exact_mod_cast ga)
  have gd : (g : Int) ∣ a * (d : Int) - (b : Int) * c := by
    exact dvd_sub (dvd_mul_of_dvd_left ga' _) (dvd_mul_of_dvd_left gb' _)
  have gd1 : (g : Int) ∣ 1 := by simpa [hd] using gd
  have ge : (g : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le g)) gd1
  have gn : g = 1 := by exact_mod_cast ge
  simp [g, gn]

private theorem hv32At253 :
    ∀ (Q : FordFareyParameter), (Q.q₁ = 1) → ((Q.q₂ = 1) → ((Q.p₁ = Q.p₂ + 1) → ((Q.q = 2) →
        ((FordCircleCoordinate Q.p₂ 1 = (1, 1 + 2 * (⟨0, Q.p₂ - 1⟩ : GaussianInt) + 2 * (⟨0, 1⟩ :
        GaussianInt))) → ((BandVectors.1 ((0 : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 :
        GaussianInt)) = (0 : GaussianInt) ∧ BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ),
        (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) *
        ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2
        : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0
        : ℤ), (-1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0 : ℤ), (-1 :
        GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0 : ℤ),
        (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1
        : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) - ⟨(0 : ℤ), Q.p₂ -
        (1 : ℤ)⟩ - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 :
        GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 :
        ℤ), (-1 : GaussianInt)) = ⟨(0 : ℤ), Q.p₂⟩) → ((BandVectors.1 ((1 : ℤ), (1 : GaussianInt)
        + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)
        ((0 : ℤ), (-1 : GaussianInt)) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 ((0 : ℤ), (-1 :
        GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩
        + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)
        ((0 : ℤ), (-1 : GaussianInt)) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 ((0 : ℤ), (-1 :
        GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩
        + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)) → (BandVectors.1 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) =
        -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt))))))))) := by
  classical
  intro Q qone hqone hp hq coord2 b2 f1
  have hx := f1.1
  have hbase := b2.2.2.1
  have hi : (⟨0, 1⟩ : GaussianInt) * ⟨0, 1⟩ = -1 := by
    ext <;> norm_num
  have hx' : (⟨0, 1⟩ : GaussianInt) *
        BandVectors.1 ((FordRecursiveQuadruple Q) 3)
          ((FordRecursiveQuadruple Q) 2) = 1 := by
    simpa [FordRecursiveQuadruple, qone, hqone, hp, hq,
      Q.sum_p, Q.sum_q, coord2] using hx.symm.trans hbase
  calc
    BandVectors.1 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) =
        (-((⟨0, 1⟩ : GaussianInt))) *
          ((⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 ((FordRecursiveQuadruple Q) 3)
              ((FordRecursiveQuadruple Q) 2)) := by
                simp only [neg_mul]
                rw [← mul_assoc, hi]
                simp
    _ = -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)) := by
      rw [hx']
      simp [hqone]

private theorem ha13At278 :
    ∀ (Q : FordFareyParameter), (Q.q₁ = 1) → ((Q.q₂ = 1) → ((Q.p₁ = Q.p₂ + 1) → ((Q.q = 2) → (
    let z : GaussianInt := ⟨0, Q.p₂⟩
    (FordCircleCoordinate (Q.p₂ + 1) 1 = (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))) →
        ((BandVectors.1 ((0 : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (0 :
        GaussianInt) ∧ BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) ∧
        BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) *
        ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 : ℤ), (-1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0
        : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (1 : GaussianInt) ∧
        BandVectors.2 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 :
        GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) - z - ⟨(0
        : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 :
        GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 : ℤ), (-1 : GaussianInt)) = z + ⟨(0 : ℤ), (1 :
        ℤ)⟩) → (BandVectors.2 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) =
        (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt))))))) := by
  classical
  intro Q qone hqone hp hq z coord1 b1
  calc
    BandVectors.2 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) = ⟨0, Q.p₂ + 1⟩ := by
      simpa [FordRecursiveQuadruple, qone, hqone, hp, hq, Q.sum_p,
        Q.sum_q, z, coord1] using b1.2.2.2.2.2
    _ = (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt) := by
      ext <;> simp [hp]

private theorem ha32At288 :
    ∀ (Q : FordFareyParameter), (Q.q₁ = 1) → ((Q.q₂ = 1) → ((Q.p₁ = Q.p₂ + 1) → ((Q.q = 2) →
        ((FordCircleCoordinate Q.p₂ 1 = (1, 1 + 2 * (⟨0, Q.p₂ - 1⟩ : GaussianInt) + 2 * (⟨0, 1⟩ :
        GaussianInt))) → ((BandVectors.1 ((0 : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 :
        GaussianInt)) = (0 : GaussianInt) ∧ BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ),
        (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) *
        ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) ∧ BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2
        : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0
        : ℤ), (-1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0 : ℤ), (-1 :
        GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0 : ℤ),
        (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1
        : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) - ⟨(0 : ℤ), Q.p₂ -
        (1 : ℤ)⟩ - ⟨(0 : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 :
        GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 :
        ℤ), (-1 : GaussianInt)) = ⟨(0 : ℤ), Q.p₂⟩) → ((BandVectors.1 ((1 : ℤ), (1 : GaussianInt)
        + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)
        ((0 : ℤ), (-1 : GaussianInt)) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 ((0 : ℤ), (-1 :
        GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩
        + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩ + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)
        ((0 : ℤ), (-1 : GaussianInt)) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2 ((0 : ℤ), (-1 :
        GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * ⟨(0 : ℤ), Q.p₂ - (1 : ℤ)⟩
        + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩)) → (BandVectors.2 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) = -(Q.p₂ : GaussianInt)))))))) := by
  classical
  intro Q qone hqone hp hq coord2 b2 f1
  have hx := f1.2
  have hbase := b2.2.2.2.2.2
  have hx' : -(⟨0, 1⟩ : GaussianInt) *
        BandVectors.2 ((FordRecursiveQuadruple Q) 3)
          ((FordRecursiveQuadruple Q) 2) =
        ⟨0, Q.p₂⟩ := by
    simpa [FordRecursiveQuadruple, qone, hqone, hp, hq,
      Q.sum_p, Q.sum_q, coord2] using hx.symm.trans hbase
  calc
    BandVectors.2 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) =
        (⟨0, 1⟩ : GaussianInt) *
          (-(⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 ((FordRecursiveQuadruple Q) 3)
              ((FordRecursiveQuadruple Q) 2)) := by
                rw [← mul_assoc]
                ext <;> norm_num
    _ = -(Q.p₂ : GaussianInt) := by
      rw [hx']
      ext <;> simp

private theorem hsemiAt342 :
    ∀ (Q : FordFareyParameter),
      ∀ (q1pos : 0 < Q.q₁),
        ∀ (hgtq : Q.q₁ > Q.q₂),
          let pd : Int := Q.p₁ - Q.p₂
          let qd : Nat := Q.q₁ - Q.q₂
          0 < qd →
            ∀ (hqdlt : qd < Q.q₁),
              ∀ (hd1 : pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1),
                ∀ (hd2 : Q.p₂ * (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1),
                  ∀ (hred : Nat.Coprime Q.q₁ Q.p₁.natAbs),
                    ∀ (hq1gt : 1 < Q.q₁),
                      let R : FordFareyParameter :=
                        { p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred, p₁ := pd,
                          q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂, sum_p := by dsimp [pd]; ring,
                          sum_q := by dsimp [qd]; omega, det₁ := hd1, det₂ := hd2,
                          q₁_lt := hqdlt, q₂_pos := Q.q₂_pos,
                          unit_case := by intro hu; omega }
                      SemiProperQuadruple
                          ![((2 : ℤ) * (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))).1 -
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) *
                            (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) *
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) *
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))).2 -
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))).2),
                            FordRecursiveQuadruple R (0 : Fin (4 : ℕ)),
                            FordRecursiveQuadruple R (2 : Fin (4 : ℕ)),
                            FordRecursiveQuadruple R (3 : Fin (4 : ℕ))] →
                        SemiProperQuadruple (FordRecursiveQuadruple Q) := by
  classical
  intro Q q1pos hgtq pd qd hqdpos hqdlt hd1 hd2 hred hq1gt R hsucc
  convert hsucc using 1;
    simp only [FordRecursiveQuadruple, FordCircleCoordinate, Q.sum_q, Nat.cast_mul,
        Nat.cast_add, Int.reduceNeg, Q.sum_p, hqdpos.ne', ↓reduceIte, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val, mul_zero, add_zero, Matrix.cons_val_one,
        mul_neg, mul_one, Matrix.vecCons_inj, Prod.mk.injEq, ite_eq_right_iff, zero_eq_mul,
        Int.natCast_eq_zero, or_self, and_true, qd, pd, R]
  all_goals try rw [Nat.cast_sub (by omega)]
  repeat' first | constructor | (ext <;> simp; ring)
  all_goals try ring
  all_goals try (intro hz; omega)

private theorem hv13At359 :
    ∀ (Q : FordFareyParameter),
      ∀ (q1pos : 0 < Q.q₁),
        ∀ (hgtq : Q.q₁ > Q.q₂),
          let pd : Int := Q.p₁ - Q.p₂
          let qd : Nat := Q.q₁ - Q.q₂
          ∀ (hqdlt : qd < Q.q₁),
            ∀ (hd1 : pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1),
              ∀ (hd2 : Q.p₂ * (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1),
                ∀ (hred : Nat.Coprime Q.q₁ Q.p₁.natAbs),
                  ∀ (hq1gt : 1 < Q.q₁),
                    let R : FordFareyParameter :=
                      { p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred, p₁ := pd,
                        q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂, sum_p := by dsimp [pd]; ring,
                        sum_q := by dsimp [qd]; omega, det₁ := hd1, det₂ := hd2,
                        q₁_lt := hqdlt, q₂_pos := Q.q₂_pos,
                        unit_case := by intro hu; omega }
                    BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                          (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) =
                        -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.q₂ : GaussianInt)) →
                      BandVectors.1 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                          (↑R.q₁ : GaussianInt) →
                        BandVectors.1 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))) =
                            BandVectors.1 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.1 (FordRecursiveQuadruple R (0 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                            BandVectors.1 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))) =
                            BandVectors.2 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (FordRecursiveQuadruple R (0 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                            BandVectors.2 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) →
                          BandVectors.1 ((FordRecursiveQuadruple Q) 1)
                            ((FordRecursiveQuadruple Q) 3) =
                            (Q.q₁ : GaussianInt) := by
  classical
  intro Q q1pos hgtq pd qd hqdlt hd1 hd2 hred hq1gt R rv32 rv13 direct
  have hx := direct.2.1
  rw [rv13, rv32] at hx
  simp only [FordRecursiveQuadruple, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val,
      Int.reduceNeg, mul_neg, R] at hx
  have hcalc : (qd : GaussianInt) +
      (⟨0, 1⟩ : GaussianInt) *
        (-((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt))) =
      (Q.q₁ : GaussianInt) := by
    have hle : Q.q₂ ≤ Q.q₁ := Nat.le_of_lt hgtq
    have hi : (⟨0, 1⟩ : GaussianInt) * ⟨0, 1⟩ = -1 := by
      ext <;> norm_num
    have hmul : (⟨0, 1⟩ : GaussianInt) *
          (-((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt))) =
          (Q.q₂ : GaussianInt) := by
      rw [mul_neg, ← mul_assoc, hi]
      simp
    rw [hmul]
    ext <;> simp [qd, Nat.cast_sub hle];
  rw [← mul_neg] at hx
  rw [hcalc] at hx
  simpa [FordRecursiveQuadruple, R, Q.sum_q, q1pos.ne'] using hx

private theorem ha13At390 :
    ∀ (Q : FordFareyParameter),
      ∀ (q1pos : 0 < Q.q₁),
        ∀ (hgtq : Q.q₁ > Q.q₂),
          let pd : Int := Q.p₁ - Q.p₂
          let qd : Nat := Q.q₁ - Q.q₂
          ∀ (hqdlt : qd < Q.q₁),
            ∀ (hd1 : pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1),
              ∀ (hd2 : Q.p₂ * (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1),
                ∀ (hred : Nat.Coprime Q.q₁ Q.p₁.natAbs),
                  ∀ (hq1gt : 1 < Q.q₁),
                    let R : FordFareyParameter :=
                      { p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred, p₁ := pd,
                        q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂, sum_p := by dsimp [pd]; ring,
                        sum_q := by dsimp [qd]; omega, det₁ := hd1, det₂ := hd2,
                        q₁_lt := hqdlt, q₂_pos := Q.q₂_pos,
                        unit_case := by intro hu; omega }
                    BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                          (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) =
                        -(↑R.p₂ : GaussianInt) →
                      BandVectors.2 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                          ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.p₁ : GaussianInt) →
                        BandVectors.1 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))) =
                            BandVectors.1 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.1 (FordRecursiveQuadruple R (0 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                            BandVectors.1 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (0 : Fin (4 : ℕ))) =
                            BandVectors.2 (FordRecursiveQuadruple R (2 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (FordRecursiveQuadruple R (0 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                            BandVectors.2 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) →
                          BandVectors.2 ((FordRecursiveQuadruple Q) 1)
                            ((FordRecursiveQuadruple Q) 3) =
                            (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt) := by
  classical
  intro Q q1pos hgtq pd qd hqdlt hd1 hd2 hred hq1gt R ra32 ra13 direct
  have hx := direct.2.2.2
  rw [ra13, ra32] at hx
  have hx' : BandVectors.2 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) =
        (⟨0, 1⟩ : GaussianInt) * (pd : GaussianInt) +
          (⟨0, 1⟩ : GaussianInt) * (Q.p₂ : GaussianInt) := by
    simpa [FordRecursiveQuadruple, R, q1pos.ne'] using hx
  calc
    BandVectors.2 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) =
        (⟨0, 1⟩ : GaussianInt) * (pd : GaussianInt) +
          (⟨0, 1⟩ : GaussianInt) * (Q.p₂ : GaussianInt) := hx'
    _ = (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt) := by
      dsimp [pd]
      ext <;> simp

private theorem hsemiAt448 :
    ∀ (Q : FordFareyParameter),
      ∀ (hgtq : ¬Q.q₁ > Q.q₂),
        let pd : Int := Q.p₂ - Q.p₁
        let qd : Nat := Q.q₂ - Q.q₁
        0 < Q.q₁ →
          ∀ (hqdpos : 0 < qd),
            ∀ (hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1),
              ∀ (hd2 : pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1),
                ∀ (hred : Nat.Coprime Q.q₂ Q.p₂.natAbs),
                  ∀ (hq2gt : 1 < Q.q₂),
                    let R : FordFareyParameter :=
                      { p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
                        p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
                        sum_p := by dsimp [pd]; ring, sum_q := by dsimp [qd]; omega,
                        det₁ := hd1, det₂ := hd2, q₁_lt := by omega, q₂_pos := hqdpos,
                        unit_case := by intro hu; omega }
                    let rotatedTuple : Fin 4 → CircleCoordinates :=
                      ![FordRecursiveQuadruple R 0, FordRecursiveQuadruple R 2,
                        FordRecursiveQuadruple R 3, FordRecursiveQuadruple R 1]
                    SemiProperQuadruple
                        ![![![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (0 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (2 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (3 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (1 : Fin (4 : ℕ))]
                            (0 : Fin (4 : ℕ)),
                          ![![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (0 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (2 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (3 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (1 : Fin (4 : ℕ))]
                            (2 : Fin (4 : ℕ)),
                          ![![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (0 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (2 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (3 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (1 : Fin (4 : ℕ))]
                            (3 : Fin (4 : ℕ)),
                          ![![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (0 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (2 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (3 : Fin (4 : ℕ)),
                            ![((2 : ℤ) * (rotatedTuple (0 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (2 : Fin (4 : ℕ))).1 +
                            (2 : ℤ) * (rotatedTuple (3 : Fin (4 : ℕ))).1 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).1,
                            (2 : GaussianInt) * (rotatedTuple (0 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (2 : Fin (4 : ℕ))).2 +
                            (2 : GaussianInt) * (rotatedTuple (3 : Fin (4 : ℕ))).2 -
                            (rotatedTuple (1 : Fin (4 : ℕ))).2),
                            rotatedTuple (0 : Fin (4 : ℕ)), rotatedTuple (2 : Fin (4 : ℕ)),
                            rotatedTuple (3 : Fin (4 : ℕ))]
                            (1 : Fin (4 : ℕ))]
                            (1 : Fin (4 : ℕ))] →
                      SemiProperQuadruple (FordRecursiveQuadruple Q) := by
  classical
  intro Q hgtq pd qd q1pos' hqdpos hd1 hd2 hred hq2gt R rotatedTuple hfinal
  have rcond : R.q₁ ≠ 0 := by simp [R, q1pos'.ne']
  have rentry : FordRecursiveQuadruple R 1 =
      FordCircleCoordinate Q.p₁ Q.q₁ := by
    simp [FordRecursiveQuadruple, R, q1pos'.ne']
  convert hfinal using 1;
    simp only [FordRecursiveQuadruple, FordCircleCoordinate, Q.sum_q, Nat.cast_mul,
        Nat.cast_add, Int.reduceNeg, Q.sum_p, rcond, ↓reduceIte, Nat.succ_eq_add_one,
        Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val,
        Matrix.cons_val_one, Matrix.vecCons_inj, Prod.mk.injEq, and_true, R]
  all_goals try simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val,
      Matrix.cons_val_one, Int.reduceNeg, rotatedTuple]
  repeat' first | constructor | (ext <;> simp only [Fin.isValue, Int.reduceNeg, Zsqrtd.im_sub,
      Zsqrtd.im_add, Zsqrtd.im_mul, Zsqrtd.re_ofNat, Nat.cast_ofNat, Zsqrtd.im_ofNat,
      zero_mul, add_zero, Zsqrtd.re_sub, Zsqrtd.re_add, Zsqrtd.re_mul, mul_zero] <;> ring)
  all_goals try ring
  all_goals try rw [rentry]
  all_goals try simp only [Fin.isValue, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      one_mul]
  all_goals try simp only [FordRecursiveQuadruple, q1pos'.ne', ↓reduceIte, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val, zero_mul, add_zero, R, Int.reduceNeg,
      Zsqrtd.im_neg, Zsqrtd.im_one, neg_zero, Zsqrtd.re_neg, Zsqrtd.re_one, neg_mul, one_mul,
      neg_add_cancel_right]
  all_goals try simp only [FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg, qd, pd, one_mul,
      Int.reduceSub]
  all_goals try rw [Nat.cast_sub (by omega)]
  all_goals try ring


private theorem hv32At473 :
    ∀ (Q : FordFareyParameter),
      ∀ (hgtq : ¬Q.q₁ > Q.q₂),
        let pd : Int := Q.p₂ - Q.p₁
        let qd : Nat := Q.q₂ - Q.q₁
        0 < Q.q₁ →
          ∀ (hqdpos : 0 < qd),
            ∀ (hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1),
              ∀ (hd2 : pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1),
                ∀ (hred : Nat.Coprime Q.q₂ Q.p₂.natAbs),
                  ∀ (hq2gt : 1 < Q.q₂),
                    let R : FordFareyParameter :=
                      { p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
                        p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
                        sum_p := by dsimp [pd]; ring, sum_q := by dsimp [qd]; omega,
                        det₁ := hd1, det₂ := hd2, q₁_lt := by omega, q₂_pos := hqdpos,
                        unit_case := by intro hu; omega }
                    BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                          (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) =
                        -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.q₂ : GaussianInt)) →
                      BandVectors.1 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                          (↑R.q₁ : GaussianInt) →
                        let rotatedTuple : Fin 4 → CircleCoordinates :=
                          ![FordRecursiveQuadruple R 0, FordRecursiveQuadruple R 2,
                            FordRecursiveQuadruple R 3, FordRecursiveQuadruple R 1]
                        BandVectors.1 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (0 : Fin (4 : ℕ))) =
                            BandVectors.1 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (1 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.1 (rotatedTuple (0 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) =
                            BandVectors.1 (rotatedTuple (1 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (0 : Fin (4 : ℕ))) =
                            BandVectors.2 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (1 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (rotatedTuple (0 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) =
                            BandVectors.2 (rotatedTuple (1 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) →
                          BandVectors.1 ((FordRecursiveQuadruple Q) 3)
                            ((FordRecursiveQuadruple Q) 2) =
                            -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)) := by
  classical
  intro Q hgtq pd qd q1pos' hqdpos hd1 hd2 hred hq2gt R rv32 rv13 rotatedTuple direct
  have hx := direct.1
  have rv32' : BandVectors.1 (rotatedTuple 2) (rotatedTuple 1) =
      -((⟨0, 1⟩ : GaussianInt) * (qd : GaussianInt)) := by
    simpa [rotatedTuple, FordRecursiveQuadruple, R, q1pos'.ne'] using rv32
  have rv13' : BandVectors.1 (rotatedTuple 3) (rotatedTuple 2) =
      (Q.q₁ : GaussianInt) := by
    simpa [rotatedTuple, FordRecursiveQuadruple, R, q1pos'.ne'] using rv13
  rw [rv32', rv13'] at hx
  have hqdrel : qd + Q.q₁ = Q.q₂ := by
    dsimp [qd]
    omega
  have hcalc : -((⟨0, 1⟩ : GaussianInt) * (qd : GaussianInt)) -
      (⟨0, 1⟩ : GaussianInt) * (Q.q₁ : GaussianInt) =
      -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)) := by
    have hle : Q.q₁ ≤ Q.q₂ := by omega
    ext <;> simp [qd, Nat.cast_sub hle];
  rw [hcalc] at hx
  simpa [rotatedTuple, FordRecursiveQuadruple, R, q1pos'.ne'] using hx

private theorem ha32At503 :
    ∀ (Q : FordFareyParameter),
      ∀ (hgtq : ¬Q.q₁ > Q.q₂),
        let pd : Int := Q.p₂ - Q.p₁
        let qd : Nat := Q.q₂ - Q.q₁
        0 < Q.q₁ →
          ∀ (hqdpos : 0 < qd),
            ∀ (hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1),
              ∀ (hd2 : pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1),
                ∀ (hred : Nat.Coprime Q.q₂ Q.p₂.natAbs),
                  ∀ (hq2gt : 1 < Q.q₂),
                    let R : FordFareyParameter :=
                      { p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
                        p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
                        sum_p := by dsimp [pd]; ring, sum_q := by dsimp [qd]; omega,
                        det₁ := hd1, det₂ := hd2, q₁_lt := by omega, q₂_pos := hqdpos,
                        unit_case := by intro hu; omega }
                    BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ)))
                          (FordRecursiveQuadruple R (2 : Fin (4 : ℕ))) =
                        -(↑R.p₂ : GaussianInt) →
                      BandVectors.2 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ)))
                            (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) =
                          ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.p₁ : GaussianInt) →
                        let rotatedTuple : Fin 4 → CircleCoordinates :=
                          ![FordRecursiveQuadruple R 0, FordRecursiveQuadruple R 2,
                            FordRecursiveQuadruple R 3, FordRecursiveQuadruple R 1]
                        BandVectors.1 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (0 : Fin (4 : ℕ))) =
                            BandVectors.1 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (1 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.1 (rotatedTuple (0 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) =
                            BandVectors.1 (rotatedTuple (1 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.1 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (0 : Fin (4 : ℕ))) =
                            BandVectors.2 (rotatedTuple (2 : Fin (4 : ℕ)))
                            (rotatedTuple (1 : Fin (4 : ℕ))) +
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) ∧
                            BandVectors.2 (rotatedTuple (0 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) =
                            BandVectors.2 (rotatedTuple (1 : Fin (4 : ℕ)))
                            (rotatedTuple (3 : Fin (4 : ℕ))) -
                            ⟨(0 : ℤ), (1 : ℤ)⟩ *
                            BandVectors.2 (rotatedTuple (3 : Fin (4 : ℕ)))
                            (rotatedTuple (2 : Fin (4 : ℕ))) →
                          BandVectors.2 ((FordRecursiveQuadruple Q) 3)
                            ((FordRecursiveQuadruple Q) 2) =
                            -(Q.p₂ : GaussianInt) := by
  classical
  intro Q hgtq pd qd q1pos' hqdpos hd1 hd2 hred hq2gt R ra32 ra13 rotatedTuple direct
  have hx := direct.2.2.1
  have ra32' : BandVectors.2 (rotatedTuple 2) (rotatedTuple 1) =
      -(pd : GaussianInt) := by
    simpa [rotatedTuple, FordRecursiveQuadruple, R, q1pos'.ne'] using ra32
  have ra13' : BandVectors.2 (rotatedTuple 3) (rotatedTuple 2) =
      (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt) := by
    simpa [rotatedTuple, FordRecursiveQuadruple, R, q1pos'.ne'] using ra13
  rw [ra32', ra13'] at hx
  simp only [FordRecursiveQuadruple, q1pos'.ne', ↓reduceIte, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val, Matrix.cons_val_one, Int.reduceNeg, rotatedTuple,
      R] at hx
  calc
    BandVectors.2 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) =
        -(((Q.p₂ - Q.p₁ : Int) : GaussianInt)) +
          (⟨0, 1⟩ : GaussianInt) *
            ((⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt)) := hx
    _ = -(Q.p₂ : GaussianInt) := by
      ext <;> simp; ring

private theorem circleExists :
    ∀ (P : FordFareyParameter), (∀ n : Nat, ∀ Q : FordFareyParameter, Q.q = n → 1 < Q.q →
        SemiProperQuadruple (FordRecursiveQuadruple Q) ∧ BandVectors.1 ((FordRecursiveQuadruple
        Q) 3) ((FordRecursiveQuadruple Q) 2) = -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)) ∧
        BandVectors.1 ((FordRecursiveQuadruple Q) 1) ((FordRecursiveQuadruple Q) 3) = (Q.q₁ :
        GaussianInt) ∧ BandVectors.2 ((FordRecursiveQuadruple Q) 3) ((FordRecursiveQuadruple Q)
        2) = -(Q.p₂ : GaussianInt) ∧ BandVectors.2 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) = (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt)) → (∃ C :
        BandCircle, C.1.1 = FordCircleCoordinate P.p P.q) := by
  classical
  intro P claim
  by_cases hu : P.q = 1
  · have hp1 : P.q₁ = 0 := by
      have h := P.q₁_lt
      omega
    let z : GaussianInt := ⟨0, P.p - 1⟩
    have hs : SemiProperQuadruple
        ![(1, 1 + 2 * z), (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)),
          (0, 1), (0, -1)] := SemiProperQuadruple.base z
    have hc : FordCircleCoordinate P.p 1 =
        (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)) := by
      dsimp [FordCircleCoordinate, z]
      ext <;> simp; ring
    refine ⟨⟨⟨FordCircleCoordinate P.p P.q, ?_⟩, ?_⟩, rfl⟩
    · refine ⟨Or.inl (by
          change (0 : Int) < (P.q : Int) * P.q
          exact_mod_cast Nat.mul_pos P.q_pos P.q_pos), ?_⟩
      refine ⟨![((1, 1 + 2 * z)),
          (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)), (0, 1), (0, -1)],
          hs, 1, ?_⟩
      simp [hu, hc]
    · change (0 : Int) < (P.q : Int) * P.q
      exact_mod_cast Nat.mul_pos P.q_pos P.q_pos
  · have hgt : 1 < P.q := by
      have hpq : 1 ≤ P.q := P.q_pos
      omega
    have hs := claim P.q P rfl hgt
    refine ⟨⟨⟨FordCircleCoordinate P.p P.q, ?_⟩, ?_⟩, rfl⟩
    · refine ⟨Or.inl (by
          change (0 : Int) < (P.q : Int) * P.q
          exact_mod_cast Nat.mul_pos P.q_pos P.q_pos), ?_⟩
      refine ⟨FordRecursiveQuadruple P, hs.1, 0, ?_⟩
      simp [FordRecursiveQuadruple, FordCircleCoordinate]
    · change (0 : Int) < (P.q : Int) * P.q
      exact_mod_cast Nat.mul_pos P.q_pos P.q_pos

private theorem hproper :
    ∀ (P : FordFareyParameter), (0 < P.q₁) → ((P.q₂ < P.q) → ((SemiProperQuadruple
        (FordRecursiveQuadruple P) ∧ BandVectors.1 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.q₂ :
        GaussianInt)) ∧ BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = (↑P.q₁ : GaussianInt) ∧ BandVectors.2
        (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
        = -(↑P.p₂ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.p₁ :
        GaussianInt)) → (ProperBandQuadruple (FordRecursiveQuadruple P)))) := by
  classical
  intro P hq1pos hq2lt hs
  refine ⟨hs.1, ?_⟩
  intro j
  fin_cases j
  · simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      hq1pos.ne', ↓reduceIte, Fin.zero_eta, Fin.isValue, Fin.succ_zero_eq_one,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    change (P.q₁ : Int) * P.q₁ < (P.q : Int) * P.q
    exact_mod_cast Nat.mul_self_lt_mul_self P.q₁_lt
  · simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      Fin.mk_one, Fin.isValue, Fin.succ_one_eq_two, Matrix.cons_val, Matrix.cons_val_zero]
    change (P.q₂ : Int) * P.q₂ < (P.q : Int) * P.q
    exact_mod_cast Nat.mul_self_lt_mul_self hq2lt
  · simp only [FordRecursiveQuadruple, FordCircleCoordinate, Nat.cast_mul, Int.reduceNeg,
      Fin.reduceFinMk, Fin.reduceSucc, Matrix.cons_val, Fin.isValue, Matrix.cons_val_zero,
      mul_self_pos, ne_eq, Int.natCast_eq_zero]
    exact Nat.ne_of_gt P.q_pos

end FordConfigurationProof

namespace FordConfigurationDetails

private theorem q1pos :
    ∀ (n : ℕ), ∀ (Q : FordFareyParameter), (Q.q = n) → (((1 : ℕ) < Q.q) → (0 < Q.q₁)) := by
  classical
  intro n Q hQ hgt
  by_contra h
  have hz : Q.q₁ = 0 := by omega
  have hd := Q.det₁
  simp [hz] at hd
  have hdv : (Q.q : Int) ∣ 1 := ⟨Q.p₁, by simpa [mul_comm] using hd.symm⟩
  have hqone : (Q.q : Int) = 1 :=
    Int.eq_one_of_dvd_one (by omega) hdv
  omega

private theorem q2lt :
    ∀ (n : ℕ), ∀ (Q : FordFareyParameter), (Q.q = n) → ((0 < Q.q₁) → (Q.q₂ < Q.q)) := by
  classical
  intro n Q hQ q1pos
  have hsum := Q.sum_q
  omega

private abbrev cross :=
  FordFareySum.determinant

private theorem qone :
    ∀ (Q : FordFareyParameter), (0 < Q.q₁) → ((Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1) →
        ((Q.q₁ = Q.q₂) → (Q.q₁ = 1))) := by
  classical
  intro Q q1pos cross heq
  have hc := cross
  rw [heq] at hc
  have hm : (Q.q₁ : Int) * (Q.p₁ - Q.p₂) = 1 := by
    nlinarith [hc]
  have hd : (Q.q₁ : Int) ∣ 1 := ⟨Q.p₁ - Q.p₂, hm.symm⟩
  have hu : (Q.q₁ : Int) = 1 :=
    Int.eq_one_of_dvd_one (by exact_mod_cast (Nat.zero_le Q.q₁)) hd
  exact_mod_cast hu

private theorem hp :
    ∀ (Q : FordFareyParameter), (0 < Q.q₁) → ((Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1) →
        ((Q.q₁ = Q.q₂) → (Q.p₁ = Q.p₂ + 1))) := by
  classical
  intro Q q1pos cross heq
  have hc := cross
  rw [heq] at hc
  have hm : (Q.q₁ : Int) * (Q.p₁ - Q.p₂) = 1 := by nlinarith [hc]
  have hu : (Q.q₁ : Int) = 1 := by
    have hd : (Q.q₁ : Int) ∣ 1 := ⟨Q.p₁ - Q.p₂, hm.symm⟩
    exact Int.eq_one_of_dvd_one
      (by exact_mod_cast (Nat.zero_le Q.q₁)) hd
  nlinarith [hu]

private theorem hq :
    ∀ (n : ℕ), ∀ (Q : FordFareyParameter), (Q.q = n) → ((Q.q₁ = Q.q₂) → ((Q.q₁ = 1) → (Q.q = 2)))
        := by
  classical
  intro n Q hQ heq qone
  have hsum := Q.sum_q
  omega

private theorem coord1 :
    ∀ (Q : FordFareyParameter),
    let z : GaussianInt := ⟨0, Q.p₂⟩
    FordCircleCoordinate (Q.p₂ + 1) 1 =
      (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt)) := by
  classical
  intro Q z
  dsimp [FordCircleCoordinate, z]
  ext <;> simp; ring

private theorem coord2 :
    ∀ (Q : FordFareyParameter), FordCircleCoordinate Q.p₂ 1 =
      (1, 1 + 2 * (⟨0, Q.p₂ - 1⟩ : GaussianInt) +
        2 * (⟨0, 1⟩ : GaussianInt)) := by
  classical
  intro Q
  dsimp [FordCircleCoordinate]
  apply Prod.ext
  · simp
  · ext <;> simp; ring

private theorem hv13At868 :
    ∀ (Q : FordFareyParameter), (Q.q₁ = 1) → ((Q.q₂ = 1) → ((Q.p₁ = Q.p₂ + 1) → ((Q.q = 2) → (
    let z : GaussianInt := ⟨0, Q.p₂⟩
    (FordCircleCoordinate (Q.p₂ + 1) 1 = (1, 1 + 2 * z + 2 * (⟨0, 1⟩ : GaussianInt))) →
        ((BandVectors.1 ((0 : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (0 :
        GaussianInt) ∧ BandVectors.1 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) +
        (2 : GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) ∧
        BandVectors.1 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 : GaussianInt) *
        ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 : ℤ), (-1 : GaussianInt)) = (1 : GaussianInt) ∧ BandVectors.2 ((0
        : ℤ), (-1 : GaussianInt)) ((0 : ℤ), (1 : GaussianInt)) = (1 : GaussianInt) ∧
        BandVectors.2 ((0 : ℤ), (1 : GaussianInt)) ((1 : ℤ), (1 : GaussianInt) + (2 :
        GaussianInt) * z + (2 : GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) = (-1 : GaussianInt) - z - ⟨(0
        : ℤ), (1 : ℤ)⟩ ∧ BandVectors.2 ((1 : ℤ), (1 : GaussianInt) + (2 : GaussianInt) * z + (2 :
        GaussianInt) * ⟨(0 : ℤ), (1 : ℤ)⟩) ((0 : ℤ), (-1 : GaussianInt)) = z + ⟨(0 : ℤ), (1 :
        ℤ)⟩) → (BandVectors.1 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) = (Q.q₁ : GaussianInt))))))) := by
  classical
  intro Q qone hqone hp hq z coord1 b1
  simpa [FordRecursiveQuadruple, qone, hqone, hp, hq, Q.sum_p,
    Q.sum_q, z, coord1] using b1.2.2.1

private theorem hd1At883 :
    ∀ (Q : FordFareyParameter),
      Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1 →
        Q.q₁ > Q.q₂ →
          let pd : Int := Q.p₁ - Q.p₂
          let qd : Nat := Q.q₁ - Q.q₂
          pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1 := by
  classical
  intro Q cross hgtq pd qd
  dsimp [pd, qd]
  rw [Nat.cast_sub (by omega)]
  nlinarith [cross]

private theorem hq1ltN :
    ∀ (n : ℕ), ∀ (Q : FordFareyParameter), (Q.q = n) → (Q.q₁ < n) := by
  classical
  intro n Q hQ
  have hlt := Q.q₁_lt
  omega

private theorem hv32At908 :
    (∀ (Q : FordFareyParameter), ∀ (q1pos : 0 < Q.q₁), ∀ (hgtq : Q.q₁ > Q.q₂), let pd : Int
        := Q.p₁ - Q.p₂;
    let qd : Nat := Q.q₁ - Q.q₂;
    ∀ (hqdlt : qd < Q.q₁), ∀ (hd1 : pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1), ∀ (hd2 : Q.p₂ *
        (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1), ∀ (hred : Nat.Coprime Q.q₁ Q.p₁.natAbs), ∀
            (hq1gt : 1 < Q.q₁), let R : FordFareyParameter := {
      p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred,
      p₁ := pd, q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂,
      sum_p := by dsimp [pd]; ring,
      sum_q := by dsimp [qd]; omega,
      det₁ := hd1, det₂ := hd2, q₁_lt := hqdlt,
      q₂_pos := Q.q₂_pos,
      unit_case := by intro hu; omega };
    (BandVectors.1 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple R (2 :
        Fin (4 : ℕ))) = -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.q₂ : GaussianInt))) → (BandVectors.1
        ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) =
        -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)))) := by
  classical
  intro Q q1pos hgtq pd qd hqdlt hd1 hd2 hred hq1gt R rv32
  simpa [FordRecursiveQuadruple, R] using rv32

private theorem ha32At914 :
    (∀ (Q : FordFareyParameter), ∀ (q1pos : 0 < Q.q₁), ∀ (hgtq : Q.q₁ > Q.q₂), let pd : Int
        := Q.p₁ - Q.p₂;
    let qd : Nat := Q.q₁ - Q.q₂;
    ∀ (hqdlt : qd < Q.q₁), ∀ (hd1 : pd * (Q.q₁ : Int) - (qd : Int) * Q.p₁ = 1), ∀ (hd2 : Q.p₂ *
        (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1), ∀ (hred : Nat.Coprime Q.q₁ Q.p₁.natAbs), ∀
            (hq1gt : 1 < Q.q₁), let R : FordFareyParameter := {
      p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred,
      p₁ := pd, q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂,
      sum_p := by dsimp [pd]; ring,
      sum_q := by dsimp [qd]; omega,
      det₁ := hd1, det₂ := hd2, q₁_lt := hqdlt,
      q₂_pos := Q.q₂_pos,
      unit_case := by intro hu; omega };
    (BandVectors.2 (FordRecursiveQuadruple R (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple R (2 :
        Fin (4 : ℕ))) = -(↑R.p₂ : GaussianInt)) → (BandVectors.2 ((FordRecursiveQuadruple Q) 3)
        ((FordRecursiveQuadruple Q) 2) = -(Q.p₂ : GaussianInt))) := by
  classical
  intro Q q1pos hgtq pd qd hqdlt hd1 hd2 hred hq1gt R ra32
  simpa [FordRecursiveQuadruple, R] using ra32

private theorem hd2At925 :
    ∀ (Q : FordFareyParameter),
      Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1 →
        ¬Q.q₁ > Q.q₂ →
          let pd : Int := Q.p₂ - Q.p₁
          let qd : Nat := Q.q₂ - Q.q₁
          pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1 := by
  classical
  intro Q cross hgtq pd qd
  dsimp [pd, qd]
  rw [Nat.cast_sub (by omega)]
  nlinarith [cross]

private theorem hredAt929 :
    ∀ (Q : FordFareyParameter), (∀ (a : ℤ), ∀ (b : ℕ), ∀ (d : ℕ), ∀ (c : ℤ), a * (↑d : ℤ) - (↑b :
        ℤ) * c = (1 : ℤ) → b.Coprime a.natAbs) → (
    let pd : Int := Q.p₂ - Q.p₁
    let qd : Nat := Q.q₂ - Q.q₁
    (pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1) → (Nat.Coprime Q.q₂ Q.p₂.natAbs)) := by
  classical
  intro Q determinantCoprime pd qd hd2
  have hh : Q.p₂ * (qd : Int) - (Q.q₂ : Int) * pd = 1 := by
    calc
      Q.p₂ * (qd : Int) - (Q.q₂ : Int) * pd =
          -(pd * (Q.q₂ : Int) - (qd : Int) * Q.p₂) := by ring
      _ = 1 := by rw [hd2]; norm_num
  simpa [Int.natAbs_neg] using
    (determinantCoprime Q.p₂ Q.q₂ qd pd hh)

private theorem hq2ltN :
    ∀ (n : ℕ), ∀ (Q : FordFareyParameter), (Q.q = n) → ((Q.q₂ < Q.q) → (Q.q₂ < n)) := by
  classical
  intro n Q hQ q2lt
  omega

private theorem hv13At961 :
    (∀ (Q : FordFareyParameter), ∀ (hgtq : ¬Q.q₁ > Q.q₂), let pd : Int := Q.p₂ - Q.p₁;
    let qd : Nat := Q.q₂ - Q.q₁;
    ∀ (hqdpos : 0 < qd), ∀ (hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1), ∀ (hd2 : pd *
        (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1), ∀ (hred : Nat.Coprime Q.q₂ Q.p₂.natAbs), ∀ (hq2gt
            : 1 < Q.q₂), let R : FordFareyParameter := {
      p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
      p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
      sum_p := by dsimp [pd]; ring,
      sum_q := by dsimp [qd]; omega,
      det₁ := hd1, det₂ := hd2, q₁_lt := by omega,
      q₂_pos := hqdpos,
      unit_case := by intro hu; omega };
    (BandVectors.1 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple R (3 :
        Fin (4 : ℕ))) = (↑R.q₁ : GaussianInt)) → (BandVectors.1 ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) = (Q.q₁ : GaussianInt))) := by
  classical
  intro Q hgtq pd qd hqdpos hd1 hd2 hred hq2gt R rv13
  simpa [FordRecursiveQuadruple, R] using rv13

private theorem ha13At966 :
    (∀ (Q : FordFareyParameter), ∀ (hgtq : ¬Q.q₁ > Q.q₂), let pd : Int := Q.p₂ - Q.p₁;
    let qd : Nat := Q.q₂ - Q.q₁;
    ∀ (hqdpos : 0 < qd), ∀ (hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1), ∀ (hd2 : pd *
        (Q.q₂ : Int) - (qd : Int) * Q.p₂ = -1), ∀ (hred : Nat.Coprime Q.q₂ Q.p₂.natAbs), ∀ (hq2gt
            : 1 < Q.q₂), let R : FordFareyParameter := {
      p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
      p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
      sum_p := by dsimp [pd]; ring,
      sum_q := by dsimp [qd]; omega,
      det₁ := hd1, det₂ := hd2, q₁_lt := by omega,
      q₂_pos := hqdpos,
      unit_case := by intro hu; omega };
    (BandVectors.2 (FordRecursiveQuadruple R (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple R (3 :
        Fin (4 : ℕ))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑R.p₁ : GaussianInt)) → (BandVectors.2
        ((FordRecursiveQuadruple Q) 1)
        ((FordRecursiveQuadruple Q) 3) =
        (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt))) := by
  classical
  intro Q hgtq pd qd hqdpos hd1 hd2 hred hq2gt R ra13
  simpa [FordRecursiveQuadruple, R] using ra13

private theorem hq1pos :
    ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (0 < P.q₁) := by
  classical
  intro P hgt
  by_contra hz
  have hz' : P.q₁ = 0 := by omega
  have hd := P.det₁
  simp [hz'] at hd
  have hdv : (P.q : Int) ∣ 1 := ⟨P.p₁, by simpa [mul_comm] using hd.symm⟩
  have : (P.q : Int) = 1 := Int.eq_one_of_dvd_one (by omega) hdv
  omega

private theorem hq2lt :
    ∀ (P : FordFareyParameter), (0 < P.q₁) → (P.q₂ < P.q) := by
  classical
  intro P hq1pos
  have hsum := P.sum_q
  omega

private theorem v21 :
    ∀ (P : FordFareyParameter), (SemiProperQuadruple (FordRecursiveQuadruple P) ∧ BandVectors.1
        (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
        = -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.q₂ : GaussianInt)) ∧ BandVectors.1 (FordRecursiveQuadruple P
        (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = (↑P.q₁ : GaussianInt) ∧
        BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))) = -(↑P.p₂ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple P (1 : Fin
        (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.p₁ :
        GaussianInt)) → ((BandVectors.1 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) + BandVectors.1 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + BandVectors.1
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        = (0 : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) + BandVectors.2 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + BandVectors.2
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        = (0 : GaussianInt) ∧ BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = BandVectors.1 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = BandVectors.2 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))) ∧ (ProperBandQuadruple (FordRecursiveQuadruple P) → ∀ (j : Fin (3 : ℕ)),
        BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P
        j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (FordRecursiveQuadruple P j.succ)
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (0
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) →
        (BandVectors.1 ((FordRecursiveQuadruple P) 2)
        ((FordRecursiveQuadruple P) 1) =
        -((P.q₁ : GaussianInt)) +
          (⟨0, 1⟩ : GaussianInt) * (P.q₂ : GaussianInt))) := by
  classical
  intro P hs laws
  have h := laws.1
  have hh := eq_neg_of_add_eq_zero_right h
  rw [hs.2.1, hs.2.2.1] at hh
  rw [neg_add, neg_neg] at hh
  simpa [add_comm] using hh

private theorem hv20' :
    ∀ (P : FordFareyParameter), (BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple
        P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P
        (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) =
        BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ)))) → (BandVectors.1
        ((FordRecursiveQuadruple P) 2)
        ((FordRecursiveQuadruple P) 0) =
        BandVectors.1 ((FordRecursiveQuadruple P) 2)
          ((FordRecursiveQuadruple P) 1) -
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 ((FordRecursiveQuadruple P) 3)
              ((FordRecursiveQuadruple P) 2)) := by
  classical
  intro P hv20
  simpa using hv20

private theorem hv30' :
    ∀ (P : FordFareyParameter), (BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple
        P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P
        (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) =
        BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ)))) → (BandVectors.1
        ((FordRecursiveQuadruple P) 3)
        ((FordRecursiveQuadruple P) 0) =
        BandVectors.1 ((FordRecursiveQuadruple P) 3)
          ((FordRecursiveQuadruple P) 2) -
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.1 ((FordRecursiveQuadruple P) 1)
              ((FordRecursiveQuadruple P) 3)) := by
  classical
  intro P hv30
  simpa using hv30

private theorem a21 :
    ∀ (P : FordFareyParameter), (SemiProperQuadruple (FordRecursiveQuadruple P) ∧ BandVectors.1
        (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 : Fin (4 : ℕ)))
        = -(⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.q₂ : GaussianInt)) ∧ BandVectors.1 (FordRecursiveQuadruple P
        (1 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = (↑P.q₁ : GaussianInt) ∧
        BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))) = -(↑P.p₂ : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple P (1 : Fin
        (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) = ⟨(0 : ℤ), (1 : ℤ)⟩ * (↑P.p₁ :
        GaussianInt)) → ((BandVectors.1 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) + BandVectors.1 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + BandVectors.1
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        = (0 : GaussianInt) ∧ BandVectors.2 (FordRecursiveQuadruple P (3 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) + BandVectors.2 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + BandVectors.2
        (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        = (0 : GaussianInt) ∧ BandVectors.1 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = BandVectors.1 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) - ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.1 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (1 : Fin (4 : ℕ)))
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) = BandVectors.2 (FordRecursiveQuadruple P (1
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (FordRecursiveQuadruple P (2 : Fin (4 : ℕ))) (FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))) ∧ (ProperBandQuadruple (FordRecursiveQuadruple P) → ∀ (j : Fin (3 : ℕ)),
        BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P
        j.succ) = ⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.1 (FordRecursiveQuadruple P j.succ)
        (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (FordRecursiveQuadruple P (0
        : Fin (4 : ℕ))) (FordRecursiveQuadruple P j.succ) = -⟨(0 : ℤ), (1 : ℤ)⟩ * BandVectors.2
        (FordRecursiveQuadruple P j.succ) (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))))) →
        (BandVectors.2 ((FordRecursiveQuadruple P) 2)
        ((FordRecursiveQuadruple P) 1) =
        (P.p₂ : GaussianInt) -
          (⟨0, 1⟩ : GaussianInt) * (P.p₁ : GaussianInt))) := by
  classical
  intro P hs laws
  have h := laws.2.1
  have hh := eq_neg_of_add_eq_zero_right h
  rw [hs.2.2.2.1, hs.2.2.2.2] at hh
  rw [hh]
  abel

private theorem ha20' :
    ∀ (P : FordFareyParameter), (BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple
        P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P
        (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) =
        BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 :
        Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (1 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ)))) → (BandVectors.2
        ((FordRecursiveQuadruple P) 2)
        ((FordRecursiveQuadruple P) 0) =
        BandVectors.2 ((FordRecursiveQuadruple P) 2)
          ((FordRecursiveQuadruple P) 1) +
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 ((FordRecursiveQuadruple P) 3)
              ((FordRecursiveQuadruple P) 2)) := by
  classical
  intro P ha20
  simpa using ha20

private theorem ha30' :
    ∀ (P : FordFareyParameter), (BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple
        P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P
        (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (0 : Fin (4 : ℕ))) =
        BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))] (1 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (3 : Fin (4 : ℕ))) + ⟨(0 : ℤ), (1 : ℤ)⟩ *
        BandVectors.2 (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)), FordRecursiveQuadruple P (3
        : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)), FordRecursiveQuadruple P (2 :
        Fin (4 : ℕ))] (2 : Fin (4 : ℕ))) (![FordRecursiveQuadruple P (0 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (3 : Fin (4 : ℕ)), FordRecursiveQuadruple P (1 : Fin (4 : ℕ)),
        FordRecursiveQuadruple P (2 : Fin (4 : ℕ))] (1 : Fin (4 : ℕ)))) → (BandVectors.2
        ((FordRecursiveQuadruple P) 3)
        ((FordRecursiveQuadruple P) 0) =
        BandVectors.2 ((FordRecursiveQuadruple P) 3)
          ((FordRecursiveQuadruple P) 2) +
          (⟨0, 1⟩ : GaussianInt) *
            BandVectors.2 ((FordRecursiveQuadruple P) 1)
              ((FordRecursiveQuadruple P) 3)) := by
  classical
  intro P ha30
  simpa using ha30

end FordConfigurationDetails

theorem FordCoordinateConfiguration (P : FordFareyParameter) :
    (∃ C : BandCircle, C.1.1 = FordCircleCoordinate P.p P.q) ∧
    (1 < P.q →
      ProperBandQuadruple (FordRecursiveQuadruple P) ∧
      BandVectors.1 ((FordRecursiveQuadruple P) 1)
          ((FordRecursiveQuadruple P) 0) =
        ⟨(P.q : Int), (P.q₁ : Int)⟩ ∧
      BandVectors.1 ((FordRecursiveQuadruple P) 2)
          ((FordRecursiveQuadruple P) 0) =
        ⟨-(P.q : Int), (P.q₂ : Int)⟩ ∧
      BandVectors.1 ((FordRecursiveQuadruple P) 3)
          ((FordRecursiveQuadruple P) 0) =
        ⟨0, -(P.q : Int)⟩ ∧
      BandVectors.2 ((FordRecursiveQuadruple P) 1)
          ((FordRecursiveQuadruple P) 0) =
        ⟨P.p₁, P.p⟩ ∧
      BandVectors.2 ((FordRecursiveQuadruple P) 2)
          ((FordRecursiveQuadruple P) 0) =
        ⟨P.p₂, -P.p⟩ ∧
      BandVectors.2 ((FordRecursiveQuadruple P) 3)
          ((FordRecursiveQuadruple P) 0) =
        ⟨-P.p, 0⟩ ∧
      BandVectors.2 ((FordRecursiveQuadruple P) 3)
          ((FordRecursiveQuadruple P) 2) =
        ⟨-P.p₂, 0⟩ ∧
      BandVectors.2 ((FordRecursiveQuadruple P) 1)
          ((FordRecursiveQuadruple P) 3) =
        ⟨0, P.p₁⟩) := by
-- BODY
  have claim : ∀ n : Nat, ∀ Q : FordFareyParameter, Q.q = n →
      1 < Q.q → SemiProperQuadruple (FordRecursiveQuadruple Q) ∧
        BandVectors.1 ((FordRecursiveQuadruple Q) 3)
            ((FordRecursiveQuadruple Q) 2) =
          -((⟨0, 1⟩ : GaussianInt) * (Q.q₂ : GaussianInt)) ∧
        BandVectors.1 ((FordRecursiveQuadruple Q) 1)
            ((FordRecursiveQuadruple Q) 3) = (Q.q₁ : GaussianInt) ∧
        BandVectors.2 ((FordRecursiveQuadruple Q) 3)
            ((FordRecursiveQuadruple Q) 2) = -(Q.p₂ : GaussianInt) ∧
        BandVectors.2 ((FordRecursiveQuadruple Q) 1)
            ((FordRecursiveQuadruple Q) 3) =
          (⟨0, 1⟩ : GaussianInt) * (Q.p₁ : GaussianInt) := by
    have systemLaw : RecursiveVectorSystem BandVectors :=
      by simpa [BandVectors] using (Classical.choose_spec RecursiveVectorsExistUnique).1
    rcases systemLaw with ⟨zeroLaw, baseLaw, stepLaw, flipLaw⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Q hQ hgt
      have q1pos := FordConfigurationDetails.q1pos n Q hQ hgt
      have q2lt := FordConfigurationDetails.q2lt n Q hQ q1pos
      have cross := FordConfigurationDetails.cross Q
      have determinantCoprime := FordConfigurationProof.determinantCoprime
      by_cases heq : Q.q₁ = Q.q₂
      · have qone : Q.q₁ = 1 := FordConfigurationDetails.qone Q q1pos cross heq
        have hqone : Q.q₂ = 1 := by omega
        have hp := FordConfigurationDetails.hp Q q1pos cross heq
        have hq := FordConfigurationDetails.hq n Q hQ heq qone
        let z : GaussianInt := ⟨0, Q.p₂⟩
        have hb := SemiProperQuadruple.base z
        have hr := SemiProperQuadruple.rotate hb
        have hs := SemiProperQuadruple.successor hr
        have ht := SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hs)
        have coord1 := FordConfigurationDetails.coord1 Q
        have coord2 := FordConfigurationDetails.coord2 Q
        have hsemi : SemiProperQuadruple (FordRecursiveQuadruple Q) := by
          convert ht using 1;
            simp only [FordRecursiveQuadruple, FordCircleCoordinate, hq, Nat.reduceMul,
                Nat.cast_ofNat, Int.reduceNeg, Q.sum_p, hp, qone, one_ne_zero, ↓reduceIte,
                mul_one, Nat.cast_one, hqone, Fin.isValue, Matrix.cons_val_zero,
                Matrix.cons_val, Matrix.cons_val_one, mul_zero, add_zero, Int.reduceAdd,
                sub_zero, mul_neg, Matrix.vecCons_inj, Prod.mk.injEq, true_and, and_true, z]
          constructor
          · ext <;> simp; ring
          constructor
          · ext <;> simp; ring
          · ext <;> simp
        have b1 := baseLaw z
        simp only [Int.reduceNeg, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
            Matrix.cons_val_zero] at b1
        have b2 := baseLaw ⟨0, Q.p₂ - 1⟩
        simp only [Int.reduceNeg, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
            Matrix.cons_val_zero, Zsqrtd.add_def, add_zero, sub_add_cancel] at b2
        have f1 := flipLaw _ _ (PrimitiveVectorOrientation.base31 ⟨0, Q.p₂ - 1⟩)
        have hv13 := FordConfigurationDetails.hv13At868 Q qone hqone hp hq coord1 b1
        have hv32 := FordConfigurationProof.hv32At253 Q qone hqone hp hq coord2 b2 f1
        have ha13 := FordConfigurationProof.ha13At278 Q
                  qone hqone hp hq coord1 b1
        have ha32 := FordConfigurationProof.ha32At288 Q qone hqone hp hq coord2 b2 f1
        exact ⟨hsemi, hv32, hv13, ha32, ha13⟩
      · by_cases hgtq : Q.q₁ > Q.q₂
        · let pd : Int := Q.p₁ - Q.p₂
          let qd : Nat := Q.q₁ - Q.q₂
          have q2pos : 0 < Q.q₂ := Q.q₂_pos
          have hqdpos : 0 < qd := by dsimp [qd]; omega
          have hqdlt : qd < Q.q₁ := by dsimp [qd]; omega
          have hd1 := FordConfigurationDetails.hd1At883 Q cross hgtq
          have hd2 : Q.p₂ * (Q.q₁ : Int) - (Q.q₂ : Int) * Q.p₁ = -1 := by
            nlinarith [cross]
          have hred : Nat.Coprime Q.q₁ Q.p₁.natAbs :=
            determinantCoprime Q.p₁ Q.q₁ Q.q₂ Q.p₂ cross
          have hq1gt : 1 < Q.q₁ := by omega
          have hq1ltN := FordConfigurationDetails.hq1ltN n Q hQ
          let R : FordFareyParameter := {
            p := Q.p₁, q := Q.q₁, q_pos := q1pos, reduced := hred,
            p₁ := pd, q₁ := qd, p₂ := Q.p₂, q₂ := Q.q₂,
            sum_p := by dsimp [pd]; ring,
            sum_q := by dsimp [qd]; omega,
            det₁ := hd1, det₂ := hd2, q₁_lt := hqdlt,
            q₂_pos := Q.q₂_pos,
            unit_case := by intro hu; omega }
          have hrec := ih Q.q₁ hq1ltN R (by simp [R]) (by simpa [R] using hq1gt)
          rcases hrec with ⟨rsemi, rv32, rv13, ra32, ra13⟩
          have hsucc := SemiProperQuadruple.successor rsemi
          have hsemi := FordConfigurationProof.hsemiAt342 Q q1pos hgtq hqdpos hqdlt hd1 hd2
              hred hq1gt hsucc
          have direct := stepLaw (FordRecursiveQuadruple R) rsemi
          have hv32 := FordConfigurationDetails.hv32At908 Q q1pos hgtq hqdlt hd1 hd2 hred hq1gt
              rv32
          have hv13 := FordConfigurationProof.hv13At359 Q q1pos hgtq hqdlt hd1 hd2 hred hq1gt rv32
                    rv13 direct
          have ha32 := FordConfigurationDetails.ha32At914 Q q1pos hgtq hqdlt hd1 hd2 hred hq1gt
              ra32
          have ha13 := FordConfigurationProof.ha13At390 Q q1pos hgtq hqdlt hd1 hd2 hred hq1gt
              ra32 ra13 direct
          exact ⟨hsemi, hv32, hv13, ha32, ha13⟩
        · let pd : Int := Q.p₂ - Q.p₁
          let qd : Nat := Q.q₂ - Q.q₁
          have q1pos' : 0 < Q.q₁ := q1pos
          have hqdpos : 0 < qd := by dsimp [qd]; omega
          have hd1 : Q.p₁ * (Q.q₂ : Int) - (Q.q₁ : Int) * Q.p₂ = 1 := cross
          have hd2 := FordConfigurationDetails.hd2At925 Q cross hgtq
          have hred := FordConfigurationDetails.hredAt929 Q
              determinantCoprime hd2
          have hq2gt : 1 < Q.q₂ := by omega
          have hq2ltN := FordConfigurationDetails.hq2ltN n Q hQ q2lt
          let R : FordFareyParameter := {
            p := Q.p₂, q := Q.q₂, q_pos := Q.q₂_pos, reduced := hred,
            p₁ := Q.p₁, q₁ := Q.q₁, p₂ := pd, q₂ := qd,
            sum_p := by dsimp [pd]; ring,
            sum_q := by dsimp [qd]; omega,
            det₁ := hd1, det₂ := hd2, q₁_lt := by omega,
            q₂_pos := hqdpos,
            unit_case := by intro hu; omega }
          have hrec := ih Q.q₂ hq2ltN R (by simp [R])
            (by simpa [R] using hq2gt)
          rcases hrec with ⟨rsemi, rv32, rv13, ra32, ra13⟩
          let rotatedTuple : Fin 4 → CircleCoordinates :=
            ![FordRecursiveQuadruple R 0, FordRecursiveQuadruple R 2,
              FordRecursiveQuadruple R 3, FordRecursiveQuadruple R 1]
          have trot : SemiProperQuadruple rotatedTuple := by
            simpa [rotatedTuple] using SemiProperQuadruple.rotate rsemi
          have hsucc := SemiProperQuadruple.successor trot
          have hfinal := SemiProperQuadruple.rotate (SemiProperQuadruple.rotate hsucc)
          have hsemi := FordConfigurationProof.hsemiAt448 Q hgtq q1pos' hqdpos hd1 hd2 hred
              hq2gt hfinal
          have direct := stepLaw _ trot
          have hv13 := FordConfigurationDetails.hv13At961 Q hgtq hqdpos hd1 hd2 hred hq2gt rv13
          have hv32 := FordConfigurationProof.hv32At473 Q hgtq q1pos' hqdpos hd1 hd2 hred hq2gt
                    rv32 rv13 direct
          have ha13 := FordConfigurationDetails.ha13At966 Q hgtq hqdpos hd1 hd2 hred hq2gt ra13
          have ha32 := FordConfigurationProof.ha32At503 Q hgtq q1pos' hqdpos hd1 hd2 hred hq2gt
                    ra32 ra13 direct
          exact ⟨hsemi, hv32, hv13, ha32, ha13⟩
  have circleExists := FordConfigurationProof.circleExists P claim
  refine ⟨circleExists, ?_⟩
  intro hgt
  have hq1pos := FordConfigurationDetails.hq1pos P hgt
  have hq2lt := FordConfigurationDetails.hq2lt P hq1pos
  have hs := claim P.q P rfl hgt
  have hproper := FordConfigurationProof.hproper
      P hq1pos hq2lt hs
  have laws := VectorRecursionLaws (FordRecursiveQuadruple P) hs.1
  have v21 := FordConfigurationDetails.v21 P hs laws
  have hv10 := laws.2.2.1
  have hv20 := (VectorRecursionLaws
      ![(FordRecursiveQuadruple P) 0, (FordRecursiveQuadruple P) 2,
        (FordRecursiveQuadruple P) 3, (FordRecursiveQuadruple P) 1] (by
          simpa using SemiProperQuadruple.rotate hs.1)).2.2.1
  have hv30 := (VectorRecursionLaws
      ![(FordRecursiveQuadruple P) 0, (FordRecursiveQuadruple P) 3,
        (FordRecursiveQuadruple P) 1, (FordRecursiveQuadruple P) 2] (by
          simpa using SemiProperQuadruple.rotate
            (SemiProperQuadruple.rotate hs.1))).2.2.1
  have hv20' := FordConfigurationDetails.hv20' P hv20
  have hv30' := FordConfigurationDetails.hv30' P hv30
  have a21 := FordConfigurationDetails.a21 P hs laws
  have ha10 := laws.2.2.2.1
  have ha20 := (VectorRecursionLaws
      ![(FordRecursiveQuadruple P) 0, (FordRecursiveQuadruple P) 2,
        (FordRecursiveQuadruple P) 3, (FordRecursiveQuadruple P) 1] (by
          simpa using SemiProperQuadruple.rotate hs.1)).2.2.2.1
  have ha30 := (VectorRecursionLaws
      ![(FordRecursiveQuadruple P) 0, (FordRecursiveQuadruple P) 3,
        (FordRecursiveQuadruple P) 1, (FordRecursiveQuadruple P) 2] (by
          simpa using SemiProperQuadruple.rotate
            (SemiProperQuadruple.rotate hs.1))).2.2.2.1
  have ha20' := FordConfigurationDetails.ha20' P ha20
  have ha30' := FordConfigurationDetails.ha30' P ha30
  refine ⟨hproper, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv10, hs.2.2.1, v21]
    have hi : (⟨0, 1⟩ : GaussianInt) * ⟨0, 1⟩ = -1 := by
      ext <;> norm_num
    ext <;>
      simp [P.sum_q, sub_eq_add_neg, mul_add];
  · rw [hv20', v21, hs.2.1]
    have hi : (⟨0, 1⟩ : GaussianInt) * ⟨0, 1⟩ = -1 := by
      ext <;> norm_num
    ext <;> simp [P.sum_q, sub_eq_add_neg];
      ring
  · rw [hv30', hs.2.1, hs.2.2.1]
    ext <;> simp [P.sum_q]; ring
  · rw [ha10, hs.2.2.2.2, a21]
    ext <;> simp [P.sum_p]
  · rw [ha20', a21, hs.2.2.2.1]
    ext <;> simp [P.sum_p]; ring
  · rw [ha30', hs.2.2.2.1, hs.2.2.2.2]
    ext <;> simp [P.sum_p]
  · rw [hs.2.2.2.1]
    ext <;> simp
  · rw [hs.2.2.2.2]
    ext <;> simp

end ApollonianSuperharmonic

end
