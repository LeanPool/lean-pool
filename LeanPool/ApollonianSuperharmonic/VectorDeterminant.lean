/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.VectorNonvanishing

-- [TABLET NODE: VectorDeterminant]

/-!
# VectorDeterminant

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem VectorDeterminant (q : Fin 4 → CircleCoordinates)
    (hq : SemiProperQuadruple q) (hc : 0 < (q 1).1) :
    star (BandVectors.1 (q 1) (q 3)) * BandVectors.1 (q 2) (q 1) +
        BandVectors.1 (q 1) (q 3) * star (BandVectors.1 (q 2) (q 1)) =
      (-2 * (q 1).1 : ℤ) ∧
    Int.natAbs
        ((BandVectors.1 (q 3) (q 1)).re *
          (BandVectors.1 (q 2) (q 1)).im -
        (BandVectors.1 (q 3) (q 1)).im *
          (BandVectors.1 (q 2) (q 1)).re) =
      (q 1).1.natAbs := by
-- BODY
  have hrec := (VectorRecursionLaws q hq).1
  have hsq13 := (VectorSquareProduct q hq 1 3 (by decide)).1
  have hsq21 := (VectorSquareProduct q hq 2 1 (by decide)).1
  have hsq32 := (VectorSquareProduct q hq 3 2 (by decide)).1
  have hnon13 := VectorNonvanishing q hq 1 3 (by decide) (Or.inl hc)
  have hnon21 := VectorNonvanishing q hq 2 1 (by decide) (Or.inr hc)
  have nonnegative : ∀ r : Fin 4 → CircleCoordinates,
      SemiProperQuadruple r → ∀ k : Fin 4, 0 ≤ (r k).1 := by
    intro r hr
    induction hr with
    | base z => intro k; fin_cases k <;> simp
    | rotate hr ih =>
        intro k
        fin_cases k
        · simpa using ih 0
        · simpa using ih 2
        · simpa using ih 3
        · simpa using ih 1
    | @successor r hr ih =>
        intro k
        have classification := BandSuccessorClassification r hr
        dsimp at classification
        rcases classification with special | proper
        · fin_cases k
          · simp [special]
          · simpa using ih 0
          · simpa using ih 2
          · simpa using ih 3
        · rcases proper with ⟨_, larger0, larger2, larger3⟩
          fin_cases k
          · change 0 ≤ 2 * (r 0).1 + 2 * (r 2).1 + 2 * (r 3).1 - (r 1).1
            exact (ih 0).trans larger0.le
          · exact ih 0
          · exact ih 2
          · exact ih 3
  have hcurv := nonnegative q hq
  have hnorm13sq : Zsqrtd.norm
      (BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 1) (q 3)) =
      ((q 1).1 + (q 3).1) ^ 2 := by
    rw [show BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 1) (q 3) =
        BandVectors.1 (q 1) (q 3) ^ 2 by ring, hsq13]
    exact TangencyCoordinateIdentity q hq 1 3 (by decide)
  have hnorm21sq : Zsqrtd.norm
      (BandVectors.1 (q 2) (q 1) * BandVectors.1 (q 2) (q 1)) =
      ((q 2).1 + (q 1).1) ^ 2 := by
    rw [show BandVectors.1 (q 2) (q 1) * BandVectors.1 (q 2) (q 1) =
        BandVectors.1 (q 2) (q 1) ^ 2 by ring, hsq21]
    exact TangencyCoordinateIdentity q hq 2 1 (by decide)
  have hnorm13 : Zsqrtd.norm (BandVectors.1 (q 1) (q 3)) =
      (q 1).1 + (q 3).1 := by
    have hs : (Zsqrtd.norm (BandVectors.1 (q 1) (q 3))) ^ 2 =
        ((q 1).1 + (q 3).1) ^ 2 := by
      simpa [pow_two, Zsqrtd.norm_mul] using hnorm13sq
    nlinarith [Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0)
      (BandVectors.1 (q 1) (q 3)), add_nonneg hc.le (hcurv 3)]
  have hnorm21 : Zsqrtd.norm (BandVectors.1 (q 2) (q 1)) =
      (q 2).1 + (q 1).1 := by
    have hs : (Zsqrtd.norm (BandVectors.1 (q 2) (q 1))) ^ 2 =
        ((q 2).1 + (q 1).1) ^ 2 := by
      simpa [pow_two, Zsqrtd.norm_mul] using hnorm21sq
    nlinarith [Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0)
      (BandVectors.1 (q 2) (q 1)), add_nonneg (hcurv 2) hc.le]
  have hnorm13mul :
      BandVectors.1 (q 1) (q 3) * star (BandVectors.1 (q 1) (q 3)) =
        ((q 1).1 + (q 3).1 : ℤ) := by
    have identity := Zsqrtd.norm_eq_mul_conj (BandVectors.1 (q 1) (q 3))
    rw [hnorm13] at identity
    exact identity.symm
  have hnorm21mul :
      BandVectors.1 (q 2) (q 1) * star (BandVectors.1 (q 2) (q 1)) =
        ((q 2).1 + (q 1).1 : ℤ) := by
    have identity := Zsqrtd.norm_eq_mul_conj (BandVectors.1 (q 2) (q 1))
    rw [hnorm21] at identity
    exact identity.symm
  have hmul : BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 2) (q 1) ≠ 0 := mul_ne_zero hnon13 hnon21
  have hcross :
      (BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 2) (q 1)) *
          (star (BandVectors.1 (q 1) (q 3)) * BandVectors.1 (q 2) (q 1) +
            BandVectors.1 (q 1) (q 3) * star (BandVectors.1 (q 2) (q 1))) =
        (-2 * (q 1).1 : ℤ) *
            (BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 2) (q 1)) := by
    have castidentity : ((-2 * (q 1).1 : ℤ) : GaussianInt) =
        (-2 : GaussianInt) * (q 1).1 := by
      norm_num [Int.cast_mul]
    rw [castidentity]
    calc
      _ = (BandVectors.1 (q 1) (q 3) * star (BandVectors.1 (q 1) (q 3))) *
            BandVectors.1 (q 2) (q 1) ^ 2 +
          BandVectors.1 (q 1) (q 3) ^ 2 *
            (BandVectors.1 (q 2) (q 1) * star (BandVectors.1 (q 2) (q 1))) := by ring
      _ = ((q 1).1 + (q 3).1) * BandVectors.1 (q 2) (q 1) ^ 2 +
          BandVectors.1 (q 1) (q 3) ^ 2 * ((q 2).1 + (q 1).1) := by
        rw [hnorm13mul, hnorm21mul]
        norm_num
      _ = (-2 * (q 1).1 : GaussianInt) *
          (BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 2) (q 1)) := by
        have hrel : BandVectors.1 (q 3) (q 2) ^ 2 =
            (BandVectors.1 (q 1) (q 3) + BandVectors.1 (q 2) (q 1)) ^ 2 := by
          rw [show BandVectors.1 (q 3) (q 2) =
            -(BandVectors.1 (q 1) (q 3) + BandVectors.1 (q 2) (q 1)) by
              have hsum : BandVectors.1 (q 3) (q 2) +
                  (BandVectors.1 (q 1) (q 3) + BandVectors.1 (q 2) (q 1)) = 0 := by
                simpa [add_assoc] using hrec
              exact eq_neg_of_add_eq_zero_left hsum]
          ring
        have hcoord := hsq32
        rw [hrel] at hcoord
        simp only [zsmul_eq_mul] at hcoord
        calc
          _ = (q 1).1 *
                (BandVectors.1 (q 1) (q 3) ^ 2 +
                  BandVectors.1 (q 2) (q 1) ^ 2) +
                (q 3).1 * BandVectors.1 (q 2) (q 1) ^ 2 +
                (q 2).1 * BandVectors.1 (q 1) (q 3) ^ 2 := by ring
          _ = (q 1).1 *
                (BandVectors.1 (q 1) (q 3) ^ 2 +
                  BandVectors.1 (q 2) (q 1) ^ 2) -
                (q 1).1 * ((q 2).1 * (q 3).2 -
                  (q 3).1 * (q 2).2) := by
            rw [hsq13, hsq21]
            ring
          _ = (-2 * (q 1).1 : GaussianInt) *
              (BandVectors.1 (q 1) (q 3) * BandVectors.1 (q 2) (q 1)) := by
            rw [← hcoord]
            ring_nf
  constructor
  · apply (mul_left_cancel₀ hmul)
    simpa [mul_comm] using hcross
  · have tangency : BandTangency (q 1) (q 3) := by
      refine ⟨q, hq, 1, 3, by decide, rfl, rfl⟩
    have directions := (PrimitiveVectorOrientationUnique (q 1) (q 3)).2 tangency
    have system := Classical.choose_spec RecursiveVectorsExistUnique
    dsimp [RecursiveVectorSystem, BandVectors] at system
    have hfirst :
        star (BandVectors.1 (q 1) (q 3)) * BandVectors.1 (q 2) (q 1) +
            BandVectors.1 (q 1) (q 3) * star (BandVectors.1 (q 2) (q 1)) =
          (-2 * (q 1).1 : ℤ) := by
      apply (mul_left_cancel₀ hmul)
      simpa [mul_comm] using hcross
    rcases directions.2 with forward | backward
    · have flip := system.1.2.2.2 (q 1) (q 3) forward.1
      have flip' : BandVectors.1 (q 3) (q 1) =
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3) := by
        have flipone := flip.1
        change BandVectors.1 (q 3) (q 1) =
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 3) at flipone
        exact flipone
      have realpart := congrArg (fun z : GaussianInt => z.re) hfirst
      have determinant := congrArg (fun z : GaussianInt => z.im) flip'
      have determinant' := congrArg (fun z : GaussianInt => z.re) flip'
      simp? at realpart determinant determinant'
      rw [determinant, determinant']
      have dot :
          (BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re +
            (BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im =
            -(q 1).1 := by omega
      have inner :
          -(BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im -
            (BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re =
            (q 1).1 := by
        calc
          _ = -((BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re +
              (BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im) := by ring
          _ = _ := by omega
      rw [inner]
    · have flip := system.1.2.2.2 (q 3) (q 1) backward.1
      have flip' : BandVectors.1 (q 1) (q 3) =
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 1) := by
        have flipone := flip.1
        change BandVectors.1 (q 1) (q 3) =
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 1) at flipone
        exact flipone
      have realpart := congrArg (fun z : GaussianInt => z.re) hfirst
      have determinant := congrArg (fun z : GaussianInt => z.im) flip'
      have determinant' := congrArg (fun z : GaussianInt => z.re) flip'
      simp? at realpart determinant determinant'
      have imagpart : (BandVectors.1 (q 3) (q 1)).im =
          -(BandVectors.1 (q 1) (q 3)).re := by omega
      rw [← determinant, imagpart]
      have inner :
          (BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im -
            -(BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re =
            -(q 1).1 := by
        have dot :
            (BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re +
              (BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im =
              -(q 1).1 := by omega
        calc
          _ = (BandVectors.1 (q 1) (q 3)).re * (BandVectors.1 (q 2) (q 1)).re +
              (BandVectors.1 (q 1) (q 3)).im * (BandVectors.1 (q 2) (q 1)).im := by ring
          _ = _ := dot
      rw [inner]
      simp

end ApollonianSuperharmonic

end
