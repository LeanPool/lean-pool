/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreSecond

/-!
# Conjugation of the backward heat operator

The pointwise change of variables used in `prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript and
`prop:carleman-halfspace` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

local instance carlemanCoreConjugationNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

local instance carlemanCoreConjugationNormedSpace : NormedSpace ℝ ParabolicPoint :=
  carlemanProductNormedSpace

private theorem conjugation_algebra
    (E w tw phit : ℝ) (p q r s : Fin 3 → ℝ) :
    E * (tw + w * phit) +
        (∑ i, E * (s i + p i * q i + p i * q i + w * (r i + p i ^ 2))) -
        2 * (∑ i, p i * (E * (q i + w * p i))) +
        ((∑ i, p i ^ 2) - phit - (∑ i, r i)) * (E * w) =
      E * (tw + ∑ i, s i) := by
  have hsum :
      (∑ i, E * (s i + p i * q i + p i * q i + w * (r i + p i ^ 2))) -
          2 * (∑ i, p i * (E * (q i + w * p i))) =
        E * (∑ i, s i) + E * w * (∑ i, r i) - E * w * (∑ i, p i ^ 2) := by
    calc
      _ = ∑ i, (E * (s i + p i * q i + p i * q i + w * (r i + p i ^ 2)) -
            2 * (p i * (E * (q i + w * p i)))) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = ∑ i, (E * s i + E * w * r i - E * w * p i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
            simp only [Finset.mul_sum]
  calc
    _ = E * (tw + w * phit) +
          ((∑ i, E * (s i + p i * q i + p i * q i + w * (r i + p i ^ 2))) -
            2 * (∑ i, p i * (E * (q i + w * p i)))) +
          ((∑ i, p i ^ 2) - phit - (∑ i, r i)) * (E * w) := by ring
    _ = E * (tw + w * phit) +
          (E * (∑ i, s i) + E * w * (∑ i, r i) - E * w * (∑ i, p i ^ 2)) +
          ((∑ i, p i ^ 2) - phit - (∑ i, r i)) * (E * w) := by rw [hsum]
    _ = _ := by ring

/-- Exponential conjugation expands to the scalar backward heat operator on
the open set where the phase is smooth. -/
theorem carlemanConj_exp_mul
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) :
    carlemanConj φ (fun y => Real.exp (φ y) * w y) z =
      Real.exp (φ z) * (timePartial w z + scalarLaplacian w z) := by
  have htime := timePartial_exp_mul_at hU hφ hw hz
  have hspace (i : Fin 3) := spatialPartial_exp_mul_at hU hφ hw hz i
  have hsecond (i : Fin 3) := spatialSecondPartial_exp_mul_at hU hφ hw hz i i
  unfold carlemanConj scalarLaplacian scalarGradSq
  rw [htime]
  simp_rw [hspace, hsecond]
  simp_rw [← pow_two]
  exact conjugation_algebra (Real.exp (φ z)) (w z) (timePartial w z)
    (timePartial φ z) (fun i => spatialPartial φ i z)
    (fun i => spatialPartial w i z)
    (fun i => spatialSecondPartial φ i i z)
    (fun i => spatialSecondPartial w i i z)

end CKN
