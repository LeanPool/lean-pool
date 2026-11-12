/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandCircleEuclideanData
public import LeanPool.ApollonianSuperharmonic.BandSuccessorClassification
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TangencyCoordinateIdentity

-- [TABLET NODE: BandDescartesGapSubdivision]

/-!
# BandDescartesGapSubdivision

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandDescartesGapSubdivision
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q) :
    let D : CircleCoordinates :=
      (2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2)
    ∃ C₀ D₀ : BandCircle,
      C₀.1.1 = q 0 ∧ D₀.1.1 = D ∧
      dist (BandCircleEuclideanData C₀).center
          (BandCircleEuclideanData D₀).center =
        (BandCircleEuclideanData C₀).radius +
          (BandCircleEuclideanData D₀).radius ∧
      (BandCircleEuclideanData D₀).radius <
        (BandCircleEuclideanData C₀).radius ∧
      (∀ k : Fin 4, (k = 2 ∨ k = 3) → 0 < (q k).1 →
        ∃ Cₖ : BandCircle, Cₖ.1.1 = q k ∧
          dist (BandCircleEuclideanData Cₖ).center
              (BandCircleEuclideanData D₀).center =
            (BandCircleEuclideanData Cₖ).radius +
              (BandCircleEuclideanData D₀).radius ∧
          (BandCircleEuclideanData D₀).radius <
            (BandCircleEuclideanData Cₖ).radius) := by
-- BODY
  dsimp
  have makeCircle : ∀ (r : Fin 4 → CircleCoordinates),
      SemiProperQuadruple r → ∀ i : Fin 4, 0 < (r i).1 →
        ∃ C : BandCircle, C.1.1 = r i := by
    intro r hr i hi
    refine ⟨⟨⟨r i, ?_⟩, hi⟩, rfl⟩
    exact ⟨Or.inl hi, ⟨r, hr, i, rfl⟩⟩
  have curvature := ProperBandCurvatureStructure q hq
  have successor := SemiProperQuadruple.successor hq.1
  have classified := BandSuccessorClassification q hq.1
  dsimp at classified
  rcases classified with special | classified
  · exfalso
    have hpos := curvature.1
    have n1 : 0 ≤ (q 1).1 := by simpa using curvature.2.1 (0 : Fin 3)
    have n2 : 0 ≤ (q 2).1 := by simpa using curvature.2.1 (1 : Fin 3)
    have n3 : 0 ≤ (q 3).1 := by simpa using curvature.2.1 (2 : Fin 3)
    have hlt : (q 1).1 < (q 0).1 := by simpa using hq.2 (0 : Fin 3)
    have hzero := curvature.2.2
    change 2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1 = 1 at special
    have hz2 : (q 2).1 = 0 := by omega
    have hz3 : (q 3).1 = 0 := by omega
    have hz1 : (q 1).1 = 0 := by omega
    have : (1 : Fin 3) = 2 := hzero 1 2 (by simpa using hz2) (by simpa using hz3)
    exact (by decide : (1 : Fin 3) ≠ 2) this
  rcases classified with ⟨hs, h0, h2, h3⟩
  let s : Fin 4 → CircleCoordinates :=
    ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
      q 0, q 2, q 3]
  have hsdef : s = ![(2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1,
        2 * (q 0).2 + 2 * (q 2).2 + 2 * (q 3).2 - (q 1).2),
      q 0, q 2, q 3] := rfl
  have hssemi : SemiProperQuadruple s := by
    simpa [s] using successor
  have hdpos : 0 < (s 0).1 := by
    change 0 < 2 * (q 0).1 + 2 * (q 2).1 + 2 * (q 3).1 - (q 1).1
    omega
  have hcpos : 0 < (s 1).1 := by simpa [s] using curvature.1
  obtain ⟨C₀, hC₀⟩ := makeCircle s hssemi 1 hcpos
  obtain ⟨D₀, hD₀⟩ := makeCircle s hssemi 0 hdpos
  have tangentNorm : ∀ (r : Fin 4 → CircleCoordinates),
      SemiProperQuadruple r → ∀ i j : Fin 4, i ≠ j →
      0 < (r i).1 → 0 < (r j).1 →
      ‖((r i).2 : Complex) / (r i).1 - (r j).2 / (r j).1‖ =
        (1 / (r i).1 : ℝ) + 1 / (r j).1 := by
    intro r hr i j hij hi hj
    have ht := TangencyCoordinateIdentity r hr i j hij
    have htcast := congrArg (fun z : ℤ => (z : ℝ)) ht
    simp only [GaussianInt.intCast_real_norm, Int.cast_pow, Int.cast_add] at htcast
    have hsq :
        ‖((r i).2 : Complex) / (r i).1 - (r j).2 / (r j).1‖ ^ 2 =
          ((1 / (r i).1 : ℝ) + 1 / (r j).1) ^ 2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, GaussianInt.toComplex_def₂]
      norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]
      field_simp
      simp only [Complex.normSq_apply, GaussianInt.toComplex_def₂] at htcast
      norm_num at htcast
      have ire : (GaussianInt.toComplex (r i).2).re = ((r i).2.re : ℝ) := by
        rw [GaussianInt.toComplex_def₂]
      have iim : (GaussianInt.toComplex (r i).2).im = ((r i).2.im : ℝ) := by
        rw [GaussianInt.toComplex_def₂]
      have jre : (GaussianInt.toComplex (r j).2).re = ((r j).2.re : ℝ) := by
        rw [GaussianInt.toComplex_def₂]
      have jim : (GaussianInt.toComplex (r j).2).im = ((r j).2.im : ℝ) := by
        rw [GaussianInt.toComplex_def₂]
      rw [ire, iim, jre, jim] at htcast
      rw [ire, iim, jre, jim] at ⊢
      ring_nf at htcast ⊢
      nlinarith [htcast]
    have hnon : 0 ≤ ‖((r i).2 : Complex) / (r i).1 - (r j).2 / (r j).1‖ := norm_nonneg _
    have hright : 0 ≤ (1 / (r i).1 : ℝ) + 1 / (r j).1 := by positivity
    nlinarith
  refine ⟨C₀, D₀, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hC₀, s]
  · simp [hD₀, s]
  · have ht := tangentNorm s hssemi 1 0 (by decide) hcpos hdpos
    simpa [BandCircleEuclideanData, hC₀, hD₀, dist_eq_norm] using ht
  · have hlt : (1 / (s 0).1 : ℝ) < 1 / (s 1).1 := by
      apply one_div_lt_one_div_of_lt
      · exact_mod_cast hcpos
      · exact_mod_cast h0
    simpa [BandCircleEuclideanData, hC₀, hD₀] using hlt
  · intro k hk hkpos
    rcases hk with rfl | rfl
    · obtain ⟨Cₖ, hCₖ⟩ := makeCircle s hssemi 2 hkpos
      refine ⟨Cₖ, ?_, ?_, ?_⟩
      · simp [hCₖ, s]
      · have ht := tangentNorm s hssemi 2 0 (by decide) (by simpa [s] using hkpos) hdpos
        simpa [BandCircleEuclideanData, hCₖ, hD₀, dist_eq_norm] using ht
      · have hlt : (1 / (s 0).1 : ℝ) < 1 / (s 2).1 := by
          apply one_div_lt_one_div_of_lt
          · exact_mod_cast (show 0 < (s 2).1 by simpa [s] using hkpos)
          · exact_mod_cast h2
        simpa [BandCircleEuclideanData, hCₖ, hD₀] using hlt
    · obtain ⟨Cₖ, hCₖ⟩ := makeCircle s hssemi 3 hkpos
      refine ⟨Cₖ, ?_, ?_, ?_⟩
      · simp [hCₖ, s]
      · have ht := tangentNorm s hssemi 3 0 (by decide) (by simpa [s] using hkpos) hdpos
        simpa [BandCircleEuclideanData, hCₖ, hD₀, dist_eq_norm] using ht
      · have hlt : (1 / (s 0).1 : ℝ) < 1 / (s 3).1 := by
          apply one_div_lt_one_div_of_lt
          · exact_mod_cast (show 0 < (s 3).1 by simpa [s] using hkpos)
          · exact_mod_cast h3
        simpa [BandCircleEuclideanData, hCₖ, hD₀] using hlt

end ApollonianSuperharmonic

end
