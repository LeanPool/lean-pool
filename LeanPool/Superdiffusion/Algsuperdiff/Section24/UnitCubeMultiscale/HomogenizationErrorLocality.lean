/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.UnitCubeMultiscale.CompatibleFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Public

/-!
# HomogenizationErrorLocality

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Root locality of CoarseGraining's homogenization error

The raw origin-cube homogenization error depends only on the coefficient on
that cube, not on a chosen compatible global family.
-/

namespace Algsuperdiff.Section24.UnitCubeMultiscale

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

variable {d : ℕ}

private theorem normalizedBlockResponseMax_eq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    (hR : R ∈ descendantsAtScale (originCube d 0) k) (a0 : Mat d) :
    Book.Ch02.normalizedBlockResponseMax R F a0 =
      Book.Ch02.normalizedBlockResponseMax R G a0 := by
  unfold Book.Ch02.normalizedBlockResponseMax
    Book.Ch02.normalizedBlockResponseValueSet
  refine congrArg sSup ?_
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [doubledResponseJ_eq_ofAEEq
      (coeffOn_aeeq_of_root_aeeq a F G hF hG hk hR)]
  · rintro ⟨e, he, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [doubledResponseJ_eq_ofAEEq
      (coeffOn_aeeq_of_root_aeeq a F G hF hG hk hR)]

private theorem maxDescendantNormalizedBlockResponseAtScale_eq_of_root_aeeq
     (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (k : ℤ) (hk : k ≤ (originCube d 0).scale) (a0 : Mat d) :
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d 0) k F a0 =
      Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
        (originCube d 0) k G a0 := by
  unfold Book.Ch02.maxDescendantNormalizedBlockResponseAtScale
  exact finsetSupReal_congr _ fun R hR =>
    normalizedBlockResponseMax_eq_of_root_aeeq a F G hF hG hk hR a0

private theorem scaleResponseAtScale_eq_of_root_aeeq (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (k : ℤ) (hk : k ≤ (originCube d 0).scale)
    (p : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.scaleResponseAtScale (originCube d 0) k p F a0 =
      Book.Ch02.scaleResponseAtScale (originCube d 0) k p G a0  := by
  cases p with
  | finite p =>
      unfold Book.Ch02.scaleResponseAtScale Book.Ch02.finsetAverageReal
      change
        Real.rpow
            (((descendantsAtScale (originCube d 0) k).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtScale (originCube d 0) k,
                Real.rpow (Book.Ch02.normalizedBlockResponseMax R F a0) (p / 2))
            (1 / p) =
          Real.rpow
            (((descendantsAtScale (originCube d 0) k).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtScale (originCube d 0) k,
                Real.rpow (Book.Ch02.normalizedBlockResponseMax R G a0) (p / 2))
            (1 / p)
      refine congrArg
        (fun x => Real.rpow
          (((descendantsAtScale (originCube d 0) k).card : ℝ)⁻¹ * x) (1 / p)) ?_
      refine Finset.sum_congr rfl fun R hR => ?_
      rw [normalizedBlockResponseMax_eq_of_root_aeeq a F G hF hG hk hR a0]
  | infinity =>
      unfold Book.Ch02.scaleResponseAtScale
      rw [maxDescendantNormalizedBlockResponseAtScale_eq_of_root_aeeq
        a F G hF hG k hk a0]

/-- CoarseGraining's raw homogenization error at the origin depends only on the
origin coefficient. -/
theorem homogenizationErrorOnCube_eq_of_root_aeeq (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    (s : ℝ) (p q : Book.Ch02.MultiscaleExponent) (a0 : Mat d) :
    Book.Ch02.HomogenizationErrorOnCube (originCube d 0) s p q F a0 =
      Book.Ch02.HomogenizationErrorOnCube (originCube d 0) s p q G a0  := by
  unfold Book.Ch02.HomogenizationErrorOnCube
  cases q with
  | finite q =>
      change Book.Ch02.HomogenizationErrorFinite
          (originCube d 0) (originCube d 0).scale s p q F a0 =
        Book.Ch02.HomogenizationErrorFinite
          (originCube d 0) (originCube d 0).scale s p q G a0
      unfold Book.Ch02.HomogenizationErrorFinite
      refine congrArg (fun x => Real.rpow x (1 / q)) ?_
      refine tsum_congr fun l => ?_
      rw [scaleResponseAtScale_eq_of_root_aeeq a F G hF hG
        ((originCube d 0).scale - (l : ℤ))
        (sub_le_self _ (Int.natCast_nonneg l)) p a0]
  | infinity =>
      change Book.Ch02.HomogenizationErrorInfinity
          (originCube d 0) (originCube d 0).scale s p F a0 =
        Book.Ch02.HomogenizationErrorInfinity
          (originCube d 0) (originCube d 0).scale s p G a0
      unfold Book.Ch02.HomogenizationErrorInfinity
      refine congrArg sSup ?_
      ext m
      constructor <;> rintro ⟨l, rfl⟩ <;> refine ⟨l, ?_⟩
      all_goals
        rw [scaleResponseAtScale_eq_of_root_aeeq a F G hF hG
          ((originCube d 0).scale - (l : ℤ))
          (sub_le_self _ (Int.natCast_nonneg l)) p a0]

end Algsuperdiff.Section24.UnitCubeMultiscale
