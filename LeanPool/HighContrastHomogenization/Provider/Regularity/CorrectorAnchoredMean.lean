/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorAnchoredMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-unit normalization of every local corrector representative

The projective carrier stores zero mean only at scale zero.  Compatibility of
the global representative transports that normalization to the restriction of
every larger canonical local `H¹` representative.  This is the anchor for the
successive-cube mean telescope used in the Liouville growth argument.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

/-- The global scalar representative and the canonical local `H¹`
representative have the same average on every exhaustion cube. -/
theorem NormalizedLocalH1Carrier.cubeAverage_globalValueRepresentative_eq_localH1Function
    {d : ℕ} (z : NormalizedLocalH1Carrier d) (n : ℕ) :
    cubeAverage (originCube d (n : ℤ)) z.globalValueRepresentative =
      cubeAverage (originCube d (n : ℤ)) (z.localH1Function n).toFun := by
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  congr 1
  exact integral_congr_ae
    (z.globalValueRepresentative_ae_eq_localH1Function n)

/-- A larger canonical local representative has the same average on every
smaller exhaustion cube as the smaller canonical representative. -/
theorem NormalizedLocalH1Carrier.cubeAverage_localH1Function_eq_of_le
    {d m n : ℕ} (z : NormalizedLocalH1Carrier d) (hmn : m ≤ n) :
    cubeAverage (originCube d (m : ℤ)) (z.localH1Function n).toFun =
      cubeAverage (originCube d (m : ℤ)) (z.localH1Function m).toFun := by
  have hsubset : localGradientCube d m ⊆ localGradientCube d n :=
    localGradientCube_mono hmn
  have hμ : volume.restrict (localGradientCube d m) ≤
      volume.restrict (localGradientCube d n) :=
    Measure.restrict_mono_set volume hsubset
  have hn :=
    (z.globalValueRepresentative_ae_eq_localH1Function n).filter_mono
      (ae_mono hμ)
  have hm := z.globalValueRepresentative_ae_eq_localH1Function m
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  congr 1
  exact integral_congr_ae (hn.symm.trans hm)

/-- The global representative has zero average on the unit origin cube. -/
theorem NormalizedLocalH1Carrier.cubeAverage_globalValueRepresentative_zero
    {d : ℕ} (z : NormalizedLocalH1Carrier d) :
    cubeAverage (originCube d 0) z.globalValueRepresentative = 0 := by
  change cubeAverage (originCube d ((0 : ℕ) : ℤ))
    z.globalValueRepresentative = 0
  rw [z.cubeAverage_globalValueRepresentative_eq_localH1Function 0]
  have hmean :
      ∫ x in openCubeSet (originCube d ((0 : ℕ) : ℤ)),
          (z.localH1Function 0).toFun x ∂volume = 0 := by
    simpa only [localGradientCube] using! z.localH1Function_zero_mean
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    hmean, mul_zero]

end

end HighContrast
end HCPolySupport
