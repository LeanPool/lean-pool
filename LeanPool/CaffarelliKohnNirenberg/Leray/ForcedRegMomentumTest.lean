/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm

/-!
# Smooth test fields in frequency variables

A smooth compactly supported real vector field on Vec3 is transported to the
Euclidean carrier and complexified; it is then a Schwartz field whose class is
the complexification of its real `L²` class. The integral of a real test field
against the representative of the real part of a complex `L²` field is the
real part of the frequency pairing with the transformed test, by Plancherel.
These are the pairings in the frequency form of `eq:reg-momentum-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

/-- The complexification of a coordinate vector, as a Euclidean complex
three-vector. -/
@[expose]
def coordComplexify : Vec3 →L[ℝ] ComplexVec3 :=
  complexifyValue.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap

theorem coordComplexify_apply (v : Vec3) (i : Fin 3) : coordComplexify v i = (v i : ℂ) := rfl

/-- The complexified test field on the Euclidean carrier of a coordinate
field. -/
@[expose]
def testField (g : Vec3 → Vec3) : L2Vec3 → ComplexVec3 :=
  fun y => coordComplexify (g (WithLp.ofLp y))

theorem testField_contDiff {g : Vec3 → Vec3} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (testField g) := by
  have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff (n := (⊤ : ℕ∞))
  exact coordComplexify.contDiff.comp (hg.comp he)

theorem testField_hasCompactSupport {g : Vec3 → Vec3} (hgc : HasCompactSupport g) :
    HasCompactSupport (testField g) := by
  have h1 := hgc.comp_homeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph
  exact h1.comp_left (g := coordComplexify) (map_zero _)

/-- The Schwartz field of a smooth compactly supported coordinate field. -/
@[expose]
def testSchwartz (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    𝓢(L2Vec3, ComplexVec3) :=
  (testField_hasCompactSupport hgc).toSchwartzMap (testField_contDiff hg)

theorem testSchwartz_apply (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (y : L2Vec3) : testSchwartz g hg hgc y = testField g y := rfl

theorem fourier_testSchwartz (g : Vec3 → Vec3) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (ξ : L2Vec3) :
    (𝓕 (testSchwartz g hg hgc) : 𝓢(L2Vec3, ComplexVec3)) ξ = 𝓕 (testField g) ξ := rfl

/-- The complexified class of a smooth compactly supported coordinate field is
the class of its Schwartz field. -/
theorem complexify_realVectorL2OfCoordinateFunction (g : Vec3 → Vec3) (hg2 : MemLp g 2 volume)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    complexifyVectorL2 (realVectorL2OfCoordinateFunction g hg2) =
      (testSchwartz g hg hgc).toLp 2 := by
  apply Lp.ext
  filter_upwards [complexifyValue.coeFn_compLpL (p := 2) (μ := volume)
      (realVectorL2OfCoordinateFunction g hg2),
    realVectorL2OfCoordinateFunction_ae_eq_toLp g hg2,
    (testSchwartz g hg hgc).coeFn_toLp 2 (volume : Measure L2Vec3)] with y h1 h2 h3
  change (complexifyValue.compLpL 2 volume (realVectorL2OfCoordinateFunction g hg2)) y = _
  rw [h1, h2, h3]
  rfl

/-- Plancherel for a Schwartz test field. -/
theorem re_inner_testSchwartz (Z : ComplexVectorL2) (g : Vec3 → Vec3)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    (inner ℂ Z ((testSchwartz g hg hgc).toLp 2)).re =
      ∫ ξ, (inner ℂ ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3) ξ)
        (𝓕 (testField g) ξ)).re := by
  set Ψ := testSchwartz g hg hgc with hΨ
  have hΨLp : Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (Ψ.toLp 2) = (𝓕 Ψ).toLp 2 :=
    SchwartzMap.toLp_fourier_eq Ψ
  rw [← (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).inner_map_map, hΨLp, L2.inner_def,
    ← RCLike.re_to_complex, ← integral_re (L2.integrable_inner _ _)]
  refine integral_congr_ae ?_
  filter_upwards [(𝓕 Ψ).coeFn_toLp 2 (volume : Measure L2Vec3)] with ξ hξ
  rw [hξ, hΨ, fourier_testSchwartz]
  rfl

/-- The integral of a smooth test field against the representative of the real
part of a complex `L²` field is the real part of the frequency pairing. -/
theorem integral_test_eq_fourier (Z : ComplexVectorL2) {w : Vec3 → Vec3}
    (hw : w =ᵐ[volume] realVectorL2Representative (realPartVectorL2 Z)) (g : Vec3 → Vec3)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ x, ∑ i : Fin 3, g x i * w x i =
      ∫ ξ, (inner ℂ ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 Z : L2Vec3 → ComplexVec3) ξ)
        (𝓕 (testField g) ξ)).re := by
  have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  rw [← inner_realVectorL2OfCoordinateFunction hw g hg2, inner_realPartVectorL2_eq_re,
    complexify_realVectorL2OfCoordinateFunction g hg2 hg hgc, re_inner_testSchwartz]

end CKN.Leray

end
