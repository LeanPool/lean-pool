/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CutoffBasic
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Existence
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.Setup.UniformBounds
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# High-contrast homogenization: Provider.Response.CutoffAdaptedMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Mean normalization after adapted linear transport

The determinant factor in the integral and the volume of the adapted cell is
the same, so the normalized mean is unchanged by the grid transformation.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Set MeasureTheory

/-- Linear change of variables from the centered cube to its adapted image. -/
theorem setIntegral_adaptedCell_comp_inv {d : ℕ} {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (ψ : Vec d → ℝ) :
    ∫ x in adaptedCell q t, ψ (matVecMul q⁻¹ x) ∂volume =
      |q.det| * ∫ y in centeredCube d t, ψ y ∂volume := by
  let L : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)
  have hLdet : L.det = q.det := by
    dsimp [L]
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' q
  have hderiv : ∀ x ∈ centeredCube d t,
      HasFDerivWithinAt (matVecMul q) L (centeredCube d t) x := by
    intro x _hx
    exact (L.hasFDerivAt.congr_of_eventuallyEq (by
      filter_upwards with z
      rfl)).hasFDerivWithinAt
  have hinj : Set.InjOn (matVecMul q) (centeredCube d t) :=
    (Matrix.mulVec_injective_of_isUnit hq.isUnit).injOn
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (s := centeredCube d t) (f := matVecMul q)
    (f' := fun _ => L) (F := ℝ)
    (isOpen_openCubeSet (originCube d t)).measurableSet hderiv hinj
    (fun x => ψ (matVecMul q⁻¹ x))
  change (∫ x in matVecMul q '' centeredCube d t,
    ψ (matVecMul q⁻¹ x) ∂volume) = _
  rw [hchange]
  have hdet : IsUnit q.det := (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hcancel : ∀ y : Vec d, matVecMul q⁻¹ (matVecMul q y) = y := by
    intro y
    change Matrix.mulVec q⁻¹ (Matrix.mulVec q y) = y
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  simp_rw [hLdet, hcancel, smul_eq_mul]
  rw [integral_const_mul]

/-- The real volume of an adapted cell is the determinant times that of its
centered reference cube. -/
theorem volume_adaptedCell_toReal {d : ℕ} {q : Mat d}
    (t : ℤ) :
    (volume (adaptedCell q t)).toReal =
      |q.det| * (volume (centeredCube d t)).toReal := by
  have hvol := MeasureTheory.Measure.addHaar_image_linearMap
    (μ := (volume : Measure (Vec d))) (Matrix.mulVecLin q) (centeredCube d t)
  have hdet : LinearMap.det (Matrix.mulVecLin q) = q.det := by
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' q
  rw [hdet] at hvol
  have hvol' : volume (matVecMul q '' centeredCube d t) =
      ENNReal.ofReal |q.det| * volume (centeredCube d t) := by
    exact hvol
  rw [adaptedCell, hvol', ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg q.det)]

/-- Linear change of variables from a standard aligned cube to its physical
adapted image. -/
theorem setIntegral_adaptedCellAt_eq_det_mul {d : ℕ} {q : Mat d}
    (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ) (φ : Vec d → ℝ) :
    ∫ x in adaptedCellAt q k w, φ x ∂volume =
      |q.det| * ∫ y in standardCell d k w, φ (matVecMul q y) ∂volume := by
  let L : Vec d →L[ℝ] Vec d :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin q)
  have hLdet : L.det = q.det := by
    dsimp [L]
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' q
  have hderiv : ∀ x ∈ standardCell d k w,
      HasFDerivWithinAt (matVecMul q) L (standardCell d k w) x := by
    intro x _hx
    exact (L.hasFDerivAt.congr_of_eventuallyEq (by
      filter_upwards with z
      rfl)).hasFDerivWithinAt
  have hinj : Set.InjOn (matVecMul q) (standardCell d k w) :=
    (Matrix.mulVec_injective_of_isUnit hq.isUnit).injOn
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) (s := standardCell d k w) (f := matVecMul q)
    (f' := fun _ => L) (F := ℝ)
    (isOpen_openCubeSet (translateCube w (originCube d k))).measurableSet
    hderiv hinj φ
  rw [Recurrence.adaptedCellAt_eq_image]
  rw [hchange]
  simp_rw [hLdet, smul_eq_mul]
  rw [integral_const_mul]

/-- The real volume of an aligned adapted cell is the determinant times the
volume of its standard reference cube. -/
theorem volume_adaptedCellAt_toReal {d : ℕ} (q : Mat d)
    (k : ℤ) (w : Fin d → ℤ) :
    (volume (adaptedCellAt q k w)).toReal =
      |q.det| * (volume (standardCell d k w)).toReal := by
  have hvol := MeasureTheory.Measure.addHaar_image_linearMap
    (μ := (volume : Measure (Vec d))) (Matrix.mulVecLin q) (standardCell d k w)
  have hdet : LinearMap.det (Matrix.mulVecLin q) = q.det := by
    rw [← Matrix.toLin'_apply']
    exact LinearMap.det_toLin' q
  rw [hdet] at hvol
  change volume (matVecMul q '' standardCell d k w) =
    ENNReal.ofReal |q.det| * volume (standardCell d k w) at hvol
  rw [Recurrence.adaptedCellAt_eq_image, hvol, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg q.det)]

/-- Normalized physical averages on aligned adapted cells equal ordinary cube
averages after pullback by the grid matrix. -/
theorem volumeAverage_adaptedCellAt_eq_cubeAverage_pullback {d : ℕ}
    {q : Mat d} (hq : q.PosDef) (k : ℤ) (w : Fin d → ℤ)
    (φ : Vec d → ℝ) :
    volumeAverage (adaptedCellAt q k w) φ =
      cubeAverage (translateCube w (originCube d k))
        (fun y => φ (matVecMul q y)) := by
  let R : TriadicCube d := translateCube w (originCube d k)
  let u : Vec d → ℝ := fun y => φ (matVecMul q y)
  have hdetpos : 0 < |q.det| := abs_pos.mpr hq.det_pos.ne'
  have hstdvol : 0 < (volume (standardCell d k w)).toReal := by
    rw [standardCell, volume_openCubeSet_toReal]
    exact cubeVolume_pos R
  have havg : volumeAverage (adaptedCellAt q k w) φ =
      volumeAverage (standardCell d k w) u := by
    unfold volumeAverage
    rw [volume_adaptedCellAt_toReal,
      setIntegral_adaptedCellAt_eq_det_mul hq]
    simp only [u]
    field_simp [hdetpos.ne', hstdvol.ne']
  calc
    volumeAverage (adaptedCellAt q k w) φ =
        volumeAverage (standardCell d k w) u := havg
    _ = volumeAverage (openCubeSet R) u := by rfl
    _ = volumeAverage (cubeSet R) u :=
      (ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube
        R u).symm
    _ = cubeAverage R u := volumeAverage_cubeSet_eq_cubeAverage R u

/-- The adapted cutoff has normalized mean one on the physical adapted cell. -/
theorem volumeAverage_adaptedPreYoungCutoff_eq_one {d : ℕ} [NeZero d]
    {q : Mat d} (hq : q.PosDef) (t : ℤ) :
    volumeAverage (adaptedCell q t) (adaptedPreYoungCutoff q hq t) = 1 := by
  let η : Vec d → ℝ := QuantitativeCubeCutoff.canonicalFun (originCube d t)
    (1 - 1 / (2 * (d : ℝ))) (1 - 1 / (4 * (d : ℝ)))
  let A : ℝ := cubeAverage (originCube d t) η
  let ψ : Vec d → ℝ := fun y => A⁻¹ * η y
  have hcutoff : adaptedPreYoungCutoff q hq t = fun x => ψ (matVecMul q⁻¹ x) := by
    funext x
    rfl
  have href : volumeAverage (centeredCube d t) ψ = 1 := by
    rw [centeredCube]
    rw [← volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) t ψ]
    rw [volumeAverage_cubeSet_eq_cubeAverage]
    have hpull := cubeAverage_adaptedPreYoungCutoff_pullback_eq_one hq t
    have hpullfun : (fun y => adaptedPreYoungCutoff q hq t (matVecMul q y)) = ψ := by
      funext y
      simpa [ψ, A, η] using adaptedPreYoungCutoff_pullback_apply hq t y
    rwa [hpullfun] at hpull
  have hint :
      ∫ x in adaptedCell q t, adaptedPreYoungCutoff q hq t x ∂volume =
        |q.det| * ∫ y in centeredCube d t, ψ y ∂volume := by
    rw [hcutoff]
    exact setIntegral_adaptedCell_comp_inv hq t ψ
  have hvol := volume_adaptedCell_toReal (q := q) t
  have hdetpos : 0 < |q.det| := abs_pos.mpr hq.det_pos.ne'
  have hrefvol : 0 < (volume (centeredCube d t)).toReal := by
    rw [centeredCube, volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d t)
  unfold volumeAverage at href ⊢
  rw [hvol, hint]
  calc
    (|q.det| * (volume (centeredCube d t)).toReal)⁻¹ *
        (|q.det| * ∫ y in centeredCube d t, ψ y ∂volume) =
      (volume (centeredCube d t)).toReal⁻¹ *
        ∫ y in centeredCube d t, ψ y ∂volume := by
          field_simp [hdetpos.ne', hrefvol.ne']
    _ = 1 := href

end

end Response
end HighContrast
end HCPolySupport
