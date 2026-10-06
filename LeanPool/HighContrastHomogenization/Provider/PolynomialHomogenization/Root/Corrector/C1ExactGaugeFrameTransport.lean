/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FinitePrefixAbsorption
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1NormalizedRootEllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorWeightedGradientBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCenteredCoeffSpace
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedCoefficientWeightedNormGauge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1ExactGaugeFrameTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exact gauge-frame transport for the C1 estimate

The normalized-root frame uses the exact centered coefficient and the
canonical joint corrector.  An estimate in that frame returns to the physical
ellipsoids without introducing a rounded coefficient family.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem normalizedRoot_transpose_eq
    {m : Mat d} (hm : m.PosDef) :
    matTranspose (Selection.normalizedRoot m) = Selection.normalizedRoot m := by
  have hq := normalizedRoot_posDef_of_posDef hm
  simpa only [matTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using!
    hq.isHermitian

private theorem normalizedRoot_mul_inv_vec
    {m : Mat d} (hm : m.PosDef) (e : Vec d) :
    matVecMul (Selection.normalizedRoot m)
        (matVecMul (Selection.normalizedRoot m)⁻¹ e) = e := by
  let q := Selection.normalizedRoot m
  have hq : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hm).isUnit
  rw [matVecMul_mul, Matrix.mul_nonsing_inv q hq, matVecMul_one]

private theorem weightedGradNorm_le_of_normalizedSkewGauge_le_twoFields
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (a : CoeffField d) (U V : Set (Vec d))
    (F G : Vec d → Vec d) (C : ℝ≥0∞)
    (hbound : weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) U F ≤
      C * weightedGradNorm
        (fun x ↦ specBound ((symmPart abar)⁻¹) •
          (a x - skewPart abar)) V G) :
    weightedGradNorm a U F ≤ C * weightedGradNorm a V G := by
  let scale : ℝ≥0∞ :=
    (ENNReal.ofReal (specBound ((symmPart abar)⁻¹))) ^ (1 / 2 : ℝ)
  have hscalePos : 0 < scale := by
    exact ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (normalizedRootScale_pos hS))
      ENNReal.ofReal_ne_top
  have hscaleTop : scale ≠ ⊤ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  rw [weightedGradNorm_normalizedSkewGauge abar hS a U F,
    weightedGradNorm_normalizedSkewGauge abar hS a V G] at hbound
  have hbound' : scale * weightedGradNorm a U F ≤
      scale * (C * weightedGradNorm a V G) := by
    simpa only [scale, mul_assoc, mul_left_comm, mul_comm] using hbound
  exact (ENNReal.mul_le_mul_iff_right hscalePos.ne' hscaleTop).mp hbound'

/-- A decay estimate at a larger exponent implies the same estimate at a
smaller exponent on a nested-radius interval. -/
theorem c1DecayBound_weaken_exponent
    (A eta etaFast r R : ℝ) (hA : 0 ≤ A)
    (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (heta : eta ≤ etaFast) {X Y : ℝ≥0∞}
    (hbound : X ≤ ENNReal.ofReal (A * (r / R) ^ etaFast) * Y) :
    X ≤ ENNReal.ofReal (A * (r / R) ^ eta) * Y := by
  have hratio0 : 0 < r / R := div_pos hr hR
  have hratio1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  have hpow : (r / R) ^ etaFast ≤ (r / R) ^ eta :=
    Real.rpow_le_rpow_of_exponent_ge hratio0 hratio1 heta
  have hcoeff : ENNReal.ofReal (A * (r / R) ^ etaFast) ≤
      ENNReal.ofReal (A * (r / R) ^ eta) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hA)
  exact hbound.trans (by
    simpa only [mul_comm] using mul_le_mul_left hcoeff Y)

/-- A delayed C1 estimate for the exact normalized coefficient and canonical
joint corrector transports to the same delayed estimate on physical
ellipsoids. -/
theorem delayedPhysicalC1_of_exactRootGaugeFrame
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    (a : CoeffSpace d)
    (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d)
    (PhiRef : Vec d → NormalizedLocalH1Carrier d)
    (hpullback : ∀ e : Vec d,
      (fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar))
        (e + gradPhi e a
          (matVecMul (Selection.normalizedRoot (symmPart abar)) y))) =ᵐ[volume]
        fun y ↦ matVecMul (Selection.normalizedRoot (symmPart abar)) e +
          (PhiRef (matVecMul
            (Selection.normalizedRoot (symmPart abar)) e)).globalGradientRepresentative y)
    (L : ℕ) (eta A x R : ℝ) (Du : Vec d → Vec d) :
    (let rStart := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L);
      rStart ≤ R) →
    (let q := Selection.normalizedRoot (symmPart abar)
      let hq : IsUnit q.det :=
        (Matrix.isUnit_iff_isUnit_det _).mp
          (normalizedRoot_posDef_of_posDef hS).isUnit
      let bRef := affineCoefficient q hq
        (⇑(normalizedCenteredCoeff a abar hS).1)
      let rStart := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)
        ∃ eRef : Vec d, ∀ r : ℝ, r ∈ Icc rStart R →
          weightedGradNorm bRef {y | vecNormSq y ≤ r ^ 2}
              (fun y ↦ matVecMul q (Du (matVecMul q y)) -
                (eRef + (PhiRef eRef).globalGradientRepresentative y)) ≤
            ENNReal.ofReal (A * (r / R) ^ eta) *
              weightedGradNorm bRef {y | vecNormSq y ≤ R ^ 2}
                (fun y ↦ matVecMul q (Du (matVecMul q y)))) →
      ∃ e : Vec d, ∀ r : ℝ,
        r ∈ Icc ((3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)) R →
        weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r)
            (fun y ↦ Du y - (e + gradPhi e a y)) ≤
          ENNReal.ofReal (A * (r / R) ^ eta) *
            weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du := by
  dsimp only
  intro _hStartR hGauge
  let q : Mat d := Selection.normalizedRoot (symmPart abar)
  let hq : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (normalizedRoot_posDef_of_posDef hS).isUnit
  let b : CoeffField d := ⇑(normalizedCenteredCoeff a abar hS).1
  let bRef : CoeffField d := affineCoefficient q hq b
  let rStart : ℝ := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)
  obtain ⟨eRef, heRef⟩ := hGauge
  let e : Vec d := matVecMul q⁻¹ eRef
  have hqe : matVecMul q e = eRef := by
    simpa only [q, e] using
      normalizedRoot_mul_inv_vec hS eRef
  have hqT : matTranspose q = q := by
    simpa only [q] using normalizedRoot_transpose_eq hS
  have hgeom : ∀ t : ℝ,
      matImage q⁻¹ (ellipsoid abar t) =
        {y : Vec d | vecNormSq y ≤ t ^ 2} := by
    intro t
    simpa only [q] using matImage_normalizedRoot_inv_ellipsoid_eq hS t
  have himage : ∀ t : ℝ,
      matImage q {y : Vec d | vecNormSq y ≤ t ^ 2} = ellipsoid abar t := by
    intro t
    rw [← hgeom t]
    exact matImage_matImage_inv hq (ellipsoid abar t)
  have hmeas : ∀ t : ℝ,
      MeasurableSet {y : Vec d | vecNormSq y ≤ t ^ 2} := by
    intro t
    rw [← hgeom t]
    exact measurableSet_affinePullback hq (measurableSet_ellipsoid abar t)
  have hcoeff : b =ᵐ[volume]
      fun y ↦ specBound ((symmPart abar)⁻¹) •
        ((a.1 y : Mat d) - skewPart abar) := by
    simpa only [b] using normalizedCenteredCoeff_ae a abar hS
  refine ⟨e, ?_⟩
  intro r hr
  have hframe := heRef r hr
  have hpull := hpullback e
  have hresidual :
      (fun y ↦ matVecMul q
        (Du (matVecMul q y) -
          (e + gradPhi e a (matVecMul q y)))) =ᵐ[volume]
        fun y ↦ matVecMul q (Du (matVecMul q y)) -
          (eRef + (PhiRef eRef).globalGradientRepresentative y) := by
    filter_upwards [hpull] with y hy
    rw [← matVecMul_sub_vec, hy, hqe]
  have hinnerAffine := weightedGradNorm_matImage hq (hmeas r) b
    (fun y ↦ Du y - (e + gradPhi e a y))
  rw [himage r, hqT] at hinnerAffine
  have houterAffine := weightedGradNorm_matImage hq (hmeas R) b Du
  rw [himage R, hqT] at houterAffine
  have hinnerCongr := weightedGradNorm_congr_ae bRef
    {y : Vec d | vecNormSq y ≤ r ^ 2}
    (ae_restrict_of_ae hresidual)
  have hpackaged : weightedGradNorm b (ellipsoid abar r)
      (fun y ↦ Du y - (e + gradPhi e a y)) ≤
        ENNReal.ofReal (A * (r / R) ^ eta) *
          weightedGradNorm b (ellipsoid abar R) Du := by
    rw [hinnerAffine, hinnerCongr, houterAffine]
    exact hframe
  have hcoeffR := weightedGradNorm_congr_coeff_ae_on
    (U := ellipsoid abar R) Du
    (ae_restrict_of_ae hcoeff)
  have hcoeffr := weightedGradNorm_congr_coeff_ae_on
    (U := ellipsoid abar r)
    (fun y ↦ Du y - (e + gradPhi e a y))
    (ae_restrict_of_ae hcoeff)
  exact weightedGradNorm_le_of_normalizedSkewGauge_le_twoFields abar hS
    (fun y ↦ a.1 y) (ellipsoid abar r) (ellipsoid abar R)
      (fun y ↦ Du y - (e + gradPhi e a y))
      Du
      (ENNReal.ofReal (A * (r / R) ^ eta)) (by
        rw [← hcoeffr, ← hcoeffR]
        exact hpackaged)

end


end Root
end HighContrast
end HCPolySupport
