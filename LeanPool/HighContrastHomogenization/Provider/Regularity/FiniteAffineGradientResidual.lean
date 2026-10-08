/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcess
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeEnergyRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineGradientResidual

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine gradient residuals

This module realizes the difference between a finite cube solution and a
finite affine-boundary solution as an actual harmonic solution on every
smaller centered cube.  It is the bridge from the gradient-excess definition
to the finite Caccioppoli estimates.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weighted gradient norm respects almost-everywhere equality on its
integration set. -/
theorem weightedGradNorm_congr_ae
    {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn V] G) :
    weightedGradNorm b V F = weightedGradNorm b V G := by
  unfold weightedGradNorm eVolumeAverage
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hFG] with x hx
  rw [hx]

/-- Subtracting two fields and their affine candidates costs at most the sum
of the two candidate errors. -/
theorem normalizedAffineCandidateError_sub_le_add
    {d : ℕ} (Q : TriadicCube d) (f g : Vec d → ℝ)
    (c₁ c₂ : ℝ) (e₁ e₂ : Vec d)
    (h₁ : MemLp (fun x ↦ f x - (c₁ + vecDot e₁ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (h₂ : MemLp (fun x ↦ g x - (c₂ + vecDot e₂ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    normalizedAffineCandidateError Q (fun x ↦ f x - g x)
        (c₁ - c₂) (e₁ - e₂) ≤
      normalizedAffineCandidateError Q f c₁ e₁ +
        normalizedAffineCandidateError Q g c₂ e₂ := by
  let r₁ : Vec d → ℝ := fun x ↦ f x - (c₁ + vecDot e₁ x)
  let r₂ : Vec d → ℝ := fun x ↦ g x - (c₂ + vecDot e₂ x)
  have htri := cubeLpNorm_add_le Q (2 : ℝ≥0∞) r₁ (-r₂) h₁ h₂.neg
    (by norm_num)
  have hneg : cubeLpNorm Q (2 : ℝ≥0∞) (-r₂) =
      cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by
    unfold cubeLpNorm
    rw [MeasureTheory.eLpNorm_neg]
  have hweight : 0 ≤ cubeBesovScaleWeight 1 Q :=
    cubeBesovScaleWeight_nonneg 1 Q
  unfold normalizedAffineCandidateError normalizedCubeL2Distance
  rw [hneg] at htri
  calc
    cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ (f x - g x) -
              ((c₁ - c₂) + vecDot (e₁ - e₂) x)) =
        cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) (r₁ + -r₂) := by
      congr 2
      funext x
      dsimp [r₁, r₂]
      rw [vecDot_sub_left]
      ring
    _ ≤ cubeBesovScaleWeight 1 Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) r₁ + cubeLpNorm Q (2 : ℝ≥0∞) r₂) :=
      mul_le_mul_of_nonneg_left htri hweight
    _ = cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
          cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by
      ring

theorem cubeSolution_weakFluxIntegrable_finiteAffineGradientResidual {d : ℕ}
    {Q : TriadicCube d} {a : Book.Ch02.TriadicCoeffFamily d}
    (u : Book.Ch03.CubeSolution Q a) :
    weakFluxIntegrable (Book.Ch02.cubeDomain Q : Set (Vec d))
      (a.coeffOn Q).toCoeffField u := by
  intro φ
  exact integrableOn_vecDot_of_memVectorL2
    (Book.Ch02.Solution.flux_memVectorL2 u)
    φ.toH1Function.grad_memVectorL2

/-- The harmonic residual `u - w_m(e)` on the centered cube `Q_n`. -/
@[expose]
noncomputable def finiteAffineGradientResidual
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d n) a :=
  let uR := finiteCubeSolutionRestriction a hnm u
  let wR := finiteCubeSolutionRestriction a hnm
    (finiteAffineCubeSolution a m e)
  AHarmonicFunction.subOfIntegrable uR wR
    (cubeSolution_weakFluxIntegrable_finiteAffineGradientResidual uR)
    (cubeSolution_weakFluxIntegrable_finiteAffineGradientResidual wR)

/-- The residual has the literal value representative `u - w_m(e)`. -/
@[simp] theorem finiteAffineGradientResidual_toFun
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    (finiteAffineGradientResidual a hnm u e).toH1.toFun =
      fun x ↦ u.toH1.toFun x - (finiteAffineSolution a m e).toH1.toFun x := by
  simp only [finiteAffineGradientResidual,
    AHarmonicFunction.toH1_subOfIntegrable, H1Function.sub_toFun,
    finiteCubeSolutionRestriction_toFun, finiteAffineCubeSolution]

/-- The residual has the literal gradient representative `∇u - ∇w_m(e)`. -/
@[simp] theorem finiteAffineGradientResidual_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    (finiteAffineGradientResidual a hnm u e).toH1.grad =
      fun x ↦ u.toH1.grad x - (finiteAffineSolution a m e).toH1.grad x := by
  unfold finiteAffineGradientResidual
  rw [AHarmonicFunction.grad_subOfIntegrable]
  simp only [finiteCubeSolutionRestriction_grad, finiteAffineCubeSolution]
  funext x
  rfl

/-- A gradient-excess candidate is exactly the `ENNReal` realization of the
cube energy of its harmonic residual. -/
theorem weightedGradNorm_finiteAffineGradientResidual
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    weightedGradNorm
        (a.coeffOn (originCube d n)).toCoeffField
        (openCubeSet (originCube d n))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a m e).toH1.grad x) =
      ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d n) a
          (finiteAffineGradientResidual a hnm u e).toH1) := by
  rw [← finiteAffineGradientResidual_grad a hnm u e,
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]

/-- The canonical excess is bounded by the energy of every harmonic affine
residual. -/
theorem finiteAffineGradientExcess_le_residualEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℤ} (hnm : n ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    finiteAffineGradientExcess a n m u ≤
      ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d n) a
          (finiteAffineGradientResidual a hnm u e).toH1) := by
  rw [← weightedGradNorm_finiteAffineGradientResidual a hnm u e]
  exact finiteAffineGradientExcess_le a n m u e

/-- The residual `u - w_m(e) - w_m(p)` realized as a harmonic solution on
`Q_k`.  Both affine solutions retain the original outer scale `m`. -/
@[expose]
noncomputable def finiteAffineGradientUpdatedResidual
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k m : ℤ} (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e p : Vec d) :
    Book.Ch03.CubeSolution (originCube d k) a :=
  let v := finiteAffineGradientResidual a hkm u e
  let w := finiteCubeSolutionRestriction a hkm
    (finiteAffineCubeSolution a m p)
  AHarmonicFunction.subOfIntegrable v w
    (cubeSolution_weakFluxIntegrable_finiteAffineGradientResidual v)
    (cubeSolution_weakFluxIntegrable_finiteAffineGradientResidual w)

/-- The updated residual has the literal value representative
`u - w_m(e) - w_m(p)`. -/
@[simp] theorem finiteAffineGradientUpdatedResidual_toFun
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k m : ℤ} (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e p : Vec d) :
    (finiteAffineGradientUpdatedResidual a hkm u e p).toH1.toFun =
      fun x ↦ u.toH1.toFun x -
        (finiteAffineSolution a m e).toH1.toFun x -
        (finiteAffineSolution a m p).toH1.toFun x := by
  simp only [finiteAffineGradientUpdatedResidual,
    AHarmonicFunction.toH1_subOfIntegrable, H1Function.sub_toFun,
    finiteAffineGradientResidual_toFun, finiteCubeSolutionRestriction_toFun,
    finiteAffineCubeSolution]

/-- The updated residual has gradient `∇u - ∇w_m(e) - ∇w_m(p)`. -/
@[simp] theorem finiteAffineGradientUpdatedResidual_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k m : ℤ} (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e p : Vec d) :
    (finiteAffineGradientUpdatedResidual a hkm u e p).toH1.grad =
      fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a m e).toH1.grad x -
        (finiteAffineSolution a m p).toH1.grad x := by
  unfold finiteAffineGradientUpdatedResidual
  rw [AHarmonicFunction.grad_subOfIntegrable]
  simp only [finiteAffineGradientResidual_grad,
    finiteCubeSolutionRestriction_grad, finiteAffineCubeSolution]
  funext x
  rfl

/-- Updating an outer affine residual is, in weighted gradient norm, the same
as updating its outer boundary slope by addition. -/
theorem weightedGradNorm_finiteAffineGradientUpdatedResidual
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j k m : ℤ} (hjk : j ≤ k) (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e p : Vec d) :
    weightedGradNorm
        (a.coeffOn (originCube d j)).toCoeffField
        (openCubeSet (originCube d j))
        (finiteCubeSolutionRestriction a hjk
          (finiteAffineGradientUpdatedResidual a hkm u e p)).toH1.grad =
      weightedGradNorm
        (a.coeffOn (originCube d j)).toCoeffField
        (openCubeSet (originCube d j))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a m (e + p)).toH1.grad x) := by
  apply weightedGradNorm_congr_ae
  have hsub : openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m) :=
    openCubeSet_originCube_subset_of_le (hjk.trans hkm)
  have hadd := finiteAffineSolution_grad_add a m e p
  have hadd' := ae_mono
    (Measure.restrict_mono hsub (le_refl volume)) hadd
  filter_upwards [hadd'] with x hx
  simp only [finiteCubeSolutionRestriction_grad,
    finiteAffineGradientUpdatedResidual_grad]
  rw [hx]
  abel

/-- Every updated outer residual gives a candidate upper bound for the
original solution's gradient excess. -/
theorem finiteAffineGradientExcess_le_updatedResidualEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j k m : ℤ} (hjk : j ≤ k) (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e p : Vec d) :
    finiteAffineGradientExcess a j m u ≤
      ENNReal.ofReal
        (Book.Ch03.h1EnergyNormOnCube (originCube d j) a
          (finiteCubeSolutionRestriction a hjk
            (finiteAffineGradientUpdatedResidual a hkm u e p)).toH1) := by
  calc
    finiteAffineGradientExcess a j m u ≤
        weightedGradNorm
          (a.coeffOn (originCube d j)).toCoeffField
          (openCubeSet (originCube d j))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m (e + p)).toH1.grad x) :=
      finiteAffineGradientExcess_le a j m u (e + p)
    _ = weightedGradNorm
          (a.coeffOn (originCube d j)).toCoeffField
          (openCubeSet (originCube d j))
          (finiteCubeSolutionRestriction a hjk
            (finiteAffineGradientUpdatedResidual a hkm u e p)).toH1.grad :=
      (weightedGradNorm_finiteAffineGradientUpdatedResidual
        a hjk hkm u e p).symm
    _ = ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d j) a
            (finiteCubeSolutionRestriction a hjk
              (finiteAffineGradientUpdatedResidual a hkm u e p)).toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube _ _ _

/-- A pointwise contraction for every affine residual descends to the
canonical infimum without assuming that the infimum is attained. -/
theorem finiteAffineGradientExcess_le_mul_of_forall_candidate
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {j k m : ℤ} (u : Book.Ch03.CubeSolution (originCube d m) a)
    (q : ℝ≥0∞) (hq_zero : q ≠ 0) (hq_top : q ≠ ∞)
    (hpointwise : ∀ e : Vec d,
      finiteAffineGradientExcess a j m u ≤
        q * weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x)) :
    finiteAffineGradientExcess a j m u ≤
      q * finiteAffineGradientExcess a k m u := by
  change finiteAffineGradientExcess a j m u ≤ q * (⨅ e : Vec d,
    weightedGradNorm
      (a.coeffOn (originCube d k)).toCoeffField
      (openCubeSet (originCube d k))
      (fun x ↦ u.toH1.grad x -
        (finiteAffineSolution a m e).toH1.grad x))
  rw [ENNReal.mul_iInf_of_ne hq_zero hq_top]
  exact le_iInf hpointwise

end

end HighContrast
end HCPolySupport
