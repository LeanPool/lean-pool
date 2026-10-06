/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeMap
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitz
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodMax

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineBestFitInduction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine best-fit induction

This module develops the pre-inverse best-fit error and forward-slope
estimates used in the finite flatness argument.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open CubeCalderonZygmund
open scoped ENNReal

noncomputable section

/-- Normalized error of the canonical best affine fit to the finite solution
posed on `Q_m`, measured on the inner cube `Q_k`. -/
@[expose]
noncomputable def finiteAffineBestFitError
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) : ℝ :=
  normalizedAffineCandidateError (originCube d k)
    (finiteAffineSolution a m b).toH1.toFun
    (finiteAffineBestFitIntercept a k m hkm b)
    (finiteAffineBestFitSlope a k m hkm b)

/-- Canonical finite affine best-fit errors are nonnegative. -/
theorem finiteAffineBestFitError_nonneg
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) :
    0 ≤ finiteAffineBestFitError a k m hkm b :=
  normalizedAffineCandidateError_nonneg _ _ _ _

theorem finiteAffineBestFitError_congr_index
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k l m : ℤ} (hkl : k = l) (hk : k ≤ m) (hl : l ≤ m) (b : Vec d) :
    finiteAffineBestFitError a k m hk b =
      finiteAffineBestFitError a l m hl b := by
  subst l
  rfl

theorem finiteAffineBestFitSlope_congr_index
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {k l m : ℤ} (hkl : k = l) (hk : k ≤ m) (hl : l ≤ m) (b : Vec d) :
    finiteAffineBestFitSlope a k m hk b =
      finiteAffineBestFitSlope a l m hl b := by
  subst l
  rfl

/-- The canonical best-fit error is no larger than the error of any affine
candidate on the same cube. -/
theorem finiteAffineBestFitError_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) (c : ℝ) (e : Vec d) :
    finiteAffineBestFitError a k m hkm b ≤
      normalizedAffineCandidateError (originCube d k)
        (finiteAffineSolution a m b).toH1.toFun c e := by
  exact normalizedAffineCandidateError_finiteAffineBestFit_le
    a k m hkm b c e

/-- The generic centered-cube best-fit row agrees with the canonical finite
affine best fit when the cube solution carries affine boundary slope `b`. -/
theorem finiteCenteredCubeBestFitError_finiteAffineCubeSolution_of_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) :
    finiteCenteredCubeBestFitErrorAt a m
        (finiteAffineCubeSolution a m b) k hkm =
      finiteAffineBestFitError a k m hkm b := by
  apply le_antisymm
  · simpa only [finiteAffineBestFitError, finiteAffineCubeSolution] using
      finiteCenteredCubeBestFitErrorAt_le a m
        (finiteAffineCubeSolution a m b) k hkm
        (finiteAffineBestFitIntercept a k m hkm b)
        (finiteAffineBestFitSlope a k m hkm b)
  · obtain ⟨c, e, heq⟩ :=
      finiteCenteredCubeBestFitErrorAt_exists_eq a m
        (finiteAffineCubeSolution a m b) k hkm
    rw [heq]
    simpa only [finiteAffineCubeSolution] using
      finiteAffineBestFitError_le a k m hkm b c e

/-- The canonical finite-affine best-fit errors satisfy the fixed-step
contraction supplied by the finite Lipschitz core. -/
theorem exists_finiteAffineBestFitOneStepConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (b : Vec d)
        (k : ℤ) (hkm : k ≤ m),
        finiteAffineBestFitError a (k - (N : ℤ)) m (by omega) b ≤
          (1 / 8 : ℝ) * finiteAffineBestFitError a k m hkm b +
            C * scalarIdentityWeakError a s k *
              finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) k := by
  obtain ⟨N, hN, C, hC, hstep⟩ :=
    exists_scalarIdentityFiniteBestFitOneStepConstant d s hs hs_lt
  refine ⟨N, hN, C, hC, ?_⟩
  intro a m b k hkm
  have h := hstep a m (finiteAffineCubeSolution a m b) k hkm
  rw [finiteCenteredCubeBestFitError_finiteAffineCubeSolution_of_le
      a (k - (N : ℤ)) m (by omega) b,
    finiteCenteredCubeBestFitError_finiteAffineCubeSolution_of_le
      a k m hkm b] at h
  exact h

private theorem normalizedAffineCandidateError_finiteAffineSolution_zero_boundary_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (b : Vec d) :
    normalizedAffineCandidateError (originCube d m)
        (finiteAffineSolution a m b).toH1.toFun 0 b =
      cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (fun x ↦ (finiteAffineCorrection a m b).toH1Function.toFun x) := by
  unfold normalizedAffineCandidateError normalizedCubeL2Distance
  rw [finiteAffineSolution_toH1]
  simp only [H1Function.add_toFun, finiteAffineBoundaryH1_toFun,
    zero_add]
  congr 2
  funext x
  ring

private theorem cubeBesovScaleWeight_one_originCube_sub_nat
    {d : ℕ} (k : ℤ) (N : ℕ) :
    cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) =
      (3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ]
      have hindex : k - (N : ℤ) - 1 = k - ((N : ℤ) + 1) := by ring
      rw [← hindex]
      have hone :
          cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ) - 1)) =
            3 * cubeBesovScaleWeight 1 (originCube d (k - (N : ℤ))) := by
        unfold cubeBesovScaleWeight
        rw [Real.rpow_neg_one, Real.rpow_neg_one]
        change ((3 : ℝ) ^ (k - (N : ℤ) - 1))⁻¹ =
          3 * ((3 : ℝ) ^ (k - (N : ℤ)))⁻¹
        rw [show k - (N : ℤ) = (k - (N : ℤ) - 1) + 1 by ring]
        rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
        field_simp
        ring_nf
      rw [hone, ih]
      ring

private theorem cubeLpNorm_originCube_sub_nat_le
    {d : ℕ} (k : ℤ) (N : ℕ) (f : Vec d → ℝ)
    (hmem : MemLp f (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    cubeLpNorm (originCube d (k - (N : ℤ))) (2 : ℝ≥0∞) f ≤
      (((3 ^ d) ^ N : ℕ) : ℝ) *
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞) f := by
  have hraw :=
    CubeCalderonZygmund.eLpNorm_centralDescendant_le_descendantCount_mul
      (originCube d k) N FiniteLpExponent.two f
  rw [centralDescendant_originCube_eq_originCube_sub] at hraw
  have htop :
      ENNReal.ofReal (((3 ^ d) ^ N : ℕ) : ℝ) *
          eLpNorm f 2 (normalizedCubeMeasure (originCube d k)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop hraw
  simpa [cubeLpNorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal,
    Nat.cast_nonneg] using hreal

private theorem normalizedAffineCandidateError_originCube_sub_nat_le
    {d : ℕ} (k : ℤ) (N : ℕ) (f : Vec d → ℝ) (c : ℝ) (e : Vec d)
    (hmem : MemLp (fun x ↦ f x - (c + vecDot e x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k))) :
    normalizedAffineCandidateError (originCube d (k - (N : ℤ))) f c e ≤
      ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
        normalizedAffineCandidateError (originCube d k) f c e := by
  unfold normalizedAffineCandidateError normalizedCubeL2Distance
  rw [cubeBesovScaleWeight_one_originCube_sub_nat]
  calc
    ((3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k)) *
          cubeLpNorm (originCube d (k - (N : ℤ))) (2 : ℝ≥0∞)
            (fun x ↦ f x - (c + vecDot e x)) ≤
        ((3 : ℝ) ^ N * cubeBesovScaleWeight 1 (originCube d k)) *
          ((((3 ^ d) ^ N : ℕ) : ℝ) *
            cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
              (fun x ↦ f x - (c + vecDot e x))) :=
      mul_le_mul_of_nonneg_left
        (cubeLpNorm_originCube_sub_nat_le k N _ hmem)
        (mul_nonneg (by positivity) (cubeBesovScaleWeight_nonneg 1 _))
    _ = ((3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)) *
          (cubeBesovScaleWeight 1 (originCube d k) *
            cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
              (fun x ↦ f x - (c + vecDot e x))) := by ring

private theorem normalizedAffineCandidateError_zero_sub_le_add
    {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ)
    (c₁ c₂ : ℝ) (e₁ e₂ : Vec d)
    (h₁ : MemLp (fun x ↦ f x - (c₁ + vecDot e₁ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q))
    (h₂ : MemLp (fun x ↦ f x - (c₂ + vecDot e₂ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    normalizedAffineCandidateError Q (fun _ ↦ 0) (c₁ - c₂) (e₁ - e₂) ≤
      normalizedAffineCandidateError Q f c₁ e₁ +
        normalizedAffineCandidateError Q f c₂ e₂ := by
  let r₁ : Vec d → ℝ := fun x ↦ f x - (c₁ + vecDot e₁ x)
  let r₂ : Vec d → ℝ := fun x ↦ f x - (c₂ + vecDot e₂ x)
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
            (fun x ↦ 0 - ((c₁ - c₂) + vecDot (e₁ - e₂) x)) =
        cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) (r₁ + -r₂) := by
      congr 2
      funext x
      dsimp [r₁, r₂]
      rw [vecDot_sub_left]
      ring
    _ ≤ cubeBesovScaleWeight 1 Q *
          (cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
            cubeLpNorm Q (2 : ℝ≥0∞) r₂) :=
      mul_le_mul_of_nonneg_left htri hweight
    _ = cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
          cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by ring

private theorem originCubeAffineH1LinearMap_weakPoisson
    (d : ℕ) [NeZero d] (k : ℤ) (p : AffineCoefficients d) :
    WeakPoissonEquationOn (openCubeSet (originCube d k))
      (originCubeAffineH1LinearMap d k p) (fun _ ↦ 0) := by
  intro phi hphi hcompact hsupport
  let psi : H10Function (openCubeSet (originCube d k)) :=
    H10Function.ofContDiff (isOpen_openCubeSet (originCube d k))
      hphi hcompact hsupport
  have hpsiGrad : psi.toH1Function.grad = euclideanGradient phi := rfl
  have hzero := integral_vecDot_const_zeroTraceGrad_eq_zero psi p.2
  simpa only [originCubeAffineH1LinearMap_grad, hpsiGrad, zero_mul,
    integral_zero] using hzero

theorem exists_originCubeAffineSlopeErrorConstant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (c : ℝ) (e : Vec d),
      euclideanNorm e ≤ C *
        normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0) c e := by
  obtain ⟨C, hC, hCbound⟩ :=
    CubeCalderonZygmund.exists_harmonic_centralChild_euclideanGradient_cubeLpNorm_le d
  refine ⟨C, hC, ?_⟩
  intro k c e
  let v : H1Function (openCubeSet (originCube d k)) :=
    originCubeAffineH1LinearMap d k (-c, -e)
  have hv : WeakPoissonEquationOn (openCubeSet (originCube d k)) v (fun _ ↦ 0) := by
    simpa only [v] using originCubeAffineH1LinearMap_weakPoisson d k (-c, -e)
  have hbound := hCbound (originCube d k) v hv
  have hleft : cubeLpNorm
        (CubeCalderonZygmund.centralChild (originCube d k)) (2 : ℝ≥0∞)
        (fun x ↦ euclideanNorm (v.grad x)) = euclideanNorm e := by
    rw [show v.grad = fun _ ↦ -e by
      simpa only [v] using originCubeAffineH1LinearMap_grad d k (-c, -e)]
    rw [cubeLpNorm_const _ _ (euclideanNorm (-e)) (by norm_num)]
    simp only [Real.norm_of_nonneg (euclideanNorm_nonneg _), euclideanNorm_neg]
  have hright :
      (cubeScaleFactor (originCube d k))⁻¹ *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞) v.toFun =
        normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0) c e := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
    rw [show v.toFun = fun x ↦ -(c + vecDot e x) by
      funext x
      dsimp only [v]
      change (originCubeAffineH1LinearMap d k (-c, -e)).toFun x =
        -(c + vecDot e x)
      rw [congrFun (originCubeAffineH1LinearMap_toFun d k (-c, -e)) x]
      rw [vecDot_neg_left]
      ring]
    congr 2
    · unfold cubeBesovScaleWeight
      rw [Real.rpow_neg_one]
    · funext x
      ring
  rw [← hleft, ← hright]
  simpa only [mul_assoc] using hbound

private theorem finiteAffineBestFitResidual_memLp
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) :
    MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (finiteAffineBestFitIntercept a k m hkm b +
          vecDot (finiteAffineBestFitSlope a k m hkm b) x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
  let uk := finiteAffineSolutionInnerH1 a k m hkm b
  let p : AffineCoefficients d :=
    (finiteAffineBestFitIntercept a k m hkm b,
      finiteAffineBestFitSlope a k m hkm b)
  let v : H1Function (openCubeSet (originCube d k)) :=
    uk - originCubeAffineH1LinearMap d k p
  have hv := v.memL2_normalizedCubeMeasure
  simpa only [v, p, H1Function.sub_toFun, finiteAffineSolutionInnerH1_toFun,
    originCubeAffineH1LinearMap_toFun] using! hv

/-- Best-fit slopes on adjacent centered cubes differ by at most a
dimension-only multiple of the outer best-fit error. -/
theorem exists_finiteAffineBestFitAdjacentSlopeConstant
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k m : ℤ)
        (hkm : k + 1 ≤ m) (b : Vec d),
        euclideanNorm
            (finiteAffineBestFitSlope a k m (by omega) b -
              finiteAffineBestFitSlope a (k + 1) m hkm b) ≤
          C * finiteAffineBestFitError a (k + 1) m hkm b := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_originCubeAffineSlopeErrorConstant d
  let A : ℝ := 3 * ((3 ^ d : ℕ) : ℝ)
  let C : ℝ := C₀ * (1 + 2 * A)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := mul_pos hC₀ (by linarith only [hA])
  refine ⟨C, hC, ?_⟩
  intro a k m hkm b
  let hk : k ≤ m := by omega
  let c₀ := finiteAffineBestFitIntercept a k m hk b
  let e₀ := finiteAffineBestFitSlope a k m hk b
  let c₁ := finiteAffineBestFitIntercept a (k + 1) m hkm b
  let e₁ := finiteAffineBestFitSlope a (k + 1) m hkm b
  let E₁ := finiteAffineBestFitError a (k + 1) m hkm b
  have hres₀ : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (c₀ + vecDot e₀ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) := by
    simpa only [c₀, e₀] using finiteAffineBestFitResidual_memLp a k m hk b
  have hres₁Outer : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (c₁ + vecDot e₁ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (k + 1))) := by
    simpa only [c₁, e₁] using
      finiteAffineBestFitResidual_memLp a (k + 1) m hkm b
  have hres₁ : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (c₁ + vecDot e₁ x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d (k + 1)) 1 hres₁Outer
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    change MemLp _ (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d (k + 1 - (1 : ℤ)))) at h
    rw [show k + 1 - (1 : ℤ) = k by ring] at h
    exact h
  have houter :
      normalizedAffineCandidateError (originCube d k)
          (finiteAffineSolution a m b).toH1.toFun c₁ e₁ ≤ A * E₁ := by
    have h := normalizedAffineCandidateError_originCube_sub_nat_le
      (d := d) (k + 1) 1 (finiteAffineSolution a m b).toH1.toFun c₁ e₁
      hres₁Outer
    change normalizedAffineCandidateError (originCube d (k + 1 - (1 : ℤ)))
        (finiteAffineSolution a m b).toH1.toFun c₁ e₁ ≤
      ((3 : ℝ) ^ 1 * (((3 ^ d) ^ 1 : ℕ) : ℝ)) *
        normalizedAffineCandidateError (originCube d (k + 1))
          (finiteAffineSolution a m b).toH1.toFun c₁ e₁ at h
    rw [show k + 1 - (1 : ℤ) = k by ring] at h
    simpa only [A, E₁, c₁, e₁, finiteAffineBestFitError, pow_one] using h
  have hbest₀ :
      normalizedAffineCandidateError (originCube d k)
          (finiteAffineSolution a m b).toH1.toFun c₀ e₀ ≤ A * E₁ := by
    exact (finiteAffineBestFitError_le a k m hk b c₁ e₁).trans houter
  have htriangle :
      normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) ≤ 2 * A * E₁ := by
    calc
      normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) ≤
          normalizedAffineCandidateError (originCube d k)
              (finiteAffineSolution a m b).toH1.toFun c₀ e₀ +
            normalizedAffineCandidateError (originCube d k)
              (finiteAffineSolution a m b).toH1.toFun c₁ e₁ :=
        normalizedAffineCandidateError_zero_sub_le_add
          (originCube d k) (finiteAffineSolution a m b).toH1.toFun
          c₀ c₁ e₀ e₁ hres₀ hres₁
      _ ≤ A * E₁ + A * E₁ := add_le_add hbest₀ houter
      _ = 2 * A * E₁ := by ring
  have hslope := hC₀bound k (c₀ - c₁) (e₀ - e₁)
  have hE₁ : 0 ≤ E₁ := finiteAffineBestFitError_nonneg a (k + 1) m hkm b
  calc
    euclideanNorm
        (finiteAffineBestFitSlope a k m (by omega) b -
          finiteAffineBestFitSlope a (k + 1) m hkm b) =
        euclideanNorm (e₀ - e₁) := by rfl
    _ ≤ C₀ * normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - e₁) := hslope
    _ ≤ C₀ * (2 * A * E₁) :=
      mul_le_mul_of_nonneg_left htriangle hC₀.le
    _ ≤ C * E₁ := by
      have hfactor : C₀ * (2 * A) ≤ C := by
        dsimp [C]
        nlinarith only [hC₀.le, hA]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfactor hE₁
    _ = C * finiteAffineBestFitError a (k + 1) m hkm b := rfl

/-- At the terminal scale, the best-fit slope is close to the prescribed
boundary slope at response-error order. -/
theorem exists_finiteAffineBestFitTerminalSlopeConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (b : Vec d)
        (delta : ℝ), 0 ≤ delta → delta ≤ 1 →
          scalarIdentityWeakError a s m ≤ delta →
          euclideanNorm
              (finiteAffineBestFitSlope a m m (le_refl m) b - b) ≤
            C * delta * euclideanNorm b := by
  obtain ⟨Cr, hCr, hresponse⟩ :=
    exists_finiteAffineSolutionL2SlopeErrorEstimateConstant_at_error_order d s
      hs hs_lt
  obtain ⟨Cp, hCp, hp⟩ := exists_originCubeAffineSlopeErrorConstant d
  let C : ℝ := 1 + 4 * Cp * Cr
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a m b delta hdelta hdelta_one herr
  let R := normalizedAffineCandidateError (originCube d m)
    (finiteAffineSolution a m b).toH1.toFun 0 b
  let E := finiteAffineBestFitError a m m (le_refl m) b
  let c := finiteAffineBestFitIntercept a m m (le_refl m) b
  let p := finiteAffineBestFitSlope a m m (le_refl m) b
  have herr_nonneg : 0 ≤ scalarIdentityWeakError a s m :=
    scalarIdentityWeakError_nonneg a s m
  have htail : scalarIdentityWeakError a s m *
      (1 + scalarIdentityWeakError a s m) ≤ 2 * delta := by
    nlinarith only [herr_nonneg, herr, hdelta, hdelta_one]
  have hRraw := hresponse a m b
  have hR : R ≤ 2 * Cr * delta * euclideanNorm b := by
    rw [← normalizedAffineCandidateError_finiteAffineSolution_zero_boundary_eq]
      at hRraw
    calc
      R ≤ Cr * scalarIdentityWeakError a s m *
            (1 + scalarIdentityWeakError a s m) *
              euclideanNorm b := by simpa only [R] using hRraw
      _ = Cr * (scalarIdentityWeakError a s m *
            (1 + scalarIdentityWeakError a s m)) * euclideanNorm b := by ring_nf
      _ ≤ Cr * (2 * delta) * euclideanNorm b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htail hCr.le) (euclideanNorm_nonneg b)
      _ = 2 * Cr * delta * euclideanNorm b := by ring
  have hE : E ≤ R := finiteAffineBestFitError_le a m m (le_refl m) b 0 b
  have hresBest : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (c + vecDot p x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c, p] using
      finiteAffineBestFitResidual_memLp a m m (le_refl m) b
  have hresBoundary : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (0 + vecDot b x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    rw [finiteAffineSolution_toH1]
    simpa only [H1Function.add_toFun, finiteAffineBoundaryH1_toFun,
      zero_add, add_sub_cancel_left] using
      (finiteAffineCorrection a m b).toH1Function.memL2_normalizedCubeMeasure
  have htriangle := normalizedAffineCandidateError_zero_sub_le_add
    (originCube d m) (finiteAffineSolution a m b).toH1.toFun
    c 0 p b hresBest hresBoundary
  have hzero : normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
      (c - 0) (p - b) ≤ 4 * Cr * delta * euclideanNorm b := by
    calc
      normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c - 0) (p - b) ≤ E + R := by simpa only [E, R, c, p] using! htriangle
      _ ≤ R + R := add_le_add hE (le_refl R)
      _ ≤ 2 * (2 * Cr * delta * euclideanNorm b) := by
        nlinarith only [hR]
      _ = 4 * Cr * delta * euclideanNorm b := by ring
  have hslope := hp m (c - 0) (p - b)
  have hbound_nonneg : 0 ≤ delta * euclideanNorm b :=
    mul_nonneg hdelta (euclideanNorm_nonneg b)
  calc
    euclideanNorm
        (finiteAffineBestFitSlope a m m (le_refl m) b - b) =
        euclideanNorm (p - b) := rfl
    _ ≤ Cp * normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
        (c - 0) (p - b) := hslope
    _ ≤ Cp * (4 * Cr * delta * euclideanNorm b) :=
      mul_le_mul_of_nonneg_left hzero hCp.le
    _ = (4 * Cp * Cr) * (delta * euclideanNorm b) := by ring
    _ ≤ C * (delta * euclideanNorm b) :=
      mul_le_mul_of_nonneg_right (by
        dsimp [C]
        linarith only [hCr.le, hCp.le]) hbound_nonneg
    _ = C * delta * euclideanNorm b := by ring

/-- Two-scale Caccioppoli control specialized to the canonical best affine
fit of a finite affine-boundary solution. -/
theorem exists_finiteAffineBestFitCaccioppoliConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (b : Vec d)
        (k : ℤ) (hkm : k + 2 ≤ m),
        scalarIdentityWeakError a s (k + 2) ≤ 1 →
          finiteCenteredCubeSolutionEnergy a m
              (finiteAffineCubeSolution a m b) k ≤
            C * (finiteAffineBestFitError a (k + 2) m hkm b +
              euclideanNorm
                (finiteAffineBestFitSlope a (k + 2) m hkm b)) := by
  obtain ⟨C, hC, hcacc⟩ :=
    exists_scalarIdentityFiniteCaccioppoliAffineConstant d s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a m b k hkm herr
  let r : ℤ := k + 2
  let ur : Book.Ch03.CubeSolution (originCube d r) a :=
    finiteCubeSolutionRestriction a hkm (finiteAffineCubeSolution a m b)
  let c := finiteAffineBestFitIntercept a r m hkm b
  let p := finiteAffineBestFitSlope a r m hkm b
  have h := hcacc a r ur c p herr
  have henergy : finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k =
      finiteCenteredCubeSolutionEnergy a r ur k := by
    calc
      finiteCenteredCubeSolutionEnergy a m
          (finiteAffineCubeSolution a m b) k =
          Book.Ch03.h1EnergyNormOnCube (originCube d k) a
            (finiteCubeSolutionRestriction a (by omega : k ≤ m)
              (finiteAffineCubeSolution a m b)).toH1 :=
        finiteCenteredCubeSolutionEnergy_eq_of_le a m
          (finiteAffineCubeSolution a m b) k (by omega)
      _ = Book.Ch03.h1EnergyNormOnCube (originCube d k) a
          (finiteCubeSolutionRestriction a (by omega : k ≤ r) ur).toH1 := by
        unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
        simp only [ur, finiteAffineCubeSolution, finiteCubeSolutionRestriction_grad]
      _ = finiteCenteredCubeSolutionEnergy a r ur k :=
        (finiteCenteredCubeSolutionEnergy_eq_of_le a r ur k (by omega)).symm
  rw [henergy]
  simpa only [r, show k + 2 - 2 = k by ring, ur, c, p, finiteAffineCubeSolution,
    finiteCubeSolutionRestriction_toFun, finiteAffineBestFitError] using h

private theorem finiteForwardBound_two
    (p : ℕ → ℝ) (L : ℕ) (x : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hx : 0 ≤ x)
    (hsmall : (L : ℝ) * x ≤ 1 / 2)
    (hadj : ∀ q : ℕ, q < L →
      p (q + 1) ≤ p q + x * p (q + 1)) :
    ∀ q : ℕ, q ≤ L → p q ≤ 2 * p 0 := by
  have hweighted : ∀ q : ℕ, q ≤ L →
      (1 - (q : ℝ) * x) * p q ≤ p 0 := by
    intro q hq
    induction q with
    | zero => simp
    | succ q ih =>
        have hqL : q < L := by omega
        have hqle : q ≤ L := by omega
        have hqcast : (q : ℝ) ≤ L := by exact_mod_cast hqle
        have hfactor : 0 ≤ 1 - (q : ℝ) * x := by
          have : (q : ℝ) * x ≤ (L : ℝ) * x :=
            mul_le_mul_of_nonneg_right hqcast hx
          linarith only [this, hsmall]
        have honeStep : (1 - x) * p (q + 1) ≤ p q := by
          have ha := hadj q hqL
          nlinarith only [ha]
        calc
          (1 - ((q + 1 : ℕ) : ℝ) * x) *
                p (q + 1) ≤
              ((1 - (q : ℝ) * x) * (1 - x)) *
                p (q + 1) := by
            apply mul_le_mul_of_nonneg_right _ (hp _)
            calc
              1 - ((q + 1 : ℕ) : ℝ) * x =
                  (1 - (q : ℝ) * x) * (1 - x) - (q : ℝ) * x ^ 2 := by
                push_cast
                ring
              _ ≤ (1 - (q : ℝ) * x) * (1 - x) :=
                sub_le_self _ (mul_nonneg (Nat.cast_nonneg q) (sq_nonneg x))
          _ = (1 - (q : ℝ) * x) *
                ((1 - x) * p (q + 1)) := by ring
          _ ≤ (1 - (q : ℝ) * x) * p q :=
            mul_le_mul_of_nonneg_left honeStep hfactor
          _ ≤ p 0 := ih hqle
  intro q hq
  have hqcast : (q : ℝ) ≤ L := by exact_mod_cast hq
  have hqx : (q : ℝ) * x ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_right hqcast hx).trans hsmall
  have hw := hweighted q hq
  have hpq := hp q
  nlinarith only [hw, hqx, hpq]

private theorem euclideanNorm_le_add_sub
    {d : ℕ} (x y : Vec d) :
    euclideanNorm y ≤ euclideanNorm x + euclideanNorm (x - y) := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 y‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 (x - y)‖
  have h := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 (y - x))
  rw [← WithLp.toLp_add] at h
  have hsum : x + (y - x) = y := by abel
  rw [hsum] at h
  simpa only [show y - x = -(x - y) by abel, WithLp.toLp_neg, norm_neg] using h

/-- Uniform initialization of the best-fit error and slope throughout a
fixed terminal band. -/
theorem exists_finiteAffineBestFitTerminalBandConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (b : Vec d)
        (delta : ℝ) (k : ℤ), 0 ≤ delta → delta ≤ 1 →
          m - (N : ℤ) ≤ k → ∀ hkm : k ≤ m,
          scalarIdentityWeakError a s m ≤ delta →
          finiteAffineBestFitError a k m hkm b ≤
              C * delta * euclideanNorm b ∧
            euclideanNorm
                (finiteAffineBestFitSlope a k m hkm b - b) ≤
              C * delta * euclideanNorm b := by
  obtain ⟨Cr, hCr, hresponse⟩ :=
    exists_finiteAffineSolutionL2SlopeErrorEstimateConstant_at_error_order d s
      hs hs_lt
  obtain ⟨Cp, hCp, hp⟩ := exists_originCubeAffineSlopeErrorConstant d
  let B : ℝ := (3 : ℝ) ^ N * (((3 ^ d) ^ N : ℕ) : ℝ)
  let C : ℝ := 1 + 2 * B * Cr + 4 * Cp * B * Cr
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a m b delta k hdelta hdelta_one hband hkm herr
  let q : ℕ := Int.toNat (m - k)
  have hgap : 0 ≤ m - k := sub_nonneg.mpr hkm
  have hqcast : (q : ℤ) = m - k := Int.toNat_of_nonneg hgap
  have hqN : q ≤ N := by dsimp [q] at hqcast ⊢; omega
  have hfactor : (3 : ℝ) ^ q * (((3 ^ d) ^ q : ℕ) : ℝ) ≤ B := by
    dsimp [B]
    exact mul_le_mul
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hqN)
      (by exact_mod_cast Nat.pow_le_pow_right (by positivity : 0 < 3 ^ d) hqN)
      (by positivity) (by positivity)
  let Rm := normalizedAffineCandidateError (originCube d m)
    (finiteAffineSolution a m b).toH1.toFun 0 b
  let Rk := normalizedAffineCandidateError (originCube d k)
    (finiteAffineSolution a m b).toH1.toFun 0 b
  let E := finiteAffineBestFitError a k m hkm b
  let c := finiteAffineBestFitIntercept a k m hkm b
  let p := finiteAffineBestFitSlope a k m hkm b
  have herr_nonneg : 0 ≤ scalarIdentityWeakError a s m :=
    scalarIdentityWeakError_nonneg a s m
  have htail : scalarIdentityWeakError a s m *
      (1 + scalarIdentityWeakError a s m) ≤ 2 * delta := by
    nlinarith only [herr_nonneg, herr, hdelta, hdelta_one]
  have hRmraw := hresponse a m b
  have hRm : Rm ≤ 2 * Cr * delta * euclideanNorm b := by
    rw [← normalizedAffineCandidateError_finiteAffineSolution_zero_boundary_eq]
      at hRmraw
    calc
      Rm ≤ Cr * scalarIdentityWeakError a s m *
            (1 + scalarIdentityWeakError a s m) *
              euclideanNorm b := by simpa only [Rm] using hRmraw
      _ = Cr * (scalarIdentityWeakError a s m *
            (1 + scalarIdentityWeakError a s m)) * euclideanNorm b := by ring_nf
      _ ≤ Cr * (2 * delta) * euclideanNorm b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htail hCr.le) (euclideanNorm_nonneg b)
      _ = 2 * Cr * delta * euclideanNorm b := by ring
  have hresOuter : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (0 + vecDot b x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    rw [finiteAffineSolution_toH1]
    simpa only [H1Function.add_toFun, finiteAffineBoundaryH1_toFun,
      zero_add, add_sub_cancel_left] using
      (finiteAffineCorrection a m b).toH1Function.memL2_normalizedCubeMeasure
  have hrestrict := normalizedAffineCandidateError_originCube_sub_nat_le
    m q (finiteAffineSolution a m b).toH1.toFun 0 b hresOuter
  rw [show m - (q : ℤ) = k by omega] at hrestrict
  have hRk : Rk ≤ 2 * B * Cr * delta * euclideanNorm b := by
    calc
      Rk ≤ ((3 : ℝ) ^ q * (((3 ^ d) ^ q : ℕ) : ℝ)) * Rm := by
        simpa only [Rk, Rm] using hrestrict
      _ ≤ B * Rm := mul_le_mul_of_nonneg_right hfactor
        (normalizedAffineCandidateError_nonneg _ _ _ _)
      _ ≤ B * (2 * Cr * delta * euclideanNorm b) :=
        mul_le_mul_of_nonneg_left hRm hB
      _ = 2 * B * Cr * delta * euclideanNorm b := by ring
  have hE : E ≤ Rk := finiteAffineBestFitError_le a k m hkm b 0 b
  have hresBest : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (c + vecDot p x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) := by
    simpa only [c, p] using finiteAffineBestFitResidual_memLp a k m hkm b
  have hresBoundary : MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (0 + vecDot b x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d k)) := by
    have h := CubeCalderonZygmund.memLp_centralDescendant_of_memLp
      (Q := originCube d m) q hresOuter
    rw [centralDescendant_originCube_eq_originCube_sub] at h
    rwa [show m - (q : ℤ) = k by omega] at h
  have htriangle := normalizedAffineCandidateError_zero_sub_le_add
    (originCube d k) (finiteAffineSolution a m b).toH1.toFun
    c 0 p b hresBest hresBoundary
  have hzero : normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
      (c - 0) (p - b) ≤ 4 * B * Cr * delta * euclideanNorm b := by
    calc
      normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c - 0) (p - b) ≤ E + Rk := by simpa only [E, Rk, c, p] using! htriangle
      _ ≤ Rk + Rk := add_le_add hE (le_refl Rk)
      _ ≤ 2 * (2 * B * Cr * delta * euclideanNorm b) := by
        nlinarith only [hRk]
      _ = 4 * B * Cr * delta * euclideanNorm b := by ring
  have hslope := hp k (c - 0) (p - b)
  have hbound_nonneg : 0 ≤ delta * euclideanNorm b :=
    mul_nonneg hdelta (euclideanNorm_nonneg b)
  have hX : 0 ≤ 2 * B * Cr := by positivity
  have hY : 0 ≤ 4 * Cp * B * Cr := by positivity
  constructor
  · exact hE.trans (hRk.trans (by
      calc
        2 * B * Cr * delta * euclideanNorm b =
            (2 * B * Cr) * (delta * euclideanNorm b) := by ring
        _ ≤ C * (delta * euclideanNorm b) :=
          mul_le_mul_of_nonneg_right (by
            dsimp [C]
            linarith only [hX, hY]) hbound_nonneg
        _ = C * delta * euclideanNorm b := by ring))
  · calc
      euclideanNorm (finiteAffineBestFitSlope a k m hkm b - b) =
          euclideanNorm (p - b) := rfl
      _ ≤ Cp * normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
          (c - 0) (p - b) := hslope
      _ ≤ Cp * (4 * B * Cr * delta * euclideanNorm b) :=
        mul_le_mul_of_nonneg_left hzero hCp.le
      _ = (4 * Cp * B * Cr) * (delta * euclideanNorm b) := by ring
      _ ≤ C * (delta * euclideanNorm b) :=
        mul_le_mul_of_nonneg_right (by
          dsimp [C]
          linarith only [hX, hY]) hbound_nonneg
      _ = C * delta * euclideanNorm b := by ring

/-- A sufficiently small good-max row forces the canonical best-affine
error to be proportional to the current best-fit slope at every scale. -/
theorem exists_scalarIdentityFiniteAffineBestFitErrorInductionConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
            finiteAffineBestFitError a k m (Finset.mem_Icc.mp hk).2 b ≤
              C * delta * euclideanNorm
                (finiteAffineBestFitSlope a k m
                  (Finset.mem_Icc.mp hk).2 b) := by
  obtain ⟨N, hN, Cs, hCs, hstep⟩ :=
    exists_finiteAffineBestFitOneStepConstant d s hs hs_lt
  obtain ⟨Ca, hCa, hadj⟩ := exists_finiteAffineBestFitAdjacentSlopeConstant d
  obtain ⟨Cc, hCc, hcacc⟩ :=
    exists_finiteAffineBestFitCaccioppoliConstant d s hs hs_lt
  let L : ℕ := N + 2
  obtain ⟨Ct, hCt, hterminal⟩ :=
    exists_finiteAffineBestFitTerminalBandConstant d s hs hs_lt L
  let Z : ℝ := Cs * Cc
  let C : ℝ := 1 + 2 * Ct + 8 * Z
  let W : ℝ := (L : ℝ) * Ca * C
  let c : ℝ := min (1 / 2 : ℝ)
    (min ((2 * C)⁻¹) (min ((2 * Ct)⁻¹) ((2 * W)⁻¹)))
  have hZ : 0 < Z := mul_pos hCs hCc
  have hC : 1 ≤ C := by
    dsimp [C]
    have hCt' : 0 ≤ 2 * Ct := by positivity
    have hZ' : 0 ≤ 8 * Z := by positivity
    linarith only [hCt', hZ']
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hL : 0 < L := by dsimp [L]; omega
  have hW : 0 < W := by dsimp [W]; positivity
  have hcpos : 0 < c := by
    dsimp [c]
    repeat' apply lt_min
    · norm_num
    · exact inv_pos.mpr (mul_pos (by norm_num) hCpos)
    · exact inv_pos.mpr (mul_pos (by norm_num) hCt)
    · exact inv_pos.mpr (mul_pos (by norm_num) hW)
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood k hk b
  have hdelta_nonneg : 0 ≤ delta := hdelta.1.le
  have hdelta_one : delta ≤ 1 := by
    exact hdelta.2.trans ((min_le_left _ _).trans (by norm_num))
  have hdeltaC : C * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * C)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    calc
      C * delta ≤ C * (2 * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hCpos.le
      _ = 1 / 2 := by field_simp
  have hdeltaCt : Ct * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * Ct)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    calc
      Ct * delta ≤ Ct * (2 * Ct)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hCt.le
      _ = 1 / 2 := by field_simp
  have hdeltaW : W * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * W)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    calc
      W * delta ≤ W * (2 * W)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hW.le
      _ = 1 / 2 := by field_simp
  let total : ℕ := Int.toNat (m - n)
  have hind : ∀ q : ℕ, q ≤ total →
      ∀ (j : ℤ) (hjn : n ≤ j) (hjm : j ≤ m),
        Int.toNat (m - j) = q →
          finiteAffineBestFitError a j m hjm b ≤
            C * delta * euclideanNorm
              (finiteAffineBestFitSlope a j m hjm b) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hqtotal j hjn hjm hgapq
      by_cases hband : m - (L : ℤ) ≤ j
      · have herrm := hgood.weakError_le
          (Finset.mem_Icc.2 ⟨hnm.le, le_rfl⟩)
        obtain ⟨hE, hpj⟩ := hterminal a m b delta j
          hdelta_nonneg hdelta_one hband hjm herrm
        have hb : euclideanNorm b ≤ 2 * euclideanNorm
            (finiteAffineBestFitSlope a j m hjm b) := by
          have htri : euclideanNorm b ≤
              euclideanNorm (finiteAffineBestFitSlope a j m hjm b) +
                euclideanNorm
                  (finiteAffineBestFitSlope a j m hjm b - b) := by
            exact euclideanNorm_le_add_sub
              (finiteAffineBestFitSlope a j m hjm b) b
          have hsmall : Ct * delta * euclideanNorm b ≤
              (1 / 2 : ℝ) * euclideanNorm b :=
            mul_le_mul_of_nonneg_right hdeltaCt (euclideanNorm_nonneg b)
          nlinarith only [htri, hpj, hsmall, euclideanNorm_nonneg b,
            euclideanNorm_nonneg (finiteAffineBestFitSlope a j m hjm b)]
        calc
          finiteAffineBestFitError a j m hjm b ≤
              Ct * delta * euclideanNorm b := hE
          _ ≤ Ct * delta *
              (2 * euclideanNorm (finiteAffineBestFitSlope a j m hjm b)) :=
            mul_le_mul_of_nonneg_left hb
              (mul_nonneg hCt.le hdelta_nonneg)
          _ = (2 * Ct) * delta *
              euclideanNorm (finiteAffineBestFitSlope a j m hjm b) := by ring
          _ ≤ C * delta *
              euclideanNorm (finiteAffineBestFitSlope a j m hjm b) := by
            apply mul_le_mul_of_nonneg_right
            · apply mul_le_mul_of_nonneg_right _ hdelta_nonneg
              dsimp [C]
              have : 0 ≤ 8 * Z := by positivity
              linarith only [this]
            · exact euclideanNorm_nonneg _
      · have hjfar : j + (L : ℤ) ≤ m := by omega
        have hfuture : ∀ t : ℕ, 0 < t → t ≤ L →
            ∀ hjtm : j + (t : ℤ) ≤ m,
            finiteAffineBestFitError a (j + (t : ℤ)) m hjtm b ≤
              C * delta * euclideanNorm
                (finiteAffineBestFitSlope a (j + (t : ℤ)) m hjtm b) := by
          intro t ht htL hjtm
          let qt : ℕ := Int.toNat (m - (j + (t : ℤ)))
          have hjtn : n ≤ j + (t : ℤ) := by omega
          have hgap_nonneg : 0 ≤ m - j := sub_nonneg.mpr hjm
          have hgap_cast : (q : ℤ) = m - j := by
            rw [← hgapq]
            exact Int.toNat_of_nonneg hgap_nonneg
          have hqt_nonneg : 0 ≤ m - (j + (t : ℤ)) := sub_nonneg.mpr hjtm
          have hqt_cast : (qt : ℤ) = m - (j + (t : ℤ)) :=
            Int.toNat_of_nonneg hqt_nonneg
          have hqtq : qt < q := by
            omega
          have hqttotal : qt ≤ total := le_trans hqtq.le hqtotal
          exact ih qt hqtq hqttotal (j + (t : ℤ)) hjtn hjtm rfl
        let pseq : ℕ → ℝ := fun t ↦
          if ht : t ≤ L then
            euclideanNorm
              (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b)
          else 0
        have hpseq : ∀ t, 0 ≤ pseq t := by
          intro t
          by_cases ht : t ≤ L
          · simp only [pseq, dite_eq_left ht]
            exact euclideanNorm_nonneg _
          · simp only [pseq, dite_eq_right ht]
            exact le_rfl
        have hadjseq : ∀ t : ℕ, t < L →
            pseq (t + 1) ≤ pseq t + (Ca * C * delta) * pseq (t + 1) := by
          intro t ht
          have htL : t ≤ L := by omega
          have hsuccL : t + 1 ≤ L := by omega
          have hE := hfuture (t + 1) (by omega) hsuccL (by omega)
          have ha := hadj a (j + (t : ℤ)) m (by omega) b
          have hnorm : euclideanNorm
                (finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                  (by omega) b) ≤
              euclideanNorm
                (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b) +
              euclideanNorm
                (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b -
                  finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                    (by omega) b) := by
            exact euclideanNorm_le_add_sub
              (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b)
              (finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                (by omega) b)
          simp only [pseq, dite_eq_left htL, dite_eq_left hsuccL]
          calc
            euclideanNorm
                (finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                  (by omega) b) ≤
                euclideanNorm
                    (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b) +
                  euclideanNorm
                    (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b -
                      finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                        (by omega) b) := hnorm
            _ ≤ euclideanNorm
                    (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b) +
                  Ca * finiteAffineBestFitError a
                    (j + ((t + 1 : ℕ) : ℤ)) m (by omega) b :=
              add_le_add (le_refl _) (by
                simpa only [show j + (t : ℤ) + 1 =
                    j + ((t + 1 : ℕ) : ℤ) by push_cast; ring] using ha)
            _ ≤ euclideanNorm
                    (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b) +
                  Ca * (C * delta * euclideanNorm
                    (finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                      (by omega) b)) :=
              add_le_add (le_refl _)
                (mul_le_mul_of_nonneg_left hE hCa.le)
            _ = euclideanNorm
                    (finiteAffineBestFitSlope a (j + (t : ℤ)) m (by omega) b) +
                  (Ca * C * delta) * euclideanNorm
                    (finiteAffineBestFitSlope a (j + ((t + 1 : ℕ) : ℤ)) m
                      (by omega) b) := by ring
        have hx : 0 ≤ Ca * C * delta := by positivity
        have hwindow : (L : ℝ) * (Ca * C * delta) ≤ 1 / 2 := by
          dsimp [W] at hdeltaW
          nlinarith only [hdeltaW]
        have hpbound := finiteForwardBound_two pseq L (Ca * C * delta)
          hpseq hx hwindow hadjseq
        have hPN : euclideanNorm
            (finiteAffineBestFitSlope a (j + (N : ℤ)) m (by omega) b) ≤
              2 * euclideanNorm (finiteAffineBestFitSlope a j m hjm b) := by
          have := hpbound N (by dsimp [L]; omega)
          have hNL : N ≤ L := by dsimp [L]; omega
          simp only [pseq, dite_eq_left hNL, dite_eq_left (Nat.zero_le L), Nat.cast_zero] at this
          have hbase := congrArg euclideanNorm
            (finiteAffineBestFitSlope_congr_index a (by ring : j + (0 : ℤ) = j)
              (by omega) hjm b)
          rw [hbase] at this
          exact this
        have hPL : euclideanNorm
            (finiteAffineBestFitSlope a (j + (L : ℤ)) m (by omega) b) ≤
              2 * euclideanNorm (finiteAffineBestFitSlope a j m hjm b) := by
          have := hpbound L le_rfl
          simp only [pseq, dite_eq_left le_rfl, dite_eq_left (Nat.zero_le L), Nat.cast_zero]
            at this
          have hbase := congrArg euclideanNorm
            (finiteAffineBestFitSlope_congr_index a (by ring : j + (0 : ℤ) = j)
              (by omega) hjm b)
          rw [hbase] at this
          exact this
        have hEN := hfuture N hN (by dsimp [L]; omega) (by omega)
        have hEL := hfuture L (by dsimp [L]; omega) le_rfl hjfar
        have herrCacc : scalarIdentityWeakError a s (j + (N : ℤ) + 2) ≤ 1 :=
          (hgood.weakError_le (Finset.mem_Icc.2 ⟨by omega, by
            dsimp [L] at hjfar
            omega⟩)).trans hdelta_one
        have hD := hcacc a m b (j + (N : ℤ))
          (by dsimp [L] at hjfar; omega) herrCacc
        have hD' : finiteCenteredCubeSolutionEnergy a m
              (finiteAffineCubeSolution a m b) (j + (N : ℤ)) ≤
            4 * Cc * euclideanNorm
              (finiteAffineBestFitSlope a j m hjm b) := by
          calc
            finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) (j + (N : ℤ)) ≤
                Cc * (finiteAffineBestFitError a (j + (L : ℤ)) m
                    (by dsimp [L] at hjfar ⊢; omega) b +
                  euclideanNorm
                    (finiteAffineBestFitSlope a (j + (L : ℤ)) m
                      (by dsimp [L] at hjfar ⊢; omega) b)) := by
              simpa only [L, show j + (N : ℤ) + 2 = j + ((N + 2 : ℕ) : ℤ) by
                push_cast; ring] using hD
            _ ≤ Cc * ((C * delta) *
                  euclideanNorm
                    (finiteAffineBestFitSlope a (j + (L : ℤ)) m
                      (by omega) b) +
                euclideanNorm
                  (finiteAffineBestFitSlope a (j + (L : ℤ)) m
                    (by omega) b)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add hEL (le_refl _)) hCc.le
            _ ≤ Cc * ((1 / 2 : ℝ) *
                  (2 * euclideanNorm (finiteAffineBestFitSlope a j m hjm b)) +
                2 * euclideanNorm (finiteAffineBestFitSlope a j m hjm b)) := by
              apply mul_le_mul_of_nonneg_left _ hCc.le
              exact add_le_add
                (mul_le_mul hdeltaC hPL (euclideanNorm_nonneg _) (by norm_num)) hPL
            _ ≤ 4 * Cc * euclideanNorm
                (finiteAffineBestFitSlope a j m hjm b) := by
              ring_nf
              nlinarith only [hCc.le,
                euclideanNorm_nonneg (finiteAffineBestFitSlope a j m hjm b)]
        have herrStep : scalarIdentityWeakError a s (j + (N : ℤ)) ≤ delta :=
          hgood.weakError_le
          (Finset.mem_Icc.2 ⟨by omega, by dsimp [L] at hjfar; omega⟩)
        have hrec := hstep a m b (j + (N : ℤ)) (by omega)
        have hrec' : finiteAffineBestFitError a j m hjm b ≤
            (1 / 8 : ℝ) * finiteAffineBestFitError a (j + (N : ℤ)) m
                (by omega) b +
              Cs * delta * finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) (j + (N : ℤ)) := by
          have henergyNonneg : 0 ≤ finiteCenteredCubeSolutionEnergy a m
              (finiteAffineCubeSolution a m b) (j + (N : ℤ)) := by
            unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
            exact Real.sqrt_nonneg _
          calc
            finiteAffineBestFitError a j m hjm b =
                finiteAffineBestFitError a (j + (N : ℤ) - (N : ℤ)) m
                  (by omega) b :=
              (finiteAffineBestFitError_congr_index a
                (show j + (N : ℤ) - (N : ℤ) = j by ring)
                (by omega) hjm b).symm
            _ ≤ (1 / 8 : ℝ) * finiteAffineBestFitError a (j + (N : ℤ)) m
                  (by omega) b +
                Cs * scalarIdentityWeakError a s (j + (N : ℤ)) *
                  finiteCenteredCubeSolutionEnergy a m
                    (finiteAffineCubeSolution a m b) (j + (N : ℤ)) := hrec
            _ ≤ (1 / 8 : ℝ) * finiteAffineBestFitError a (j + (N : ℤ)) m
                  (by omega) b +
                Cs * delta * finiteCenteredCubeSolutionEnergy a m
                  (finiteAffineCubeSolution a m b) (j + (N : ℤ)) :=
              add_le_add (le_refl _)
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left herrStep hCs.le) henergyNonneg)
        calc
          finiteAffineBestFitError a j m hjm b ≤
              (1 / 8 : ℝ) * finiteAffineBestFitError a (j + (N : ℤ)) m
                  (by omega) b +
                Cs * delta * finiteCenteredCubeSolutionEnergy a m
                  (finiteAffineCubeSolution a m b) (j + (N : ℤ)) := hrec'
          _ ≤ (1 / 8 : ℝ) *
                  (C * delta * (2 * euclideanNorm
                    (finiteAffineBestFitSlope a j m hjm b))) +
                Cs * delta * (4 * Cc * euclideanNorm
                  (finiteAffineBestFitSlope a j m hjm b)) :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                (hEN.trans (mul_le_mul_of_nonneg_left hPN
                  (mul_nonneg hCpos.le hdelta_nonneg))) (by norm_num))
              (mul_le_mul_of_nonneg_left hD'
                (mul_nonneg hCs.le hdelta_nonneg))
          _ ≤ C * delta * euclideanNorm
                (finiteAffineBestFitSlope a j m hjm b) := by
            have hCZ : 8 * Z ≤ C := by
              dsimp [C]
              have : 0 ≤ 2 * Ct := by positivity
              linarith only [this]
            dsimp [Z] at hCZ
            have hnorm := euclideanNorm_nonneg
              (finiteAffineBestFitSlope a j m hjm b)
            have hcoeff : C / 4 + 4 * (Cs * Cc) ≤ C := by
              linarith only [hCZ, hCpos.le]
            calc
              (1 / 8 : ℝ) *
                    (C * delta * (2 * euclideanNorm
                      (finiteAffineBestFitSlope a j m hjm b))) +
                  Cs * delta * (4 * Cc * euclideanNorm
                    (finiteAffineBestFitSlope a j m hjm b)) =
                  (C / 4 + 4 * (Cs * Cc)) *
                    (delta * euclideanNorm
                      (finiteAffineBestFitSlope a j m hjm b)) := by ring
              _ ≤ C * (delta * euclideanNorm
                    (finiteAffineBestFitSlope a j m hjm b)) :=
                mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdelta_nonneg hnorm)
              _ = C * delta * euclideanNorm
                    (finiteAffineBestFitSlope a j m hjm b) := by ring
  have hkn := (Finset.mem_Icc.mp hk).1
  have hkm := (Finset.mem_Icc.mp hk).2
  let q : ℕ := Int.toNat (m - k)
  have hgap_nonneg : 0 ≤ m - k := sub_nonneg.mpr hkm
  have hqtotal : q ≤ total := by
    dsimp [q, total]
    exact Int.toNat_le_toNat (by omega)
  exact hind q hqtotal k hkn hkm rfl

end

end HighContrast
end HCPolySupport
