/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientResidual
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeFamily

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineGradientExcessStep

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# One-step finite affine gradient excess

This module assembles the ruled best-fit normalization with harmonic
residuals.  It first records the exact value-error bridge consumed by the
two-scale Caccioppoli estimate.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Restricting a solution and then taking its outer-scale best-fit error is
the same as taking the original solution's best-fit error on that inner
cube. -/
theorem finiteCenteredCubeBestFitErrorAt_restriction_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) :
    let uk := finiteCubeSolutionRestriction a hkm u
    finiteCenteredCubeBestFitErrorAt a k uk k (le_refl k) =
      finiteCenteredCubeBestFitErrorAt a m u k hkm := by
  dsimp only
  let uk := finiteCubeSolutionRestriction a hkm u
  let c₀ := finiteCenteredCubeBestFitInterceptAt a k uk k
  let p₀ := finiteCenteredCubeBestFitSlopeAt a k uk k
  let c₁ := finiteCenteredCubeBestFitInterceptAt a m u k
  let p₁ := finiteCenteredCubeBestFitSlopeAt a m u k
  apply le_antisymm
  · calc
      finiteCenteredCubeBestFitErrorAt a k uk k (le_refl k) ≤
          normalizedAffineCandidateError (originCube d k)
            uk.toH1.toFun c₁ p₁ :=
        finiteCenteredCubeBestFitErrorAt_le a k uk k (le_refl k) c₁ p₁
      _ = normalizedAffineCandidateError (originCube d k)
            u.toH1.toFun c₁ p₁ := by
        simp only [uk, finiteCubeSolutionRestriction_toFun]
      _ = finiteCenteredCubeBestFitErrorAt a m u k hkm := by
        simpa only [c₁, p₁] using
          (finiteCenteredCubeBestFitErrorAt_eq_candidate a m u k hkm).symm
  · calc
      finiteCenteredCubeBestFitErrorAt a m u k hkm ≤
          normalizedAffineCandidateError (originCube d k)
            u.toH1.toFun c₀ p₀ :=
        finiteCenteredCubeBestFitErrorAt_le a m u k hkm c₀ p₀
      _ = normalizedAffineCandidateError (originCube d k)
            uk.toH1.toFun c₀ p₀ := by
        simp only [uk, finiteCubeSolutionRestriction_toFun]
      _ = finiteCenteredCubeBestFitErrorAt a k uk k (le_refl k) := by
        simpa only [c₀, p₀] using
          (finiteCenteredCubeBestFitErrorAt_eq_candidate a k uk k
            (le_refl k)).symm

/-- The ruled finite-affine comparison turns the canonical affine best fit of
an arbitrary harmonic residual into a zero-slope affine candidate for the
updated residual. -/
theorem finiteAffineGradientUpdatedResidual_candidateError_le
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {delta C : ℝ} {n m : ℤ} {Q : ℤ → Mat d}
    (hfamily : IsFiniteAffineSlopeFamily a delta C n m Q)
    {r k : ℤ} (hr : r ∈ Finset.Icc n m) (hrk : r ≤ k) (hkm : k ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d) :
    let v := finiteAffineGradientResidual a hkm u e
    let vR := finiteCubeSolutionRestriction a hrk v
    let c := finiteCenteredCubeBestFitInterceptAt a r vR r
    let p := finiteCenteredCubeBestFitSlopeAt a r vR r
    let q := matVecMul (Q r) p
    let cQ := finiteAffineBestFitIntercept a r m
      (Finset.mem_Icc.mp hr).2 q
    normalizedAffineCandidateError (originCube d r)
        (finiteAffineGradientUpdatedResidual a
          (Finset.mem_Icc.mp hr).2 u e q).toH1.toFun
        (c - cQ) 0 ≤
      finiteCenteredCubeBestFitErrorAt a r vR r (le_refl r) +
        C * delta * euclideanNorm p := by
  dsimp only
  let v := finiteAffineGradientResidual a hkm u e
  let vR := finiteCubeSolutionRestriction a hrk v
  let c := finiteCenteredCubeBestFitInterceptAt a r vR r
  let p := finiteCenteredCubeBestFitSlopeAt a r vR r
  let q := matVecMul (Q r) p
  let cQ := finiteAffineBestFitIntercept a r m
    (Finset.mem_Icc.mp hr).2 q
  let ellV := originCubeAffineH1LinearMap d r (c, p)
  let wR := finiteAffineSolutionInnerH1 a r m
    (Finset.mem_Icc.mp hr).2 q
  let ellW := originCubeAffineH1LinearMap d r (cQ, p)
  have hvMem : MemLp (fun x ↦ v.toH1.toFun x - (c + vecDot p x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d r)) := by
    simpa only [vR, ellV, H1Function.sub_toFun,
      finiteCubeSolutionRestriction_toFun,
      originCubeAffineH1LinearMap_toFun] using
      (vR.toH1 - ellV).memL2_normalizedCubeMeasure
  have hwMem : MemLp
      (fun x ↦ (finiteAffineSolution a m q).toH1.toFun x -
        (cQ + vecDot p x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d r)) := by
    simpa only [wR, ellW, H1Function.sub_toFun,
      finiteAffineSolutionInnerH1_toFun,
      originCubeAffineH1LinearMap_toFun] using
      (wR - ellW).memL2_normalizedCubeMeasure
  have htriangle := normalizedAffineCandidateError_sub_le_add
    (originCube d r) v.toH1.toFun
      (finiteAffineSolution a m q).toH1.toFun c cQ p p hvMem hwMem
  have hbest : normalizedAffineCandidateError (originCube d r)
        v.toH1.toFun c p =
      finiteCenteredCubeBestFitErrorAt a r vR r (le_refl r) := by
    simpa only [v, vR, c, p] using!
      (finiteCenteredCubeBestFitErrorAt_eq_candidate a r vR r
        (le_refl r)).symm
  have hflat : normalizedAffineCandidateError (originCube d r)
        (finiteAffineSolution a m q).toH1.toFun cQ p ≤
      C * delta * euclideanNorm p := by
    simpa only [q, cQ] using hfamily.flatness_at r hr p
  calc
    normalizedAffineCandidateError (originCube d r)
        (finiteAffineGradientUpdatedResidual a
          (Finset.mem_Icc.mp hr).2 u e q).toH1.toFun
        (c - cQ) 0 =
      normalizedAffineCandidateError (originCube d r)
        (fun x ↦ v.toH1.toFun x -
          (finiteAffineSolution a m q).toH1.toFun x)
        (c - cQ) (p - p) := by
      simp only [v, finiteAffineGradientUpdatedResidual_toFun,
        finiteAffineGradientResidual_toFun, sub_self]
    _ ≤ normalizedAffineCandidateError (originCube d r)
          v.toH1.toFun c p +
        normalizedAffineCandidateError (originCube d r)
          (finiteAffineSolution a m q).toH1.toFun cQ p := htriangle
    _ ≤ finiteCenteredCubeBestFitErrorAt a r vR r (le_refl r) +
        C * delta * euclideanNorm p := by
      rw [hbest]
      exact add_le_add le_rfl hflat

/-- The source one-step argument, before taking the infimum over the incoming
outer slope.  The displayed multiplier keeps the four analytic constants
separate so the subsequent smallness choice is transparent. -/
private theorem exists_scalarIdentityFiniteAffineGradientExcessPointwiseStepConstants_of_bestFitStep
    (d : ℕ) [NeZero d] (s : ℝ)
    (N : ℕ) (hN : 0 < N) (theta Cs : ℝ) (htheta : 0 < theta) (hCs : 0 < Cs)
    (hstep : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
      (u : Book.Ch03.CubeSolution (originCube d m) a)
      (k : ℤ) (hkm : k ≤ m),
        finiteCenteredCubeBestFitErrorAt a m u (k - (N : ℤ)) (by omega) ≤
          theta * finiteCenteredCubeBestFitErrorAt a m u k hkm +
            Cs * scalarIdentityWeakError a s k *
              finiteCenteredCubeSolutionEnergy a m u k)
    (Cc Ce Ct : ℝ) (hCc : 0 < Cc) (hCe : 0 < Ce) (hCt : 0 < Ct)
    (hcacc : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
      (u : Book.Ch03.CubeSolution (originCube d k) a) (c : ℝ) (e : Vec d),
      scalarIdentityWeakError a s k ≤ 1 →
        finiteCenteredCubeSolutionEnergy a k u (k - 2) ≤
          Cc * (normalizedAffineCandidateError (originCube d k)
            u.toH1.toFun c e + euclideanNorm e))
    (herror : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
      (u : Book.Ch03.CubeSolution (originCube d k) a),
      scalarIdentityWeakError a s k ≤ 1 →
        finiteCenteredCubeBestFitErrorAt a k u k (le_refl k) ≤
          Ce * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1)
    (hslope : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
      (u : Book.Ch03.CubeSolution (originCube d k) a),
      scalarIdentityWeakError a s k ≤ 1 →
        euclideanNorm (finiteCenteredCubeBestFitSlopeAt a k u k) ≤
          Ct * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1) :
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta C : ℝ)
        (n m : ℤ) (Q : ℤ → Mat d),
        0 ≤ delta → 1 ≤ C →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          IsFiniteAffineSlopeFamily a delta C n m Q →
          ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m)
            (_hr : k - (N : ℤ) ∈ Finset.Icc n m)
            (u : Book.Ch03.CubeSolution (originCube d m) a) (e : Vec d),
            finiteAffineGradientExcess a (k - (N : ℤ) - 2) m u ≤
              ENNReal.ofReal
                (Cc * (theta * Ce + Cs * delta +
                  C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ)))) *
                weightedGradNorm
                  (a.coeffOn (originCube d k)).toCoeffField
                  (openCubeSet (originCube d k))
                  (fun x ↦ u.toH1.grad x -
                    (finiteAffineSolution a m e).toH1.grad x) := by
  intro a delta C n m Q hdelta hC hgood hfamily k hk hr u e
  let r : ℤ := k - (N : ℤ)
  have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
  have hrm : r ≤ m := (Finset.mem_Icc.mp hr).2
  have hrk : r ≤ k := by dsimp [r]; omega
  let v := finiteAffineGradientResidual a hkm u e
  let vR := finiteCubeSolutionRestriction a hrk v
  let c := finiteCenteredCubeBestFitInterceptAt a r vR r
  let p := finiteCenteredCubeBestFitSlopeAt a r vR r
  let q := matVecMul (Q r) p
  let cQ := finiteAffineBestFitIntercept a r m hrm q
  let z := finiteAffineGradientUpdatedResidual a hrm u e q
  let D := Book.Ch03.h1EnergyNormOnCube (originCube d k) a v.toH1
  let Dr := Book.Ch03.h1EnergyNormOnCube (originCube d r) a vR.toH1
  let Ek := finiteCenteredCubeBestFitErrorAt a k v k (le_refl k)
  let Er := finiteCenteredCubeBestFitErrorAt a r vR r (le_refl r)
  let A : ℝ := ((((3 ^ d) ^ N : ℕ) : ℝ))
  let B : ℝ := Cc * (theta * Ce + Cs * delta +
    C * delta * Ct * A)
  have hdelta_one : delta ≤ 1 := by
    have hmul : delta ≤ C * delta := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hdelta
    exact hmul.trans (hfamily.small.trans (by norm_num))
  have hweakK : scalarIdentityWeakError a s k ≤ delta :=
    hgood.weakError_le hk
  have hweakR : scalarIdentityWeakError a s r ≤ delta :=
    hgood.weakError_le hr
  have hweakK_one : scalarIdentityWeakError a s k ≤ 1 :=
    hweakK.trans hdelta_one
  have hweakR_one : scalarIdentityWeakError a s r ≤ 1 :=
    hweakR.trans hdelta_one
  have hD : 0 ≤ D := by
    dsimp [D, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hDr : 0 ≤ Dr := by
    dsimp [Dr, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hEk : Ek ≤ Ce * D := by
    simpa only [Ek, D, v] using herror a k v hweakK_one
  have henergySelf : finiteCenteredCubeSolutionEnergy a k v k = D := by
    rw [finiteCenteredCubeSolutionEnergy_eq_of_le a k v k (le_refl k)]
    dsimp [D]
    unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
    simp only [finiteCubeSolutionRestriction_grad]
  have hstepRaw := hstep a k v k (le_refl k)
  rw [henergySelf] at hstepRaw
  have hstep' : finiteCenteredCubeBestFitErrorAt a k v r hrk ≤
      theta * Ek + Cs * delta * D := by
    calc
      finiteCenteredCubeBestFitErrorAt a k v r hrk =
          finiteCenteredCubeBestFitErrorAt a k v
            (k - (N : ℤ)) (by omega) := by
        congr 2
      _ ≤ theta * Ek +
          Cs * scalarIdentityWeakError a s k * D := by
        simpa only [Ek, D, finiteCenteredCubeSolutionEnergy_eq_of_le,
          v] using hstepRaw
      _ ≤ theta * Ek + Cs * delta * D := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hweakK hCs.le) hD)
  have hEr_eq : Er = finiteCenteredCubeBestFitErrorAt a k v r hrk := by
    simpa only [Er, vR, v] using
      finiteCenteredCubeBestFitErrorAt_restriction_eq a k v r hrk
  have hEr : Er ≤ (theta * Ce + Cs * delta) * D := by
    rw [hEr_eq]
    calc
      finiteCenteredCubeBestFitErrorAt a k v r hrk ≤
          theta * Ek + Cs * delta * D := hstep'
      _ ≤ theta * (Ce * D) + Cs * delta * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left hEk htheta.le) le_rfl
      _ = (theta * Ce + Cs * delta) * D := by ring
  have hDr_le : Dr ≤ A * D := by
    simpa only [Dr, D, A, r, vR, v] using
      h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_nat_le
        a k N v
  have hp : euclideanNorm p ≤ Ct * Dr := by
    simpa only [p, vR] using hslope a r vR hweakR_one
  have hpD : euclideanNorm p ≤ Ct * A * D := by
    calc
      euclideanNorm p ≤ Ct * Dr := hp
      _ ≤ Ct * (A * D) := mul_le_mul_of_nonneg_left hDr_le hCt.le
      _ = Ct * A * D := by ring
  have hcandidate := finiteAffineGradientUpdatedResidual_candidateError_le
    hfamily hr hrk hkm u e
  have hcandidate' : normalizedAffineCandidateError (originCube d r)
        z.toH1.toFun (c - cQ) 0 ≤
      ((theta * Ce + Cs * delta) + C * delta * Ct * A) * D := by
    calc
      normalizedAffineCandidateError (originCube d r)
          z.toH1.toFun (c - cQ) 0 ≤ Er + C * delta * euclideanNorm p := by
        simpa only [r, v, vR, c, p, q, cQ, z, Er] using hcandidate
      _ ≤ (theta * Ce + Cs * delta) * D +
          C * delta * (Ct * A * D) := by
        exact add_le_add hEr
          (mul_le_mul_of_nonneg_left hpD
            (mul_nonneg (zero_le_one.trans hC) hdelta))
      _ = ((theta * Ce + Cs * delta) +
          C * delta * Ct * A) * D := by ring
  have hcaccRaw := hcacc a r z (c - cQ) 0 hweakR_one
  have hcacc' : Book.Ch03.h1EnergyNormOnCube (originCube d (r - 2)) a
        (finiteCubeSolutionRestriction a (by omega : r - 2 ≤ r) z).toH1 ≤
      B * D := by
    rw [finiteCenteredCubeSolutionEnergy_eq_of_le a r z (r - 2) (by omega)] at hcaccRaw
    calc
      Book.Ch03.h1EnergyNormOnCube (originCube d (r - 2)) a
          (finiteCubeSolutionRestriction a (by omega : r - 2 ≤ r) z).toH1 ≤
          Cc * (normalizedAffineCandidateError (originCube d r)
            z.toH1.toFun (c - cQ) 0 + euclideanNorm (0 : Vec d)) := hcaccRaw
      _ = Cc * normalizedAffineCandidateError (originCube d r)
          z.toH1.toFun (c - cQ) 0 := by simp
      _ ≤ Cc * (((theta * Ce + Cs * delta) +
          C * delta * Ct * A) * D) :=
        mul_le_mul_of_nonneg_left hcandidate' hCc.le
      _ = B * D := by dsimp [B]; ring
  have hexcess := finiteAffineGradientExcess_le_updatedResidualEnergy
    a (by omega : r - 2 ≤ r) hrm u e q
  have hcoef : 0 ≤ B := by
    dsimp [B, A]
    positivity
  calc
    finiteAffineGradientExcess a (k - (N : ℤ) - 2) m u =
        finiteAffineGradientExcess a (r - 2) m u := by rfl
    _ ≤ ENNReal.ofReal
          (Book.Ch03.h1EnergyNormOnCube (originCube d (r - 2)) a
            (finiteCubeSolutionRestriction a (by omega : r - 2 ≤ r) z).toH1) := by
      simpa only [z, q] using hexcess
    _ ≤ ENNReal.ofReal (B * D) := ENNReal.ofReal_mono hcacc'
    _ = ENNReal.ofReal B * ENNReal.ofReal D := by
      rw [ENNReal.ofReal_mul hcoef]
    _ = ENNReal.ofReal B *
        weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x) := by
      rw [weightedGradNorm_finiteAffineGradientResidual a hkm u e]
    _ = ENNReal.ofReal
          (Cc * (theta * Ce + Cs * delta +
            C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ)))) *
        weightedGradNorm
          (a.coeffOn (originCube d k)).toCoeffField
          (openCubeSet (originCube d k))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a m e).toH1.grad x) := by
      rfl

/-- Integer-rate Step 1 for the canonical gradient excess.  The deterministic
coefficient has effective per-scale exponent `1 - 1 / (2p)`; the two
coefficient-error terms remain explicit for the later smallness choice. -/
theorem exists_scalarIdentityFiniteAffineGradientExcessIntegerRateStepConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (p : ℕ) (hp : 0 < p) :
    ∃ (depth : ℕ) (C₀ Cc Ce Ct : ℝ),
      0 < C₀ ∧ 0 < Cc ∧ 0 < Ce ∧ 0 < Ct ∧
      ∀ t : ℕ,
        let N := depth + 2 * p * t + 2
        ∃ Cs : ℝ, 0 < Cs ∧
        ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta C : ℝ)
          (n m : ℤ) (Q : ℤ → Mat d),
          0 ≤ delta → 1 ≤ C →
            ScalarIdentityGoodMaxOnInterval a s delta n m →
            IsFiniteAffineSlopeFamily a delta C n m Q →
            ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m)
              (_hr : k - (N : ℤ) ∈ Finset.Icc n m)
              (u : Book.Ch03.CubeSolution (originCube d m) a),
              finiteAffineGradientExcess a (k - (N : ℤ) - 2) m u ≤
                ENNReal.ofReal
                  (Cc * ((C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) * Ce +
                    Cs * delta +
                    C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ)))) *
                  finiteAffineGradientExcess a k m u := by
  obtain ⟨depth, C₀, hC₀, hbest⟩ :=
    exists_scalarIdentityFiniteBestFitIntegerRateStepConstants
      d s hs hs_lt p hp
  obtain ⟨Cc, hCc, hcacc⟩ :=
    exists_scalarIdentityFiniteCaccioppoliAffineConstant d s hs hs_lt
  obtain ⟨Ce, hCe, herror⟩ :=
    exists_scalarIdentityFiniteTerminalBestFitErrorConstant d s hs hs_lt
  obtain ⟨Ct, hCt, hslope⟩ :=
    exists_scalarIdentityFiniteTerminalBestFitSlopeConstant d s hs hs_lt
  refine ⟨depth, C₀, Cc, Ce, Ct, hC₀, hCc, hCe, hCt, ?_⟩
  intro t
  dsimp only
  let N : ℕ := depth + 2 * p * t + 2
  let theta : ℝ := C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)
  have hN : 0 < N := by dsimp [N]; omega
  have htheta : 0 < theta := by dsimp [theta]; positivity
  obtain ⟨Cs, hCs, hstep⟩ := hbest t
  have hpoint :=
    exists_scalarIdentityFiniteAffineGradientExcessPointwiseStepConstants_of_bestFitStep
      d s N hN theta Cs htheta hCs (by
        simpa only [N, theta] using hstep)
      Cc Ce Ct hCc hCe hCt hcacc herror hslope
  refine ⟨Cs, hCs, ?_⟩
  intro a delta C n m Q hdelta hC hgood hfamily k hk hr u
  let q : ℝ≥0∞ := ENNReal.ofReal
    (Cc * (theta * Ce + Cs * delta +
      C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ))))
  have hcoef : 0 < Cc * (theta * Ce + Cs * delta +
      C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ))) := by
    apply mul_pos hCc
    have hbase : 0 < theta * Ce := mul_pos htheta hCe
    have hweak : 0 ≤ Cs * delta := mul_nonneg hCs.le hdelta
    have hflat : 0 ≤ C * delta * Ct * ((((3 ^ d) ^ N : ℕ) : ℝ)) := by
      positivity
    linarith only [hbase, hweak, hflat]
  have hq_zero : q ≠ 0 := by
    dsimp [q]
    exact ENNReal.ofReal_ne_zero_iff.mpr hcoef
  have hq_top : q ≠ ∞ := by
    dsimp [q]
    exact ENNReal.ofReal_ne_top
  apply finiteAffineGradientExcess_le_mul_of_forall_candidate
    a u q hq_zero hq_top
  intro e
  simpa only [q, N, theta] using
    hpoint a delta C n m Q hdelta hC hgood hfamily k hk hr u e

end

end HighContrast
end HCPolySupport
