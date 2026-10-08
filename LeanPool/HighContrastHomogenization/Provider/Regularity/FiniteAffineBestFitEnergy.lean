/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitBounds

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineBestFitEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine best-fit energy comparison

This module proves the fixed-boundary, pre-inverse energy comparison between
the finite affine solution on an inner centered cube and its canonical
best-fit slope.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem euclideanNorm_le_add_sub_energy
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

private theorem normalizedAffineCandidateError_zero_sub_le_add_energy
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
          (cubeLpNorm Q (2 : ℝ≥0∞) r₁ + cubeLpNorm Q (2 : ℝ≥0∞) r₂) :=
      mul_le_mul_of_nonneg_left htri hweight
    _ = cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₁ +
          cubeBesovScaleWeight 1 Q * cubeLpNorm Q (2 : ℝ≥0∞) r₂ := by ring

private theorem finiteAffineBestFitResidual_memLp_energy
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

private theorem finiteAffineMeanResidual_memLp_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) :
    MemLp
      (fun x ↦ (finiteAffineSolution a m b).toH1.toFun x -
        (cubeAverage (originCube d k)
            (finiteAffineSolutionInnerH1 a k m hkm b).toFun +
          vecDot (0 : Vec d) x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d k)) := by
  let uk := finiteAffineSolutionInnerH1 a k m hkm b
  let c := cubeAverage (originCube d k) uk.toFun
  let v : H1Function (openCubeSet (originCube d k)) :=
    uk - originCubeAffineH1LinearMap d k (c, (0 : Vec d))
  have hv := v.memL2_normalizedCubeMeasure
  simpa only [v, c, H1Function.sub_toFun, finiteAffineSolutionInnerH1_toFun,
    originCubeAffineH1LinearMap_toFun, vecDot_zero_left, add_zero] using! hv

private theorem finiteAffineSlope_le_energy_of_small_error
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) (s B delta Ks Kp C : ℝ)
    (hKs : 0 < Ks) (hKsBdelta : Ks * B * delta ≤ 1 / 2)
    (hKsKpC : 2 * Ks * Kp ≤ C) (hweak : scalarIdentityWeakError a s k ≤ 1)
    (herror : finiteAffineBestFitError a k m hkm b ≤
      B * delta * euclideanNorm (finiteAffineBestFitSlope a k m hkm b))
    (hpoincare : ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
      (u : Book.Ch03.CubeSolution (originCube d k) a),
      scalarIdentityWeakError a s k ≤ 1 →
        cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) u.toH1.toFun) ≤
        Kp * Book.Ch03.h1EnergyNormOnCube (originCube d k) a u.toH1)
    (hslopeError : ∀ (k : ℤ) (c : ℝ) (e : Vec d),
      euclideanNorm e ≤ Ks *
        normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0) c e) :
    euclideanNorm (finiteAffineBestFitSlope a k m hkm b) ≤
      C * finiteCenteredCubeSolutionEnergy a m (finiteAffineCubeSolution a m b) k := by
  have henergy_nonneg : 0 ≤ finiteCenteredCubeSolutionEnergy a m
      (finiteAffineCubeSolution a m b) k := by
    unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  let uk := finiteAffineSolutionInnerH1 a k m hkm b
  let cmean := cubeAverage (originCube d k) uk.toFun
  let cbest := finiteAffineBestFitIntercept a k m hkm b
  let pbest := finiteAffineBestFitSlope a k m hkm b
  have hp := hpoincare a k
    (finiteCubeSolutionRestriction a hkm
      (finiteAffineCubeSolution a m b)) hweak
  have hmeanEq : normalizedAffineCandidateError (originCube d k)
        (finiteAffineSolution a m b).toH1.toFun cmean (0 : Vec d) =
      cubeBesovScaleWeight 1 (originCube d k) *
        cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
          (cubeFluctuation (originCube d k) uk.toFun) := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance cubeFluctuation
    dsimp [cmean, uk]
    simp only [vecDot_zero_left, add_zero]
  have henergyEq : Book.Ch03.h1EnergyNormOnCube (originCube d k) a
        (finiteCubeSolutionRestriction a hkm
          (finiteAffineCubeSolution a m b)).toH1 =
      finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k := by
    exact (finiteCenteredCubeSolutionEnergy_eq_of_le a m
      (finiteAffineCubeSolution a m b) k hkm).symm
  have hmean : normalizedAffineCandidateError (originCube d k)
        (finiteAffineSolution a m b).toH1.toFun cmean (0 : Vec d) ≤
      Kp * finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k := by
    rw [hmeanEq, ← henergyEq]
    simpa only [uk] using! hp
  have hresBest := finiteAffineBestFitResidual_memLp_energy a k m
    hkm b
  have hresMean := finiteAffineMeanResidual_memLp_energy a k m
    hkm b
  have hzero := normalizedAffineCandidateError_zero_sub_le_add_energy
    (originCube d k) (finiteAffineSolution a m b).toH1.toFun
    cbest cmean pbest (0 : Vec d) hresBest hresMean
  have hslope := hslopeError k (cbest - cmean) pbest
  have hraw : euclideanNorm pbest ≤
      Ks * (finiteAffineBestFitError a k m hkm b +
        Kp * finiteCenteredCubeSolutionEnergy a m
          (finiteAffineCubeSolution a m b) k) := by
    calc
      euclideanNorm pbest = euclideanNorm (pbest - (0 : Vec d)) := by simp
      _ ≤ Ks * normalizedAffineCandidateError (originCube d k) (fun _ ↦ 0)
            (cbest - cmean) (pbest - (0 : Vec d)) := by
        simpa only [sub_zero] using hslope
      _ ≤ Ks * (finiteAffineBestFitError a k m
            hkm b +
          normalizedAffineCandidateError (originCube d k)
            (finiteAffineSolution a m b).toH1.toFun cmean (0 : Vec d)) := by
        exact mul_le_mul_of_nonneg_left (by
          simpa only [cbest, cmean, pbest, finiteAffineBestFitError] using hzero) hKs.le
      _ ≤ Ks * (finiteAffineBestFitError a k m
            hkm b +
          Kp * finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) k) :=
        mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hmean) hKs.le
  have habsorb : euclideanNorm pbest ≤
      2 * Ks * Kp * finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k := by
    have herr := herror
    have hsmall := mul_le_mul_of_nonneg_right hKsBdelta
      (euclideanNorm_nonneg pbest)
    have hE_nonneg := finiteAffineBestFitError_nonneg a k m
      hkm b
    nlinarith only [hraw, herr, hsmall, hE_nonneg, henergy_nonneg,
      hKs.le]
  exact habsorb.trans (mul_le_mul_of_nonneg_right hKsKpC henergy_nonneg)

private theorem nearTerminalAffineEnergy_le_slope
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k m : ℤ) (hkm : k ≤ m) (b : Vec d) (Ke C : ℝ) (hKe : 0 < Ke)
    (hterminalIndex : k = m ∨ k = m - 1)
    (hRKeC : 6 * (((3 ^ d : ℕ) : ℝ)) * Ke ≤ C)
    (houterRaw : Book.Ch03.h1EnergyNormOnCube (originCube d m) a
      (finiteAffineCubeSolution a m b).toH1 ≤ 2 * Ke * euclideanNorm b)
    (hbPm : euclideanNorm b ≤ 2 * euclideanNorm (finiteAffineBestFitSlope a m m le_rfl b))
    (hprevious : k = m - 1 → euclideanNorm (finiteAffineBestFitSlope a m m le_rfl b) ≤
      (3 / 2 : ℝ) * euclideanNorm (finiteAffineBestFitSlope a (m - 1) m (by omega) b)) :
    finiteCenteredCubeSolutionEnergy a m (finiteAffineCubeSolution a m b) k ≤
      C * euclideanNorm (finiteAffineBestFitSlope a k m hkm b) := by
  let R : ℝ := ((3 ^ d : ℕ) : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hDm : finiteCenteredCubeSolutionEnergy a m
      (finiteAffineCubeSolution a m b) m ≤ 2 * Ke * euclideanNorm b := by
    rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m
      (finiteAffineCubeSolution a m b) m le_rfl]
    simpa only [Book.Ch03.h1EnergyNormOnCube,
      Book.Ch03.localizedCoeffEnergyValue, finiteCubeSolutionRestriction_grad] using houterRaw
  rcases hterminalIndex with hkterminal | hkprev
  · subst k
    exact hDm.trans (by
      calc
        2 * Ke * euclideanNorm b ≤
            2 * Ke * (2 * euclideanNorm
              (finiteAffineBestFitSlope a m m le_rfl b)) :=
          mul_le_mul_of_nonneg_left hbPm (mul_nonneg (by norm_num) hKe.le)
        _ = (4 * Ke) * euclideanNorm
              (finiteAffineBestFitSlope a m m le_rfl b) := by ring
        _ ≤ (6 * R * Ke) * euclideanNorm
              (finiteAffineBestFitSlope a m m le_rfl b) := by
          have hRone : 1 ≤ R := by dsimp [R]; exact_mod_cast
            Nat.one_le_iff_ne_zero.mpr (pow_ne_zero d (by norm_num : (3 : ℕ) ≠ 0))
          apply mul_le_mul_of_nonneg_right _ (euclideanNorm_nonneg _)
          have : (4 : ℝ) ≤ 6 * R := by nlinarith only [hRone]
          exact mul_le_mul_of_nonneg_right this hKe.le
        _ ≤ C * euclideanNorm
              (finiteAffineBestFitSlope a m m le_rfl b) :=
          mul_le_mul_of_nonneg_right hRKeC (euclideanNorm_nonneg _))
  · subst k
    have hPm' := hprevious rfl
    have hrestrict :=
      h1EnergyNormOnCube_finiteCubeSolutionRestriction_sub_one_le
        a m (finiteAffineCubeSolution a m b)
    rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m
      (finiteAffineCubeSolution a m b) (m - 1) (by omega)]
    calc
      Book.Ch03.h1EnergyNormOnCube (originCube d (m - 1)) a
          (finiteCubeSolutionRestriction a (by omega)
            (finiteAffineCubeSolution a m b)).toH1 ≤
          R * Book.Ch03.h1EnergyNormOnCube (originCube d m) a
            (finiteAffineCubeSolution a m b).toH1 := by
        simpa only [R] using hrestrict
      _ ≤ R * (2 * Ke * euclideanNorm b) :=
        mul_le_mul_of_nonneg_left houterRaw hR.le
      _ ≤ R * (2 * Ke * (2 * euclideanNorm
            (finiteAffineBestFitSlope a m m le_rfl b))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbPm (mul_nonneg (by norm_num) hKe.le)) hR.le
      _ = (4 * R * Ke) * euclideanNorm
            (finiteAffineBestFitSlope a m m le_rfl b) := by ring
      _ ≤ (4 * R * Ke) * ((3 / 2 : ℝ) * euclideanNorm
            (finiteAffineBestFitSlope a (m - 1) m (by omega) b)) :=
        mul_le_mul_of_nonneg_left hPm'
          (mul_nonneg (mul_nonneg (by norm_num) hR.le) hKe.le)
      _ = (6 * R * Ke) * euclideanNorm
            (finiteAffineBestFitSlope a (m - 1) m (by omega) b) := by ring
      _ ≤ C * euclideanNorm
            (finiteAffineBestFitSlope a (m - 1) m (by omega) b) :=
        mul_le_mul_of_nonneg_right hRKeC (euclideanNorm_nonneg _)

/-- On a sufficiently good finite row, the inner energy of a fixed-boundary
affine solution is comparable in both directions to its current best-fit
slope. This statement is deliberately prior to, and independent of, any
inverse slope family. -/
theorem exists_scalarIdentityFiniteAffineBestFitEnergyConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
            finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) k ≤
              C * euclideanNorm
                (finiteAffineBestFitSlope a k m
                  (Finset.mem_Icc.mp hk).2 b) ∧
            euclideanNorm
                (finiteAffineBestFitSlope a k m
                  (Finset.mem_Icc.mp hk).2 b) ≤
              C * finiteCenteredCubeSolutionEnergy a m
                (finiteAffineCubeSolution a m b) k := by
  obtain ⟨B, cb, hB, hcb, hbounds⟩ :=
    exists_scalarIdentityFiniteAffineBestFitInductionConstants d s hs hs_lt
  obtain ⟨Kc, hKc, hcacc⟩ :=
    exists_finiteAffineBestFitCaccioppoliConstant d s hs hs_lt
  obtain ⟨Ke, hKe, houterEnergy⟩ :=
    exists_finiteAffineSolutionEnergyEstimateConstant d s hs
      (by linarith only [hs_lt])
  obtain ⟨Kp, hKp, hpoincare⟩ :=
    exists_finiteLipschitzPoincareConstant d s hs hs_lt
  obtain ⟨Ks, hKs, hslopeError⟩ :=
    exists_originCubeAffineSlopeErrorConstant d
  let R : ℝ := ((3 ^ d : ℕ) : ℝ)
  let C : ℝ := 1 + B + 5 * Kc + 6 * R * Ke + 2 * Ks * Kp
  let c : ℝ := min (1 / 2 : ℝ)
    (min cb (min ((2 * C)⁻¹) ((2 * Ks * B)⁻¹)))
  have hR : 0 < R := by dsimp [R]; positivity
  have hC : 1 ≤ C := by
    dsimp [C]
    have hc : 0 ≤ 5 * Kc := by positivity
    have he : 0 ≤ 6 * R * Ke := by positivity
    have hp : 0 ≤ 2 * Ks * Kp := by positivity
    linarith only [hB, hc, he, hp]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hKsB : 0 < 2 * Ks * B := by
    exact mul_pos (mul_pos (by norm_num) hKs) (lt_of_lt_of_le zero_lt_one hB)
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min hcb.1 (lt_min
      (inv_pos.mpr (mul_pos (by norm_num) hCpos)) (inv_pos.mpr hKsB)))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hKcC : 5 * Kc ≤ C := by
    dsimp [C]
    have he : 0 ≤ 6 * R * Ke := by positivity
    have hp : 0 ≤ 2 * Ks * Kp := by positivity
    linarith only [hB, he, hp]
  have hRKeC : 6 * R * Ke ≤ C := by
    dsimp [C]
    have hc : 0 ≤ 5 * Kc := by positivity
    have hp : 0 ≤ 2 * Ks * Kp := by positivity
    linarith only [hB, hc, hp]
  have hKsKpC : 2 * Ks * Kp ≤ C := by
    dsimp [C]
    have hc : 0 ≤ 5 * Kc := by positivity
    have he : 0 ≤ 6 * R * Ke := by positivity
    linarith only [hB, hc, he]
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood k hk b
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cb :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdelta_nonneg : 0 ≤ delta := hdelta.1.le
  have hdelta_one : delta ≤ 1 :=
    hdelta.2.trans ((min_le_left _ _).trans (by norm_num))
  have hBdelta : B * delta ≤ 1 / 2 := by
    have hd := hdeltaB.2.trans hcb.2
    calc
      B * delta ≤ B * (2 * B)⁻¹ :=
        mul_le_mul_of_nonneg_left hd (lt_of_lt_of_le zero_lt_one hB).le
      _ = 1 / 2 := by field_simp
  have hKsBdelta : Ks * B * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * Ks * B)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    calc
      Ks * B * delta ≤ Ks * B * (2 * Ks * B)⁻¹ :=
        mul_le_mul_of_nonneg_left hd
          (mul_nonneg hKs.le (zero_le_one.trans hB))
      _ = 1 / 2 := by field_simp
  have hpack := hbounds a delta n m hnm hdeltaB hgood k hk b
  have henergy_nonneg : 0 ≤ finiteCenteredCubeSolutionEnergy a m
      (finiteAffineCubeSolution a m b) k := by
    unfold finiteCenteredCubeSolutionEnergy Book.Ch03.h1EnergyNormOnCube
    exact Real.sqrt_nonneg _
  have hupper : finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k ≤
      C * euclideanNorm
        (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := by
    by_cases hinterior : k + 2 ≤ m
    · have hk2 : k + 2 ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨by
          exact (Finset.mem_Icc.mp hk).1.trans (by omega), hinterior⟩
      have hpack2 := hbounds a delta n m hnm hdeltaB hgood (k + 2) hk2 b
      have hweak2 : scalarIdentityWeakError a s (k + 2) ≤ 1 :=
        (hgood.weakError_le hk2).trans hdelta_one
      have hD := hcacc a m b k hinterior hweak2
      have hP2 := (hpack2.2.2.1 k hk (by omega)).2
      have hpow : (1 + B * delta) ^ Int.toNat (k + 2 - k) ≤ 9 / 4 := by
        have hgap : Int.toNat (k + 2 - k) = 2 := by
          rw [show k + 2 - k = (2 : ℤ) by ring]
          decide
        rw [hgap, pow_two]
        have hx0 : 0 ≤ B * delta :=
          mul_nonneg (zero_le_one.trans hB) hdelta_nonneg
        have hxx : (B * delta) * (B * delta) ≤ (1 / 2 : ℝ) * (1 / 2) :=
          mul_le_mul hBdelta hBdelta hx0 (by norm_num)
        nlinarith only [hBdelta, hx0, hxx]
      have hP2' : euclideanNorm
            (finiteAffineBestFitSlope a (k + 2) m hinterior b) ≤
          (9 / 4 : ℝ) * euclideanNorm
            (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) :=
        hP2.trans (mul_le_mul_of_nonneg_right hpow (euclideanNorm_nonneg _))
      calc
        finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) k ≤
            Kc * (finiteAffineBestFitError a (k + 2) m hinterior b +
              euclideanNorm
                (finiteAffineBestFitSlope a (k + 2) m hinterior b)) := hD
        _ ≤ Kc * ((B * delta) * euclideanNorm
              (finiteAffineBestFitSlope a (k + 2) m hinterior b) +
            euclideanNorm
              (finiteAffineBestFitSlope a (k + 2) m hinterior b)) :=
          mul_le_mul_of_nonneg_left (add_le_add hpack2.1 (le_refl _)) hKc.le
        _ ≤ Kc * ((1 / 2 : ℝ) *
              ((9 / 4 : ℝ) * euclideanNorm
                (finiteAffineBestFitSlope a k m
                  (Finset.mem_Icc.mp hk).2 b)) +
            (9 / 4 : ℝ) * euclideanNorm
              (finiteAffineBestFitSlope a k m
                (Finset.mem_Icc.mp hk).2 b)) := by
          apply mul_le_mul_of_nonneg_left _ hKc.le
          exact add_le_add
            (mul_le_mul hBdelta hP2' (euclideanNorm_nonneg _) (by norm_num)) hP2'
        _ ≤ (5 * Kc) * euclideanNorm
              (finiteAffineBestFitSlope a k m
                (Finset.mem_Icc.mp hk).2 b) := by
          nlinarith only [hKc.le, euclideanNorm_nonneg
            (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b)]
        _ ≤ C * euclideanNorm
              (finiteAffineBestFitSlope a k m
                (Finset.mem_Icc.mp hk).2 b) :=
          mul_le_mul_of_nonneg_right hKcC (euclideanNorm_nonneg _)
    · have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
      have hterminalIndex : k = m ∨ k = m - 1 := by omega
      have hm : m ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hnm.le, le_rfl⟩
      have hpackm := hbounds a delta n m hnm hdeltaB hgood m hm b
      have hweakm := hgood.weakError_le hm
      have houterRaw : Book.Ch03.h1EnergyNormOnCube (originCube d m) a
            (finiteAffineCubeSolution a m b).toH1 ≤
          2 * Ke * euclideanNorm b := by
        calc
          Book.Ch03.h1EnergyNormOnCube (originCube d m) a
              (finiteAffineCubeSolution a m b).toH1 ≤
              Ke * (1 + scalarIdentityWeakError a s m) * euclideanNorm b := by
            simpa only [finiteAffineCubeSolution] using houterEnergy a m b
          _ ≤ Ke * (1 + delta) * euclideanNorm b := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith only [hweakm]) hKe.le)
              (euclideanNorm_nonneg _)
          _ ≤ 2 * Ke * euclideanNorm b := by
            apply mul_le_mul_of_nonneg_right _ (euclideanNorm_nonneg b)
            nlinarith only [hKe.le, hdelta_one]
      have hDm : finiteCenteredCubeSolutionEnergy a m
            (finiteAffineCubeSolution a m b) m ≤
          2 * Ke * euclideanNorm b := by
        rw [finiteCenteredCubeSolutionEnergy_eq_of_le a m
          (finiteAffineCubeSolution a m b) m le_rfl]
        simpa only [Book.Ch03.h1EnergyNormOnCube,
          Book.Ch03.localizedCoeffEnergyValue, finiteCubeSolutionRestriction_grad]
          using houterRaw
      have hterminal := hpackm.2.2.2 rfl
      have hbPm : euclideanNorm b ≤ 2 * euclideanNorm
          (finiteAffineBestFitSlope a m m le_rfl b) := by
        have htri := euclideanNorm_le_add_sub_energy
          (finiteAffineBestFitSlope a m m le_rfl b) b
        have hsmall := mul_le_mul_of_nonneg_right hBdelta (euclideanNorm_nonneg b)
        nlinarith only [htri, hterminal, hsmall,
          euclideanNorm_nonneg (finiteAffineBestFitSlope a m m le_rfl b)]
      apply nearTerminalAffineEnergy_le_slope a k m (Finset.mem_Icc.mp hk).2 b
        Ke C hKe hterminalIndex hRKeC houterRaw hbPm
      intro hkprev
      have hm1 : m - 1 ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨by
        rw [← hkprev]
        exact (Finset.mem_Icc.mp hk).1, by omega⟩
      have hPm := (hpackm.2.2.1 (m - 1) hm1 (by omega)).2
      have hpow : (1 + B * delta) ^ Int.toNat (m - (m - 1)) ≤ 3 / 2 := by
        norm_num [Int.toNat_of_nonneg (by omega : 0 ≤ m - (m - 1))]
        linarith only [hBdelta]
      exact hPm.trans (mul_le_mul_of_nonneg_right hpow (euclideanNorm_nonneg _))
  have hlower : euclideanNorm
        (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) ≤
      C * finiteCenteredCubeSolutionEnergy a m
        (finiteAffineCubeSolution a m b) k :=
    finiteAffineSlope_le_energy_of_small_error a k m (Finset.mem_Icc.mp hk).2 b
      s B delta Ks Kp C hKs hKsBdelta hKsKpC
      ((hgood.weakError_le hk).trans hdelta_one) hpack.1 hpoincare hslopeError
  exact ⟨hupper, hlower⟩

end

end HighContrast
end HCPolySupport
