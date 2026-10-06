/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationFiniteEllipticity

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationFinitePoincareRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Printed-order Poincare rows for the finite recurrence

The fluctuation estimate uses the weak-error row at the same fractional
order.  Its proof only requires that half of this order lie below one half;
the stronger small-order binder in the archived wrapper is not used.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal Matrix MatrixOrder

noncomputable section

open FiniteLipschitzCoreInternal
open RoundedFiniteEnergyInternal

/-- Poincare's fluctuation estimate at any positive order below one half. -/
theorem exists_roundedGenerationFiniteLipschitzPoincareConstant
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aRounded.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (k : ℤ) (u : Book.Ch03.CubeSolution (originCube d k) aRounded),
          geom.spatialWeakError a abar hS s k ≤ 1 →
            cubeBesovScaleWeight 1 (originCube d k) *
                cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
                  (cubeFluctuation (originCube d k) u.toH1.toFun) ≤
              C * Book.Ch03.h1EnergyNormOnCube
                (originCube d k) aRounded u.toH1 := by
  let G : ℝ := Real.sqrt
    ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 2)))⁻¹)
  let P : ℝ :=
    (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
        (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G))
  let L : ℝ := Real.sqrt (5 * (d : ℝ))
  let B : ℝ := Book.Ch03.poincareDiscountFactor s (.finite 2)
  let C : ℝ := 1 + P * B * L
  have hP : 0 ≤ P := by
    dsimp [P, G]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity)
          (Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
        (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  have hB : 0 ≤ B := by
    dsimp [B, Book.Ch03.poincareDiscountFactor]
    exact Real.rpow_nonneg
      (HCPolySupport.geometricDiscount_pos
        (mul_pos hs (by norm_num : (0 : ℝ) < 2))).le _
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hP hB) hL)
  refine ⟨C, hC, ?_⟩
  intro a abar hS aRounded hRounded k u herror
  let Q : TriadicCube d := originCube d k
  let D : ℝ := Book.Ch03.h1EnergyNormOnCube Q aRounded u.toH1
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q s u.toH1.grad
  have ht : 0 < s / 2 := by linarith only [hs]
  have ht_lt : s / 2 < 1 / 2 := by linarith only [hs_lt]
  have hfluctRaw :=
    Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
      Q u.toH1 ht ht_lt
  have hfluct :
      cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) ≤
        P * N := by
    simpa only [Q, P, G, Book.Ch02.cubeDomain_coe,
      Book.Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant,
      show 2 * (s / 2) = s by ring] using hfluctRaw
  have hnegative :
      N ≤ Book.Ch03.coarsePoincareGradientRHS Q aRounded s (.finite 2) u := by
    simpa only [N,
      scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
      using! Book.Ch03.coarsePoincareGradient_negativeBesov_le
        Q aRounded u hs (q := .finite 2) (by norm_num)
  have hlower :
      Book.Ch03.poincareLowerEllipticityFactor Q aRounded s (.finite 2) ≤ L := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv]
    exact Real.sqrt_le_sqrt (by
      simpa only [Q, L] using
        (roundedGenerationWeakError_le_one_finiteTwoEllipticity
          (geom := geom) a abar hS aRounded hRounded hs herror).2)
  have henergy : Book.Ch03.solutionEnergyNorm Q aRounded u = D :=
    solutionEnergyNorm_eq_h1EnergyNormOnCube Q aRounded u
  have hN : N ≤ B * L * D := by
    calc
      N ≤ Book.Ch03.coarsePoincareGradientRHS Q aRounded s (.finite 2) u :=
        hnegative
      _ = B * Book.Ch03.poincareLowerEllipticityFactor
          Q aRounded s (.finite 2) * D := by
        rw [Book.Ch03.coarsePoincareGradientRHS, henergy]
      _ ≤ B * L * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlower hB)
          (by
            dsimp [D, Book.Ch03.h1EnergyNormOnCube]
            exact Real.sqrt_nonneg _)
  have hBLC : P * B * L ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_left (by norm_num)
  have hD : 0 ≤ D := by
    dsimp [D, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  calc
    cubeBesovScaleWeight 1 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun) ≤
        P * N := hfluct
    _ ≤ P * (B * L * D) := mul_le_mul_of_nonneg_left hN hP
    _ = (P * B * L) * D := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_right hBLC hD
    _ = C * Book.Ch03.h1EnergyNormOnCube
        (originCube d k) aRounded u.toH1 := rfl

/-- The best affine error is controlled by the energy row at a printed-order
good scale. -/
theorem exists_roundedGenerationFiniteLipschitzAffineErrorEnergyConstant
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aRounded.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) aRounded)
          (k : ℤ), k ≤ m →
          geom.spatialWeakError a abar hS s k ≤ 1 →
            finiteLipschitzAffineErrorRow aRounded m u k ≤
              C * finiteLipschitzEnergyRow aRounded m u k := by
  obtain ⟨C, hC, hPoincare⟩ :=
    exists_roundedGenerationFiniteLipschitzPoincareConstant
      d geom s hs hs_lt
  refine ⟨C, hC, ?_⟩
  intro a abar hS aRounded hRounded m u k hkm herror
  let uk : Book.Ch03.CubeSolution (originCube d k) aRounded :=
    finiteCubeSolutionRestriction aRounded hkm u
  let c : ℝ := cubeAverage (originCube d k) uk.toH1.toFun
  have hbest :=
    finiteLipschitzAffineErrorRow_best_le aRounded m u hkm c (0 : Vec d)
  have hcandidate :
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c (0 : Vec d) =
        cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) uk.toH1.toFun) := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance cubeFluctuation
    dsimp only [c]
    rw [finiteCubeSolutionRestriction_toFun]
    simp only [vecDot_zero_left, add_zero]
  have hp := hPoincare a abar hS aRounded hRounded k uk herror
  have henergy :
      Book.Ch03.h1EnergyNormOnCube (originCube d k) aRounded uk.toH1 =
        finiteLipschitzEnergyRow aRounded m u k := by
    simpa only [uk] using
      (finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le
        aRounded m u k hkm).symm
  calc
    finiteLipschitzAffineErrorRow aRounded m u k ≤
        normalizedAffineCandidateError
          (originCube d k) u.toH1.toFun c (0 : Vec d) := hbest
    _ = cubeBesovScaleWeight 1 (originCube d k) *
          cubeLpNorm (originCube d k) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d k) uk.toH1.toFun) := hcandidate
    _ ≤ C * Book.Ch03.h1EnergyNormOnCube
          (originCube d k) aRounded uk.toH1 := hp
    _ = C * finiteLipschitzEnergyRow aRounded m u k := by rw [henergy]

/-- The top-scale best affine slope is controlled by the top energy row at a
printed-order good scale. -/
theorem exists_roundedGenerationFiniteLipschitzTerminalSlopeConstant
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aRounded.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) aRounded),
          geom.spatialWeakError a abar hS s m ≤ 1 →
            euclideanNorm (finiteLipschitzBestSlope aRounded m u m) ≤
              C * finiteLipschitzEnergyRow aRounded m u m := by
  obtain ⟨C₀, hC₀, hC₀bound⟩ := exists_originCubeAffineSlopeErrorConstant d
  obtain ⟨C₁, hC₁, hPoincare⟩ :=
    exists_roundedGenerationFiniteLipschitzPoincareConstant
      d geom s hs hs_lt
  let C : ℝ := 1 + 2 * C₀ * C₁
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a abar hS aRounded hRounded m u herror
  let c₀ := finiteLipschitzBestIntercept aRounded m u m
  let e₀ := finiteLipschitzBestSlope aRounded m u m
  let c₁ := cubeAverage (originCube d m) u.toH1.toFun
  let E := finiteLipschitzAffineErrorRow aRounded m u m
  let D := finiteLipschitzEnergyRow aRounded m u m
  have hres₀ : MemLp (fun x ↦ u.toH1.toFun x - (c₀ + vecDot e₀ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c₀, e₀] using
      finiteLipschitzBestResidual_memLp aRounded m u (le_refl m)
  have hres₁ :
      MemLp (fun x ↦ u.toH1.toFun x - (c₁ + vecDot (0 : Vec d) x))
        (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
    simpa only [c₁, vecDot_zero_left, add_zero, cubeFluctuation] using!
      u.toH1.memL2_normalizedCubeMeasure.sub (memLp_const _)
  have htriangle := normalizedAffineCandidateError_zero_sub_le_add
    (originCube d m) u.toH1.toFun c₀ c₁ e₀ (0 : Vec d) hres₀ hres₁
  have hbestEq :
      normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₀ e₀ = E := by
    simp only [E, c₀, e₀, finiteLipschitzAffineErrorRow,
      finiteLipschitzBestIntercept, finiteLipschitzBestSlope,
      finiteLipschitzRestriction_toFun, min_self]
  have hcandidateEq :
      normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₁ (0 : Vec d) =
        cubeBesovScaleWeight 1 (originCube d m) *
          cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
            (cubeFluctuation (originCube d m) u.toH1.toFun) := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance cubeFluctuation
    simp only [c₁, vecDot_zero_left, add_zero]
  have hP := hPoincare a abar hS aRounded hRounded m u herror
  have htopEnergy :
      Book.Ch03.h1EnergyNormOnCube (originCube d m) aRounded u.toH1 = D := by
    simpa only [D] using (finiteLipschitzEnergyRow_self aRounded m u).symm
  rw [htopEnergy] at hP
  have hE : E ≤ C₁ * D := by
    have hbest : E ≤ normalizedAffineCandidateError
        (originCube d m) u.toH1.toFun c₁ (0 : Vec d) := by
      simpa only [E] using
        finiteLipschitzAffineErrorRow_best_le
          aRounded m u (le_refl m) c₁ (0 : Vec d)
    exact hbest.trans ((le_of_eq hcandidateEq).trans hP)
  have hD : 0 ≤ D := finiteLipschitzEnergyRow_nonneg aRounded m u m
  have hslope := hC₀bound m (c₀ - c₁) (e₀ - (0 : Vec d))
  have hcombined :
      normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) ≤ 2 * C₁ * D := by
    calc
      normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) ≤
          normalizedAffineCandidateError (originCube d m) u.toH1.toFun c₀ e₀ +
            normalizedAffineCandidateError
              (originCube d m) u.toH1.toFun c₁ (0 : Vec d) := htriangle
      _ = E + normalizedAffineCandidateError
          (originCube d m) u.toH1.toFun c₁ (0 : Vec d) := by rw [hbestEq]
      _ ≤ C₁ * D + C₁ * D :=
        add_le_add hE ((le_of_eq hcandidateEq).trans hP)
      _ = 2 * C₁ * D := by ring
  calc
    euclideanNorm (finiteLipschitzBestSlope aRounded m u m) =
        euclideanNorm (e₀ - (0 : Vec d)) := by simp [e₀]
    _ ≤ C₀ * normalizedAffineCandidateError (originCube d m) (fun _ ↦ 0)
          (c₀ - c₁) (e₀ - (0 : Vec d)) := hslope
    _ ≤ C₀ * (2 * C₁ * D) :=
      mul_le_mul_of_nonneg_left hcombined hC₀.le
    _ ≤ C * D := by
      have hfactor : C₀ * (2 * C₁) ≤ C := by
        calc
          C₀ * (2 * C₁) = 2 * C₀ * C₁ := by ring
          _ ≤ 1 + 2 * C₀ * C₁ := le_add_of_nonneg_left zero_le_one
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfactor hD
    _ = C * finiteLipschitzEnergyRow aRounded m u m := rfl

end

end HighContrast
end HCPolySupport
