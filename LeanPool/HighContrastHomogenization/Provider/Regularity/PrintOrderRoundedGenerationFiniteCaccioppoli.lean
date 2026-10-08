/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.MultiscaleEllipticityExponentGap
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedGenerationFinitePoincareRows

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedGenerationFiniteCaccioppoli

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Printed-order Caccioppoli row for the finite recurrence

The Caccioppoli parameters are chosen strictly between the response order and
one half.  The exponent-gap ellipticity bridge then supplies both `q = 1`
rows from the printed `q = 2` weak-error row.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set Book.Ch03
open scoped BigOperators ENNReal Matrix MatrixOrder

noncomputable section

open FiniteLipschitzCoreInternal
open RoundedFiniteEnergyInternal

private theorem caccioppoliPrefactor_roundedGenerationWeakError_le_one
    {d : ℕ} [NeZero d] {geom : RoundedGenerationAnalyticGeometry d}
    {C₀ s : ℝ}
    (hC₀ : 0 < C₀) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (a : CoeffSpace d) (abar : Mat d) (hS : (symmPart abar).PosDef)
    (aRounded : Book.Ch03.CoeffFamily d)
    (hRounded : ∀ Q : TriadicCube d,
      (aRounded.coeffOn Q).toCoeffField =
        (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d))
    {k : ℤ} (herror : geom.spatialWeakError a abar hS s k ≤ 1) :
    let r : ℝ := (s + 1 / 2) / 2
    let G : ℝ :=
      (Book.Ch02.geometricDiscount r 1 *
          (Real.sqrt (Book.Ch02.geometricDiscount (r - s) 2))⁻¹ *
          (Real.sqrt (Book.Ch02.geometricDiscount s 2))⁻¹) ^ 2
    let D : ℝ := G * (5 * (d : ℝ))
    let alpha : ℝ := r / (1 - 2 * r)
    let K : ℝ :=
      Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) *
        Real.rpow (D * D) alpha * D
    Book.Ch03.caccioppoliPrefactor C₀ (originCube d k) aRounded r r ≤
      K * cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by
  dsimp
  let r : ℝ := (s + 1 / 2) / 2
  let G : ℝ :=
    (Book.Ch02.geometricDiscount r 1 *
        (Real.sqrt (Book.Ch02.geometricDiscount (r - s) 2))⁻¹ *
        (Real.sqrt (Book.Ch02.geometricDiscount s 2))⁻¹) ^ 2
  let D : ℝ := G * (5 * (d : ℝ))
  let alpha : ℝ := r / (1 - 2 * r)
  have hr : 0 < r := by
    dsimp only [r]
    linarith only [hs]
  have hsr : s < r := by
    dsimp only [r]
    linarith only [hs_lt]
  have hr_lt : r < 1 / 2 := by
    dsimp only [r]
    linarith only [hs_lt]
  have hden : 0 < 1 - 2 * r := by
    linarith only [hr_lt]
  have hG : 0 < G := by
    dsimp only [G]
    have hgap : 0 < r - s := sub_pos.mpr hsr
    have hdisc_r : 0 < Book.Ch02.geometricDiscount r 1 := by
      simpa only [Book.Ch02.geometricDiscount_eq_old] using
        geometricDiscount_pos (by simpa only [mul_one] using hr)
    have hdisc_gap : 0 < Book.Ch02.geometricDiscount (r - s) 2 := by
      simpa only [Book.Ch02.geometricDiscount_eq_old] using
        geometricDiscount_pos
          (mul_pos hgap (by norm_num : (0 : ℝ) < 2))
    have hdisc_s : 0 < Book.Ch02.geometricDiscount s 2 := by
      simpa only [Book.Ch02.geometricDiscount_eq_old] using
        geometricDiscount_pos
          (mul_pos hs (by norm_num : (0 : ℝ) < 2))
    exact sq_pos_of_pos (mul_pos
      (mul_pos hdisc_r (inv_pos.mpr (Real.sqrt_pos.2 hdisc_gap)))
      (inv_pos.mpr (Real.sqrt_pos.2 hdisc_s)))
  have hd : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos hG (mul_pos (by norm_num) hd)
  have halpha : 0 ≤ alpha := by
    dsimp only [alpha]
    exact div_nonneg hr.le hden.le
  obtain ⟨hLambdaTwo, hlambdaTwo⟩ :=
    roundedGenerationWeakError_le_one_finiteTwoEllipticity
      (geom := geom) a abar hS aRounded hRounded hs herror
  have hLambda :
      Book.Ch02.LambdaS (originCube d k) r aRounded ≤ D := by
    calc
      Book.Ch02.LambdaS (originCube d k) r aRounded ≤
          G * Book.Ch02.LambdaSq (originCube d k) s (.finite 2) aRounded := by
        simpa only [G] using
          LambdaS_le_exponentGap_mul_LambdaSq_finite_two
            (originCube d k) aRounded hs hsr
      _ ≤ G * (5 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hLambdaTwo hG.le
      _ = D := rfl
  have hlambda :
      (Book.Ch02.lambdaS (originCube d k) r aRounded)⁻¹ ≤ D := by
    calc
      (Book.Ch02.lambdaS (originCube d k) r aRounded)⁻¹ ≤
          G * (Book.Ch02.lambdaSq
            (originCube d k) s (.finite 2) aRounded)⁻¹ := by
        simpa only [G] using
          lambdaS_inv_le_exponentGap_mul_lambdaSq_finite_two_inv
            (originCube d k) aRounded hs hsr
      _ ≤ G * (5 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hlambdaTwo hG.le
      _ = D := rfl
  have hLambda_nonneg :
      0 ≤ Book.Ch02.LambdaS (originCube d k) r aRounded := by
    unfold Book.Ch02.LambdaS
    exact Book.Ch02.LambdaSq_finite_nonneg _ _ hr (by norm_num)
  have hlambda_inv_nonneg :
      0 ≤ (Book.Ch02.lambdaS (originCube d k) r aRounded)⁻¹ := by
    exact inv_nonneg.mpr (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have htheta_nonneg :
      0 ≤ Book.Ch02.ThetaRatio (originCube d k) r r aRounded := by
    unfold Book.Ch02.ThetaRatio
    exact div_nonneg hLambda_nonneg (by
      unfold Book.Ch02.lambdaS
      exact Book.Ch02.lambdaSq_finite_nonneg _ _ hr (by norm_num))
  have htheta :
      Book.Ch02.ThetaRatio (originCube d k) r r aRounded ≤ D * D := by
    unfold Book.Ch02.ThetaRatio
    rw [div_eq_mul_inv]
    exact mul_le_mul hLambda hlambda hlambda_inv_nonneg hD.le
  have hthetaPow := Real.rpow_le_rpow htheta_nonneg htheta halpha
  have hfront :
      0 ≤ Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
        Real.rpow r (-(2 * r / (1 - 2 * r))) := by
    exact mul_nonneg
      (Real.rpow_nonneg (div_nonneg hC₀.le hden.le) _)
      (Real.rpow_nonneg hr.le _)
  have hscale : Real.rpow (3 : ℝ) (-2 * (k : ℝ)) =
      cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by
    calc
      Real.rpow (3 : ℝ) (-2 * (k : ℝ)) =
          cubeBesovScaleWeight 2 (originCube d k) := by
        simpa using! Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight
          (originCube d k) (2 : ℝ)
      _ = cubeBesovScaleWeight 1 (originCube d k) *
          cubeBesovScaleWeight 1 (originCube d k) := by
        rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        norm_num
      _ = cubeBesovScaleWeight 1 (originCube d k) ^ 2 := by ring
  unfold Book.Ch03.caccioppoliPrefactor
  rw [show 1 - r - r = 1 - 2 * r by ring]
  change
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow
            (Book.Ch02.ThetaRatio (originCube d k) r r aRounded) alpha *
          Book.Ch02.LambdaS (originCube d k) r aRounded *
          Real.rpow (3 : ℝ) (-2 * (k : ℝ)) ≤
      (Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) alpha * D) *
        cubeBesovScaleWeight 1 (originCube d k) ^ 2
  rw [← hscale]
  have hscale_nonneg : 0 ≤ Real.rpow (3 : ℝ) (-2 * (k : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow
              (Book.Ch02.ThetaRatio (originCube d k) r r aRounded) alpha *
            Book.Ch02.LambdaS (originCube d k) r aRounded *
            Real.rpow (3 : ℝ) (-2 * (k : ℝ)) ≤
        Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
            Real.rpow r (-(2 * r / (1 - 2 * r))) *
            Real.rpow (D * D) alpha *
            Book.Ch02.LambdaS (originCube d k) r aRounded *
            Real.rpow (3 : ℝ) (-2 * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hthetaPow hfront)
          hLambda_nonneg)
        hscale_nonneg
    _ ≤ Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
          Real.rpow r (-(2 * r / (1 - 2 * r))) *
          Real.rpow (D * D) alpha * D *
          Real.rpow (3 : ℝ) (-2 * (k : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLambda
          (mul_nonneg hfront
            (Real.rpow_nonneg (mul_nonneg hD.le hD.le) _)))
        hscale_nonneg

/-- The coarse Caccioppoli row at every positive printed order below one
half. -/
theorem exists_roundedGenerationFiniteLipschitzCaccioppoliAffineConstant
    (d : ℕ) [NeZero d] (geom : RoundedGenerationAnalyticGeometry d)
    (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffSpace d) (abar : Mat d)
        (hS : (symmPart abar).PosDef)
        (aRounded : Book.Ch03.CoeffFamily d),
        (∀ Q : TriadicCube d,
          (aRounded.coeffOn Q).toCoeffField =
            (⇑(geom.centeredCoeffSpace abar hS a).1 : CoeffField d)) →
        ∀ (k : ℤ) (u : Book.Ch03.CubeSolution (originCube d k) aRounded)
          (c : ℝ) (e : Vec d),
          geom.spatialWeakError a abar hS s k ≤ 1 →
            Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) aRounded
                (finiteCubeSolutionRestriction aRounded
                  (by omega : k - 2 ≤ k) u).toH1 ≤
              C * (normalizedAffineCandidateError
                  (originCube d k) u.toH1.toFun c e + euclideanNorm e) := by
  rcases (Book.Ch03.coarseCaccioppoliTheory d).exists_constant with
    ⟨C₀, hC₀, _hboundary, hinterior⟩
  let r : ℝ := (s + 1 / 2) / 2
  let G : ℝ :=
    (Book.Ch02.geometricDiscount r 1 *
        (Real.sqrt (Book.Ch02.geometricDiscount (r - s) 2))⁻¹ *
        (Real.sqrt (Book.Ch02.geometricDiscount s 2))⁻¹) ^ 2
  let D : ℝ := G * (5 * (d : ℝ))
  let alpha : ℝ := r / (1 - 2 * r)
  let K : ℝ :=
    Real.rpow (C₀ / (1 - 2 * r)) (2 + 4 * r / (1 - 2 * r)) *
      Real.rpow r (-(2 * r / (1 - 2 * r))) *
      Real.rpow (D * D) alpha * D
  let A : ℝ := max 1 (cubeBesovW12LocalPoincareConstant d)
  let C : ℝ := 1 + 2 * Real.sqrt K * A
  have hr : 0 < r := by
    dsimp only [r]
    linarith only [hs]
  have hsr : s < r := by
    dsimp only [r]
    linarith only [hs_lt]
  have hr_lt : r < 1 / 2 := by
    dsimp only [r]
    linarith only [hs_lt]
  have hden : 0 < 1 - 2 * r := by
    linarith only [hr_lt]
  have hG : 0 < G := by
    dsimp only [G]
    have hgap : 0 < r - s := sub_pos.mpr hsr
    exact sq_pos_of_pos (mul_pos
      (mul_pos
        (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos (by simpa only [mul_one] using hr))
        (inv_pos.mpr (Real.sqrt_pos.2 (by
          simpa only [Book.Ch02.geometricDiscount_eq_old] using
            geometricDiscount_pos
              (mul_pos hgap (by norm_num : (0 : ℝ) < 2))))))
      (inv_pos.mpr (Real.sqrt_pos.2 (by
        simpa only [Book.Ch02.geometricDiscount_eq_old] using
          geometricDiscount_pos
            (mul_pos hs (by norm_num : (0 : ℝ) < 2))))))
  have hD : 0 < D := by
    dsimp only [D]
    have hd : (0 : ℝ) < d := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact mul_pos hG (mul_pos (by norm_num) hd)
  have hK : 0 < K := by
    dsimp only [K]
    exact mul_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos (div_pos hC₀ hden) _)
          (Real.rpow_pos_of_pos hr _))
        (Real.rpow_pos_of_pos (mul_pos hD hD) _)) hD
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hA.le)
  refine ⟨C, hC, ?_⟩
  intro a abar hS aRounded hRounded k u c e herror
  let Q : TriadicCube d := originCube d k
  let W : ℝ := cubeBesovScaleWeight 1 Q
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toH1.toFun)
  let E : ℝ := normalizedAffineCandidateError Q u.toH1.toFun c e
  let N : ℝ := euclideanNorm e
  let B : ℝ := E + cubeBesovW12LocalPoincareConstant d * N
  have hW : 0 ≤ W := cubeBesovScaleWeight_nonneg 1 Q
  have hL : 0 ≤ L := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _
  have hE : 0 ≤ E := normalizedAffineCandidateError_nonneg Q u.toH1.toFun c e
  have hN : 0 ≤ N := euclideanNorm_nonneg e
  have hP : 0 ≤ cubeBesovW12LocalPoincareConstant d :=
    cubeBesovW12LocalPoincareConstant_nonneg d
  have hB : 0 ≤ B := add_nonneg hE (mul_nonneg hP hN)
  have hpref :
      Book.Ch03.caccioppoliPrefactor C₀ Q aRounded r r ≤ K * W ^ 2 := by
    simpa only [Q, W, r, G, D, alpha, K] using
      caccioppoliPrefactor_roundedGenerationWeakError_le_one hC₀ hs hs_lt
        (geom := geom) a abar hS aRounded hRounded herror
  have hoscEq :
      Book.Ch03.interiorCaccioppoliParentOscillationL2Sq Q aRounded u = L ^ 2 := by
    unfold Book.Ch03.interiorCaccioppoliParentOscillationL2Sq
    simpa [L, cubeFluctuation, Book.Ch01.Legacy.normalizedAverage] using!
      Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q
        (cubeFluctuation Q u.toH1.toFun)
        (u.toH1.memL2_normalizedCubeMeasure.sub (memLp_const _))
  have hWL : W * L ≤ 2 * B := by
    simpa only [Q, W, L, E, N, B] using
      normalized_fluctuation_le_affine_error_add_slope Q u.toH1 c e
  have hcore := hinterior u hr hr (by linarith only [hr_lt] : r + r < 1)
  have hcoreBound :
      Book.Ch03.interiorCaccioppoliCoreEnergy Q aRounded (cubeCenter Q) u ≤
        K * (2 * B) ^ 2 := by
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q aRounded (cubeCenter Q) u ≤
          Book.Ch03.interiorCaccioppoliRHS C₀ Q aRounded r r u := hcore
      _ = Book.Ch03.caccioppoliPrefactor C₀ Q aRounded r r * L ^ 2 := by
        rw [Book.Ch03.interiorCaccioppoliRHS, hoscEq]
      _ ≤ (K * W ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hpref (sq_nonneg L)
      _ = K * (W * L) ^ 2 := by ring
      _ ≤ K * (2 * B) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (mul_nonneg hW hL) (mul_nonneg (by norm_num) hB)).2 hWL)
          hK.le
  have hroot :
      Real.sqrt (Book.Ch03.interiorCaccioppoliCoreEnergy
          Q aRounded (cubeCenter Q) u) ≤ 2 * Real.sqrt K * B := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hB, ?_⟩
    calc
      Book.Ch03.interiorCaccioppoliCoreEnergy Q aRounded (cubeCenter Q) u ≤
          K * (2 * B) ^ 2 := hcoreBound
      _ = (2 * Real.sqrt K * B) ^ 2 := by
        calc
          K * (2 * B) ^ 2 = (Real.sqrt K) ^ 2 * (2 * B) ^ 2 := by
            rw [Real.sq_sqrt hK.le]
          _ = (2 * Real.sqrt K * B) ^ 2 := by ring
  have hBA : B ≤ A * (E + N) := by
    have hP_le : cubeBesovW12LocalPoincareConstant d ≤ A := le_max_right _ _
    have hOne_le : 1 ≤ A := le_max_left _ _
    calc
      B = E + cubeBesovW12LocalPoincareConstant d * N := rfl
      _ ≤ A * E + A * N :=
        add_le_add
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOne_le hE)
          (mul_le_mul_of_nonneg_right hP_le hN)
      _ = A * (E + N) := by ring
  have hfactor : 2 * Real.sqrt K * A ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_left zero_le_one
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2)) aRounded
          (finiteCubeSolutionRestriction aRounded (by omega : k - 2 ≤ k) u).toH1 =
        Real.sqrt (Book.Ch03.interiorCaccioppoliCoreEnergy
          Q aRounded (cubeCenter Q) u) := by
      simpa only [Q] using
        finiteCubeRestriction_sub_two_energy_eq_coreEnergy aRounded k u
    _ ≤ 2 * Real.sqrt K * B := hroot
    _ ≤ 2 * Real.sqrt K * (A * (E + N)) :=
      mul_le_mul_of_nonneg_left hBA
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = (2 * Real.sqrt K * A) * (E + N) := by ring
    _ ≤ C * (E + N) :=
      mul_le_mul_of_nonneg_right hfactor (add_nonneg hE hN)
    _ = C * (normalizedAffineCandidateError
          (originCube d k) u.toH1.toFun c e + euclideanNorm e) := rfl

end

end HighContrast
end HCPolySupport
