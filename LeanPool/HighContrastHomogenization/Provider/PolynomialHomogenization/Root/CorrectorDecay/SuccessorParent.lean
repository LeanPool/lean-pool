/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.ExactFiniteResponse
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.LpTriangle
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSuccessorDifference
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.SuccessorParent

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

theorem successor_toFun_eq_correction_sub
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    (finiteAffineSuccessorDifference a m e).toH1.toFun =
      fun x ↦ (finiteAffineCorrection a (m + 1) e).toH1Function.toFun x -
        (finiteAffineCorrection a m e).toH1Function.toFun x := by
  funext x
  rw [congrFun (finiteAffineSuccessorDifference_toFun a m e) x]
  simp only [finiteAffineCubeSolution, finiteAffineSolution_toH1,
    H1Function.add_toFun, finiteAffineBoundaryH1_toFun]
  ring

theorem weight_pred_eq_three_mul
    {d : ℕ} (m : ℤ) :
    cubeBesovScaleWeight 1 (originCube d (m - 1)) =
      3 * cubeBesovScaleWeight 1 (originCube d m) := by
  simpa using cubeBesovScaleWeight_one_originCube_sub_nat (d := d) m 1

/-- The successive finite affine difference restricted three centered scales
inside its outer cube. -/
@[expose]
noncomputable def successorInnerRestriction
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d (m - 1 - 2)) a :=
  finiteCubeSolutionRestriction a (by omega : m - 1 - 2 ≤ m - 1)
    (finiteCubeSolutionRestriction a (by omega : m - 1 ≤ m)
      (finiteAffineSuccessorDifference a m e))

private theorem nextCorrection_memLp_parent
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    MemLp (finiteAffineCorrection a (m + 1) e).toH1Function.toFun
      (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d m)) := by
  simpa only [show m + 1 - 1 = m by omega] using
    memLp_originCube_pred (m + 1)
      (finiteAffineCorrection a (m + 1) e).toH1Function.toFun
      (finiteAffineCorrection a (m + 1) e).toH1Function.memL2_normalizedCubeMeasure

private theorem successorRawBookkeeping
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) {B0 B1 : ℝ}
    (h0 : cubeBesovScaleWeight 1 (originCube d m) *
        cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
          (finiteAffineCorrection a m e).toH1Function.toFun ≤ B0)
    (h1 : cubeBesovScaleWeight 1 (originCube d (m + 1)) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (finiteAffineCorrection a (m + 1) e).toH1Function.toFun ≤ B1) :
    cubeBesovScaleWeight 1 (originCube d (m - 1)) *
        cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
          (finiteAffineSuccessorDifference a m e).toH1.toFun ≤
      3 * ((3 * ((3 ^ d : ℕ) : ℝ)) * B1 + B0) := by
  let f0 : Vec d → ℝ :=
    (finiteAffineCorrection a m e).toH1Function.toFun
  let f1 : Vec d → ℝ :=
    (finiteAffineCorrection a (m + 1) e).toH1Function.toFun
  let w : Vec d → ℝ :=
    (finiteAffineSuccessorDifference a m e).toH1.toFun
  let Wpred := cubeBesovScaleWeight 1 (originCube d (m - 1))
  let Wmid := cubeBesovScaleWeight 1 (originCube d m)
  let Wsucc := cubeBesovScaleWeight 1 (originCube d (m + 1))
  have hw : w = fun x ↦ f1 x - f0 x := by
    simpa only [w, f1, f0] using successor_toFun_eq_correction_sub a m e
  have hf0 : MemLp f0 (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    exact (finiteAffineCorrection a m e).toH1Function.memL2_normalizedCubeMeasure
  have hf1 : MemLp f1 (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    exact nextCorrection_memLp_parent a m e
  have hWpred : 0 ≤ Wpred := cubeBesovScaleWeight_nonneg 1 _
  have hpredMid : Wpred = 3 * Wmid := by
    simpa only [Wpred, Wmid] using weight_pred_eq_three_mul (d := d) m
  have hmidSucc : Wmid = 3 * Wsucc := by
    simpa only [Wmid, Wsucc, show m + 1 - 1 = m by omega] using
      weight_pred_eq_three_mul (d := d) (m + 1)
  have h0' : Wmid * cubeLpNorm (originCube d (m - 1))
      (2 : ℝ≥0∞) f0 ≤ B0 := by
    exact h0
  have h1' : Wsucc * cubeLpNorm (originCube d m)
      (2 : ℝ≥0∞) f1 ≤ B1 := by
    exact h1
  have hpriced := weightedSuccessorPrice_le m f0 f1 w
    Wpred Wmid Wsucc B0 B1 hw hf0 hf1 hWpred hpredMid hmidSucc h0' h1'
  exact hpriced

private theorem parent_price_algebra
    {D Cresp E0 E1 N : ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ Cresp)
    (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hN : 0 ≤ N) :
    3 * ((3 * D) * (Cresp * E1 * N) + Cresp * E0 * N) ≤
      3 * (1 + 3 * D) * (1 + Cresp) * (E0 + E1) * N := by
  calc
    3 * ((3 * D) * (Cresp * E1 * N) + Cresp * E0 * N) ≤
        3 * ((1 + 3 * D) * Cresp * (E0 + E1) * N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        (3 * D) * (Cresp * E1 * N) + Cresp * E0 * N =
            (Cresp * N) * ((3 * D) * E1 + E0) := by ring
        _ ≤ (Cresp * N) * ((1 + 3 * D) * (E0 + E1)) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hN)
          calc
            (3 * D) * E1 + E0 ≤
                (3 * D) * E1 + E0 + (E1 + (3 * D) * E0) :=
              le_add_of_nonneg_right
                (add_nonneg hE1 (mul_nonneg (mul_nonneg (by norm_num) hD) hE0))
            _ = (1 + 3 * D) * (E0 + E1) := by ring
        _ = (1 + 3 * D) * Cresp * (E0 + E1) * N := by ring
    _ ≤ 3 * (1 + 3 * D) * (1 + Cresp) * (E0 + E1) * N := by
      calc
        3 * ((1 + 3 * D) * Cresp * (E0 + E1) * N) =
            (3 * (1 + 3 * D) * (E0 + E1) * N) * Cresp := by ring
        _ ≤ (3 * (1 + 3 * D) * (E0 + E1) * N) * (1 + Cresp) :=
          mul_le_mul_of_nonneg_left (by linarith only [hC])
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num)
                  (add_nonneg (by norm_num)
                    (mul_nonneg (by norm_num) hD)))
                (add_nonneg hE0 hE1)) hN)
        _ = 3 * (1 + 3 * D) * (1 + Cresp) * (E0 + E1) * N := by ring

private theorem successorResponseRaw
    {d : ℕ} [NeZero d] {g Cresp : ℝ}
    (hresponse : ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ) (e : Vec d),
      scalarIdentityWeakError a (printCertificateOrder g) m ≤ 1 →
      let u := (finiteAffineSolution a m e).toH1
      let E := scalarIdentityWeakError a (printCertificateOrder g) m
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g)
          (fun x ↦ u.grad x - e) ≤ Cresp * E * euclideanNorm e ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          (originCube d m) (printCertificateOrder g)
          (fun x ↦ matVecMul (Book.Ch03.publicCoeffField
            (originCube d m) a x) (u.grad x) - e) ≤
        Cresp * E * euclideanNorm e ∧
      cubeBesovScaleWeight 1 (originCube d m) *
          cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
            (finiteAffineCorrection a m e).toH1Function.toFun ≤
        Cresp * E * euclideanNorm e)
    (a : Book.Ch03.CoeffFamily d) (m : ℤ) (e : Vec d)
    (herr0 : scalarIdentityWeakError a (printCertificateOrder g) m ≤ 1)
    (herr1 : scalarIdentityWeakError a (printCertificateOrder g) (m + 1) ≤ 1) :
    cubeBesovScaleWeight 1 (originCube d (m - 1)) *
        cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
          (finiteAffineSuccessorDifference a m e).toH1.toFun ≤
      3 * ((3 * ((3 ^ d : ℕ) : ℝ)) *
          (Cresp * scalarIdentityWeakError a (printCertificateOrder g) (m + 1) *
            euclideanNorm e) +
        Cresp * scalarIdentityWeakError a (printCertificateOrder g) m *
          euclideanNorm e) := by
  have hrow0 := hresponse a m e herr0
  have hrow1 := hresponse a (m + 1) e herr1
  have hrow1Value : cubeBesovScaleWeight 1 (originCube d (m + 1)) *
      cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
        (finiteAffineCorrection a (m + 1) e).toH1Function.toFun ≤
      Cresp * scalarIdentityWeakError a (printCertificateOrder g) (m + 1) *
        euclideanNorm e := by
    simpa only [show m + 1 - 1 = m by omega] using hrow1.2.2
  exact successorRawBookkeeping a m e hrow0.2.2 hrow1Value

/-- The two finite response value rows control the successor difference one
scale inside its outer cube. -/
theorem exists_identitySuccessorParentL2Constant
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ) (e : Vec d),
        scalarIdentityWeakError a (printCertificateOrder g) m ≤ 1 →
        scalarIdentityWeakError a (printCertificateOrder g) (m + 1) ≤ 1 →
        cubeBesovScaleWeight 1 (originCube d (m - 1)) *
            cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
              (finiteAffineSuccessorDifference a m e).toH1.toFun ≤
          C * (scalarIdentityWeakError a (printCertificateOrder g) m +
              scalarIdentityWeakError a (printCertificateOrder g) (m + 1)) *
            euclideanNorm e := by
  obtain ⟨Cresp, hCresp, hresponse⟩ :=
    exists_identityFiniteResponseConstant d g hg
  let D : ℝ := ((3 ^ d : ℕ) : ℝ)
  let C : ℝ := 3 * (1 + 3 * D) * (1 + Cresp)
  have hC : 0 < C := by dsimp only [C, D]; positivity
  refine ⟨C, hC, ?_⟩
  intro a m e herr0 herr1
  have hraw := successorResponseRaw hresponse a m e herr0 herr1
  let E0 := scalarIdentityWeakError a (printCertificateOrder g) m
  let E1 := scalarIdentityWeakError a (printCertificateOrder g) (m + 1)
  let N := euclideanNorm e
  have halg := parent_price_algebra
    (D := D) (Cresp := Cresp) (E0 := E0) (E1 := E1) (N := N)
    (by dsimp only [D]; positivity) hCresp
    (scalarIdentityWeakError_nonneg _ _ _)
    (scalarIdentityWeakError_nonneg _ _ _) (euclideanNorm_nonneg e)
  exact hraw.trans (by simpa only [C, D, E0, E1, N] using halg)

end

end HighContrast
end HCPolySupport
