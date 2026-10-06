/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderDualBesovPerturbationAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ConstantMatrixDualIdentityReduction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceDualIdentityReduction

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderNearIdentityDualAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Near-identity absorption for cube full-dual regularity

An `A`-solenoidal potential field is an identity-solenoidal field after the
defect `(A - I)w` is moved into the datum.  The estimates below isolate the
exact smallness coefficient required by this reduction.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Identity-coefficient cube dual regularity with a named uniform constant,
at the order selected after `g`. -/
@[expose]
def PrintOrderIdentityCubeDualRegularityWithConstant
    (d : ℕ) [NeZero d] (g Cid : ℝ) : Prop :=
  0 ≤ Cid ∧
    ∀ (Q : TriadicCube d) {w F : Vec d → Vec d},
      MemVectorL2 (cubeSet Q) F →
      IsPotentialZeroTraceOn (cubeSet Q) w →
      IsSolenoidalOn (cubeSet Q) (fun x ↦ w x + F x) →
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) w ≤
        Cid * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) F ∧
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) (fun x ↦ w x + F x) ≤
        Cid * cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) F

private theorem matVecMul_one_absorption {d : ℕ} (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

private theorem matVecMul_eq_add_defect_absorption
    {d : ℕ} (A : Mat d) (x : Vec d) :
    matVecMul A x = x + matVecMul (A - 1) x := by
  rw [sub_matVecMul, matVecMul_one_absorption]
  abel

/-- The operator-norm defect bound implies the action-size smallness needed
by the component-sum full-dual norm. -/
theorem identityActionSmallness_of_opNorm_defect
    {d : ℕ} {Cid eps : ℝ} (hCid : 0 ≤ Cid)
    (hsmall : Cid * ((d : ℝ) ^ 2 * eps) ≤ 1 / 2)
    {E : Mat d} (hE : ‖E‖ ≤ eps) :
    Cid * dualBesovMatrixActionSize E ≤ 1 / 2 := by
  have haction : dualBesovMatrixActionSize E ≤ (d : ℝ) ^ 2 * eps := by
    exact (dualBesovMatrixActionSize_le_dim_sq_mul_norm E).trans
      (mul_le_mul_of_nonneg_left hE (sq_nonneg (d : ℝ)))
  exact (mul_le_mul_of_nonneg_left haction hCid).trans hsmall

/-- Quantitative perturbation lemma for one constant matrix and one cube.
The first coefficient also carries an upper bound for the action of `A`; the
second coefficient is the absorbed identity constant. -/
theorem printOrder_dual_bounds_of_identity_of_action_absorption
    {d : ℕ} [NeZero d] {g Cid B : ℝ}
    (hg : g ∈ Ico (0 : ℝ) 1)
    (hidentity : PrintOrderIdentityCubeDualRegularityWithConstant d g Cid)
    {A : Mat d} (hAaction : dualBesovMatrixActionSize A ≤ B)
    (hB : 0 ≤ B)
    (hsmall : Cid * dualBesovMatrixActionSize (A - 1) ≤ 1 / 2)
    (Q : TriadicCube d) {w F : Vec d → Vec d}
    (hF : MemVectorL2 (cubeSet Q) F)
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q)
      (fun x ↦ matVecMul A (w x) + F x)) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo
        Q (printCertificateOrder g) (fun x ↦ matVecMul A (w x)) ≤
      (B * (2 * Cid)) *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) F ∧
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo
        Q (printCertificateOrder g)
          (fun x ↦ matVecMul A (w x) + F x) ≤
      (2 * Cid) *
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
          Q (printCertificateOrder g) F := by
  let s : ℝ := printCertificateOrder g
  let E : Mat d := A - 1
  let F' : Vec d → Vec d := fun x ↦ matVecMul E (w x) + F x
  let N : (Vec d → Vec d) → ℝ :=
    fun H ↦ cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s H
  have hs : 0 < s := by
    simpa only [s] using (printOrder_margins hg).1
  have hCid : 0 ≤ Cid := hidentity.1
  have hwL2 : MemVectorL2 (cubeSet Q) w :=
    Book.Ch01.IsPotentialZeroTraceOn.memVectorL2 hw
  have hEL2 : MemVectorL2 (cubeSet Q) (fun x ↦ matVecMul E (w x)) :=
    memVectorL2_constMatrix_mul E hwL2
  have hF'L2 : MemVectorL2 (cubeSet Q) F' := by
    simpa only [F', Pi.add_apply] using! hEL2.add hF
  have hfield : (fun x ↦ w x + F' x) =
      (fun x ↦ matVecMul A (w x) + F x) := by
    funext x
    dsimp only [F', E]
    have hAw := matVecMul_eq_add_defect_absorption A (w x)
    calc
      w x + (matVecMul (A - 1) (w x) + F x) =
          (w x + matVecMul (A - 1) (w x)) + F x := by abel
      _ = matVecMul A (w x) + F x := by rw [hAw]
  have hsolIdentity : IsSolenoidalOn (cubeSet Q) (fun x ↦ w x + F' x) := by
    rw [hfield]
    exact hsol
  have hidentityBounds := hidentity.2 Q hF'L2 hw hsolIdentity
  have hNw0 : 0 ≤ N w := by
    exact cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg Q s w
  have hNF0 : 0 ≤ N F := by
    exact cubeScaleNormalizedDualNegativeBesovVectorNormTwo_nonneg Q s F
  have hdelta0 : 0 ≤ dualBesovMatrixActionSize E :=
    dualBesovMatrixActionSize_nonneg E
  have hdefectNorm :
      N (fun x ↦ matVecMul E (w x)) ≤
        dualBesovMatrixActionSize E * N w := by
    simpa only [N] using
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo_matVecMul_le
        Q hs E w hwL2
  have hdatumNorm : N F' ≤ dualBesovMatrixActionSize E * N w + N F := by
    calc
      N F' = N (fun x ↦ matVecMul E (w x) + F x) := rfl
      _ ≤ N (fun x ↦ matVecMul E (w x)) + N F := by
        simpa only [N] using
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo_add_le
            Q hs (fun x ↦ matVecMul E (w x)) F hEL2 hF
      _ ≤ dualBesovMatrixActionSize E * N w + N F :=
        by simpa only [add_comm] using add_le_add_right hdefectNorm (N F)
  have hgradientRaw : N w ≤
      Cid * (dualBesovMatrixActionSize E * N w + N F) := by
    calc
      N w ≤ Cid * N F' := by simpa only [N, s] using hidentityBounds.1
      _ ≤ Cid * (dualBesovMatrixActionSize E * N w + N F) :=
        mul_le_mul_of_nonneg_left hdatumNorm hCid
  have hcoefficient :
      (Cid * dualBesovMatrixActionSize E) * N w ≤ (1 / 2) * N w :=
    mul_le_mul_of_nonneg_right (by simpa only [E] using hsmall) hNw0
  have hgradientHalf : N w ≤ (1 / 2) * N w + Cid * N F := by
    calc
      N w ≤ (Cid * dualBesovMatrixActionSize E) * N w + Cid * N F := by
        calc
          N w ≤ Cid * (dualBesovMatrixActionSize E * N w + N F) := hgradientRaw
          _ = (Cid * dualBesovMatrixActionSize E) * N w + Cid * N F := by ring
      _ ≤ (1 / 2) * N w + Cid * N F :=
        by simpa only [add_comm] using
          add_le_add_right hcoefficient (Cid * N F)
  have hgradient : N w ≤ 2 * Cid * N F := by
    linarith only [hgradientHalf]
  have hdatumTwo : N F' ≤ 2 * N F := by
    have hdeltaGradient :
        dualBesovMatrixActionSize E * N w ≤
          dualBesovMatrixActionSize E * (2 * Cid * N F) :=
      mul_le_mul_of_nonneg_left hgradient hdelta0
    have hcoef : 2 * (Cid * dualBesovMatrixActionSize E) + 1 ≤ 2 := by
      have hsmall' : Cid * dualBesovMatrixActionSize E ≤ 1 / 2 := by
        simpa only [E] using hsmall
      linarith only [hsmall']
    calc
      N F' ≤ dualBesovMatrixActionSize E * N w + N F := hdatumNorm
      _ ≤ dualBesovMatrixActionSize E * (2 * Cid * N F) + N F :=
        by simpa only [add_comm] using add_le_add_right hdeltaGradient (N F)
      _ = (2 * (Cid * dualBesovMatrixActionSize E) + 1) * N F := by ring
      _ ≤ 2 * N F := mul_le_mul_of_nonneg_right hcoef hNF0
  have htotal : N (fun x ↦ matVecMul A (w x) + F x) ≤
      (2 * Cid) * N F := by
    calc
      N (fun x ↦ matVecMul A (w x) + F x) = N (fun x ↦ w x + F' x) := by
        exact congrArg N hfield.symm
      _ ≤ Cid * N F' := by simpa only [N, s] using hidentityBounds.2
      _ ≤ Cid * (2 * N F) := mul_le_mul_of_nonneg_left hdatumTwo hCid
      _ = (2 * Cid) * N F := by ring
  have hmatrix : N (fun x ↦ matVecMul A (w x)) ≤
      dualBesovMatrixActionSize A * N w := by
    simpa only [N] using
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo_matVecMul_le
        Q hs A w hwL2
  have hmatrixB : N (fun x ↦ matVecMul A (w x)) ≤ B * N w :=
    hmatrix.trans (mul_le_mul_of_nonneg_right hAaction hNw0)
  constructor
  · calc
      N (fun x ↦ matVecMul A (w x)) ≤ B * N w := hmatrixB
      _ ≤ B * (2 * Cid * N F) := mul_le_mul_of_nonneg_left hgradient hB
      _ = (B * (2 * Cid)) * N F := by ring
  · exact htotal

end

end HighContrast
end HCPolySupport
