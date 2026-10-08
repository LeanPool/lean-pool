/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.EnergyDefectBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ReferenceCubeAveragePullback

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentEnergyMapSupport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# EccentricityScaleDecay for the recent-difference energy map

This file proves the matrix-order, spectral and Minkowski-type facts the recent-difference energy
map of the diagonal weak-norm estimate needs: the equivalence of a block's spectral bound with its
operator norm at a positive semidefinite block, existence of a nonempty child-maximizer family, a
Minkowski-type inequality for a normalized sum of block pairings, the Loewner comparison
transported through a congruence, and the matrix-square-root identities that let it commute with
the normalizer.  The module serves the manuscript's `p.response.transfer`.
-/

section
/-!
## EccentricityScaleDecay part 2: matrix order, spectral carriers, Minkowski, head/tail

The matrix-order / spectral / Minkowski / head-tail package is in this file;
the remaining declarations are in `RecentHeadDefectHalves.lean`; the target itself is in
`DiagonalWeakNormBound.lean`.

Two declarations are public rather than `private` because their only consumers are in
the next module: `centered_metric_quadratic_le` and
`nonempty_childMaximizerFamily`.  Everything else in this file stays `private`.
-/

open HCPolySupport.HighContrast (CoeffSpace blockScale matSqrt matSqrt_spec)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Block quadratic-form order implies matrix Loewner order after flattening. -/
private theorem blockMatLoewnerLE_toFull_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro q
  let X : BlockVec d := ofFullBlockVec q
  have hquad :
      dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q) =
        blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) := by
    rw [← dotProduct_toFullBlockVec X
      (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X)]
    rw [toFullBlockVec_blockMatVecMul]
    simp [X]
  have hdiff :
      blockVecDot X
          (blockMatVecMul (ofFullBlockMat (toFullBlockMat B - toFullBlockMat A)) X) =
        blockVecDot X (blockMatVecMul B X) -
          blockVecDot X (blockMatVecMul A X) := by
    simpa using blockVecDot_blockMatVecMul_ofFullBlockMat_sub B A X
  have hle := hAB X
  change 0 ≤ dotProduct q (Matrix.mulVec (toFullBlockMat B - toFullBlockMat A) q)
  rw [hquad, hdiff]
  linarith only [hle]

omit [NeZero d] in
/-- A positive semidefinite full block is bounded above by its operator norm times
the doubled identity. -/
private theorem loewner_le_norm_identity (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    BlockMatLoewnerLE N
      (blockScale ‖toFullBlockMat N‖ (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := psd_dot_le_opNorm hN (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X
      (blockMatVecMul
        (blockScale ‖toFullBlockMat N‖ (Book.Ch02.blockIdentity d)) X) =
      ‖toFullBlockMat N‖ * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockScale_identity]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hL, hR]
  linarith only [h]

omit [NeZero d] in
/-- Quadratic comparison.  On positive semidefinite blocks the spectral
positive-part carrier `blockSpecBound` is exactly the full Euclidean operator norm. -/
theorem blockSpecBound_eq_norm_of_posSemidef (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    blockSpecBound N = ‖toFullBlockMat N‖ := by
  let S : Set ℝ :=
    {c : ℝ | 0 ≤ c ∧ BlockMatLoewnerLE N
      (blockScale c (Book.Ch02.blockIdentity d))}
  have hw : ‖toFullBlockMat N‖ ∈ S :=
    ⟨norm_nonneg _, loewner_le_norm_identity N hN⟩
  have hbelow : ∀ c ∈ S, ‖toFullBlockMat N‖ ≤ c := by
    intro c hc
    have hscale :
        (toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d))).IsHermitian := by
      rw [toFullBlockMat_blockScale_identity]
      simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial,
        Matrix.isHermitian_one.eq]
    have hfull := blockMatLoewnerLE_toFull_le hN.isHermitian hscale hc.2
    rw [toFullBlockMat_blockScale_identity] at hfull
    exact GeometricMean.norm_le_of_le_smul_one hN hc.1 hfull
  change sInf S = ‖toFullBlockMat N‖
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hc => hc.1⟩ hw
  · exact le_csInf ⟨_, hw⟩ hbelow

omit [NeZero d] in
private theorem posDef_sqrt_full {m : FullBlockMat d} (hm : m.PosDef) :
    (CFC.sqrt m).PosDef :=
  Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.sqrt m (Matrix.isStrictlyPositive_iff_posDef.mpr hm))

omit [NeZero d] in
private theorem cfc_sqrt_inv_full {m : FullBlockMat d} (hm : m.PosDef) :
    (CFC.sqrt m)⁻¹ = CFC.sqrt m⁻¹ := by
  rw [eq_comm,
    CFC.sqrt_eq_iff _ _ hm.inv.posSemidef.nonneg
      (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg m)).inv.nonneg,
    ← sq, Matrix.inv_pow', CFC.sq_sqrt m]

omit [NeZero d] in
private theorem matSqrt_mul_matSqrt_inv_full {m : FullBlockMat d} (hm : m.PosDef) :
    matSqrt m * matSqrt m⁻¹ = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_eq_cfc_sqrt hm.inv.posSemidef,
    ← cfc_sqrt_inv_full hm]
  exact Matrix.mul_nonsing_inv (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt_full hm).isUnit)

omit [NeZero d] in
private theorem matSqrt_inv_mul_matSqrt_full {m : FullBlockMat d} (hm : m.PosDef) :
    matSqrt m⁻¹ * matSqrt m = 1 := by
  rw [matSqrt_eq_cfc_sqrt hm.posSemidef, matSqrt_eq_cfc_sqrt hm.inv.posSemidef,
    ← cfc_sqrt_inv_full hm]
  exact Matrix.nonsing_inv_mul (CFC.sqrt m)
    ((Matrix.isUnit_iff_isUnit_det (CFC.sqrt m)).mp (posDef_sqrt_full hm).isUnit)

omit [NeZero d] in
/-- Quadratic comparison.  A centered defect measured in `M⁻¹` is
controlled by the `M`-relative size of `E`, the `E`-normalized defect norm, and the
`E`-quadratic load. -/
theorem centered_metric_quadratic_le {M E D : FullBlockMat d}
    (hM : M.PosDef) (hE : E.PosDef) (x : FullBlockVec d) :
    (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) ≤
      ‖matSqrt M⁻¹ * E * matSqrt M⁻¹‖ *
        ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 *
          (x ⬝ᵥ E *ᵥ x) := by
  set SM : FullBlockMat d := matSqrt M⁻¹ with hSM
  set SE : FullBlockMat d := matSqrt E with hSE
  set SI : FullBlockMat d := matSqrt E⁻¹ with hSI
  set B : FullBlockMat d := SI * D * SI with hB
  set N : FullBlockMat d := SM * SE with hN
  set y : FullBlockVec d := SE *ᵥ x with hy
  set z : FullBlockVec d := B *ᵥ y with hz
  set w : FullBlockVec d := N *ᵥ z with hw
  have hSMsymm : SMᴴ = SM := by
    rw [hSM]
    exact (matSqrt_spec hM.inv.posSemidef).1.isHermitian
  have hSEsymm : SEᴴ = SE := by
    rw [hSE]
    exact (matSqrt_spec hE.posSemidef).1.isHermitian
  have hSMSM : SM * SM = M⁻¹ := by
    rw [hSM]
    exact (matSqrt_spec hM.inv.posSemidef).2
  have hSESE : SE * SE = E := by
    rw [hSE]
    exact (matSqrt_spec hE.posSemidef).2
  have hSESI : SE * SI = 1 := by
    rw [hSE, hSI]
    exact matSqrt_mul_matSqrt_inv_full hE
  have hSISE : SI * SE = 1 := by
    rw [hSI, hSE]
    exact matSqrt_inv_mul_matSqrt_full hE
  have hfactorD : SE * B * SE = D := by
    rw [hB]
    calc
      SE * (SI * D * SI) * SE = (SE * SI) * D * (SI * SE) := by
        noncomm_ring
      _ = D := by rw [hSESI, hSISE, Matrix.one_mul, Matrix.mul_one]
  have hquadM :
      (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) =
        (SM *ᵥ (D *ᵥ x)) ⬝ᵥ (SM *ᵥ (D *ᵥ x)) := by
    rw [← hSMSM, ← Matrix.mulVec_mulVec]
    exact GeometricMean.dotProduct_mulVec_symm
      (by rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hSMsymm) _ _
  have hwform : w = SM *ᵥ (D *ᵥ x) := by
    have hmatrix : N * B * SE = SM * D := by
      rw [hN]
      calc
        SM * SE * B * SE = SM * (SE * B * SE) := by noncomm_ring
        _ = SM * D := by rw [hfactorD]
    calc
      w = N *ᵥ (B *ᵥ (SE *ᵥ x)) := by rw [hw, hz, hy]
      _ = (N * B * SE) *ᵥ x := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = (SM * D) *ᵥ x := by rw [hmatrix]
      _ = SM *ᵥ (D *ᵥ x) := by rw [Matrix.mulVec_mulVec]
  have hyquad : y ⬝ᵥ y = x ⬝ᵥ E *ᵥ x := by
    calc
      y ⬝ᵥ y = (SE *ᵥ x) ⬝ᵥ (SE *ᵥ x) := by rw [hy]
      _ = x ⬝ᵥ SE *ᵥ (SE *ᵥ x) :=
        (GeometricMean.dotProduct_mulVec_symm
          (by rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hSEsymm) _ _).symm
      _ = x ⬝ᵥ (SE * SE) *ᵥ x := by rw [Matrix.mulVec_mulVec]
      _ = x ⬝ᵥ E *ᵥ x := by rw [hSESE]
  have hNnorm : ‖N‖ ^ 2 = ‖matSqrt M⁻¹ * E * matSqrt M⁻¹‖ := by
    have hNN : N * Nᴴ = SM * E * SM := by
      rw [hN, Matrix.conjTranspose_mul, hSEsymm, hSMsymm]
      calc
        SM * SE * (SE * SM) = SM * (SE * SE) * SM := by noncomm_ring
        _ = SM * E * SM := by rw [hSESE]
    rw [pow_two, ← CStarRing.norm_self_mul_star,
      Matrix.star_eq_conjTranspose, hNN, hSM]
  have hwle : w ⬝ᵥ w ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := by
    rw [hw]
    exact vecSq_mulVec_le N z
  have hzle : z ⬝ᵥ z ≤ ‖B‖ ^ 2 * (y ⬝ᵥ y) := by
    rw [hz]
    exact vecSq_mulVec_le B y
  have hN0 : 0 ≤ ‖N‖ ^ 2 := sq_nonneg _
  have hstep : ‖N‖ ^ 2 * (z ⬝ᵥ z) ≤
      ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) :=
    mul_le_mul_of_nonneg_left hzle hN0
  calc
    (D *ᵥ x) ⬝ᵥ M⁻¹ *ᵥ (D *ᵥ x) = w ⬝ᵥ w := by
      rw [hquadM, hwform]
    _ ≤ ‖N‖ ^ 2 * (z ⬝ᵥ z) := hwle
    _ ≤ ‖N‖ ^ 2 * (‖B‖ ^ 2 * (y ⬝ᵥ y)) := hstep
    _ = ‖matSqrt M⁻¹ * E * matSqrt M⁻¹‖ *
          ‖matSqrt E⁻¹ * D * matSqrt E⁻¹‖ ^ 2 *
            (x ⬝ᵥ E *ᵥ x) := by
      rw [hNnorm, hB, hyquad]
      ring

omit [NeZero d] in
/-- Parent/child decomposition.  Child response maximizers can be chosen
simultaneously at every depth and cell label. -/
theorem nonempty_childMaximizerFamily
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty ((n : ℕ) → (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r
        (respCoeffMinus F a)) := by
  exact ⟨fun n w => Classical.choice
    (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter q hq (t - (n : ℤ)) w F
      a p r)⟩

omit [NeZero d] in
private theorem sum_blockVecDot_eq_sum_prod {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    ∑ z ∈ Z, blockVecDot (u z) (v z) =
      ∑ p ∈ Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)),
        Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 *
          Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.sum_sum_type]
  rfl

omit [NeZero d] in
private theorem sq_sum_blockVecDot_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2 ≤
      (∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ∑ z ∈ Z, blockVecDot (v z) (v z) := by
  classical
  set S : Finset (iota × (Fin d ⊕ Fin d)) :=
    Z ×ˢ (Finset.univ : Finset (Fin d ⊕ Fin d)) with hS
  set U : iota × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (u p.1).1 i) (fun i => (u p.1).2 i) p.2 with hU
  set V : iota × (Fin d ⊕ Fin d) → ℝ :=
    fun p => Sum.elim (fun i => (v p.1).1 i) (fun i => (v p.1).2 i) p.2 with hV
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := S) (f := U) (g := V)
  have hUU : ∑ p ∈ S, U p ^ 2 = ∑ z ∈ Z, blockVecDot (u z) (u z) := by
    rw [sum_blockVecDot_eq_sum_prod Z u u]
    exact Finset.sum_congr rfl fun p _ => pow_two (U p)
  have hVV : ∑ p ∈ S, V p ^ 2 = ∑ z ∈ Z, blockVecDot (v z) (v z) := by
    rw [sum_blockVecDot_eq_sum_prod Z v v]
    exact Finset.sum_congr rfl fun p _ => pow_two (V p)
  rw [sum_blockVecDot_eq_sum_prod Z u v, ← hUU, ← hVV]
  exact hcs

omit [NeZero d] in
private theorem sq_normalized_sum_blockVecDot_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z))) ^ 2 ≤
      (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z))) := by
  have hkey := sq_sum_blockVecDot_le Z u v
  have hc : 0 ≤ (((Z.card : ℝ)⁻¹) ^ 2) := sq_nonneg _
  calc
    (((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2) =
        (Z.card : ℝ)⁻¹ ^ 2 * (∑ z ∈ Z, blockVecDot (u z) (v z)) ^ 2 := by
      ring
    _ ≤ (Z.card : ℝ)⁻¹ ^ 2 *
          ((∑ z ∈ Z, blockVecDot (u z) (u z)) *
            ∑ z ∈ Z, blockVecDot (v z) (v z)) :=
      mul_le_mul_of_nonneg_left hkey hc
    _ = ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)) *
        ((Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z)) := by ring

omit [NeZero d] in
private theorem blockVecDot_add_self (u v : BlockVec d) :
    blockVecDot (u + v) (u + v) =
      blockVecDot u u + 2 * blockVecDot u v + blockVecDot v v := by
  have hd : ∀ a b : Vec d,
      vecDot (a + b) (a + b) = vecDot a a + 2 * vecDot a b + vecDot b b := by
    intro a b
    rw [vecDot_add_left, vecDot_add_right, vecDot_add_right, vecDot_comm b a]
    ring
  change vecDot (u.1 + v.1) (u.1 + v.1) + vecDot (u.2 + v.2) (u.2 + v.2) = _
  rw [hd u.1 v.1, hd u.2 v.2]
  simp only [blockVecDot]
  ring

omit [NeZero d] in
/-- Parent/child decomposition.  The normalized finite-cell `L²` length
obeys Minkowski's inequality for doubled vectors. -/
theorem normalized_blockL2_add_le {iota : Type*}
    (Z : Finset iota) (u v : iota → BlockVec d) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ z ∈ Z, blockVecDot (u z + v z) (u z + v z)) ≤
      Real.sqrt ((Z.card : ℝ)⁻¹ *
          ∑ z ∈ Z, blockVecDot (u z) (u z)) +
        Real.sqrt ((Z.card : ℝ)⁻¹ *
          ∑ z ∈ Z, blockVecDot (v z) (v z)) := by
  let A : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (u z)
  let B : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (v z) (v z)
  let C : ℝ := (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z) (v z)
  have hself : ∀ x : BlockVec d, 0 ≤ blockVecDot x x := by
    intro x
    exact add_nonneg (vecNormSq_nonneg x.1) (vecNormSq_nonneg x.2)
  have hA0 : 0 ≤ A := mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hself (u z))
  have hB0 : 0 ≤ B := mul_nonneg (by positivity) (Finset.sum_nonneg fun z _ => hself (v z))
  have hexp :
      (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, blockVecDot (u z + v z) (u z + v z) =
        A + 2 * C + B := by
    simp_rw [blockVecDot_add_self]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp only [A, B, C]
    ring
  have hCS : C ≤ Real.sqrt A * Real.sqrt B := by
    have hsq : C ^ 2 ≤ A * B := sq_normalized_sum_blockVecDot_le Z u v
    calc
      C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B
  have hexpand :
      (Real.sqrt A + Real.sqrt B) ^ 2 =
        A + 2 * (Real.sqrt A * Real.sqrt B) + B := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  rw [hexp]
  calc
    Real.sqrt (A + 2 * C + B) ≤
        Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hexpand]
      linarith only [hCS]
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (by positivity)

/-! ### Helper lemmas.  The LEFT-hand side of the target is not literally a
`cellAverageFamily`: it is the family of `M_0^{1/2}`-transported, `U_t`-recentred cell averages.
The Jensen and summability lemmas are stated for a bare `cellAverageFamily`, so none applies to
the goal.  The transport and recentring helpers close that gap (they commute with the cell
average, given integrability), and the window-split helpers supply the split at `H` that the printed
right-hand side has: a finite head weighted exactly as `weakCellSum` is, plus a geometric tail
whose weight is dominated by the printed `3^{-alpha H}`. -/

end

end HCPolySupport.HighContrast.Multiscale
end
