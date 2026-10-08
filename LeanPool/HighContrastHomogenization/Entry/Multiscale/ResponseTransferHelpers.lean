/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SelectionData
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Analysis.ReferenceComparison
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenCongruence
public import Mathlib.Analysis.Matrix.Order

/-!
# High-contrast homogenization: Entry.Multiscale.ResponseTransferHelpers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Matrix-analysis helpers for the K3/K4 kernels of the `p.response.transfer` decomposition

Generic matrix-order and Schur-complement lemmas, and the canonical-imbalance comparison
`𝔡(X) ≤ c ↔ X ≤ c • 𝐑X⁻¹𝐑`, used by `ResponseBlockObjects` and `EccentricityScaleDecay`.
-/

open HCPolySupport.HighContrast (IsSkewMat blockContrast blockContrast_le
  blockMatEntry_blockScale blockScale isUnit_det_lowerRight matSqrt matSqrt_spec normalizedBlock
  posDef_lowerRight schurSigma schurSigmaStar schurSkew)
namespace HCPolySupport.HighContrast.Multiscale

open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

/-- The canonical imbalance `𝔡(A)` of a block (`e.response.canonical.imbalance`, near
`e.response.canonical.imbalance`):
`𝔡(A) := |(𝐑A⁻¹𝐑)^{-1/2}A(𝐑A⁻¹𝐑)^{-1/2}|`, where `𝐑` is the fixed swap block near
`e.scale.selection.complete.profile`
(`blockSwap`). It is rendered
faithfully via `normalizedBlock`/`blockOpNorm`/`blockSwap`
(`HCPoly/Entry/Setup/ProjectiveDistance.lean`), not
via `explicitCanonicalMetric` (an unrelated adapted-grid reference object). -/
@[expose]
noncomputable def canonicalImbalance {d : ℕ} (A : BlockMat d) : ℝ :=
  blockOpNorm (normalizedBlock A
    (ofFullBlockMat
      (toFullBlockMat (blockSwap d) * (toFullBlockMat A)⁻¹ * toFullBlockMat (blockSwap d))))

/-! ### Private helpers for **K3** (the canonical comparison).

The route: `𝔡(X) ≤ c` is equivalent to the Loewner inequality
`X ≤ c • (𝐑 X⁻¹ 𝐑)`, because with `S := (𝐑 X 𝐑)^{1/2}` one has `S⁻¹S⁻¹ = 𝐑X⁻¹𝐑` and
`𝔡(X) = ‖S X S‖`, and congruence by `S`, resp. `S⁻¹`, turns each side into the other.
Then `M ≤ (1+η)A ≤ (1+η)(1+δ)·𝐑A⁻¹𝐑 ≤ (1+η)²(1+δ)·𝐑M⁻¹𝐑`, the last step by
antitonicity of the inverse and congruence by `𝐑`; finally `(1+η)² ≤ (1+η)³/(1-η)`. -/

/-- A positive semidefinite real matrix is symmetric. -/
theorem transpose_eq_of_psd {n : Type*} {P : Matrix n n ℝ}
    (hP : P.PosSemidef) : Pᵀ = P := by
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hP.isHermitian.eq

/-- `c • 1` is Hermitian, for any real scalar `c`. -/
theorem isHermitian_smul_one {n : Type*} [DecidableEq n] (c : ℝ) :
    ((c • (1 : Matrix n n ℝ))).IsHermitian := by
  change (c • (1 : Matrix n n ℝ))ᴴ = c • 1
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]

/-- The squared Euclidean-space norm of a vector equals its self dot product. -/
theorem toLp_norm_sq {n : Type*} [Fintype n] (v : n → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ n)‖ ^ 2 = v ⬝ᵥ v := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, Real.norm_eq_abs, sq]

/-- `(P v). (P v) ≤ ‖P‖² (v. v)`, from the operator-norm bound on `P` applied to `v`. -/
theorem vecSq_mulVec_le {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (v : n → ℝ) :
    (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ ‖P‖ ^ 2 * (v ⬝ᵥ v) := by
  have h := P.l2_opNorm_mulVec (WithLp.toLp 2 v)
  have h1 : ‖(EuclideanSpace.equiv n ℝ).symm
      (P *ᵥ (WithLp.toLp 2 v : EuclideanSpace ℝ n).ofLp)‖ ^ 2 = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) :=
    toLp_norm_sq (P *ᵥ v)
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [h1, mul_pow, toLp_norm_sq v] at h3
  exact h3

/-- Conversely, a uniform bound `(P v). (P v) ≤ K² (v. v)` for all `v` bounds the operator
norm `‖P‖ ≤ K`. -/
theorem opNorm_le_of_vecSq_le {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : n → ℝ, (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ K ^ 2 * (v ⬝ᵥ v)) : ‖P‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  have hx := h (WithLp.ofLp x)
  rw [← toLp_norm_sq, ← toLp_norm_sq] at hx
  have h2 : ‖(WithLp.toLp 2 (P *ᵥ WithLp.ofLp x) : EuclideanSpace ℝ n)‖ ^ 2
      ≤ (K * ‖(WithLp.toLp 2 (WithLp.ofLp x) : EuclideanSpace ℝ n)‖) ^ 2 := by
    rw [mul_pow]; exact hx
  have h3 := (abs_le_of_sq_le_sq' h2 (by positivity)).2
  simpa using! h3

/-- The quadratic form of the matrix square root: `(√P v). (√P v) = v. (P v)`, for `P`
positive semidefinite. -/
theorem sqrt_form {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}
    (hP : P.PosSemidef) (v : n → ℝ) :
    (matSqrt P *ᵥ v) ⬝ᵥ (matSqrt P *ᵥ v) = v ⬝ᵥ (P *ᵥ v) := by
  obtain ⟨hQ, hQQ⟩ := matSqrt_spec hP
  conv_rhs => rw [← hQQ]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    transpose_eq_of_psd hQ]
  exact dotProduct_comm _ _

/-- `‖P‖ = ‖√P‖ * ‖√P‖`, for `P` positive semidefinite. -/
theorem sqrt_norm {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ}
    (hP : P.PosSemidef) : ‖P‖ = ‖matSqrt P‖ * ‖matSqrt P‖ := by
  obtain ⟨hQ, hQQ⟩ := matSqrt_spec hP
  conv_lhs => rw [← hQQ]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (matSqrt P)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_eq_of_psd hQ] at h

/-- For a positive semidefinite `P`, the quadratic form is bounded by the operator norm. -/
theorem psd_dot_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) (v : n → ℝ) :
    v ⬝ᵥ (P *ᵥ v) ≤ ‖P‖ * (v ⬝ᵥ v) := by
  rw [← sqrt_form hP v, sqrt_norm hP, ← pow_two]
  exact vecSq_mulVec_le _ v

/-- Conversely a bound on the quadratic form bounds the operator norm. -/
theorem opNorm_le_of_psd_dot_le {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : P.PosSemidef) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : n → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ K * (v ⬝ᵥ v)) : ‖P‖ ≤ K := by
  have hb : ‖matSqrt P‖ ≤ Real.sqrt K := by
    refine opNorm_le_of_vecSq_le (Real.sqrt_nonneg K) fun v => ?_
    rw [sqrt_form hP v, Real.sq_sqrt hK]
    exact h v
  rw [sqrt_norm hP]
  calc ‖matSqrt P‖ * ‖matSqrt P‖
      ≤ ‖matSqrt P‖ * Real.sqrt K := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ Real.sqrt K * Real.sqrt K := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg K)
    _ = K := Real.mul_self_sqrt hK

/-- `P ≤ c • 1` implies the quadratic form bound `v. (P v) ≤ c (v. v)`. -/
theorem dot_le_of_le_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} {c : ℝ} (h : P ≤ c • (1 : Matrix n n ℝ)) (v : n → ℝ) :
    v ⬝ᵥ (P *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
  have h2 := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at h2
  linarith only [h2]

/-- Conversely, a uniform quadratic form bound `v. (P v) ≤ c (v. v)` for Hermitian `P`
implies `P ≤ c • 1`. -/
theorem le_smul_one_of_dot_le {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : P.IsHermitian) {c : ℝ}
    (h : ∀ v : n → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ c * (v ⬝ᵥ v)) : P ≤ c • (1 : Matrix n n ℝ) := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((isHermitian_smul_one c).sub hP) fun v => ?_)
  have hv := h v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  linarith only [hv]

/-- A nonnegative scalar multiple of a positive semidefinite matrix is positive
semidefinite. -/
theorem psd_smul {n : Type*} [Finite n] {N : Matrix n n ℝ} (hN : N.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • N).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · change (c • N)ᴴ = c • N
    rw [Matrix.conjTranspose_smul, hN.isHermitian.eq, star_trivial]
  · have h := hN.dotProduct_mulVec_nonneg v
    simp only [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h ⊢
    exact mul_nonneg hc h

/-- A positive scalar multiple of a positive definite matrix is positive definite. -/
theorem posDef_smul {n : Type*} [Finite n] {c : ℝ} (hc : 0 < c)
    {X : Matrix n n ℝ} (hX : X.PosDef) : (c • X).PosDef := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · change (c • X)ᴴ = c • X
    rw [Matrix.conjTranspose_smul, hX.isHermitian.eq, star_trivial]
  · have h := hX.dotProduct_mulVec_pos hv
    simp only [star_trivial, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h ⊢
    exact mul_pos hc h

/-- Scalar multiplication by a nonnegative `c` preserves the Loewner order: `X ≤ Y` implies
`c • X ≤ c • Y`. -/
theorem smul_le_smul_left {n : Type*} [Finite n]
    {X Y : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c) (h : X ≤ Y) : c • X ≤ c • Y := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.le_iff.mpr ?_
  rw [← smul_sub]
  exact psd_smul (Matrix.le_iff.mp h) hc

/-- For `N` positive semidefinite, `a ≤ b` implies `a • N ≤ b • N`. -/
theorem smul_le_smul_psd {n : Type*} [Finite n] {N : Matrix n n ℝ}
    (hN : N.PosSemidef) {a b : ℝ} (hab : a ≤ b) : a • N ≤ b • N := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.le_iff.mpr ?_
  rw [← sub_smul]
  exact psd_smul hN (sub_nonneg.mpr hab)

/-- A Hermitian matrix above a positive definite one, in the Loewner order, is itself
positive definite. -/
theorem posDef_of_le {n : Type*} [Finite n] {X Y : Matrix n n ℝ}
    (hX : X.PosDef) (hY : Y.IsHermitian) (h : X ≤ Y) : Y.PosDef := by
  classical
  let := Fintype.ofFinite n
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hY fun x hx => ?_
  have h1 := hX.dotProduct_mulVec_pos hx
  have h2 := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at h2 ⊢
  simp only [star_trivial] at h1
  linarith only [h1, h2]

/-- The flattened swap block `𝐑` is Hermitian. -/
theorem swap_hermitian (d : ℕ) : (toFullBlockMat (blockSwap d)).IsHermitian :=
  (Analysis.toFullBlockMat_isHermitian_iff _).2 (Analysis.isSymmetricBlockMat_blockSwap d)

/-- The flattened swap block `𝐑` is invertible, since it is its own inverse. -/
theorem swap_isUnit (d : ℕ) : IsUnit (toFullBlockMat (blockSwap d)) :=
  (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (Analysis.toFullBlockMat_blockSwap_mul_self d))

/-- The swap-conjugate `𝐑 X⁻¹ 𝐑` of the inverse of a positive definite flattened block is
positive semidefinite. -/
theorem swapConj_posSemidef {d : ℕ} {X : BlockMat d} (hX : (toFullBlockMat X).PosDef) :
    (toFullBlockMat (blockSwap d) * (toFullBlockMat X)⁻¹ *
      toFullBlockMat (blockSwap d)).PosSemidef := by
  have h := (Matrix.posDef_inv_iff.2 hX).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit (swap_isUnit d))
  simpa only [(swap_hermitian d).eq] using h.posSemidef

/-- The square root data behind the canonical imbalance of a positive block. -/
theorem imbalance_data {d : ℕ} {X : BlockMat d} (hX : (toFullBlockMat X).PosDef) :
    ∃ S : Matrix (BlockCoord d) (BlockCoord d) ℝ, Sᵀ = S ∧ S * S⁻¹ = 1 ∧ S⁻¹ * S = 1 ∧
      S⁻¹ * S⁻¹ = toFullBlockMat (blockSwap d) * (toFullBlockMat X)⁻¹ *
        toFullBlockMat (blockSwap d) ∧
      canonicalImbalance X = ‖S * toFullBlockMat X * S‖ := by
  have hRR := Analysis.toFullBlockMat_blockSwap_mul_self d
  have hRh := swap_hermitian d
  have hRinv : (toFullBlockMat (blockSwap d))⁻¹ = toFullBlockMat (blockSwap d) :=
    Matrix.inv_eq_right_inv hRR
  have hXu : IsUnit (toFullBlockMat X).det := (Matrix.isUnit_iff_isUnit_det _).1 hX.isUnit
  have hG : (toFullBlockMat (blockSwap d) * toFullBlockMat X *
      toFullBlockMat (blockSwap d)).PosDef := by
    simpa only [hRh.eq] using
      hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (swap_isUnit d))
  obtain ⟨hSpsd, hSS⟩ := matSqrt_spec hG.posSemidef
  have hSu : IsUnit (matSqrt (toFullBlockMat (blockSwap d) * toFullBlockMat X *
      toFullBlockMat (blockSwap d))).det := by
    have h1 : (matSqrt (toFullBlockMat (blockSwap d) * toFullBlockMat X *
        toFullBlockMat (blockSwap d))).det *
        (matSqrt (toFullBlockMat (blockSwap d) * toFullBlockMat X *
        toFullBlockMat (blockSwap d))).det =
        (toFullBlockMat (blockSwap d) * toFullBlockMat X *
          toFullBlockMat (blockSwap d)).det := by
      rw [← Matrix.det_mul, hSS]
    have h2 : IsUnit (toFullBlockMat (blockSwap d) * toFullBlockMat X *
        toFullBlockMat (blockSwap d)).det := (Matrix.isUnit_iff_isUnit_det _).1 hG.isUnit
    rw [← h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine ⟨_, transpose_eq_of_psd hSpsd, Matrix.mul_nonsing_inv _ hSu,
    Matrix.nonsing_inv_mul _ hSu, ?_, ?_⟩
  · rw [← Matrix.mul_inv_rev, hSS, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hRinv, ← mul_assoc]
  · have hinv : (toFullBlockMat (blockSwap d) * (toFullBlockMat X)⁻¹ *
        toFullBlockMat (blockSwap d))⁻¹ =
        toFullBlockMat (blockSwap d) * toFullBlockMat X * toFullBlockMat (blockSwap d) := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hRinv,
        Matrix.nonsing_inv_nonsing_inv _ hXu, ← mul_assoc]
    simp only [canonicalImbalance, blockOpNorm, normalizedBlock, toFullBlockMat_ofFullBlockMat,
      hinv]

/-- `𝔡(X) ≤ c` implies the Loewner inequality `X ≤ c • 𝐑X⁻¹𝐑`. -/
theorem le_of_imbalance_le {d : ℕ} {X : BlockMat d} (hX : (toFullBlockMat X).PosDef)
    {c : ℝ} (h : canonicalImbalance X ≤ c) :
    toFullBlockMat X ≤ c • (toFullBlockMat (blockSwap d) * (toFullBlockMat X)⁻¹ *
      toFullBlockMat (blockSwap d)) := by
  obtain ⟨S, hSt, hSR, hSL, hSinv, hnorm⟩ := imbalance_data hX
  have hPpsd : (S * toFullBlockMat X * S).PosSemidef := by
    have hc := hX.posSemidef.conjTranspose_mul_mul_same S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hSt] at hc
  have hP : S * toFullBlockMat X * S ≤ c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) := by
    refine le_smul_one_of_dot_le hPpsd.isHermitian fun v => ?_
    have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have h1 := psd_dot_le_opNorm hPpsd v
    have h2 : ‖S * toFullBlockMat X * S‖ ≤ c := hnorm ▸ h
    calc v ⬝ᵥ ((S * toFullBlockMat X * S) *ᵥ v)
        ≤ ‖S * toFullBlockMat X * S‖ * (v ⬝ᵥ v) := h1
      _ ≤ c * (v ⬝ᵥ v) := mul_le_mul_of_nonneg_right h2 hvv
  have hcg := Analysis.matrix_congr_le hP S⁻¹
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  rw [hSit] at hcg
  have hl : S⁻¹ * (S * toFullBlockMat X * S) * S⁻¹ = toFullBlockMat X := by
    have : S⁻¹ * (S * toFullBlockMat X * S) * S⁻¹ =
        (S⁻¹ * S) * toFullBlockMat X * (S * S⁻¹) := by
      simp [Matrix.mul_assoc]
    rw [this, hSL, hSR, Matrix.one_mul, Matrix.mul_one]
  have hr : S⁻¹ * (c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)) * S⁻¹ =
      c • (S⁻¹ * S⁻¹) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [hl, hr, hSinv] at hcg
  exact hcg

/-- Conversely the Loewner inequality `X ≤ c • 𝐑X⁻¹𝐑` implies `𝔡(X) ≤ c`. -/
theorem imbalance_le_of_le {d : ℕ} {X : BlockMat d} (hX : (toFullBlockMat X).PosDef)
    {c : ℝ} (hc : 0 ≤ c)
    (h : toFullBlockMat X ≤ c • (toFullBlockMat (blockSwap d) * (toFullBlockMat X)⁻¹ *
      toFullBlockMat (blockSwap d))) : canonicalImbalance X ≤ c := by
  obtain ⟨S, hSt, hSR, hSL, hSinv, hnorm⟩ := imbalance_data hX
  have hPpsd : (S * toFullBlockMat X * S).PosSemidef := by
    have hc' := hX.posSemidef.conjTranspose_mul_mul_same S
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hSt] at hc'
  rw [← hSinv] at h
  have hcg := Analysis.matrix_congr_le h S
  rw [hSt, Matrix.mul_smul, Matrix.smul_mul] at hcg
  have hid : S * (S⁻¹ * S⁻¹) * S = 1 := by
    have : S * (S⁻¹ * S⁻¹) * S = (S * S⁻¹) * (S⁻¹ * S) := by simp [Matrix.mul_assoc]
    rw [this, hSR, hSL, Matrix.one_mul]
  rw [hid] at hcg
  rw [hnorm]
  exact opNorm_le_of_psd_dot_le hPpsd hc (dot_le_of_le_smul_one hcg)

open Matrix
open scoped MatrixOrder

/-- For a symmetric positive definite block `E`, the lower-right block cancels the skew Schur
coefficient against the two off-diagonal blocks: `L k = -lowerLeft` and
`kᴴ L = -upperRight`. -/
theorem schur_cancel {d : ℕ} {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    E.lowerRight * schurSkew E = -E.lowerLeft ∧
      (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
  have hD : E.lowerRightᴴ = E.lowerRight := (posDef_lowerRight hs hp).isHermitian.eq
  have hC : E.lowerLeftᴴ = E.upperRight := by
    ext i j
    exact hs (Sum.inr j) (Sum.inl i)
  have hk : E.lowerRight * schurSkew E = -E.lowerLeft := by
    rw [schurSkew, mul_neg, ← mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_lowerRight hp), one_mul]
  have hk' : (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
    have hkt := congrArg Matrix.conjTranspose hk
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hD, hC] using hkt
  exact ⟨hk, hk'⟩

/-- A norm bound on the `B`-normalized form `√(B⁻¹) A √(B⁻¹)` gives the Loewner bound
`A ≤ c • B`, for `A`, `B` positive definite. -/
theorem normalized_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hB : B.PosDef) {c : ℝ}
    (hn : ‖matSqrt B⁻¹ * A * matSqrt B⁻¹‖ ≤ c) : A ≤ c • B := by
  let T := matSqrt B⁻¹
  obtain ⟨hT, hTT⟩ := matSqrt_spec hB.inv.posSemidef
  have hdet : IsUnit T.det := by
    apply isUnit_of_mul_isUnit_left (y := T.det)
    rw [← Matrix.det_mul]
    change IsUnit (matSqrt B⁻¹ * matSqrt B⁻¹).det
    rw [hTT]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hB.inv.isUnit
  have hTiT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hdet
  have hTTi : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hTiTi : T⁻¹ * T⁻¹ = B := by
    rw [← Matrix.mul_inv_rev]
    change (matSqrt B⁻¹ * matSqrt B⁻¹)⁻¹ = B
    rw [hTT, Matrix.nonsing_inv_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)]
  have hTH : Tᴴ = T := hT.isHermitian.eq
  have hN : (T * A * T).PosSemidef := by
    simpa only [hTH] using hA.posSemidef.conjTranspose_mul_mul_same T
  have hle : T * A * T ≤ c • (1 : Matrix n n ℝ) := le_smul_one_of_norm_le hN hn
  have hi := star_left_conjugate_le_conjugate hle T⁻¹
  have hTi : T⁻¹ᴴ = T⁻¹ := hT.inv.isHermitian.eq
  change T⁻¹ᴴ * (T * A * T) * T⁻¹ ≤ T⁻¹ᴴ * (c • 1) * T⁻¹ at hi
  rw [hTi] at hi
  simpa only [← mul_assoc, hTiT, one_mul, mul_assoc A T T⁻¹, hTTi,
    mul_one, Matrix.mul_smul, Matrix.smul_mul, hTiTi] using hi

/-- `(c • B)⁻¹ = c⁻¹ • B⁻¹`, for `c ≠ 0` and `B` positive definite. -/
theorem inv_smul_real {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.PosDef) {c : ℝ} (hc : c ≠ 0) :
    (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)]

/-- `𝔡(A) ≤ c` implies the flattened Loewner bound `𝐑 A 𝐑 ≤ c • A⁻¹`, for `A` symmetric
positive definite. -/
theorem canonical_dual_order {d : ℕ} {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    {c : ℝ} (hc : 0 < c) (h : canonicalImbalance A ≤ c) :
    toFullBlockMat (blockSwap d) * toFullBlockMat A * toFullBlockMat (blockSwap d) ≤
      c • (toFullBlockMat A)⁻¹ := by
  let R := toFullBlockMat (blockSwap d)
  let B := R * (toFullBlockMat A)⁻¹ * R
  have hA := posDef_toFullBlockMat hs hp
  have hB : B.PosDef := by
    simpa only [toFullBlockMat_ofFullBlockMat] using Analysis.swapConj_posDef hA
  have hle : toFullBlockMat A ≤ c • B := by
    apply normalized_le hA hB
    simpa only [canonicalImbalance, blockOpNorm, normalizedBlock,
      toFullBlockMat_ofFullBlockMat] using h
  have hi := inv_le_inv_of_le hA (hB.smul hc) hle
  rw [inv_smul_real hB hc.ne'] at hi
  have hi' := smul_le_smul_of_nonneg_left hi hc.le
  rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at hi'
  have hR : R⁻¹ = R := Matrix.inv_eq_right_inv
    (Analysis.toFullBlockMat_blockSwap_mul_self d)
  have hBi : B⁻¹ = R * toFullBlockMat A * R := by
    dsimp [B]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hR,
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)]
    simp only [mul_assoc]
  rwa [hBi] at hi'

/-- The flattened bound `𝐑 A 𝐑 ≤ c • A⁻¹` descends, via the block congruence `V`, to the
Schur-complement bound `schurSigma A + (k + kᴴ)ᴴ L (k + kᴴ) ≤ c • L⁻¹`. -/
theorem coupled_schur_le {d : ℕ} {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    {c : ℝ} (ho : toFullBlockMat (blockSwap d) * toFullBlockMat A *
      toFullBlockMat (blockSwap d) ≤ c • (toFullBlockMat A)⁻¹) :
    schurSigma A + (schurSkew A + (schurSkew A)ᴴ)ᴴ * A.lowerRight *
      (schurSkew A + (schurSkew A)ᴴ) ≤ c • A.lowerRight⁻¹ := by
  let k := schurSkew A
  let L := A.lowerRight
  let D : FullBlockMat d := Matrix.fromBlocks 0 0 0 L⁻¹
  let V := toFullBlockMat A * D
  have hA := posDef_toFullBlockMat hs hp
  have hL := posDef_lowerRight hs hp
  have hLiL : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_lowerRight hp)
  have hLLi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_lowerRight hp)
  have hLH : L⁻¹ᴴ = L⁻¹ := hL.inv.isHermitian.eq
  have hDH : Dᴴ = D := by
    simp only [D, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero, hLH]
  have hAiA := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  have hU : A.upperRight = -(kᴴ * L) := by rw [hk', neg_neg]
  have hC : A.lowerLeft = -(L * k) := by rw [hk, neg_neg]
  have hV : V = Matrix.fromBlocks 0 (-kᴴ) 0 (1 : Mat d) := by
    dsimp [V, D]
    rw [toFullBlockMat_eq_fromBlocks, Matrix.fromBlocks_multiply, hU]
    simp only [mul_zero, add_zero, zero_add, neg_mul, mul_assoc, hLLi, mul_one]
    change Matrix.fromBlocks 0 (-kᴴ) 0 (L * L⁻¹) = _
    rw [hLLi]
  have hright : Vᴴ * (toFullBlockMat A)⁻¹ * V = D := by
    dsimp [V]
    rw [Matrix.conjTranspose_mul, hDH, hA.isHermitian.eq]
    calc
      _ = D * toFullBlockMat A * D := by
        rw [mul_assoc D (toFullBlockMat A) (toFullBlockMat A)⁻¹,
          mul_assoc D (toFullBlockMat A * (toFullBlockMat A)⁻¹) (toFullBlockMat A * D),
          ← mul_assoc (toFullBlockMat A * (toFullBlockMat A)⁻¹) (toFullBlockMat A) D,
          mul_assoc (toFullBlockMat A) (toFullBlockMat A)⁻¹ (toFullBlockMat A),
          hAiA, mul_one]
        exact (mul_assoc _ _ _).symm
      _ = D := by
        dsimp [D]
        rw [toFullBlockMat_eq_fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
        simp only [mul_zero, zero_mul, add_zero, zero_add]
        change Matrix.fromBlocks 0 0 0 (L⁻¹ * L * L⁻¹) = _
        rw [hLiL, one_mul]
  have hR : toFullBlockMat (blockSwap d) =
      Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
    rw [toFullBlockMat_eq_fromBlocks]
    rfl
  have hleft : Vᴴ * (toFullBlockMat (blockSwap d) * toFullBlockMat A *
      toFullBlockMat (blockSwap d)) * V = Matrix.fromBlocks 0 0 0
        (schurSigma A + (k + kᴴ)ᴴ * L * (k + kᴴ)) := by
    rw [hV, hR, toFullBlockMat_eq_fromBlocks, Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero,
      Matrix.conjTranspose_one, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose,
      zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    congr 1
    rw [hU, hC]
    change _ = A.upperLeft - kᴴ * L * k + (k + kᴴ)ᴴ * L * (k + kᴴ)
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have ht := star_left_conjugate_le_conjugate ho V
  change Vᴴ * _ * V ≤ Vᴴ * (c • _) * V at ht
  rw [Matrix.mul_smul, Matrix.smul_mul, hright, hleft] at ht
  have hz := (Matrix.le_iff.mp ht).submatrix Sum.inr
  apply Matrix.le_iff.mpr
  exact hz

/-- The antisymmetrization `(1/2) • (k - kᵀ)` of a matrix `k` is skew. -/
theorem skew_part {d : ℕ} (k : Mat d) :
    IsSkewMat (((2 : ℝ)⁻¹) • (k - matTranspose k)) := by
  unfold IsSkewMat matTranspose
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
  rw [← smul_neg]
  congr 1
  abel

/-- The Schur-complement bound built from the antisymmetrization of the skew Schur
coefficient is Loewner-below the one built from `k + kᴴ`, since the two differ by a
nonnegative multiple of a positive semidefinite quadratic form. -/
theorem quarter_correction_le {d : ℕ} {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A) :
    schurSigma A + matTranspose (schurSkew A -
      ((2 : ℝ)⁻¹ • (schurSkew A - matTranspose (schurSkew A)))) * A.lowerRight *
      (schurSkew A - ((2 : ℝ)⁻¹ • (schurSkew A - matTranspose (schurSkew A)))) ≤
    schurSigma A + (schurSkew A + (schurSkew A)ᴴ)ᴴ * A.lowerRight *
      (schurSkew A + (schurSkew A)ᴴ) := by
  let k := schurSkew A
  have he : k - (2 : ℝ)⁻¹ • (k - matTranspose k) = (2 : ℝ)⁻¹ • (k + kᴴ) := by
    change k - (2 : ℝ)⁻¹ • (k - kᴴ) = _
    module
  have hQ := (posDef_lowerRight hs hp).posSemidef.conjTranspose_mul_mul_same (k + kᴴ)
  change schurSigma A + matTranspose (k - (2 : ℝ)⁻¹ • (k - matTranspose k)) *
    A.lowerRight * (k - (2 : ℝ)⁻¹ • (k - matTranspose k)) ≤ _
  rw [he]
  simp only [matTranspose, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsmall := smul_le_smul_of_nonneg_right
    (by norm_num : (2 : ℝ)⁻¹ * 2⁻¹ ≤ 1) hQ.nonneg
  rw [one_smul] at hsmall
  exact add_le_add le_rfl hsmall

/-- **K4.** If the canonical imbalance of a symmetric positive definite block `A` is at most
`1 + x`, then its block contrast satisfies `blockContrast A - 1 ≤ 3 * x`. -/
theorem blockContrast_sub_one_le_of_canonicalImbalance_le {d : ℕ} {A : BlockMat d}
    (hs : IsSymmetricBlockMat A) (hp : Book.Ch02.BlockPosDef A)
    {x : ℝ} (hx : 0 ≤ x) (h : canonicalImbalance A ≤ 1 + x) :
    blockContrast A - 1 ≤ 3 * x := by
  have hc : 0 < 1 + x := by linarith only [hx]
  have hle := (quarter_correction_le hs hp).trans
    (coupled_schur_le hs hp (canonical_dual_order hs hp hc h))
  have hquad : MatLoewnerLE
      (schurSigma A + matTranspose (schurSkew A -
        (2 : ℝ)⁻¹ • (schurSkew A - matTranspose (schurSkew A))) * A.lowerRight *
        (schurSkew A - (2 : ℝ)⁻¹ • (schurSkew A - matTranspose (schurSkew A))))
      ((1 + x) • schurSigmaStar A) := by
    intro y
    have ht := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg y
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at ht
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcon := blockContrast_le hc.le (skew_part (schurSkew A)) hquad
  linarith only [hcon, hx]

end HCPolySupport.HighContrast.Multiscale
