/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.EnergyDefectBound

/-!
# High-contrast homogenization: Entry.Response.Core.PathwiseFluctuationBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pathwise fluctuation bound

This file proves the pathwise bound on the normalized fluctuation of the response block across
scales, the all-scale estimate serving `p.response.transfer`: it identifies the normalized
fluctuation with an explicit difference of normalized blocks, bounds a single fluctuation term by
the operator norm through the Loewner order, and controls the resulting geometric sum by the
elementary inequality `(1 + 3^{-k})^n ≤ 3` on a compatible range. It also proves the monotonicity
of the block scale and the bound on the spectral bound of a single cell, which the pathwise
estimate needs at each scale.
-/

section
open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter adaptedMean aspectRatio blockScale
  blockSub coarseBlock matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-- The complete profile at the top of the response window is at most `eta`
(`p.response.transfer`, "decreasing `sigma_0` makes every profile and drift in
`e.global.selection.profile` at most `eta`").  `raw.prof` bounds the sum of the three profiles
and the two drifts; the two drifts are nonnegative
(`Multiscale.determinantDrift_nonneg`), so the top profile alone is below
`C_prof sigma^{(1-gamma)/8}`, which `hprof` puts below `eta`. -/
theorem profile_self_le_eta (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d)
    (s t : ℤ)
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (η : ℝ) (hprof : Cprof * σ ^ ((1 - γ) / 8) ≤ η) :
    profile P γ (respGrid jStar F) jStar t t ≤ η := by
  have _hγ := hγ
  let : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hDs : 0 ≤ determinantDrift P γ (respGrid jStar F) jStar s :=
    determinantDrift_nonneg d hd γ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm s
  have hDt : 0 ≤ determinantDrift P γ (respGrid jStar F) jStar t :=
    determinantDrift_nonneg d hd γ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t
  have hmax := le_max_right
    (max (profile P γ (respGrid jStar F) jStar s s)
      (profile P γ (respGrid jStar F) jStar s t))
    (profile P γ (respGrid jStar F) jStar t t)
  have hraw := raw.prof
  simp only [respGrid] at hDs hDt hmax ⊢
  linarith only [hmax, hraw, hDs, hDt, hprof]

/-! ## helpers

The helpers supplying the source branch `k < j_*` of the all-scale maximum, together with the
three block-algebra facts it needs: the Loewner envelope of an *arbitrary* (not positive
semidefinite) doubled block by its operator norm, the attainment of the infimum defining
`blockSpecBound`, and the normalization of a Loewner bound `A <= c R` by the positive definite
`R` itself. -/

/-- A real quadratic form of a vector with itself is nonnegative. -/
private theorem dotProduct_self_nonneg_fintype {n : Type*} [Fintype n] (v : n → ℝ) :
    (0 : ℝ) ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- **The quadratic form of an arbitrary square matrix is bounded by its L2 operator norm**
(`p.response.transfer`, the fluctuation part `V^q_{k,t}(z)`, which is a difference and
so carries no sign).  `Multiscale.psd_dot_le_opNorm` assumes positive semidefiniteness; the
general case follows from expanding the nonnegative square `|‖N‖ v - N v|^2`. -/
private theorem dot_mulVec_le_opNorm_of_square {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := dotProduct_self_nonneg_fintype v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      dotProduct_self_nonneg_fintype _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith only [hexp, hsq, hpos]

/-- The Loewner envelope of an arbitrary doubled block by its operator norm. -/
theorem loewner_le_blockOpNorm_general (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := dot_mulVec_le_opNorm_of_square (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hR : blockVecDot X (blockMatVecMul (blockScale (blockOpNorm N)
      (Book.Ch02.blockIdentity d)) X) =
      blockOpNorm N * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockScale_identity]
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hL, hR]
  unfold blockOpNorm at h ⊢
  linarith only [h]

/-- Congruence by a symmetric matrix moves through the quadratic form. -/
private theorem qform_conj_symm {n : Type*} [Fintype n] [DecidableEq n]
    (Sm M : Matrix n n ℝ) (hS : Smᵀ = Sm) (v : n → ℝ) :
    v ⬝ᵥ ((Sm * M * Sm) *ᵥ v) = (Sm *ᵥ v) ⬝ᵥ (M *ᵥ (Sm *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hS]

/-- Normalizing a Loewner bound `A ≤ c R` by the positive definite `R` itself. -/
theorem normalizedBlock_le_scale (A R : BlockMat d)
    (hR : (toFullBlockMat R).PosDef) (c : ℝ)
    (h : BlockMatLoewnerLE A (blockScale c R)) :
    BlockMatLoewnerLE (normalizedBlock A R) (blockScale c (Book.Ch02.blockIdentity d)) := by
  have key : ∀ (M : BlockMat d) (Y : BlockVec d), blockVecDot Y (blockMatVecMul M Y) =
      toFullBlockVec Y ⬝ᵥ (toFullBlockMat M *ᵥ toFullBlockVec Y) := by
    intro M Y
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hS : (matSqrt ((toFullBlockMat R)⁻¹))ᵀ = matSqrt ((toFullBlockMat R)⁻¹) :=
    transpose_eq_of_psd (matSqrt_inv_posDef_full hR).posSemidef
  intro X
  have hY := h (ofFullBlockVec (matSqrt ((toFullBlockMat R)⁻¹) *ᵥ toFullBlockVec X))
  rw [key, key] at hY
  rw [key, key]
  simp only [toFullBlockVec_ofFullBlockVec, toFullBlockMat_blockScale] at hY
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat,
    toFullBlockMat_blockScale_identity]
  rw [qform_conj_symm _ _ hS]
  have hrr : toFullBlockVec X ⬝ᵥ
      ((matSqrt ((toFullBlockMat R)⁻¹) * toFullBlockMat R * matSqrt ((toFullBlockMat R)⁻¹))
        *ᵥ toFullBlockVec X) =
      (matSqrt ((toFullBlockMat R)⁻¹) *ᵥ toFullBlockVec X) ⬝ᵥ
        (toFullBlockMat R *ᵥ (matSqrt ((toFullBlockMat R)⁻¹) *ᵥ toFullBlockVec X)) :=
    qform_conj_symm _ _ hS _
  rw [matSqrt_inv_conj hR, Matrix.one_mulVec] at hrr
  have hRHS : (matSqrt ((toFullBlockMat R)⁻¹) *ᵥ toFullBlockVec X) ⬝ᵥ
      ((c • toFullBlockMat R) *ᵥ (matSqrt ((toFullBlockMat R)⁻¹) *ᵥ toFullBlockVec X)) =
      c * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← hrr]
  rw [hRHS] at hY
  have hgoal : toFullBlockVec X ⬝ᵥ ((c • (1 : FullBlockMat d)) *ᵥ toFullBlockVec X) =
      c * (toFullBlockVec X ⬝ᵥ toFullBlockVec X) := by
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [hgoal]
  linarith only [hY]

/-- The quadratic form is homogeneous in a scalar dilation. -/
theorem qform_blockScale_smul (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  have k1 : blockVecDot X (blockMatVecMul (blockScale c A) X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat (blockScale c A) *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have k2 : blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  rw [k1, k2, toFullBlockMat_blockScale, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- A scalar dilation of a Loewner bound. -/
theorem blockScale_mono_of_nonneg (A R : BlockMat d) (c k : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE A (blockScale k R)) :
    BlockMatLoewnerLE (blockScale c A) (blockScale (c * k) R) := by
  intro X
  have hX := h X
  rw [qform_blockScale_smul] at hX
  rw [qform_blockScale_smul, qform_blockScale_smul, mul_assoc]
  nlinarith only [hX, hc]

/-- **The infimum defining `blockSpecBound` is attained** when the defining set is nonempty. -/
theorem blockSpecBound_attained_of_loewnerLE (N : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    BlockMatLoewnerLE N (blockScale (blockSpecBound N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have hid : blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockIdentity, Matrix.one_mulVec]
  set q : ℝ := toFullBlockVec X ⬝ᵥ toFullBlockVec X with hqdef
  have hq0 : (0 : ℝ) ≤ q := dotProduct_self_nonneg_fintype _
  set p : ℝ := blockVecDot X (blockMatVecMul N X) with hpdef
  have hmem : ∀ b ∈ {c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}, p ≤ b * q := by
    intro b hb
    have hbX := hb.2 X
    rw [qform_blockScale_smul, hid] at hbX
    linarith only [hbX, hpdef, hqdef]
  have hne : ({c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}).Nonempty := ⟨c, hc, h⟩
  have hkey : p ≤ blockSpecBound N * q := by
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · have hc0 := hmem c ⟨hc, h⟩
      rw [← h0] at hc0 ⊢
      simpa using hc0
    · have hdiv : p / q ≤ blockSpecBound N := by
        refine le_csInf hne fun b hb => ?_
        exact (div_le_iff₀ hpos).2 (hmem b hb)
      exact (div_le_iff₀ hpos).1 hdiv
  rw [qform_blockScale_smul, hid]
  linarith only [hkey, hpdef, hqdef]

/-- From `A ≤ c I` to a spectral bound on `A - I`. -/
private theorem blockSpecBound_sub_identity_le (A : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE A (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound (blockSub A (Book.Ch02.blockIdentity d)) ≤ c := by
  refine blockSpecBound_le_of_loewner _ _ hc ?_
  intro X
  have hfull : toFullBlockMat A =
      toFullBlockMat (blockSub A (Book.Ch02.blockIdentity d)) +
        toFullBlockMat (Book.Ch02.blockIdentity d) := by
    rw [Recurrence.toFullBlockMat_blockSub, sub_add_cancel]
  have hsplit := qform_add_of_full A (blockSub A (Book.Ch02.blockIdentity d))
    (Book.Ch02.blockIdentity d) hfull X
  have hid : blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockIdentity, Matrix.one_mulVec]
  have hq0 : (0 : ℝ) ≤ toFullBlockVec X ⬝ᵥ toFullBlockVec X := dotProduct_self_nonneg_fintype _
  have hA := h X
  rw [qform_blockScale_smul, hid] at hA
  rw [qform_blockScale_smul, hid]
  rw [hid] at hsplit
  linarith only [hA, hsplit, hq0]

/-- The crude three-term power inequality. -/
theorem add3_pow_le (Q : ℕ) (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (u + v + w) ^ Q ≤ 3 ^ Q * (u ^ Q + v ^ Q + w ^ Q) := by
  set M : ℝ := max u (max v w) with hM
  have huM : u ≤ M := le_max_left _ _
  have hvM : v ≤ M := le_trans (le_max_left _ _) (le_max_right u _)
  have hwM : w ≤ M := le_trans (le_max_right _ _) (le_max_right u _)
  have hM0 : (0 : ℝ) ≤ M := le_trans hu huM
  have hpow : M ^ Q ≤ u ^ Q + v ^ Q + w ^ Q := by
    have hu' : (0 : ℝ) ≤ u ^ Q := pow_nonneg hu Q
    have hv' : (0 : ℝ) ≤ v ^ Q := pow_nonneg hv Q
    have hw' : (0 : ℝ) ≤ w ^ Q := pow_nonneg hw Q
    rcases le_total u (max v w) with h1 | h1
    · rw [hM, max_eq_right h1]
      rcases le_total v w with h2 | h2
      · rw [max_eq_right h2]; linarith only [hu', hv']
      · rw [max_eq_left h2]; linarith only [hu', hw']
    · rw [hM, max_eq_left h1]; linarith only [hv', hw']
  calc (u + v + w) ^ Q ≤ (3 * M) ^ Q := by
        refine pow_le_pow_left₀ (by linarith only [hu, hv, hw]) (by linarith only [huM, hvM, hwM]) Q
    _ = 3 ^ Q * M ^ Q := by rw [mul_pow]
    _ ≤ 3 ^ Q * (u ^ Q + v ^ Q + w ^ Q) := by
        have : (0 : ℝ) ≤ (3 : ℝ) ^ Q := by positivity
        exact mul_le_mul_of_nonneg_left hpow this

/-- **The source branch of the all-scale maximum**: a two-step Loewner comparison of the
coarse block against the reference block and of the reference block against `E_t`. -/
private theorem cell_specBound_le (A Et Eref : BlockMat d)
    (hEt : (toFullBlockMat Et).PosDef) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hA : BlockMatLoewnerLE A (blockScale c1 Eref))
    (hE : BlockMatLoewnerLE Eref (blockScale c2 Et)) :
    blockSpecBound (blockSub (normalizedBlock A Et) (Book.Ch02.blockIdentity d)) ≤ c1 * c2 := by
  have h1 : BlockMatLoewnerLE (blockScale c1 Eref) (blockScale (c1 * c2) Et) :=
    blockScale_mono_of_nonneg Eref Et c1 c2 hc1 hE
  exact blockSpecBound_sub_identity_le _ _ (mul_nonneg hc1 hc2)
    (normalizedBlock_le_scale A Et hEt _ (hA.trans h1))

/-- **The Step 5 split with both parts made explicit** (`p.response.transfer`). -/
private theorem split_term_le_max (A Ak Et : BlockMat d) :
    blockSpecBound (blockSub (normalizedBlock A Et) (Book.Ch02.blockIdentity d)) ≤
      blockOpNorm (normalizedBlock (blockSub A Ak) Et) +
        blockSpecBound (blockSub (normalizedBlock Ak Et) (Book.Ch02.blockIdentity d)) :=
  allScale_specBound_split_le A Ak Et _ _ (norm_nonneg _) (blockSpecBound_nonneg _)
    (loewner_le_blockOpNorm_general _)
    (blockSpecBound_attained_of_loewnerLE _ (blockOpNorm _) (norm_nonneg _)
      (loewner_le_blockOpNorm_general _))

/-- The `Q`-th power of a weighted quantity. -/
theorem pow_weight (ρ : ℝ) (n : ℕ) (Q : ℕ) (x : ℝ) :
    ((3 : ℝ) ^ (-(ρ * (n : ℝ))) * x) ^ Q = (3 : ℝ) ^ (-(Q : ℝ) * ρ * (n : ℝ)) * x ^ Q := by
  rw [mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ (-(ρ * (n : ℝ)))) Q,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    show -(ρ * (n : ℝ)) * (Q : ℝ) = -(Q : ℝ) * ρ * (n : ℝ) from by ring]

/-- Passing to the `Q`-th root of a bound. -/
theorem le_rpow_inv (Q : ℕ) (hQ : Q ≠ 0) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ Q ≤ y) : x ≤ y ^ ((Q : ℝ)⁻¹) := by
  refine (pow_le_pow_iff_left₀ hx (Real.rpow_nonneg hy _) hQ).mp ?_
  rwa [Real.rpow_inv_natCast_pow hy hQ]

/-- The aligned adapted cell is the translate of the adapted cell to its centre. -/
theorem adaptedCellTranslate_center (q : Mat d) (j : ℤ) (z : Fin d → ℤ) :
    HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j z) = adaptedCellAtCenter q j z := rfl

/-- The normalized fluctuation at an aligned centre, spelled with `adaptedCellAtCenter`. -/
theorem normalizedFluctuation_eq (P : Measure (CoeffSpace d)) (q : Mat d) (j k : ℤ)
    (z : Fin d → ℤ) (a : CoeffSpace d) :
    normalizedFluctuation P q j k (adaptedCellCenter q j z) a =
      normalizedBlock (blockSub (coarseBlock (adaptedCellAtCenter q j z) a) (adaptedMean P q j))
        (adaptedMean P q k) := rfl

/-- **The fluctuation-and-mean branch** (`p.response.transfer`): for the
scales `k = t - n` at or above `j_*` the normalized block splits into `V^q_{k,t}(z)` and
`P^q_{k,t} - I`, the first dominated by the `Q`-th root of the `ℋ^fluc_q(t)` integrand and the
second by `D_{q,j_*}(t)`. -/
private theorem fluctuation_term_le_max (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (t : ℤ) (ht : (jStar : ℤ) ≤ t) (a : CoeffSpace d) (n : ℕ)
    (hn : n ∈ Set.Icc 0 (t - (jStar : ℤ)).toNat) (z : Fin d → ℤ)
    (hz : z ∈ triadicIndexBox d n) :
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)) (Book.Ch02.blockIdentity d)) ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
            blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
              bigQ d γ) ^ ((bigQ d γ : ℝ)⁻¹) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t := by
  have hQ0 : bigQ d γ ≠ 0 := by have := bigQ_two_le d γ hγ; omega
  obtain ⟨-, hn2⟩ := Set.mem_Icc.mp hn
  have hk1 : (jStar : ℤ) ≤ t - (n : ℤ) := by omega
  have hk2 : t - (n : ℤ) ≤ t := by omega
  have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hF00 : (0 : ℝ) ≤ ⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
          blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
            bigQ d γ :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hsplit := split_term_le_max
    (coarseBlock (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
    (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)))
    (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)
  have hmean := mean_part_le_determinantDrift d hd γ P E Ψ Kg Src hstat hdag
    jStar hj mt hm (t - (n : ℤ)) t hk1 hk2
  have hcast : (t : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [hcast] at hmean
  simp only [relMean] at hmean
  have hflc := scale_index_le d hd γ P E Ψ Kg Src hstat hdag jStar hj mt hm t ht
    a n hn z hz
  rw [normalizedFluctuation_eq] at hflc
  have hfl : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
      blockOpNorm (normalizedBlock (blockSub (coarseBlock
        (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ)) z) a)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) (t - (n : ℤ))))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)) ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar mt) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mt) t,
            blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar mt) j t y a) ^
              bigQ d γ) ^ ((bigQ d γ : ℝ)⁻¹) := by
    refine le_rpow_inv (bigQ d γ) hQ0 _ _ (mul_nonneg hwnn (norm_nonneg _)) hF00 ?_
    rw [pow_weight]
    exact hflc
  refine le_trans (mul_le_mul_of_nonneg_left hsplit hwnn) ?_
  rw [mul_add]
  linarith only [hfl, hmean]

/-- **The source branch** (`p.response.transfer`): for the scales `k = t - n`
strictly below `j_*` the adapted source estimate, normalized to `E_t`, bounds the entire
normalized block by `C Pi e(m)^2 RSZ 3^{-rho_max(t-j_*)}`, and `e.response.source.smallness`
turns that into `C' RSZ eta^{1/Q}`. -/
private theorem source_term_le_max (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (ht : (jStar : ℤ) ≤ t)
    (hcube : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (C₀ Cn Cs η : ℝ) (hC₀ : 0 < C₀) (hCn : 0 < Cn) (hCs : 0 < Cs)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) (hXa : 0 < X a)
    (hpath : ∀ (mm : Mat d), mm.PosDef → ∀ (j : ℤ) (y : Vec d),
      HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar mm) j y ⊆
          HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCellTranslate
            (Geometry.explicitRoundedGrid jStar mm) j y) a)
          (blockScale (C₀ * Real.sqrt (‖mm‖ * ‖mm⁻¹‖) * X a *
            (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0)) E))
    (hnormt : BlockMatLoewnerLE E (blockScale (Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)))
    (hsrcsmall : Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)))
    (n : ℕ) (hn : (t - (jStar : ℤ)).toNat < n) (z : Fin d → ℤ)
    (hz : z ∈ triadicIndexBox d n) :
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        blockSpecBound (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t))
          (Book.Ch02.blockIdentity d)) ≤
      C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a := by
  let : NeZero d := ⟨by omega⟩
  have hwnn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hEt : (toFullBlockMat (adaptedMean P
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  have hee : (0 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by positivity
  have heesq : Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) =
      ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := Real.mul_self_sqrt hee
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) :=
    Real.sqrt_nonneg _
  have hPi : (0 : ℝ) < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le hdag).1
  have hcell : HighContrast.adaptedCellTranslate
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ))
      (adaptedCellCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
        (t - (n : ℤ)) z) ⊆ HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
    rw [adaptedCellTranslate_center]
    exact fun x hx => hcube (adaptedCellAtCenter_subset_adaptedCell
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t n hz hx)
  have hb := hpath (explicitCanonicalMetric F) hm (t - (n : ℤ))
    (adaptedCellCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) (t - (n : ℤ)) z) hcell
  rw [adaptedCellTranslate_center] at hb
  have hc1 : (0 : ℝ) ≤ C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      X a * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₀.le hsq0) hXa.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hc2 : (0 : ℝ) ≤ Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) :=
    mul_nonneg (mul_nonneg hCn.le hPi.le) hsq0
  have hspec := cell_specBound_le
    (coarseBlock (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
      (t - (n : ℤ)) z) a)
    (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t) E hEt _ _
    hc1 hc2 hb hnormt
  refine le_trans (mul_le_mul_of_nonneg_left hspec hwnn) ?_
  have hT0 : (0 : ℝ) ≤ (t : ℝ) - (jStar : ℝ) := by
    have h1 : ((jStar : ℤ) : ℝ) ≤ ((t : ℤ) : ℝ) := by exact_mod_cast ht
    push_cast at h1
    linarith only [h1]
  have hn' : (t : ℝ) - (jStar : ℝ) + 1 ≤ (n : ℝ) := by
    have h2 : (t : ℤ) - (jStar : ℤ) + 1 ≤ (n : ℤ) := by omega
    have h3 : ((t : ℤ) : ℝ) - ((jStar : ℤ) : ℝ) + 1 ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    linarith only [h3]
  have hmaxeq : max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0 =
      (jStar : ℝ) - (t : ℝ) + (n : ℝ) := by
    have hc : ((t - (n : ℤ) : ℤ) : ℝ) = (t : ℝ) - (n : ℝ) := by push_cast; ring
    rw [hc, max_eq_left (by linarith only [hn'])]
    ring
  have hpw : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
      (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) ≤
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) := by
    rw [hmaxeq, ← Real.rpow_add (by norm_num)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hrho := rhoMax_lt_respRho d hd γ hγ
    have hrhoeq : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    have h1 : (0 : ℝ) ≤ (Quenched.contrastRho γ - γ) * ((n : ℝ) - ((t : ℝ) - (jStar : ℝ)) - 1) :=
      mul_nonneg (by rw [hrhoeq]; linarith only [hγ.2]) (by linarith only [hn'])
    have h2 : (0 : ℝ) ≤ (Quenched.contrastRho γ - rhoMax d γ) * ((t : ℝ) - (jStar : ℝ)) :=
      mul_nonneg (by linarith only [hrho]) hT0
    nlinarith only [h1, h2, hγ.1, hγ.2, hrho, hrhoeq, hT0, hn']
  have hss' : aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := by
    rw [le_div_iff₀ hCs]
    linarith only [hsrcsmall]
  have hXCn : (0 : ℝ) ≤ C₀ * Cn * X a := mul_nonneg (mul_nonneg hC₀.le hCn.le) hXa.le
  have hstep1 : (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
      (C₀ * Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * X a *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0) *
        (Cn * aspectRatio E *
          Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))) =
      C₀ * Cn * X a * (aspectRatio E *
        (Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
          Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖)) *
        ((3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
          (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0))) := by ring
  rw [hstep1, heesq]
  have hstep2 : aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      ((3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - ((t - (n : ℤ) : ℤ) : ℝ)) 0)) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs :=
    le_trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hPi.le hee)) hss'
  have hstep3 := mul_le_mul_of_nonneg_left hstep2 hXCn
  have hstep4 : C₀ * Cn * X a * (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) =
      C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a := by field_simp
  rw [hstep4] at hstep3
  exact hstep3

/-- **The pathwise all-scale bound**: the two branches combined through
`respAllScaleMax_le_of_forall`. -/
theorem pathwise_bound_max (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (ht : (jStar : ℤ) ≤ t)
    (hcube : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (C₀ Cn Cs η : ℝ) (hC₀ : 0 < C₀) (hCn : 0 < Cn) (hCs : 0 < Cs) (hη : 0 < η)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) (hXa : 0 < X a)
    (hpath : ∀ (mm : Mat d), mm.PosDef → ∀ (j : ℤ) (y : Vec d),
      HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar mm) j y ⊆
          HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCellTranslate
            (Geometry.explicitRoundedGrid jStar mm) j y) a)
          (blockScale (C₀ * Real.sqrt (‖mm‖ * ‖mm⁻¹‖) * X a *
            (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0)) E))
    (hnormt : BlockMatLoewnerLE E (blockScale (Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)))
    (hsrcsmall : Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ))) :
    respAllScaleMax P γ jStar F t a ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
            blockOpNorm (normalizedFluctuation P
              (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ) ^
          ((bigQ d γ : ℝ)⁻¹) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
        C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a := by
  let : NeZero d := ⟨by omega⟩
  have hF00 : (0 : ℝ) ≤ ⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
          blockOpNorm (normalizedFluctuation P
            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hu0 : (0 : ℝ) ≤ (⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
          blockOpNorm (normalizedFluctuation P
            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ) ^
      ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg hF00 _
  have hv0 : (0 : ℝ) ≤
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d hd γ P E Ψ Kg Src inferInstance hstat hunit hdag jStar hj
      (explicitCanonicalMetric F) hm t
  have hw0 : (0 : ℝ) ≤ C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
    mul_nonneg (mul_nonneg (div_pos (mul_pos hC₀ hCn) hCs).le
      (Real.rpow_nonneg hη.le _)) hXa.le
  refine respAllScaleMax_le_of_forall P γ jStar F t a _ (by linarith only [hu0, hv0, hw0]) ?_
  intro n z hz
  simp only [respMean, respGrid]
  by_cases hn : n ≤ (t - (jStar : ℤ)).toNat
  · have h := fluctuation_term_le_max d hd γ hγ P E Ψ Kg Src hstat hdag jStar hj
      (explicitCanonicalMetric F) hm t ht a n ⟨Nat.zero_le _, hn⟩ z hz
    linarith only [h, hw0]
  · push Not at hn
    have h := source_term_le_max d hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t ht hcube
      C₀ Cn Cs η hC₀ hCn hCs X a hXa hpath hnormt hsrcsmall n hn z hz
    linarith only [h, hu0, hv0]

end HCPolySupport.HighContrast.Multiscale
end
