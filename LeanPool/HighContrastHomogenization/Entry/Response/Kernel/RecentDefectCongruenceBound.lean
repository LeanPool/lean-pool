/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentCellDefectBound

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentDefectCongruenceBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The pointwise two-sided recent-defect bound via congruence

Continuing the reduction of the recent-cell defect to the two-sided quantity `respAllScaleAbs`,
this file proves the pointwise bound `‖N_{n,w} - N_0‖ ≤ (3^{ρn} + 1) · respAllScaleAbs a` on the
normalized block defect, using that the recentred and adjoint normalizers are the same congruence
of the `E_t`-picture as the coarse block itself, so a congruence applied to both leaves the
normalized operator norm unchanged (`p.response.transfer`). It also records the
positive-definiteness of the recentred and adjoint response matrices and the measurability and
integrability of `respAllScaleAbs` that the bound needs.
-/

section
open HCPolySupport.HighContrast (CoeffSpace aspectRatio blockSub coarseBlock normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Two doubled blocks with the same flat representation are equal. -/
private theorem blockMat_eq_of_full {A B : BlockMat d}
    (h : toFullBlockMat A = toFullBlockMat B) : A = B := by
  rw [← ofFullBlockMat_toFullBlockMat A, ← ofFullBlockMat_toFullBlockMat B, h]

/-- Congruence is linear over `blockSub`. -/
theorem blockCongr_blockSub (G A B : BlockMat d) :
    blockCongr G (blockSub A B) = blockSub (blockCongr G A) (blockCongr G B) := by
  refine blockMat_eq_of_full ?_
  rw [blockCongr, toFullBlockMat_ofFullBlockMat, toFullBlockMat_blockSub,
    toFullBlockMat_blockSub, blockCongr, blockCongr, toFullBlockMat_ofFullBlockMat,
    toFullBlockMat_ofFullBlockMat, Matrix.mul_sub, Matrix.sub_mul]

/-- `A - B = (A - I) - (B - I)`. -/
private theorem blockSub_shift_identity (A B : BlockMat d) :
    blockSub A B = blockSub (blockSub A (Book.Ch02.blockIdentity d))
      (blockSub B (Book.Ch02.blockIdentity d)) := by
  refine blockMat_eq_of_full ?_
  rw [toFullBlockMat_blockSub, toFullBlockMat_blockSub, toFullBlockMat_blockSub,
    toFullBlockMat_blockSub]
  abel

/-- **The pointwise η-kernel bound, `E_t`-picture.**  With `N_k = normalizedBlock A_k E_t`,
`‖N_{n,w} - N_0‖ ≤ (3 ^ (ρ n) + 1) · respAllScaleAbs a`, a.e.  Both summands come from
`weighted_blockOpNorm_le_respAllScaleAbs`, the depth-`n` one after multiplying by
`3 ^ (ρ n)` and the depth-`0` one at `z = 0`, where `triadicIndexBox d 0 = {0}` and
`adaptedCellAtCenter q t 0 = adaptedCell q t`. -/
theorem blockOpNorm_normalizedBlock_sub_le (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n,
      blockOpNorm (normalizedBlock
          (blockSub (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
            (coarseBlock (HighContrast.adaptedCell (respGrid jStar F) t) a))
          (respMean P jStar F t))
        ≤ ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) * respAllScaleAbs P γ jStar F t a := by
  filter_upwards
    [weighted_blockOpNorm_le_respAllScaleAbs hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hkey
  intro n w hw
  set q := respGrid jStar F with hq
  set Et := respMean P jStar F t with hEt
  set Ab := respAllScaleAbs P γ jStar F t a with hAb
  -- the two members of the defining set
  have hn := hkey n w hw
  have h0 := hkey 0 0 (zero_mem_triadicIndexBox 0)
  have hw0 : (0 : ℝ) < (3 : ℝ) ^ (-(Quenched.contrastRho γ * (n : ℝ))) := Real.rpow_pos_of_pos
    (by norm_num) _
  have hwmul : (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * (3 : ℝ) ^ (-(Quenched.contrastRho
    γ * (n : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have hwpos : (0 : ℝ) < (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) := Real.rpow_pos_of_pos
    (by norm_num) _
  -- depth-`n` term
  have hn' : blockOpNorm (blockSub (normalizedBlock
      (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a) Et) (Book.Ch02.blockIdentity d))
      ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * Ab := by
    have := mul_le_mul_of_nonneg_left hn hwpos.le
    calc blockOpNorm (blockSub (normalizedBlock
            (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a) Et) (Book.Ch02.blockIdentity d))
        = (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * ((3 : ℝ) ^ (-(Quenched.contrastRho γ *
          (n : ℝ))) *
            blockOpNorm (blockSub (normalizedBlock
              (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a) Et)
              (Book.Ch02.blockIdentity d))) := by
          rw [← mul_assoc, hwmul, one_mul]
      _ ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) * Ab := this
  -- depth-`0` term
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 :=
    (adaptedCellAtCenter_zero q t).symm
  have h0' : blockOpNorm (blockSub (normalizedBlock
      (coarseBlock (HighContrast.adaptedCell q t) a) Et) (Book.Ch02.blockIdentity d)) ≤ Ab := by
    have hz : t - ((0 : ℕ) : ℤ) = t := by simp
    have hp : (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((0 : ℕ) : ℝ))) = 1 := by
      rw [Nat.cast_zero, mul_zero, neg_zero, Real.rpow_zero]
    rw [hz, hp, one_mul] at h0
    rw [hcell]
    exact h0
  -- assemble
  have hsplit : normalizedBlock
      (blockSub (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a)
        (coarseBlock (HighContrast.adaptedCell q t) a)) Et =
      blockSub
        (blockSub (normalizedBlock (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a) Et)
          (Book.Ch02.blockIdentity d))
        (blockSub (normalizedBlock (coarseBlock (HighContrast.adaptedCell q t) a) Et)
          (Book.Ch02.blockIdentity d)) := by
    rw [Annealed.normalizedBlock_blockSub, ← blockSub_shift_identity]
  rw [hsplit, blockOpNorm, toFullBlockMat_blockSub]
  have htri := norm_sub_le
    (toFullBlockMat (blockSub (normalizedBlock
      (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a) Et) (Book.Ch02.blockIdentity d)))
    (toFullBlockMat (blockSub (normalizedBlock
      (coarseBlock (HighContrast.adaptedCell q t) a) Et) (Book.Ch02.blockIdentity d)))
  rw [blockOpNorm] at hn' h0'
  nlinarith only [htri, hn', h0']

/-- `Ehat^+ = D Ehat^- D` is the congruence of `E_t` by `respGPlus = respG · D`
(`ResponseBlockObjects.lean`, `blockCongr_blockCongr`), i.e. the plus sign is the same
picture with the same congruence that `coarseBlockMatrix_respCoeffPlus_at` produces. -/
theorem respEhatPlus_eq_blockCongr (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) :
    respEhatPlus P jStar F t = blockCongr (respGPlus F) (respMean P jStar F t) := by
  rw [respEhatPlus, blockAdjoint, respEhatMinus, blockCongr_blockCongr, respGPlus]

/-- The block shear `⟨1, 0, c, 1⟩` in `fromBlocks` form. -/
private theorem shear_full (c : Mat d) :
    toFullBlockMat (⟨1, 0, c, 1⟩ : BlockMat d) = Matrix.fromBlocks (1 : Mat d) 0 c 1 := by
  ext (i | i) (j | j) <;> rfl

/-- `G = ⟨1, 0, respg F, 1⟩` is a unit: the shear by `-respg F` is its right inverse. -/
private theorem isUnit_respG (F : BlockMat d) : IsUnit (toFullBlockMat (respG F)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse
      (B := toFullBlockMat (⟨1, 0, -(respg F), 1⟩ : BlockMat d)) ?_)
  rw [respG, shear_full, shear_full, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel,
    Matrix.fromBlocks_one]

/-- `D = diag(Id, -Id)` in `fromBlocks` form. -/
private theorem blockD_full :
    toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
  ext (i | i) (j | j) <;> rfl

/-- `D` is a unit: it is its own inverse. -/
private theorem isUnit_blockD : IsUnit (toFullBlockMat (blockD d)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (B := toFullBlockMat (blockD d)) ?_)
  rw [blockD_full, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.fromBlocks_one,
    Matrix.one_mul]

/-- `respGPlus = respG · D` is a unit. -/
private theorem isUnit_respGPlus (F : BlockMat d) :
    IsUnit (toFullBlockMat (respGPlus F)) := by
  rw [respGPlus, toFullBlockMat_ofFullBlockMat]
  exact (isUnit_respG F).mul isUnit_blockD

/-- `Ehat^-` is positive definite. -/
theorem respEhatMinus_posDef (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
  blockCongr_posDef (isUnit_respG F)
    (Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F)
      hm t)

/-- `Ehat^+` is positive definite. -/
theorem respEhatPlus_posDef (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    (toFullBlockMat (respEhatPlus P jStar F t)).PosDef := by
  rw [respEhatPlus_eq_blockCongr]
  exact blockCongr_posDef (isUnit_respGPlus F)
    (Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F)
      hm t)

/-- **THE η-KERNEL POINTWISE BOUND, minus sign** — the inequality the η-kernel's conjunct 3 is built
on, and the one the ONE-SIDED `respAllScaleMax` provably cannot give:

`recentDefect q t n w Ehat^- (a_-) ≤ (3 ^ (ρ n) + 1) · respAllScaleAbs a`, `P`-a.e., uniformly
in `n` and in the aligned index `w`.

Route, exactly the paper's (`p.response.transfer`): the recentred field `a_-` and the
normalizer `Ehat^- = blockCongr (respG F) E_t` are the SAME congruence of the `E_t`-picture
(`coarseBlockMatrix_respCoeffMinus_at`), congruence does not increase the
normalized operator norm (`blockOpNorm_normalizedBlock_blockCongr_le`), and in the
`E_t`-picture the defect splits as `(N_{n,w} - I) - (N_0 - I)`
(`blockOpNorm_normalizedBlock_sub_le`).

Positive definiteness of `Ehat^-` is DISCHARGED here, not assumed:
`respEhatMinus_posDef` above, from `blockCongr_posDef` and the unit block shear
`respG F = ⟨1, 0, respg F, 1⟩` (`ResponseBlockObjects.lean`). -/
theorem recentDefect_le_respAllScaleAbs_minus (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n,
      recentDefect (respGrid jStar F) t n w (respEhatMinus P jStar F t) (respCoeffMinus F a)
        ≤ ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) * respAllScaleAbs P γ jStar F t a := by
  let : NeZero d := ⟨by omega⟩
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric
      F) hm t
  have hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    respEhatMinus_posDef hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t
  filter_upwards
    [blockOpNorm_normalizedBlock_sub_le hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  intro n w hw
  set q := respGrid jStar F with hqd
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 :=
    (adaptedCellAtCenter_zero q t).symm
  have hEhd : respEhatMinus P jStar F t = blockCongr (respG F) (respMean P jStar F t) := rfl
  have hrw : recentDefect q t n w (respEhatMinus P jStar F t) (respCoeffMinus F a) =
      blockOpNorm (normalizedBlock
        (blockCongr (respG F)
          (blockSub (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a)
            (coarseBlock (HighContrast.adaptedCell q t) a)))
        (blockCongr (respG F) (respMean P jStar F t))) := by
    rw [recentDefect, recentDefectBlock, hEhd, blockOpNorm,
      coarseBlockMatrix_respCoeffMinus_at hq (t - (n : ℤ)) w F a, hcell,
      coarseBlockMatrix_respCoeffMinus_at hq t 0 F a, ← blockCongr_blockSub, ← hcell]
  rw [hrw]
  exact le_trans
    (blockOpNorm_normalizedBlock_blockCongr_le (respG F) _ _ hEt (hEhd ▸ hEhat))
    (ha n w hw)

/-- **THE η-KERNEL POINTWISE BOUND, plus sign.**  The twin of
`recentDefect_le_respAllScaleAbs_minus`, with `respGPlus` in place of `respG`. -/
theorem recentDefect_le_respAllScaleAbs_plus (hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ w ∈ triadicIndexBox d n,
      recentDefect (respGrid jStar F) t n w (respEhatPlus P jStar F t) (respCoeffPlus F a)
        ≤ ((3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ)) + 1) * respAllScaleAbs P γ jStar F t a := by
  let : NeZero d := ⟨by omega⟩
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric
      F) hm t
  have hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
    respEhatPlus_posDef hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t
  filter_upwards
    [blockOpNorm_normalizedBlock_sub_le hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  intro n w hw
  set q := respGrid jStar F with hqd
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 :=
    (adaptedCellAtCenter_zero q t).symm
  have hEhd := respEhatPlus_eq_blockCongr P jStar F t
  have hrw : recentDefect q t n w (respEhatPlus P jStar F t) (respCoeffPlus F a) =
      blockOpNorm (normalizedBlock
        (blockCongr (respGPlus F)
          (blockSub (coarseBlock (adaptedCellAtCenter q (t - (n : ℤ)) w) a)
            (coarseBlock (HighContrast.adaptedCell q t) a)))
        (blockCongr (respGPlus F) (respMean P jStar F t))) := by
    rw [recentDefect, recentDefectBlock, hEhd, blockOpNorm,
      coarseBlockMatrix_respCoeffPlus_at hq (t - (n : ℤ)) w F a, hcell,
      coarseBlockMatrix_respCoeffPlus_at hq t 0 F a, ← blockCongr_blockSub, ← hcell]
  rw [hrw]
  exact le_trans
    (blockOpNorm_normalizedBlock_blockCongr_le (respGPlus F) _ _ hEt (hEhd ▸ hEhat))
    (ha n w hw)

/-- **The two-sided carrier really is the strengthening it is meant to be**, with
its side condition discharged a.e. from `RawOutput`-level data: `respAllScaleMax ≤
respAllScaleAbs` holds `P`-a.e., so every existing consumer of the one-sided carrier survives
the η-kernel restatement. -/
theorem respAllScaleMax_le_respAllScaleAbs_ae (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, respAllScaleMax P γ jStar F t a ≤ respAllScaleAbs P γ jStar F t a := by
  filter_upwards [pathwise_envelope_abs hd γ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hbdd
  exact respAllScaleMax_le_respAllScaleAbs P γ jStar F t a hbdd

/-- **JENSEN / the power-mean step for the η-kernel.**  On a probability measure, for a
nonnegative `f` and `2 ≤ Q`,

`∫ f ^ 2 ∂P ≤ (∫ f ^ Q ∂P) ^ (2/Q)`.

Elementary route, no `eLpNorm` machinery: with `I = ∫ f ^ Q ∂P` and `θ = 2/Q ∈ (0, 1]`, the
weighted AM-GM `Real.geom_mean_le_arith_mean2_weighted` at `p₁ = f a ^ Q`, `p₂ = I` gives
pointwise `f a ^ 2 · I ^ (1-θ) ≤ θ · f a ^ Q + (1-θ) · I`; integrating over the PROBABILITY
measure the right side is `I`, and dividing by `I ^ (1-θ)` leaves `I ^ θ`.  This is the last
analytic ingredient of the η-kernel's conjunct 3. -/
theorem integral_sq_le_rpow {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (Q : ℕ) (hQ : 2 ≤ Q) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hf2 : Integrable (fun a => f a ^ 2) P) (hfQ : Integrable (fun a => f a ^ Q) P) :
    ∫ a, f a ^ 2 ∂P ≤ (∫ a, f a ^ Q ∂P) ^ ((2 : ℝ) / (Q : ℝ)) := by
  set I : ℝ := ∫ a, f a ^ Q ∂P with hI
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (0 : ℕ) < Q := by omega
    exact_mod_cast this
  set θ : ℝ := (2 : ℝ) / (Q : ℝ) with hθ
  have hθ0 : 0 < θ := div_pos (by norm_num) hQ0
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hQ0]
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith only [this]
  have hI0 : 0 ≤ I := integral_nonneg fun a => pow_nonneg (hf a) _
  rcases eq_or_lt_of_le hI0 with hIz | hIpos
  · -- `I = 0` forces `f = 0` a.e.
    have hae : ∀ᵐ a ∂P, f a ^ Q = 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun a => pow_nonneg (hf a) Q) hfQ).mp hIz.symm
      filter_upwards [this] with a ha using ha
    have hae2 : ∀ᵐ a ∂P, f a ^ 2 = 0 := by
      filter_upwards [hae] with a ha
      have hfa : f a = 0 := by
        by_contra h
        exact h (pow_eq_zero_iff (by omega : Q ≠ 0) |>.mp ha)
      rw [hfa]; ring
    rw [integral_congr_ae (g := fun _ : α => (0 : ℝ)) hae2, integral_zero, ← hIz,
      Real.zero_rpow (ne_of_gt hθ0)]
  · -- the generic case
    have hpow : ∀ a, f a ^ 2 * I ^ (1 - θ) ≤ θ * f a ^ Q + (1 - θ) * I := by
      intro a
      have hgm := Real.geom_mean_le_arith_mean2_weighted hθ0.le (by linarith only [hθ1] : (0:ℝ)
        ≤ 1 - θ)
        (pow_nonneg (hf a) Q) hI0 (by ring)
      have hlhs : (f a ^ Q) ^ θ = f a ^ 2 := by
        rw [← Real.rpow_natCast (f a) Q, ← Real.rpow_mul (hf a), hθ]
        rw [show (Q : ℝ) * ((2 : ℝ) / (Q : ℝ)) = 2 from by field_simp]
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      rw [hlhs] at hgm
      exact hgm
    have hint1 : Integrable (fun a => f a ^ 2 * I ^ (1 - θ)) P := hf2.mul_const _
    have hint2 : Integrable (fun a => θ * f a ^ Q + (1 - θ) * I) P :=
      (hfQ.const_mul θ).add (integrable_const _)
    have hmono := integral_mono hint1 hint2 hpow
    rw [integral_mul_const, integral_add (hfQ.const_mul θ) (integrable_const _),
      integral_const_mul, integral_const] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    have hmono' : (∫ a, f a ^ 2 ∂P) * I ^ (1 - θ) ≤ I := by
      have hIeq : θ * (∫ a, f a ^ Q ∂P) + (1 - θ) * I = I := by rw [← hI]; ring
      linarith only [hmono, hIeq]
    have hIr : I ^ (1 - θ) * I ^ θ = I := by
      rw [← Real.rpow_add hIpos]
      simp [Real.rpow_one]
    have hIrpos : 0 < I ^ (1 - θ) := Real.rpow_pos_of_pos hIpos _
    refine le_of_mul_le_mul_right ?_ hIrpos
    calc (∫ a, f a ^ 2 ∂P) * I ^ (1 - θ) ≤ I := hmono'
      _ = I ^ θ * I ^ (1 - θ) := by rw [mul_comm]; exact hIr.symm

/-- Entrywise measurability of a block-valued map gives measurability of its operator norm:
`blockOpNorm = ‖·‖ ∘ toFullBlockMat` and the norm is continuous on the finite-dimensional
`FullBlockMat d`. -/
private theorem measurable_blockOpNorm {α : Type*} [MeasurableSpace α]
    (X : α → BlockMat d) (h : ∀ ζ δ, Measurable fun a => toFullBlockMat (X a) ζ δ) :
    Measurable fun a => blockOpNorm (X a) := by
  have hM : Measurable fun a => toFullBlockMat (X a) :=
    Measurable.of_eval fun ζ => Measurable.of_eval fun δ => h ζ δ
  exact continuous_norm.measurable.comp hM

/-- Measurability of the two-sided all-scale maximum: the `respAllScaleAbs` twin of
`respAllScaleMax_measurable` above, with `blockOpNorm` in place of `blockSpecBound` (the norm is
continuous, so no attained-infimum argument is needed here). -/
theorem respAllScaleAbs_measurable [NeZero d]
    (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (hq : IsUnit (respGrid jStar F)) (t : ℤ) :
    Measurable (respAllScaleAbs P γ jStar F t) := by
  set g : ℕ × (Fin d → ℤ) → CoeffSpace d → ℝ := fun p a =>
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * (p.1 : ℝ))) *
      blockOpNorm (blockSub
        (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (p.1 : ℤ))
          p.2) a)
          (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) with hg
  have hrw : respAllScaleAbs P γ jStar F t =
      fun a => sSup ((fun p => g p a) ''
        {p : ℕ × (Fin d → ℤ) | p.2 ∈ triadicIndexBox d p.1}) := by
    funext a
    rw [respAllScaleAbs]
    congr 1
    ext y
    constructor
    · rintro ⟨n, z, hz, rfl⟩
      exact ⟨(n, z), hz, rfl⟩
    · rintro ⟨⟨n, z⟩, hz, rfl⟩
      exact ⟨n, z, hz, rfl⟩
  rw [hrw]
  refine Measurable.sSup (Set.to_countable _) fun p _ => ?_
  exact (measurable_blockOpNorm _ fun α β =>
    measurable_normalized_entry hq _ _ _ α β).const_mul _

/-- **The two-sided carrier.**  Measurability and
`L^Q`-integrability of `A = respAllScaleAbs` under `RawOutput`: the `respAllScaleAbs` twin of
`respAllScaleMax_aestronglyMeasurable_integrable` above.

Why this is needed.  The η-kernel twins `integral_recentDefect_sq_le_minus` / `_plus` below carry
TWO premises about the carrier: `Integrable (fun a => A a ^ Q) P` and
`∫ A ^ Q ∂P ≤ Cm η`.  The second has a producer -- `response_allscale_abs`
 -- but the first had none, since it is produced above only
for the ONE-SIDED `respAllScaleMax`, and neither premise follows from the other.  With this
theorem both premises of the η-kernel estimate have producers.

Route, the one-sided twin with the two-sided ingredients: `respAllScaleAbs_measurable` for the
measurable half; for the integrable half, the SAME own choice of the source-smallness pair
`(C_s, η) = (1, (1 + Y)^Q)` (the explicit witness making the strengthened binder
set satisfiable), `pathwise_bound` in place of `pathwise_bound_max`, and
`add4_pow_le` in place of `add3_pow_le` because the two-sided pathwise bound carries
the one extra summand `η^{1/Q} / C_s` -- which at `C_s = 1` is the CONSTANT `1 + Y`, so it costs
only two more constant terms in the majorant and no new integrability input. -/
theorem respAllScaleAbs_aestronglyMeasurable_integrable (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            AEStronglyMeasurable (respAllScaleAbs P γ jStar F t) P ∧
              Integrable (fun a => respAllScaleAbs P γ jStar F t a ^ bigQ d γ) P := by
  obtain ⟨Csrc₁, C₀, hCsrc₁, hC₀, hsrcm⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  obtain ⟨Csrc₂, Cn, hCsrc₂, hCn, hrefn⟩ :=
    Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw
  let : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hMmeas : Measurable (respAllScaleAbs P γ jStar F t) :=
    respAllScaleAbs_measurable P γ jStar F hq t
  refine ⟨hMmeas.aestronglyMeasurable, ?_⟩
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hQ0 : bigQ d γ ≠ 0 := by omega
  have hwin := respAllScale_window d hd γ S ε σ Cglob Cprof (max Csrc₁ Csrc₂) Bresp H P E Ψ Kg
    Src B jStar F s t hε hσ raw
  have hjt : (jStar : ℤ) ≤ t := le_of_lt hwin.2
  have hB0 : (1 : ℝ) ≤ S.B0 ε σ := S.one_le_B0 ε σ hε hσ
  have hB : (1 : ℝ) ≤ B := hB0.trans ((le_max_left _ _).trans raw.hB)
  have hA1 : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger raw.ell
  have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) :=
      Real.log_le_log (by norm_num) (by linarith only [hA1])
    rw [Real.logb, le_div_iff₀ hl3]
    linarith only [h2]
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [raw.ell.one_lt_growthWitness])
  have hthr : ∀ c : ℝ, c ≤ max Csrc₁ Csrc₂ → ⌈c * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
    intro c hc
    refine le_trans (Int.ceil_mono ?_) raw.hsrc
    have h1 : c * Real.logb 3 (2 * Kg) ≤ max Csrc₁ Csrc₂ * Real.logb 3 (2 * Kg) :=
      mul_le_mul_of_nonneg_right hc hlogK
    have h2 : (0 : ℝ) ≤ Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) :=
      mul_nonneg (mul_nonneg hCglob (by linarith only [hB])) (by linarith only [hlog])
    linarith only [h1, h2]
  obtain ⟨ell, X, hell, hXm, hform, hmin, hlp, hXint, hXmom, hXnorm, hpath⟩ :=
    hsrcm P E Ψ Kg Src raw.stat raw.ell jStar raw.hj (hthr Csrc₁ (le_max_left _ _))
  have hnormt := (hrefn P E Ψ Kg Src raw.stat raw.ell jStar raw.hj
    (hthr Csrc₂ (le_max_right _ _)) (explicitCanonicalMetric F) hm t hjt raw.cube).2
  have hX0 : ∀ a, (0 : ℝ) < X a := fun a => by rw [hform]; positivity
  obtain ⟨hfint, -⟩ := oneGrid_fluctuation_integrable_dominate d hd γ P E Ψ Kg Src raw.stat
    raw.ell jStar raw.hj (explicitCanonicalMetric F) hm t
  set F0 : CoeffSpace d → ℝ := fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) t,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
        F)) j ∩
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
            F)) t,
        blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar
          (explicitCanonicalMetric F))
          j t z a) ^ bigQ d γ with hF0def
  have hF00 : ∀ a, (0 : ℝ) ≤ F0 a := fun a =>
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hDr0 : (0 : ℝ) ≤ determinantDrift P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d hd γ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t
  -- OWN choice of the source-smallness pair `(Cs, η)`, the one-sided twin's: `Cs = 1`,
  -- `η = (1 + Y)^Q`.  The explicit witness.
  set Y : ℝ := aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
    (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) with hYdef
  have hPi : (0 : ℝ) < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le raw.ell).1
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hYdef]; positivity
  set η : ℝ := (1 + Y) ^ bigQ d γ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; exact pow_pos (by linarith only [hY0]) _
  have hηroot : η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) = 1 + Y := by
    rw [hηdef, one_div]
    exact Real.pow_rpow_inv_natCast (by linarith only [hY0]) hQ0
  have hsrcsmall : (1 : ℝ) * aspectRatio E * (‖explicitCanonicalMetric F‖ *
    ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) := by
    rw [hηroot, one_mul, ← hYdef]
    linarith only []
  set Kw : ℝ := C₀ * Cn / 1 with hKwdef
  have hKw : (0 : ℝ) < Kw := by rw [hKwdef]; positivity
  have hkey : ∀ᵐ a ∂P, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ≤
      (3 : ℝ) ^ bigQ d γ * (F0 a +
        (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
          jStar t) ^
          bigQ d γ +
        (3 : ℝ) ^ bigQ d γ * ((Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ +
          (1 + Y) ^ bigQ d γ + (1 + Y) ^ bigQ d γ)) := by
    filter_upwards [hpath] with a ha
    have hu0 : (0 : ℝ) ≤ F0 a ^ ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg (hF00 a) _
    have hw0 : (0 : ℝ) ≤ Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      mul_nonneg (mul_nonneg hKw.le (Real.rpow_nonneg hη.le _)) (hX0 a).le
    have hx0 : (0 : ℝ) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / 1 :=
      div_nonneg (Real.rpow_nonneg hη.le _) zero_le_one
    have hMle : respAllScaleAbs P γ jStar F t a ≤
        F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
            jStar t +
          Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
          η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / 1 :=
      pathwise_bound d hd γ P E Ψ Kg Src raw.stat raw.unit raw.ell jStar raw.hj F hm
        t hjt raw.cube C₀ Cn 1 η hC₀ hCn one_pos hη X a (hX0 a) ha.2 hnormt hsrcsmall
    calc respAllScaleAbs P γ jStar F t a ^ bigQ d γ
        ≤ (F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric
              F)) jStar t +
            Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
            η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / 1) ^ bigQ d γ :=
          pow_le_pow_left₀ (respAllScaleAbs_nonneg P γ jStar F t a) hMle _
      _ ≤ (3 : ℝ) ^ bigQ d γ * ((F0 a ^ ((bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ +
            (3 : ℝ) ^ bigQ d γ *
              ((Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ +
                (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / 1) ^ bigQ d γ +
                (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / 1) ^ bigQ d γ)) :=
          add4_pow_le _ _ _ _ _ hu0 hDr0 hw0 hx0
      _ = (3 : ℝ) ^ bigQ d γ * (F0 a +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ +
            (3 : ℝ) ^ bigQ d γ * ((Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ +
              (1 + Y) ^ bigQ d γ + (1 + Y) ^ bigQ d γ)) := by
          rw [Real.rpow_inv_natCast_pow (hF00 a) hQ0, hηroot, div_one, mul_pow]
  have hi1 : Integrable (fun a => F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
        jStar t) ^
        bigQ d γ) P := hfint.add (integrable_const _)
  have hi2 : Integrable (fun a => (3 : ℝ) ^ bigQ d γ *
      ((Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ +
        (1 + Y) ^ bigQ d γ + (1 + Y) ^ bigQ d γ)) P :=
    (((hXint.const_mul _).add (integrable_const _)).add (integrable_const _)).const_mul _
  have hgint : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * (F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
        jStar t) ^
        bigQ d γ +
      (3 : ℝ) ^ bigQ d γ * ((Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ +
        (1 + Y) ^ bigQ d γ + (1 + Y) ^ bigQ d γ))) P := (hi1.add hi2).const_mul _
  refine hgint.mono' ((hMmeas.pow_const _).aestronglyMeasurable) ?_
  filter_upwards [hkey] with a ha
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (respAllScaleAbs_nonneg P γ jStar F t a) _)]
  exact ha

/-- **From the pointwise η-kernel bound to conjuncts 2 and 3.**  If `0 ≤ g ≤ c · A` a.e. with
`A ≥ 0`, `A ^ Q` integrable and `∫ A ^ Q ∂P ≤ Cm · η` on a probability measure with `2 ≤ Q`,
then `g ^ 2` is integrable and `∫ g ^ 2 ∂P ≤ c ^ 2 · Cm ^ (2/Q) · η ^ (2/Q)`.

`A ^ 2 ≤ 1 + A ^ Q` pointwise (split at `A = 1`) gives integrability with no smallness;
`integral_sq_le_rpow` (Jensen) gives the exponent.  The last analytic step. -/
theorem conjuncts_of_pointwise (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (Q : ℕ) (hQ : 2 ≤ Q) (Cm η : ℝ) (hCm : 0 < Cm) (hη : 0 < η)
    (g A : CoeffSpace d → ℝ) (hA0 : ∀ a, 0 ≤ A a) (hg0 : ∀ a, 0 ≤ g a)
    (hgmeas : AEStronglyMeasurable (fun a => g a ^ 2) P)
    (hAmeas : AEStronglyMeasurable (fun a => A a ^ 2) P)
    (c : ℝ) (_hc : 0 ≤ c) (hbound : ∀ᵐ a ∂P, g a ≤ c * A a)
    (hAint : Integrable (fun a => A a ^ Q) P) (hAle : ∫ a, A a ^ Q ∂P ≤ Cm * η) :
    Integrable (fun a => g a ^ 2) P ∧
      ∫ a, g a ^ 2 ∂P ≤ c ^ 2 * Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ)) := by
  -- `A ^ 2 ≤ 1 + A ^ Q`, so `A ^ 2` is integrable
  have hsq_le : ∀ a, A a ^ 2 ≤ 1 + A a ^ Q := by
    intro a
    rcases le_or_gt (A a) 1 with h | h
    · have : A a ^ 2 ≤ 1 := pow_le_one₀ (hA0 a) h
      have hQnn : (0 : ℝ) ≤ A a ^ Q := pow_nonneg (hA0 a) _
      linarith only [this, hQnn]
    · have : A a ^ 2 ≤ A a ^ Q := pow_le_pow_right₀ h.le hQ
      have hQnn : (0 : ℝ) ≤ A a ^ Q := pow_nonneg (hA0 a) _
      linarith only [this, hQnn]
  have hA2 : Integrable (fun a => A a ^ 2) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hAint) hAmeas ?_
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hA0 a) 2)]
    exact hsq_le a
  -- `g ^ 2 ≤ c ^ 2 * A ^ 2`, so `g ^ 2` is integrable
  have hgle2 : ∀ᵐ a ∂P, g a ^ 2 ≤ c ^ 2 * A a ^ 2 := by
    filter_upwards [hbound] with a ha
    have := mul_self_le_mul_self (hg0 a) ha
    nlinarith only [this, hg0 a, hA0 a]
  have hg2 : Integrable (fun a => g a ^ 2) P := by
    refine Integrable.mono' (hA2.const_mul (c ^ 2)) hgmeas ?_
    filter_upwards [hgle2] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hg0 a) 2)]
    exact ha
  refine ⟨hg2, ?_⟩
  -- chain the three inequalities
  have hstep1 : ∫ a, g a ^ 2 ∂P ≤ c ^ 2 * ∫ a, A a ^ 2 ∂P := by
    have := integral_mono_ae hg2 (hA2.const_mul (c ^ 2)) (by
      filter_upwards [hgle2] with a ha using ha)
    rwa [integral_const_mul] at this
  have hstep2 : ∫ a, A a ^ 2 ∂P ≤ (∫ a, A a ^ Q ∂P) ^ ((2 : ℝ) / (Q : ℝ)) :=
    integral_sq_le_rpow P Q hQ A hA0 hA2 hAint
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by
    have : (0 : ℕ) < Q := by omega
    exact_mod_cast this
  have hexp : (0 : ℝ) ≤ (2 : ℝ) / (Q : ℝ) := le_of_lt (div_pos (by norm_num) hQ0)
  have hInn : (0 : ℝ) ≤ ∫ a, A a ^ Q ∂P := integral_nonneg fun a => pow_nonneg (hA0 a) _
  have hstep3 : (∫ a, A a ^ Q ∂P) ^ ((2 : ℝ) / (Q : ℝ)) ≤ (Cm * η) ^ ((2 : ℝ) / (Q : ℝ)) :=
    Real.rpow_le_rpow hInn hAle hexp
  have hstep4 : (Cm * η) ^ ((2 : ℝ) / (Q : ℝ)) =
      Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ)) := Real.mul_rpow hCm.le hη.le
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  calc ∫ a, g a ^ 2 ∂P ≤ c ^ 2 * ∫ a, A a ^ 2 ∂P := hstep1
    _ ≤ c ^ 2 * ((Cm * η) ^ ((2 : ℝ) / (Q : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) hc2
    _ = c ^ 2 * Cm ^ ((2 : ℝ) / (Q : ℝ)) * η ^ ((2 : ℝ) / (Q : ℝ)) := by
        rw [hstep4]; ring

end

end HCPolySupport.HighContrast.Multiscale
end
