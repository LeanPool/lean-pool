/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.TraceGap
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.SchattenSandwich
public import LeanPool.HighContrastHomogenization.Geometry.SizeAlignment

/-!
# High-contrast homogenization: Provider.PortableHistory.MajorizationSize

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scalar size of a centered block, read spectrally

The centered history `e.scale.selection.fluctuation.history` measures a *centered*
doubled block `A_j^q(z) - E_j^q` against a positive reference block, so the
scalar size that enters it is the two-sided one: the least `t ≥ 0` with
`-tF ≤ H ≤ tF`.  The identification of that infimum with the spectral norm of
the normalized block is the only fact about it the majorization argument needs,
and this file proves it.

The one new ingredient is the two-sided companion of `norm_le_iff_le_smul_one`:
a symmetric matrix caught between `∓tI` has spectral norm at most `t`.  Its
proof is the factorization

`t²I - X² = (tI - X)(tI + X) = √(tI+X) (tI - X) √(tI+X)`,

which is legitimate because the square root of `tI + X` commutes with
`tI - X = 2tI - (tI + X)`; the C⋆ identity `‖X‖² = ‖X*X‖` then reads the norm
off the square.

Three consequences follow at once, and they are exactly the three steps the
proof of `p.fixed.geometry.one.grid.propagation` takes with the centered maximum: the size is
attained, so a change of the reference block costs the relative size of the two
references; the size is dominated by the Schatten size of the same pair, which
is how the centered moments `v_j^q` enter; and the size is a continuous function
of the entries of the block, so the centered maximum is a measurable statistic.
-/

namespace HCPolySupport
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

/-! ## The two-sided spectral characterization -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **A symmetric matrix caught between `∓tI` has spectral norm at most `t`.**
The two-sided companion of `norm_le_iff_le_smul_one`. -/
theorem norm_le_of_sandwich {X : Matrix n n ℝ} (hX : Xᴴ = X) {t : ℝ} (ht : 0 ≤ t)
    (hup : X ≤ t • (1 : Matrix n n ℝ)) (hlo : (-t) • (1 : Matrix n n ℝ) ≤ X) :
    ‖X‖ ≤ t := by
  have hC : (t • (1 : Matrix n n ℝ) - X).PosSemidef := Matrix.le_iff.mp hup
  have hD : (X + t • (1 : Matrix n n ℝ)).PosSemidef := by
    have h := Matrix.le_iff.mp hlo
    rwa [neg_smul, sub_neg_eq_add] at h
  obtain ⟨hE, hEE⟩ := matSqrt_spec hD
  set E : Matrix n n ℝ := matSqrt (X + t • (1 : Matrix n n ℝ)) with hEdef
  clear_value E
  clear hEdef
  have hEsymm : Eᵀ = E := by
    rw [← conjTranspose_eq_transpose']; exact hE.isHermitian
  have hCeq : t • (1 : Matrix n n ℝ) - X
      = (2 * t) • (1 : Matrix n n ℝ) - (X + t • (1 : Matrix n n ℝ)) := by
    rw [two_mul, add_smul]; abel
  have hcomm : (t • (1 : Matrix n n ℝ) - X) * E = E * (t • (1 : Matrix n n ℝ) - X) := by
    have hED : (X + t • (1 : Matrix n n ℝ)) * E = E * (X + t • (1 : Matrix n n ℝ)) := by
      rw [← hEE, Matrix.mul_assoc]
    rw [hCeq, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hED]
  have hexp : (t • (1 : Matrix n n ℝ) - X) * (X + t • (1 : Matrix n n ℝ))
      = (t * t) • (1 : Matrix n n ℝ) - X * X := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    abel
  have hprod : (t * t) • (1 : Matrix n n ℝ) - X * X
      = E * ((t • (1 : Matrix n n ℝ) - X) * E) :=
    calc (t * t) • (1 : Matrix n n ℝ) - X * X
        = (t • (1 : Matrix n n ℝ) - X) * (X + t • (1 : Matrix n n ℝ)) := hexp.symm
      _ = (t • (1 : Matrix n n ℝ) - X) * (E * E) := by rw [hEE]
      _ = ((t • (1 : Matrix n n ℝ) - X) * E) * E := (Matrix.mul_assoc _ _ _).symm
      _ = (E * (t • (1 : Matrix n n ℝ) - X)) * E := by rw [hcomm]
      _ = E * ((t • (1 : Matrix n n ℝ) - X) * E) := Matrix.mul_assoc _ _ _
  have hpsd : ((t * t) • (1 : Matrix n n ℝ) - X * X).PosSemidef := by
    have hherm : ((t * t) • (1 : Matrix n n ℝ) - X * X).IsHermitian := by
      refine Matrix.IsHermitian.sub ?_ ?_
      · simp [Matrix.IsHermitian]
      · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hX]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
    have hnn := hC.dotProduct_mulVec_nonneg (E *ᵥ x)
    simp only [star_trivial] at hnn
    rw [hprod, ← Matrix.mulVec_mulVec, dotProduct_mulVec_symm hEsymm,
      ← Matrix.mulVec_mulVec]
    exact hnn
  have hXX : (X * X).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self X
    rwa [hX] at h
  have hnorm : ‖X * X‖ ≤ t * t :=
    norm_le_of_le_smul_one hXX (mul_nonneg ht ht) (Matrix.le_iff.mpr hpsd)
  have hstar : (star X : Matrix n n ℝ) = X := by
    rw [Matrix.star_eq_conjTranspose, hX]
  have hcs : ‖X‖ * ‖X‖ = ‖X * X‖ := by
    rw [← CStarRing.norm_star_mul_self, hstar]
  by_contra hcon
  push Not at hcon
  have hlt : t * t < ‖X‖ * ‖X‖ :=
    mul_lt_mul' hcon.le hcon ht (lt_of_le_of_lt ht hcon)
  rw [hcs] at hlt
  exact absurd hnorm (not_le.mpr hlt)

/-- **A matrix of spectral norm at most `t` is caught between `∓tI`.** -/
theorem sandwich_of_norm_le {X : Matrix n n ℝ} (hX : Xᴴ = X) {t : ℝ} (h : ‖X‖ ≤ t) :
    X ≤ t • (1 : Matrix n n ℝ) ∧ (-t) • (1 : Matrix n n ℝ) ≤ X := by
  have hxx : ∀ x : n → ℝ, (0 : ℝ) ≤ x ⬝ᵥ x := fun x =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hXherm : X.IsHermitian := hX
  have hone : (t • (1 : Matrix n n ℝ)).IsHermitian := by simp [Matrix.IsHermitian]
  have honeneg : ((-t) • (1 : Matrix n n ℝ)).IsHermitian := by simp [Matrix.IsHermitian]
  constructor
  · refine Matrix.le_iff.mpr
      (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hone.sub hXherm) fun x => ?_)
    have hbound := dotProduct_mulVec_le_norm_mul X x
    have hstep : ‖X‖ * (x ⬝ᵥ x) ≤ t * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right h (hxx x)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
    linarith only [hbound, hstep]
  · refine Matrix.le_iff.mpr
      (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hXherm.sub honeneg) fun x => ?_)
    have hbound := dotProduct_mulVec_le_norm_mul (-X) x
    rw [Matrix.neg_mulVec, dotProduct_neg, norm_neg] at hbound
    have hstep : ‖X‖ * (x ⬝ᵥ x) ≤ t * (x ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_right h (hxx x)
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul]
    simp only [star_trivial, smul_eq_mul]
    linarith only [hbound, hstep]

end Spectral

/-! ## The scalar size is the spectral norm of the normalized block -/

section Blocks

variable {d : ℕ}

/-- The lower Loewner constraint of a scalar size, read on the normalized
block. -/
theorem neg_smul_le_iff_normalize {H F : BlockMat d} (hF : (toFullBlockMat F).PosDef)
    (t : ℝ) :
    (-t) • toFullBlockMat F ≤ toFullBlockMat H ↔
      (-t) • (1 : FullBlockMat d) ≤ toFullBlockMat (normalizedBlock H F) := by
  have hsymm : (matSqrt (toFullBlockMat F)⁻¹)ᴴ = matSqrt (toFullBlockMat F)⁻¹ :=
    conjTranspose_matSqrt_inv hF
  have key := conj_le_conj_iff (A := (-t) • toFullBlockMat F) (B := toFullBlockMat H)
    (isUnit_matSqrt_inv hF)
  rw [hsymm] at key
  have hlhs : matSqrt (toFullBlockMat F)⁻¹ * ((-t) • toFullBlockMat F) *
      matSqrt (toFullBlockMat F)⁻¹ = (-t) • (1 : FullBlockMat d) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, matSqrt_inv_conj hF]
  rw [hlhs] at key
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact key.symm

/-- **The scalar size is the spectral norm of the normalized block.**  On a
symmetric numerator and a positive reference the defining set of `blockSize` is
the closed half-line above `‖F^{-1/2}HF^{-1/2}‖`. -/
theorem blockSize_eq_norm {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) :
    blockSize H F = ‖toFullBlockMat (normalizedBlock H F)‖ := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hXsymm : (toFullBlockMat (normalizedBlock H F))ᴴ =
      toFullBlockMat (normalizedBlock H F) := by
    rw [conjTranspose_eq_transpose']
    exact isSymm_toFullBlockMat (isSymmetricBlockMat_normalizedBlock (F := F) hH)
  have hset : {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale t F) ∧
      BlockMatLoewnerLE (blockScale (-t) F) H} =
        Set.Ici ‖toFullBlockMat (normalizedBlock H F)‖ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Ici]
    constructor
    · rintro ⟨ht, hup, hlo⟩
      have hup' := (blockMatLoewnerLE_iff_le hH (isSymmetricBlockMat_blockScale t hF)).mp hup
      rw [toFullBlockMat_blockScale] at hup'
      have hlo' :=
        (blockMatLoewnerLE_iff_le (isSymmetricBlockMat_blockScale (-t) hF) hH).mp hlo
      rw [toFullBlockMat_blockScale] at hlo'
      refine norm_le_of_sandwich hXsymm ht ?_ ((neg_smul_le_iff_normalize hFfull t).mp hlo')
      rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
      exact (conj_normalize hFfull t).mp hup'
    · intro hle
      have ht : 0 ≤ t := le_trans (norm_nonneg _) hle
      obtain ⟨h1, h2⟩ := sandwich_of_norm_le hXsymm hle
      rw [normalizedBlock, toFullBlockMat_ofFullBlockMat] at h1
      refine ⟨ht, blockMatLoewnerLE_of_le ?_, blockMatLoewnerLE_of_le ?_⟩
      · rw [toFullBlockMat_blockScale]
        exact (conj_normalize hFfull t).mpr h1
      · rw [toFullBlockMat_blockScale]
        exact (neg_smul_le_iff_normalize hFfull t).mpr h2
  rw [blockSize, hset]
  exact csInf_Ici

/-- The scalar size is nonnegative. -/
theorem blockSize_nonneg {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) :
    0 ≤ blockSize H F := by
  rw [blockSize_eq_norm hH hF hFpd]
  exact norm_nonneg _

/-- **The scalar size realizes its own bound.** -/
theorem blockSize_sandwich {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) :
    toFullBlockMat H ≤ blockSize H F • toFullBlockMat F ∧
      (-(blockSize H F)) • toFullBlockMat F ≤ toFullBlockMat H := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hXsymm : (toFullBlockMat (normalizedBlock H F))ᴴ =
      toFullBlockMat (normalizedBlock H F) := by
    rw [conjTranspose_eq_transpose']
    exact isSymm_toFullBlockMat (isSymmetricBlockMat_normalizedBlock (F := F) hH)
  obtain ⟨h1, h2⟩ := sandwich_of_norm_le hXsymm (le_of_eq (blockSize_eq_norm hH hF hFpd).symm)
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat] at h1
  exact ⟨(conj_normalize hFfull _).mpr h1,
    (neg_smul_le_iff_normalize hFfull _).mpr h2⟩

/-- A nonnegative two-sided Loewner bound dominates the scalar size. -/
theorem blockSize_le_of_sandwich {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {t : ℝ} (ht : 0 ≤ t)
    (hup : toFullBlockMat H ≤ t • toFullBlockMat F)
    (hlo : (-t) • toFullBlockMat F ≤ toFullBlockMat H) :
    blockSize H F ≤ t := by
  have hFfull : (toFullBlockMat F).PosDef := posDef_toFullBlockMat hF hFpd
  have hXsymm : (toFullBlockMat (normalizedBlock H F))ᴴ =
      toFullBlockMat (normalizedBlock H F) := by
    rw [conjTranspose_eq_transpose']
    exact isSymm_toFullBlockMat (isSymmetricBlockMat_normalizedBlock (F := F) hH)
  rw [blockSize_eq_norm hH hF hFpd]
  refine norm_le_of_sandwich hXsymm ht ?_ ((neg_smul_le_iff_normalize hFfull t).mp hlo)
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact (conj_normalize hFfull t).mp hup

/-- **Changing the reference block costs its relative size.**  This is the step
of `p.fixed.geometry.one.grid.propagation` that replaces the normalization `E_b^q` of the
centered maximum by `E_T^q`. -/
theorem blockSize_le_mul_blockSize {H Fb Ft : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hFb : IsSymmetricBlockMat Fb) (hFbpd : Book.Ch02.BlockPosDef Fb)
    (hFt : IsSymmetricBlockMat Ft) (hFtpd : Book.Ch02.BlockPosDef Ft) {lam : ℝ}
    (hlam : 0 ≤ lam) (hle : toFullBlockMat Fb ≤ lam • toFullBlockMat Ft) :
    blockSize H Ft ≤ lam * blockSize H Fb := by
  obtain ⟨hup, hlo⟩ := blockSize_sandwich hH hFb hFbpd
  have hs : 0 ≤ blockSize H Fb := blockSize_nonneg hH hFb hFbpd
  have hstep : blockSize H Fb • toFullBlockMat Fb ≤
      (lam * blockSize H Fb) • toFullBlockMat Ft := by
    have h := smul_le_smul_of_le hs hle
    rwa [smul_smul, mul_comm (blockSize H Fb) lam] at h
  refine blockSize_le_of_sandwich hH hFt hFtpd (mul_nonneg hlam hs)
    (le_trans hup hstep) ?_
  refine le_trans ?_ hlo
  have hneg := neg_le_neg hstep
  rwa [← neg_smul, ← neg_smul] at hneg

/-- **The scalar size is dominated by the Schatten size of the same pair.**  The
centered maximum of `e.scale.selection.fluctuation.history` is therefore controlled by
the centered moments `v_j^q`. -/
theorem blockSize_le_schattenSize {H F : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F) {Q : ℝ} (hQ : 0 < Q) :
    blockSize H F ≤ schattenSize Q H F := by
  have hXsym : IsSymmetricBlockMat (normalizedBlock H F) :=
    isSymmetricBlockMat_normalizedBlock (F := F) hH
  have hXsymm : (toFullBlockMat (normalizedBlock H F))ᴴ =
      toFullBlockMat (normalizedBlock H F) := by
    rw [conjTranspose_eq_transpose']
    exact isSymm_toFullBlockMat hXsym
  obtain ⟨hsub, hadd⟩ := Recurrence.posSemidef_schattenNorm_smul_one_sub_add hXsym hQ
  rw [blockSize_eq_norm hH hF hFpd, schattenSize]
  refine norm_le_of_sandwich hXsymm (Recurrence.zero_le_schattenNorm hXsym Q)
    (Matrix.le_iff.mpr hsub) (Matrix.le_iff.mpr ?_)
  have hrw : toFullBlockMat (normalizedBlock H F) -
      (-(schattenNorm Q (normalizedBlock H F))) • (1 : FullBlockMat d) =
      schattenNorm Q (normalizedBlock H F) • (1 : FullBlockMat d) +
        toFullBlockMat (normalizedBlock H F) := by
    rw [neg_smul, sub_neg_eq_add, add_comm]
  rw [hrw]
  exact hadd

/-! ## The scalar size of a centered response is a measurable statistic -/

/-- **The centered scalar size is measurable.**  Its value is the spectral norm
of a fixed continuous function of the entries of the response, so the
measurability of the variational coarse block is all it needs. -/
theorem aemeasurable_blockSize_coarseBlock_sub {P : Measure (CoeffSpace d)}
    {U : Set (Vec d)} (hmeas : HasMeasurableCoarseBlock P U) {E F : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    AEMeasurable (fun a => blockSize (blockSub (coarseBlock U a) E) F) P := by
  have hrw : (fun a => blockSize (blockSub (coarseBlock U a) E) F) =
      fun a => ‖(Matrix.of fun α β =>
        toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β :
          FullBlockMat d)‖ := by
    funext a
    exact blockSize_eq_norm
      (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock U a) hE) hF hFpd
  rw [hrw]
  have hpi : AEMeasurable (fun a => fun α β =>
      toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β) P :=
    aemeasurable_pi_iff.mpr fun α => aemeasurable_pi_iff.mpr fun β =>
      (Recurrence.aestronglyMeasurable_toFullBlockMat_normalizedBlock_blockSub
        hmeas E F α β).aemeasurable
  have hcont : Measurable (fun e : BlockCoord d → BlockCoord d → ℝ =>
      ‖(Matrix.of e : FullBlockMat d)‖) :=
    Continuous.measurable (continuous_norm.comp (continuous_matrix fun α β =>
      (continuous_apply β).comp (continuous_apply α)))
  exact hcont.comp_aemeasurable hpi

end Blocks

end

end PortableHistory
end HighContrast
end HCPolySupport
