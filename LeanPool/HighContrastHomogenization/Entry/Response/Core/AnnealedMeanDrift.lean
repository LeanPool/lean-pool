/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SourceLoadBound

/-!
# High-contrast homogenization: Entry.Response.Core.AnnealedMeanDrift

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed mean under drift

This file compares the annealed block mean of the recentred coefficients with the adapted mean,
bounding the drift between them, and shows the annealed block of `respCoeffMinus` (respectively
`respCoeffPlus`) agrees with the adapted block once evaluated on the adapted cell. It proves the
monotonicity of the block congruence and of the block scaling under the Loewner order, the positive
definiteness and symmetry of the block mean `respM0`, the scalewise bound on the response source
load from a Loewner hypothesis, and the two-regime evaluation of a tail sum split at the cutoff
between recent and older scales. It serves `p.response.transfer`.
-/

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock aspectRatio blockScale blockSub blockTrace coarseBlock matSqrt
  matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-- **The general-cell annealed shear identity, minus sign**
(`p.response.transfer` at an arbitrary adapted cell):
`E[A(V; a - g)] = G^t E[A(V; a)] G`.  At `V = respCell jStar F t` the right-hand side is
`respEhatMinus P jStar F t`; the point of this form is that it holds at *every* subcell
`adaptedCellAtCenter (respGrid jStar F) k z`, which is what `respSourceLoad` sums over. -/
theorem annealedBlockOf_respCoeffMinus_adapted [NeZero d]
    {P : Measure (CoeffSpace d)} (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (F : BlockMat d) (hF : (toFullBlockMat F).PosDef)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate q j y)) :
    annealedBlockOf P (HighContrast.adaptedCellTranslate q j y) (respCoeffMinus F) =
      blockCongr (respG F) (annealedBlock P (HighContrast.adaptedCellTranslate q j y)) := by
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  refine annealedBlockOf_eq_blockCongr _ _ hint fun a => ?_
  exact coarseBlockMatrix_sub_skew_eq_blockCongr hgskew
    (hasQuadraticMu_adaptedCellTranslate q hq j y a)

/-- **The general-cell annealed shear identity, plus sign**
(`p.response.transfer`): `E[A(V; a^t + g)] = D G^t E[A(V; a)] G D`.  At
`V = respCell jStar F t` the right-hand side is `respEhatPlus P jStar F t`. -/
theorem annealedBlockOf_respCoeffPlus_adapted [NeZero d]
    {P : Measure (CoeffSpace d)} (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (F : BlockMat d) (hF : (toFullBlockMat F).PosDef)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate q j y)) :
    annealedBlockOf P (HighContrast.adaptedCellTranslate q j y) (respCoeffPlus F) =
      blockAdjoint
        (blockCongr (respG F) (annealedBlock P (HighContrast.adaptedCellTranslate q j y))) := by
  set V := HighContrast.adaptedCellTranslate q j y with hV
  have hgskew : matTranspose (respg F) = -(respg F) := respCalib_respg_isSkew hF
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := matTranspose_neg_of_skew hgskew
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix V (respCoeffPlus F a)
        = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
            toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d))) (coarseBlock V a) := by
    intro a
    have hquad := hasQuadraticMu_adaptedCellTranslate q hq j y a
    have h1 : respCoeffPlus F a
        = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
      funext x
      simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
    have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := V)
      (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
      (hasQuadraticMu_adjointCoeffField hquad)
    have h3 : coarseBlockMatrix V (adjointCoeffField (⇑a.1 : CoeffField d))
        = blockCongr (blockD d) (coarseBlock V a) := by
      rw [coarseBlockMatrix_adjointCoeffField_of_exists
        (exists_coarseBlockMatrix_of_hasQuadraticMu hquad), ← blockCongr_blockD]
      rfl
    rw [h1, h2, h3, blockCongr_blockCongr]
  rw [annealedBlockOf_eq_blockCongr _ (respCoeffPlus F) hint hb, blockAdjoint,
    blockCongr_blockCongr]
  exact congrArg (fun G => blockCongr G (annealedBlock P V))
    (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))

/-! ### Round 1c: the `k ≥ j_*` branch — the determinant-drift Loewner comparison. -/

/-- Trace form of `mean_part_le_determinantDrift`
(`HCPoly/Entry/Response/Core/EnergyDefectBound.lean`): the same telescoping,
stopping one step earlier, so that the conclusion is a *Loewner* envelope rather than the
infimum `blockSpecBound` (`HCPoly/Entry/Response/Core/ResponseBlockObjects.lean`).
(`p.response.transfer`.) -/
private theorem mean_trace_le_determinantDrift (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) *
        blockTrace (blockSub (relMean P (Geometry.explicitRoundedGrid jStar mt) k t)
          (Book.Ch02.blockIdentity d))
      ≤ determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t := by
  set q := Geometry.explicitRoundedGrid jStar mt with hqdef
  have hpd : ∀ j : ℤ, (toFullBlockMat (adaptedMean P q j)).PosDef := fun j =>
    Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm j
  have hgap : ∀ i j : ℤ, (jStar : ℤ) ≤ i → i ≤ j →
      (toFullBlockMat (blockSub (relMean P q i t)
        (relMean P q j t))).PosSemidef := by
    intro i j hi hij
    simpa only [relMean] using
      normalizedBlock_gap_posSemidef (adaptedMean P q i) (adaptedMean P q j)
        (adaptedMean P q t) (hpd t) (hpd i).isHermitian (hpd j).isHermitian
        (Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm i j
          hi hij)
  set T : ℤ → ℝ := fun j =>
    blockTrace (blockSub (relMean P q (j - 1) t) (relMean P q j t)) with hTdef
  have hT0 : ∀ j : ℤ, (jStar : ℤ) + 1 ≤ j → 0 ≤ T j := by
    intro j hj
    exact Analysis.blockTrace_nonneg (hgap (j - 1) j (by omega) (by omega))
  have hI : relMean P q t t = Book.Ch02.blockIdentity d :=
    Annealed.normalizedMean_self d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm t
  have hstep1 : blockTrace (blockSub (relMean P q k t) (Book.Ch02.blockIdentity d))
      = ∑ j ∈ Finset.Icc (k + 1) t, T j := by
    have hsum : ∑ j ∈ Finset.Icc (k + 1) t, T j =
        ∑ j ∈ Finset.Icc (k + 1) t,
          (blockTrace (relMean P q (j - 1) t) - blockTrace (relMean P q j t)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hTdef, blockTrace_blockSub]
    rw [hsum, telescope_Icc (fun j => blockTrace (relMean P q j t)) k t hkt,
      ← hI, blockTrace_blockSub]
  have hrho : (1 : ℝ) / 2 ≤ Quenched.contrastRho γ := by
    unfold Quenched.contrastRho; linarith only [hγ.1]
  have hw : ∀ j ∈ Finset.Icc (k + 1) t,
      (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) ≤
        (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h1 : (j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hj.2
    have h2 : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hu : (0 : ℝ) ≤ (t : ℝ) - (j : ℝ) := by linarith only [h1]
    have hv : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by linarith only [h1, h2]
    have s1 : ((1 - γ) / 8) * ((t : ℝ) - (j : ℝ)) ≤ (1 / 8 : ℝ) * ((t : ℝ) - (j : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hγ.1]) hu
    have s2 : (1 / 8 : ℝ) * ((t : ℝ) - (j : ℝ)) ≤ (1 / 8 : ℝ) * ((t : ℝ) - (k : ℝ)) := by
      linarith only [h2]
    have s3 : (1 / 8 : ℝ) * ((t : ℝ) - (k : ℝ)) ≤ Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hrho]) hv
    linarith only [s1, s2, s3]
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) *
        blockTrace (blockSub (relMean P q k t) (Book.Ch02.blockIdentity d))
        = (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) * ∑ j ∈ Finset.Icc (k + 1)
          t, T j := by
      rw [hstep1]
    _ = ∑ j ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ)))) * T j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) * T j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm := Finset.mem_Icc.mp hj
      exact mul_le_mul_of_nonneg_right (hw j hj) (hT0 j (by omega))
    _ ≤ ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) t,
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((t : ℝ) - (j : ℝ))) * T j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        omega
      · intro j hj _
        have hjm := Finset.mem_Icc.mp hj
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hT0 j (by omega))
    _ = determinantDrift P γ q jStar t := rfl

/-- Undoing the normalization: `R^{-1/2} A R^{-1/2} ≤ c I` gives `A ≤ c R`.  Congruence by
`(R^{-1/2})⁻¹`, exactly as in the closing step of `le_detRatio_smul_of_le`
(`HCPoly/Entry/Response/Core/SkewShearCongruence.lean`). -/
private theorem le_smul_of_normalizedBlock_le_of_posDef {A R : BlockMat d} {c : ℝ}
    (hR : (toFullBlockMat R).PosDef)
    (h : toFullBlockMat (normalizedBlock A R) ≤ c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)) :
    toFullBlockMat A ≤ c • toFullBlockMat R := by
  set Rf := toFullBlockMat R with hRf
  have hSpd : (matSqrt Rf⁻¹).PosDef := matSqrt_inv_posDef_full hR
  have hSt : (matSqrt Rf⁻¹)ᵀ = matSqrt Rf⁻¹ := transpose_eq_of_psd hSpd.posSemidef
  have hSS : matSqrt Rf⁻¹ * matSqrt Rf⁻¹ = Rf⁻¹ := (matSqrt_spec hR.inv.posSemidef).2
  have hSu : IsUnit (matSqrt Rf⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hSpd.isUnit
  have hRu : IsUnit Rf.det := (Matrix.isUnit_iff_isUnit_det Rf).mp hR.isUnit
  have hiS : (matSqrt Rf⁻¹)⁻¹ * matSqrt Rf⁻¹ = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSi : matSqrt Rf⁻¹ * (matSqrt Rf⁻¹)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hSu
  have hii : (matSqrt Rf⁻¹)⁻¹ * (matSqrt Rf⁻¹)⁻¹ = Rf := by
    rw [← Matrix.mul_inv_rev, hSS, Matrix.nonsing_inv_nonsing_inv Rf hRu]
  have hSit : ((matSqrt Rf⁻¹)⁻¹)ᵀ = (matSqrt Rf⁻¹)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hSt]
  have hcongr := Analysis.matrix_congr_le h (matSqrt Rf⁻¹)⁻¹
  rw [hSit] at hcongr
  have hleft : (matSqrt Rf⁻¹)⁻¹ * toFullBlockMat (normalizedBlock A R) * (matSqrt Rf⁻¹)⁻¹
      = toFullBlockMat A := by
    have hN : toFullBlockMat (normalizedBlock A R)
        = matSqrt Rf⁻¹ * toFullBlockMat A * matSqrt Rf⁻¹ := by
      simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, hRf]
    rw [hN]
    calc (matSqrt Rf⁻¹)⁻¹ * (matSqrt Rf⁻¹ * toFullBlockMat A * matSqrt Rf⁻¹) * (matSqrt Rf⁻¹)⁻¹
        = ((matSqrt Rf⁻¹)⁻¹ * matSqrt Rf⁻¹) * toFullBlockMat A *
            (matSqrt Rf⁻¹ * (matSqrt Rf⁻¹)⁻¹) := by simp only [mul_assoc]
      _ = toFullBlockMat A := by rw [hiS, hSi, one_mul, mul_one]
  rw [hleft] at hcongr
  simpa only [Matrix.mul_smul, Matrix.smul_mul, mul_one, hii] using hcongr

private theorem toFullBlockMat_blockScale (c : ℝ) (A : BlockMat d) :
    toFullBlockMat (blockScale c A) = c • toFullBlockMat A := by
  ext (i | i) (j | j) <;> rfl

private theorem hermitian_smul_one (c : ℝ) :
    (c • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)).IsHermitian := by
  simp [Matrix.IsHermitian]

private theorem hermitian_smul {M : Matrix (BlockCoord d) (BlockCoord d) ℝ}
    (hM : M.IsHermitian) (c : ℝ) : (c • M).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hM.eq]
  simp

private theorem blockIdentity_posDef :
    Book.Ch02.BlockPosDef (Book.Ch02.blockIdentity d) := by
  intro X hX
  have hne : toFullBlockVec X ≠ 0 := by
    intro hfull
    apply hX
    rw [← ofFullBlockVec_toFullBlockVec X, hfull]
    rfl
  have hq : blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X)
      = toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockMat_blockIdentity, Matrix.one_mulVec]
  rw [hq]
  have h0 : 0 ≤ toFullBlockVec X ⬝ᵥ toFullBlockVec X :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine lt_of_le_of_ne h0 fun h => hne ?_
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (toFullBlockVec X i))).mp h.symm
  funext i
  have := hz i (Finset.mem_univ i)
  simpa using mul_self_eq_zero.mp this

/-- **The `k ≥ j_*` Loewner comparison** (`p.response.transfer`): for `j_* ≤ k ≤ t` the
generation-`k` annealed block is dominated by `(1 + 3^{ρ(t-k)} D_{q,j_*}(t)) E_t`.  This is the
"telescope the mean increments and use `3/2 > (1-γ)/8`" step, in Loewner form. -/
theorem adaptedMean_le_of_drift (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hm : mt.PosDef)
    (k t : ℤ) (hk : (jStar : ℤ) ≤ k) (hkt : k ≤ t) :
    BlockMatLoewnerLE (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) k)
      (blockScale (1 + (3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))) *
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar mt) jStar t)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar mt) t)) := by
  set q := Geometry.explicitRoundedGrid jStar mt with hqdef
  have hpd : ∀ j : ℤ, (toFullBlockMat (adaptedMean P q j)).PosDef := fun j =>
    Annealed.adaptedMean_posDef d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm j
  have hI : relMean P q t t = Book.Ch02.blockIdentity d :=
    Annealed.normalizedMean_self d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm t
  set G : BlockMat d := blockSub (relMean P q k t) (Book.Ch02.blockIdentity d) with hG
  have hgapPSD : (toFullBlockMat G).PosSemidef := by
    rw [hG, ← hI]
    simpa only [relMean] using
      normalizedBlock_gap_posSemidef (adaptedMean P q k) (adaptedMean P q t)
        (adaptedMean P q t) (hpd t) (hpd k).isHermitian (hpd t).isHermitian
        (Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hdag jStar hjStar mt hm k t
          hk hkt)
  set Tr : ℝ := blockTrace G with hTrdef
  have hTr0 : 0 ≤ Tr := Analysis.blockTrace_nonneg hgapPSD
  have hopLe : blockOpNorm G ≤ Tr :=
    (Analysis.blockOpNorm_le_absSchattenNorm hgapPSD.isHermitian le_rfl).trans
      (Analysis.absSchattenNorm_le_blockTrace hgapPSD le_rfl)
  have hblk : BlockMatLoewnerLE G (blockScale Tr (Book.Ch02.blockIdentity d)) := fun X =>
    (loewner_le_blockOpNorm_of_posSemidef G hgapPSD X).trans
      (Source.blockScale_le_blockScale_of_pos blockIdentity_posDef hopLe X)
  have hfull : toFullBlockMat G ≤ Tr • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) := by
    have h := (Annealed.fullBlock_le_iff hgapPSD.isHermitian
      (by rw [toFullBlockMat_blockScale_identity]
          exact hermitian_smul_one _)).2 hblk
    rwa [toFullBlockMat_blockScale_identity] at h
  have hnorm : toFullBlockMat (relMean P q k t)
      ≤ (1 + Tr) • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) := by
    have hsub : toFullBlockMat G
        = toFullBlockMat (relMean P q k t)
          - (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) := by
      rw [hG, Recurrence.toFullBlockMat_blockSub, toFullBlockMat_blockIdentity]
    refine Matrix.le_iff.mpr ?_
    have heq : (1 + Tr) • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ)
        - toFullBlockMat (relMean P q k t)
        = Tr • (1 : Matrix (BlockCoord d) (BlockCoord d) ℝ) - toFullBlockMat G := by
      rw [hsub, add_smul, one_smul]
      abel
    rw [heq]
    exact Matrix.le_iff.mp hfull
  have hres : toFullBlockMat (adaptedMean P q k)
      ≤ (1 + Tr) • toFullBlockMat (adaptedMean P q t) :=
    le_smul_of_normalizedBlock_le_of_posDef (hpd t) hnorm
  have hstep : BlockMatLoewnerLE (adaptedMean P q k)
      (blockScale (1 + Tr) (adaptedMean P q t)) := by
    refine (Annealed.fullBlock_le_iff (hpd k).isHermitian ?_).1 ?_
    · rw [toFullBlockMat_blockScale]; exact hermitian_smul (hpd t).isHermitian _
    · rwa [toFullBlockMat_blockScale]
  have hdrift : Tr ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))) *
      determinantDrift P γ q jStar t := by
    have h := mean_trace_le_determinantDrift d hd γ hγ P E Ψ K Src hstat hdag jStar hjStar
      mt hm k t hk hkt
    have hpow : (0 : ℝ) < (3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hinv : (3 : ℝ) ^ (-(Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))))
        = ((3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))))⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]
    rw [hinv] at h
    rw [← hTrdef] at h
    calc Tr = (3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))) *
          (((3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))))⁻¹ * Tr) := by
          field_simp
      _ ≤ (3 : ℝ) ^ (Quenched.contrastRho γ * ((t : ℝ) - (k : ℝ))) * determinantDrift P γ q
        jStar t :=
          mul_le_mul_of_nonneg_left h hpow.le
  exact fun X => (hstep X).trans
    (Source.blockScale_le_blockScale_of_pos (blockPosDef_of_full (hpd t))
      (by linarith only [hdrift]) X)

/-! ### Round 1c: the two-regime geometric summation of `L_s`. -/

/-- The printed split of `L_s` at `k = j_*` (`p.response.transfer`): a family that
is geometric with ratio `r₁` below the crossover `N` and geometric with ratio `r₂` in the
excess `n - N` above it is summable, with the two regimes contributing separately. -/
theorem tsum_two_regime {u : ℕ → ℝ} {N : ℕ} {a b r₁ r₂ : ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr₁0 : 0 ≤ r₁) (hr₁ : r₁ < 1) (hr₂0 : 0 < r₂) (hr₂ : r₂ < 1)
    (h1 : ∀ n : ℕ, n ≤ N → u n ≤ a * r₁ ^ n)
    (h2 : ∀ n : ℕ, N < n → u n ≤ b * r₂ ^ (n - N)) :
    Summable u ∧ ∑' n, u n ≤ a * (1 - r₁)⁻¹ + b * (1 - r₂)⁻¹ := by
  have hgeo₁ : Summable fun n : ℕ => a * r₁ ^ n :=
    (summable_geometric_of_lt_one hr₁0 hr₁).mul_left a
  have hgeo₂ : Summable fun n : ℕ => (b * (r₂ ^ N)⁻¹) * r₂ ^ n :=
    (summable_geometric_of_lt_one hr₂0.le hr₂).mul_left _
  have hv : ∀ n, u n ≤ a * r₁ ^ n + (b * (r₂ ^ N)⁻¹) * r₂ ^ n := by
    intro n
    rcases le_or_gt n N with h | h
    · have h0 : 0 ≤ (b * (r₂ ^ N)⁻¹) * r₂ ^ n := by positivity
      linarith only [h0, h1 n h]
    · have heq : b * r₂ ^ (n - N) = (b * (r₂ ^ N)⁻¹) * r₂ ^ n := by
        rw [pow_sub₀ _ (ne_of_gt hr₂0) h.le]
        field_simp
      have h0 : 0 ≤ a * r₁ ^ n := by positivity
      have := h2 n h
      rw [heq] at this
      linarith only [h0, this]
  have hsum : Summable u := (hgeo₁.add hgeo₂).of_nonneg_of_le hu0 hv
  refine ⟨hsum, ?_⟩
  have hsplit := hsum.sum_add_tsum_nat_add (N + 1)
  have hA : ∑ i ∈ Finset.range (N + 1), u i ≤ a * (1 - r₁)⁻¹ := by
    calc ∑ i ∈ Finset.range (N + 1), u i
        ≤ ∑ i ∈ Finset.range (N + 1), a * r₁ ^ i := by
          refine Finset.sum_le_sum fun i hi => h1 i ?_
          have := Finset.mem_range.mp hi
          omega
      _ ≤ ∑' i : ℕ, a * r₁ ^ i :=
          hgeo₁.sum_le_tsum _ (fun i _ => by positivity)
      _ = a * (1 - r₁)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr₁0 hr₁]
  have hsum' : Summable fun i : ℕ => u (i + (N + 1)) := (summable_nat_add_iff (N + 1)).mpr hsum
  have hgeo₃ : Summable fun i : ℕ => b * r₂ ^ (i + 1) := by
    have : (fun i : ℕ => b * r₂ ^ (i + 1)) = fun i : ℕ => (b * r₂) * r₂ ^ i := by
      funext i; rw [pow_succ]; ring
    rw [this]
    exact (summable_geometric_of_lt_one hr₂0.le hr₂).mul_left _
  have hB : ∑' i : ℕ, u (i + (N + 1)) ≤ b * (1 - r₂)⁻¹ := by
    calc ∑' i : ℕ, u (i + (N + 1))
        ≤ ∑' i : ℕ, b * r₂ ^ (i + 1) := by
          refine hsum'.tsum_le_tsum (fun i => ?_) hgeo₃
          have hi := h2 (i + (N + 1)) (by omega)
          have he : i + (N + 1) - N = i + 1 := by omega
          rwa [he] at hi
      _ = b * r₂ * (1 - r₂)⁻¹ := by
          have : (fun i : ℕ => b * r₂ ^ (i + 1)) = fun i : ℕ => (b * r₂) * r₂ ^ i := by
            funext i; rw [pow_succ]; ring
          rw [this, tsum_mul_left, tsum_geometric_of_lt_one hr₂0.le hr₂]
      _ ≤ b * (1 - r₂)⁻¹ := by
          have hinv : 0 < (1 - r₂)⁻¹ := by
            have h1r : 0 < 1 - r₂ := by linarith only [hr₂]
            positivity
          have hbr : b * r₂ ≤ b := by
            have hle : r₂ ≤ 1 := by linarith only [hr₂]
            calc b * r₂ ≤ b * 1 := mul_le_mul_of_nonneg_left hle hb
              _ = b := mul_one b
          exact mul_le_mul_of_nonneg_right hbr hinv.le
  rw [← hsplit]
  linarith only [hA, hB]

/-! ### Round 1c: the `k < j_*` branch — the annealed source estimate in the `E_s` scale. -/

theorem blockScale_mono_of_loewnerLE {A B : BlockMat d} (h : BlockMatLoewnerLE A B) {c : ℝ}
    (hc : 0 ≤ c) : BlockMatLoewnerLE (blockScale c A) (blockScale c B) := by
  intro X
  rw [Source.quadratic_blockScale, Source.quadratic_blockScale]
  exact mul_le_mul_of_nonneg_left (h X) hc

theorem blockScale_blockScale (c c' : ℝ) (A : BlockMat d) :
    blockScale c (blockScale c' A) = blockScale (c * c') A := by
  simp only [blockScale, smul_smul]

private theorem adaptedCellAtCenter_zero_eq_adaptedCell (q : Mat d) (j : ℤ) :
    adaptedCellAtCenter q j 0 = HighContrast.adaptedCell q j := by
  have hc : adaptedCellCenter q j (0 : Fin d → ℤ) = 0 := by
    have h0 : (fun i => (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
      funext i; simp
    rw [adaptedCellCenter, h0]
    change (3 : ℝ) ^ j • Matrix.mulVec q (0 : Vec d) = 0
    rw [Matrix.mulVec_zero, smul_zero]
  rw [adaptedCellAtCenter, hc, HighContrast.adaptedCellTranslate]
  ext x
  simp

private theorem zero_mem_triadicIndexBox_of_nat (n : ℕ) :
    (0 : Fin d → ℤ) ∈ triadicIndexBox d n := by
  simp only [triadicIndexBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]
  intro i
  exact ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩

/-- Adapted cells are nested in the generation (`p.response.transfer`). -/
theorem adaptedCell_subset (q : Mat d) {j s : ℤ} (h : j ≤ s) :
    HighContrast.adaptedCell q j ⊆ HighContrast.adaptedCell q s := by
  have hn : s - ((s - j).toNat : ℤ) = j := by omega
  have := adaptedCellAtCenter_subset_adaptedCell q s (s - j).toNat
    (zero_mem_triadicIndexBox_of_nat (d := d) (s - j).toNat)
  rwa [hn, adaptedCellAtCenter_zero_eq_adaptedCell] at this

/-- **The `k < j_*` per-cell bound** (`p.response.transfer`): the annealed block of any
aligned adapted cell is dominated by `C Π e(m)^2 3^{γ(j_*-k)_+} E_s`.  This is the printed
"the source estimate... bound the remaining sum by `C E_s`", before the summation: the source
estimate `Adapter.aligned_source_bound` lands on the reference block `E`, and the reference
normalization `Annealed.adaptedMean_refBlock_normalization` converts `E` into `E_s` at the
cost `Π e(m)`, which is exactly the factor the second inequality of
`e.response.source.smallness` is designed to absorb. -/
theorem annealedBlock_le_adaptedMean (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc C : ℝ, 0 < Csrc ∧ 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
        (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ Kg Src →
        ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) →
          ∀ (m : Mat d), m.PosDef → ∀ s : ℤ, (jStar : ℤ) ≤ s →
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) s ⊆
              HighContrast.centeredCube d (2 * (jStar : ℤ)) →
            ∀ (k : ℤ) (z : Fin d → ℤ),
              BlockMatLoewnerLE
                (annealedBlock P (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) k z))
                (blockScale (C * aspectRatio E * (‖m‖ * ‖m⁻¹‖) *
                    (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0))
                  (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc₁, C₁, hCsrc₁, hC₁, hsrc⟩ := Adapter.aligned_source_bound d hd γ hγ
  obtain ⟨Csrc₂, C₂, hCsrc₂, hC₂, hnorm⟩ := Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨max Csrc₁ Csrc₂, C₁ * C₂, lt_of_lt_of_le hCsrc₁ (le_max_left _ _),
    mul_pos hC₁ hC₂, ?_⟩
  intro P hP E Ψ Kg Src hstat hdag jStar hj hthr m hm s hjs hwin k z
  have : IsProbabilityMeasure P := hP
  have hKg : (1 : ℝ) < Kg := hdag.one_lt_growthWitness
  have hlog : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) := by
    refine Real.logb_nonneg (by norm_num) ?_
    linarith only [hKg]
  have hthr₁ : ⌈Csrc₁ * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) :=
    le_trans (Int.ceil_le_ceil
      (mul_le_mul_of_nonneg_right (le_max_left Csrc₁ Csrc₂) hlog)) hthr
  have hthr₂ : ⌈Csrc₂ * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) :=
    le_trans (Int.ceil_le_ceil
      (mul_le_mul_of_nonneg_right (le_max_right Csrc₁ Csrc₂) hlog)) hthr
  have hwinJ : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (jStar : ℤ) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) :=
    subset_trans (adaptedCell_subset (Geometry.explicitRoundedGrid jStar m) hjs) hwin
  have h1 := hsrc P E Ψ Kg Src hstat hdag jStar hj hthr₁ m hm hwinJ k z
  have h2 := (hnorm P E Ψ Kg Src hstat hdag jStar hj hthr₂ m hm s hjs hwin).2
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hstep : BlockMatLoewnerLE
      (annealedBlock P (adaptedCellAtCenter (Geometry.explicitRoundedGrid jStar m) k z))
      (blockScale ((C₁ * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) *
        (C₂ * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖)))
        (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s)) := by
    refine fun X => (h1 X).trans ?_
    have := blockScale_mono_of_loewnerLE h2
      (c := C₁ * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0))
      (by positivity)
    rw [blockScale_blockScale] at this
    exact this X
  refine fun X => (hstep X).trans ?_
  have hpos : Book.Ch02.BlockPosDef (adaptedMean P (Geometry.explicitRoundedGrid jStar m) s) :=
    blockPosDef_of_full
      (Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj m hm s)
  refine Source.blockScale_le_blockScale_of_pos hpos ?_ X
  have hecc : (1 : ℝ) ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) := Source.one_le_source_eccentricity hm
  have hecc2 : Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ ‖m‖ * ‖m⁻¹‖ := by
    calc Real.sqrt (‖m‖ * ‖m⁻¹‖)
        = Real.sqrt (‖m‖ * ‖m⁻¹‖) * 1 := (mul_one _).symm
      _ ≤ Real.sqrt (‖m‖ * ‖m⁻¹‖) * Real.sqrt (‖m‖ * ‖m⁻¹‖) :=
          mul_le_mul_of_nonneg_left hecc (Real.sqrt_nonneg _)
      _ = Real.sqrt (‖m‖ * ‖m⁻¹‖) ^ 2 := (pow_two _).symm
      _ = ‖m‖ * ‖m⁻¹‖ := Real.sq_sqrt (by positivity : (0:ℝ) ≤ ‖m‖ * ‖m⁻¹‖)
  have hAsp : (1 : ℝ) ≤ aspectRatio E :=
    HCPolySupport.HighContrast.one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hAsp0 : (0 : ℝ) ≤ aspectRatio E := le_trans zero_le_one hAsp
  have hcoef : (0 : ℝ) ≤ C₁ * C₂ * aspectRatio E *
      (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hC₂.le) hAsp0) hpow.le
  have hA : C₁ * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0) *
        (C₂ * aspectRatio E * Real.sqrt (‖m‖ * ‖m⁻¹‖))
      = (C₁ * C₂ * aspectRatio E * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) *
        Real.sqrt (‖m‖ * ‖m⁻¹‖) := by ring
  have hB : C₁ * C₂ * aspectRatio E * (‖m‖ * ‖m⁻¹‖) *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)
      = (C₁ * C₂ * aspectRatio E * (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (k : ℝ)) 0)) *
        (‖m‖ * ‖m⁻¹‖) := by ring
  rw [hA, hB]
  exact mul_le_mul_of_nonneg_left hecc2 hcoef

/-- **Scale-wise form of `h7_respSourceLoad_le_of_loewner`**: the Loewner bound on the annealed
block is allowed to depend on the generation, which is what the printed split at `k = j_*`
(`p.response.transfer`) needs.  It also records the summability of the generation
summands of `L_s`, which the same hypotheses give and without which the `tsum` defining `L_s` is
the junk value of a divergent series. -/
theorem respSourceLoad_le_of_loewner_scalewise (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (c : ℕ → ℝ) (M : ℝ)
    (hc : ∀ n, 0 ≤ c n) (hM : 0 ≤ M) (hm : (explicitCanonicalMetric F).PosDef)
    (hY : blockVecDot Y (blockMatVecMul (respM0 F) Y) ≤ M)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (c n * M)))
    (hres : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      BlockMatLoewnerLE (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ))
        z) b)
        (blockScale (c n) (respM0 F))) :
    Summable (respSourceLoadSummand P jStar F s b Y) ∧
      respSourceLoad P jStar F s b Y ≤
        ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (c n * M)) := by
  have hq1 : 0 ≤ vecDot Y.1 (matVecMul (explicitCanonicalMetric F) Y.1) := by
    have := hm.posSemidef.dotProduct_mulVec_nonneg Y.1
    simpa only [star_trivial] using! this
  have hq2 : 0 ≤ vecDot Y.2 (matVecMul (explicitCanonicalMetric F)⁻¹ Y.2) := by
    have := hm.inv.posSemidef.dotProduct_mulVec_nonneg Y.2
    simpa only [star_trivial] using! this
  rw [respM0_qform_split_canonicalMetric] at hY
  have hbound : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      vecDot Y.1 (matVecMul (annealedBlockOf P
          (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft Y.1) ≤ c n * M ∧
      vecDot Y.2 (matVecMul (annealedBlockOf P
          (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight Y.2) ≤ c n * M
            := by
    intro n z hz
    have h1 := qform_fst (hres n z hz) Y.1
    have h2 := qform_snd (hres n z hz) Y.2
    rw [blockScale_qform_upperLeft] at h1
    rw [blockScale_qform_lowerRight] at h2
    constructor
    · refine h1.trans ?_
      have hle : vecDot Y.1 (matVecMul (respM0 F).upperLeft Y.1) ≤ M := by
        simp only [respM0] at *
        linarith only [hY, hq2]
      exact mul_le_mul_of_nonneg_left hle (hc n)
    · refine h2.trans ?_
      have hle : vecDot Y.2 (matVecMul (respM0 F).lowerRight Y.2) ≤ M := by
        simp only [respM0] at *
        linarith only [hY, hq1]
      exact mul_le_mul_of_nonneg_left hle (hc n)
  exact respSourceLoad_le_scalewise P jStar F s b Y (fun n => c n * M)
    (fun n => mul_nonneg (hc n) hM) hsum hbound

/-- Nonnegativity of the profile at a single generation pair, extracted from the
inline argument (`HCPoly/Entry/OneGridPropagation.lean`). -/
theorem profile_nonneg (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d))
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (mt : Mat d) (hmt : mt.PosDef)
    (n m : ℤ) (hn : (jStar : ℤ) ≤ n) (hnm : n ≤ m) :
    0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar mt) jStar n m := by
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag
    jStar hjStar mt hmt (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar mt) jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hH0 : 0 ≤ history P γ (Geometry.explicitRoundedGrid jStar mt) jStar n := add_nonneg hfluc
    hmean0
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K Src hstat hdag
    jStar hjStar mt hmt n m hn hnm).2.2.2.2.2
  have hw (x : ℝ) : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * x) := Real.rpow_nonneg (by norm_num) _
  unfold profile
  apply add_nonneg
  · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hpen])) hH0)
      (meanHistory_nonneg d hd γ hγ P E Ψ K Src hP hstat hunit hdag
        jStar hjStar mt hmt n m hn hnm)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
      (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)

/-! ### Round 1c: block-congruence algebra and `M_0` positivity for the assembly. -/

private theorem ofFullBlockMat_smul (c : ℝ)
    (M : Matrix (BlockCoord d) (BlockCoord d) ℝ) :
    ofFullBlockMat (c • M) = blockScale c (ofFullBlockMat M) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl

theorem blockCongr_blockScale (G : BlockMat d) (c : ℝ) (A : BlockMat d) :
    blockCongr G (blockScale c A) = blockScale c (blockCongr G A) := by
  rw [blockCongr, blockCongr, toFullBlockMat_blockScale, ← ofFullBlockMat_smul]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem respM0_isSymm_of_canonicalMetric_posDef {F : BlockMat d} (hm : (explicitCanonicalMetric
  F).PosDef) :
    IsSymmetricBlockMat (respM0 F) := by
  intro α β
  have h1 := hm.isHermitian
  have h2 := hm.inv.isHermitian
  cases α with
  | inl i => cases β with
    | inl j =>
        change (explicitCanonicalMetric F) i j = (explicitCanonicalMetric F) j i
        simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
          (congrFun (congrFun h1 i) j).symm
    | inr j => rfl
  | inr i => cases β with
    | inl j => rfl
    | inr j =>
        change (explicitCanonicalMetric F)⁻¹ i j = (explicitCanonicalMetric F)⁻¹ j i
        simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
          (congrFun (congrFun h2 i) j).symm

theorem respM0_blockPosDef_of_canonicalMetric_posDef {F : BlockMat d} (hm :
  (explicitCanonicalMetric F).PosDef) :
    Book.Ch02.BlockPosDef (respM0 F) := by
  intro X hX
  rw [respM0_qform_split_canonicalMetric]
  have h1 : 0 ≤ vecDot X.1 (matVecMul (explicitCanonicalMetric F) X.1) := by
    simpa only [star_trivial] using! hm.posSemidef.dotProduct_mulVec_nonneg X.1
  have h2 : 0 ≤ vecDot X.2 (matVecMul (explicitCanonicalMetric F)⁻¹ X.2) := by
    simpa only [star_trivial] using! hm.inv.posSemidef.dotProduct_mulVec_nonneg X.2
  have hsplit : X.1 ≠ 0 ∨ X.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hX (Prod.ext hcon.1 hcon.2)
  rcases hsplit with h | h
  · have := hm.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    have hv : 0 < vecDot X.1 (matVecMul (explicitCanonicalMetric F) X.1) := this
    linarith only [hv, h2]
  · have := hm.inv.dotProduct_mulVec_pos h
    simp only [star_trivial] at this
    have hv : 0 < vecDot X.2 (matVecMul (explicitCanonicalMetric F)⁻¹ X.2) := this
    linarith only [h1, hv]

theorem pow_eq (u : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (u * (n : ℝ)) = ((3 : ℝ) ^ u) ^ n := by
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]

end HCPolySupport.HighContrast.Multiscale
end
