/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakAverageVariance
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCenteredBound

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastAverageDrops

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The averaged-defect drop bound

The printed weak-norm estimate consumes the subdivision-averaged defect —
the average of the aligned child responses against the parent response —
through its **first** moment.  By the pathwise subadditivity of the aligned
subdivision the averaged defect is positive semidefinite, so its identity
norm is dominated by its trace, whose expectation is exactly the trace of
the normalized annealed mean drop by stationarity.  This yields the
per-depth `L²` bound by the root of the mean drop alone — the sharp
replacement for the crude per-cell variance budget, and the shape the
printed one-step estimate HC (4.17) requires (the drops
enter linearly; no per-cell variance in the rooted sum).
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

private theorem matSqrt_one'' {n : Type*} [Fintype n] [DecidableEq n] :
    matSqrt (1 : Matrix n n ℝ) = 1 :=
  matSqrt_eq Matrix.PosSemidef.one Matrix.PosSemidef.one (by simp)

@[expose]

public def entryCLM' {n : Type*} [Fintype n] [DecidableEq n] (i j : n) :
    Matrix n n ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ i j)

private theorem le_rpow_inv_two_of_sq_le' {a b : ℝ≥0∞}
    (h : a ^ (2 : ℕ) ≤ b) : a ≤ b ^ ((2 : ℝ)⁻¹) := by
  have h1 : (a ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) ≤ b ^ ((2 : ℝ)⁻¹) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  rwa [← ENNReal.rpow_natCast a 2, ← ENNReal.rpow_mul,
    show ((2 : ℕ) : ℝ) * (2 : ℝ)⁻¹ = 1 by norm_num,
    ENNReal.rpow_one] at h1

private theorem adaptedResponse_eq' (q : Mat d) (k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) :
    adaptedResponse q k w a = coarseBlock (adaptedCellAt q k w) a := rfl

private theorem isSymmetricBlockMat_ofFullBlockMat_smul_sum'' {ι : Type*}
    (s : Finset ι) (c : ℝ) (A : ι → BlockMat d)
    (hA : ∀ i ∈ s, IsSymmetricBlockMat (A i)) :
    IsSymmetricBlockMat
      (ofFullBlockMat (c • ∑ i ∈ s, toFullBlockMat (A i))) := by
  intro α β
  simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  apply congrArg (c * ·)
  apply Finset.sum_congr rfl
  intro i hi
  have h := hA i hi α β
  simpa only [blockMatEntry_eq_toFullBlockMat] using h

private theorem isSymmetricBlockMat_averageDefect' (q : Mat d) (k t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    IsSymmetricBlockMat (Response.diagonalWeakAverageDefect q k t F a) := by
  rw [Response.diagonalWeakAverageDefect_eq_normalized_average]
  refine isSymmetricBlockMat_normalizedBlock ?_
  refine isSymmetricBlockMat_ofFullBlockMat_smul_sum'' _ _ _
    fun w _ => ?_
  exact isSymmetricBlockMat_blockSub
    (Recurrence.isSymmetricBlockMat_coarseBlock_adaptedCellAt q k w a)
    (isSymmetricBlockMat_coarseBlock _ _)

private theorem diag_nonneg_of_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) (i : n) :
    0 ≤ A i i := by
  have h := hA.dotProduct_mulVec_nonneg (Pi.single i 1)
  simp only [star_trivial] at h
  have hquad : Pi.single i (1 : ℝ) ⬝ᵥ A *ᵥ Pi.single i 1 = A i i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, ite_mul,
      Finset.sum_ite_eq', Finset.mem_univ]
  rwa [hquad] at h

private theorem trace_nonneg_of_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    0 ≤ Matrix.trace A :=
  Finset.sum_nonneg fun i _ => diag_nonneg_of_posSemidef hA i

private theorem norm_le_trace_of_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    ‖A‖ ≤ Matrix.trace A := by
  have htr0 : 0 ≤ Matrix.trace A := trace_nonneg_of_posSemidef hA
  refine PortableHistory.norm_le_of_sandwich hA.isHermitian htr0
    (Recurrence.le_trace_smul_one hA) ?_
  have h1 : ((Matrix.trace A • (1 : Matrix n n ℝ)) - (-A)).PosSemidef := by
    rw [sub_neg_eq_add, add_comm]
    exact hA.add (Matrix.PosSemidef.one.smul htr0)
  have h2 : -A ≤ Matrix.trace A • (1 : Matrix n n ℝ) := Matrix.le_iff.mpr h1
  have h3 := neg_le_neg h2
  rwa [neg_neg, ← neg_smul] at h3

private theorem trace_le_card_mul_norm {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    Matrix.trace A ≤ (Fintype.card n : ℝ) * ‖A‖ := by
  have hup : A ≤ ‖A‖ • (1 : Matrix n n ℝ) :=
    (PortableHistory.sandwich_of_norm_le hA.isHermitian (le_refl ‖A‖)).1
  have hpsd : (‖A‖ • (1 : Matrix n n ℝ) - A).PosSemidef :=
    Matrix.le_iff.mp hup
  have hdiag : ∀ i : n, A i i ≤ ‖A‖ := by
    intro i
    have h := diag_nonneg_of_posSemidef hpsd i
    have hentry : (‖A‖ • (1 : Matrix n n ℝ) - A) i i = ‖A‖ - A i i := by
      simp [Matrix.sub_apply, Matrix.smul_apply]
    rw [hentry] at h
    linarith only [h]
  calc Matrix.trace A ≤ ∑ _i : n, ‖A‖ :=
      Finset.sum_le_sum fun i _ => hdiag i
    _ = (Fintype.card n : ℝ) * ‖A‖ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


private theorem integrable_aligned_response_average [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {k t : ℤ}
    (hlk : l ≤ k)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t)
    {F : BlockMat d}
    (hZne : (Response.alignedIndex q k t).Nonempty)
    : (∀ w ∈ (Response.alignedIndex q k t), ∀ α β : BlockCoord d,
      Integrable (fun a =>
        toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) α β) P) ∧
    (Integrable (fun a => ∑ w ∈ (Response.alignedIndex q k t),
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a)) P) ∧
    (Integrable (fun a => ((Response.alignedIndex q k t).card : ℝ)⁻¹ •
      ∑ w ∈ (Response.alignedIndex q k t), toFullBlockMat (coarseBlock (adaptedCellAt q k w) a)) P)
        ∧
    (∀ α β : BlockCoord d,
      Integrable (fun a =>
        toFullBlockMat (coarseBlock (adaptedCell q t) a) α β) P) ∧
    (Integrable (fun a =>
    ((Response.alignedIndex q k t).card : ℝ)⁻¹ • ∑ w ∈ (Response.alignedIndex q k t),
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
      toFullBlockMat (coarseBlock (adaptedCell q t) a)) P) ∧
    (Integrable (fun a => (matSqrt (toFullBlockMat F)⁻¹) * (fun a =>
    ((Response.alignedIndex q k t).card : ℝ)⁻¹ • ∑ w ∈ (Response.alignedIndex q k t),
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
      toFullBlockMat (coarseBlock (adaptedCell q t) a)) a * (matSqrt (toFullBlockMat F)⁻¹)) P) ∧
    (∫ a, (fun a =>
    ((Response.alignedIndex q k t).card : ℝ)⁻¹ • ∑ w ∈ (Response.alignedIndex q k t),
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
      toFullBlockMat (coarseBlock (adaptedCell q t) a)) a ∂P =
      toFullBlockMat (adaptedMean P q k) -
        toFullBlockMat (adaptedMean P q t)) := by
  classical
  set M : FullBlockMat d := matSqrt (toFullBlockMat F)⁻¹ with hMdef
  set Z : Finset (Fin d → ℤ) := Response.alignedIndex q k t with hZdef
  set Y : CoeffSpace d → FullBlockMat d := fun a =>
    (Z.card : ℝ)⁻¹ • ∑ w ∈ Z,
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
      toFullBlockMat (coarseBlock (adaptedCell q t) a) with hYdef
  have hentrysum : ∀ w ∈ Z, ∀ α β : BlockCoord d,
      Integrable (fun a =>
        toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) α β) P :=
    fun w _ α β =>
      (Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hlk hintk w
          α β).congr
        (Filter.Eventually.of_forall fun a =>
          (toFullBlockMat_eq_blockMatEntry
            (coarseBlock (adaptedCellAt q k w) a) α β).symm)
  have hsumint : Integrable (fun a => ∑ w ∈ Z,
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a)) P :=
    integrable_of_entries fun α β => by
      simpa only [Matrix.sum_apply] using
        integrable_finsetSum Z fun w hw => hentrysum w hw α β
  have havgint : Integrable (fun a => (Z.card : ℝ)⁻¹ •
      ∑ w ∈ Z, toFullBlockMat (coarseBlock (adaptedCellAt q k w) a)) P :=
    integrable_of_entries fun α β => by
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      exact (integrable_finsetSum Z fun w hw => hentrysum w hw α β).const_mul _
  have htentry : ∀ α β : BlockCoord d,
      Integrable (fun a =>
        toFullBlockMat (coarseBlock (adaptedCell q t) a) α β) P :=
    fun α β => (hintt α β).congr
      (Filter.Eventually.of_forall fun a =>
        (toFullBlockMat_eq_blockMatEntry
          (coarseBlock (adaptedCell q t) a) α β).symm)
  have hYint : Integrable Y P := by
    simp only [hYdef]
    refine integrable_of_entries fun α β => ?_
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact ((integrable_finsetSum Z fun w hw => hentrysum w hw α β).const_mul _).sub
      (htentry α β)
  have hZint : Integrable (fun a => M * Y a * M) P :=
    integrable_mul_left_mul_right M M hYint
  have hYavg : ∫ a, Y a ∂P =
      toFullBlockMat (adaptedMean P q k) -
        toFullBlockMat (adaptedMean P q t) := by
    have hsplit : ∫ a, Y a ∂P =
        (∫ a, (Z.card : ℝ)⁻¹ • ∑ w ∈ Z,
            toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) ∂P) -
          ∫ a, toFullBlockMat (coarseBlock (adaptedCell q t) a) ∂P := by
      ext α β
      rw [Matrix.sub_apply, entry_integral hYint α β,
        entry_integral havgint α β,
        entry_integral (integrable_toFullBlockMat hintt) α β]
      simp only [hYdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
        smul_eq_mul]
      exact integral_sub
        ((integrable_finsetSum Z fun w hw => hentrysum w hw α β).const_mul _)
        (htentry α β)
    rw [hsplit, Recurrence.integral_alignedAverage_eq_adaptedMean hstat hgrid hlk hintk
      hZne, ← Recurrence.toFullBlockMat_adaptedMean_eq_integral hintt]
  exact ⟨hentrysum, hsumint, havgint, htentry, hYint, hZint, hYavg⟩
/-- **The per-depth averaged defect through its trace.**  By the pathwise
subadditivity of the aligned subdivision, the normalized averaged defect is
positive semidefinite; its identity-size is therefore at most its trace,
whose expectation is the trace of the normalized annealed mean drop by
stationarity of the coefficient law, and the `L²` norm of its root is bounded
by the root of `2 d` times the size of the mean drop. -/
theorem eLpNorm_sqrt_blockSize_averageDefect_le_drop [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {k t : ℤ}
    (hlk : l ≤ k) (hkt : k ≤ t)
    (hintk : HasFiniteAdaptedMean P q k)
    (hintt : HasFiniteAdaptedMean P q t)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    eLpNorm (fun a => Real.sqrt
        (blockSize (Response.diagonalWeakAverageDefect q k t F a)
          (blockIdentity d))) 2 P ≤
      ENNReal.ofReal (Real.sqrt (2 * d *
        blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t))
          F)) := by
  classical
  have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  have hFfull : (toFullBlockMat F).PosDef :=
    posDef_toFullBlockMat hFsym hFpd
  set M : FullBlockMat d := matSqrt (toFullBlockMat F)⁻¹ with hMdef
  have hMsym : Mᴴ = M := by
    rw [conjTranspose_eq_transpose', hMdef, transpose_matSqrt_inv hFfull]
  set Z : Finset (Fin d → ℤ) := Response.alignedIndex q k t with hZdef
  have hZcoe : (↑Z : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q k w ∈ adaptedCell q t} := by
    rw [hZdef]
    exact Response.coe_alignedIndex hq hkt
  have hZne : Z.Nonempty := by
    rw [hZdef]
    exact Response.alignedIndex_nonempty hq hkt
  have hcard0 : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hZne
  set Y : CoeffSpace d → FullBlockMat d := fun a =>
    (Z.card : ℝ)⁻¹ • ∑ w ∈ Z,
      toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
      toFullBlockMat (coarseBlock (adaptedCell q t) a) with hYdef
  have hXfull : ∀ a, toFullBlockMat
      (Response.diagonalWeakAverageDefect q k t F a) = M * Y a * M := by
    intro a
    rw [Response.diagonalWeakAverageDefect_eq_normalized_average,
      Recurrence.toFullBlockMat_normalizedBlock, toFullBlockMat_ofFullBlockMat,
      ← hMdef, ← hZdef]
    congr 1
    congr 1
    have hterm : ∀ w ∈ Z, toFullBlockMat
        (blockSub (adaptedResponse q k w a)
          (coarseBlock (adaptedCell q t) a)) =
        toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) -
          toFullBlockMat (coarseBlock (adaptedCell q t) a) := by
      intro w _
      rw [adaptedResponse_eq', Transport.toFullBlockMat_blockSub]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
      Finset.sum_const, smul_sub, hYdef]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hcard0), one_smul]
  have hYpsd : ∀ a, (Y a).PosSemidef := by
    intro a
    have h := Recurrence.toFullBlockMat_coarseBlock_adaptedCell_le_average
      hq hkt hZcoe a
    have h2 := Matrix.le_iff.mp h
    simp only [hYdef]
    exact h2
  have hZpsd : ∀ a, (M * Y a * M).PosSemidef := by
    intro a
    have h := (hYpsd a).conjTranspose_mul_mul_same M
    rwa [hMsym] at h
  obtain ⟨hentrysum, hsumint, havgint, htentry, hYint, hZint, hYavg⟩ :=
    integrable_aligned_response_average hstat
      hgrid hlk hintk hintt hZne
  set D : FullBlockMat d := M * (toFullBlockMat (adaptedMean P q k) -
      toFullBlockMat (adaptedMean P q t)) * M with hDdef
  have hZavg : ∫ a, M * Y a * M ∂P = D := by
    rw [integral_mul_left_mul_right M M hYint, hYavg]
  have hentryint : ∀ i j : BlockCoord d,
      Integrable (fun a => (M * Y a * M) i j) P := fun i j => by
    have h := (hZint.eval i).eval j
    convert h using 1
  have htrint : Integrable (fun a => Matrix.trace (M * Y a * M)) P := by
    have h1 : Integrable (fun a => ∑ i : BlockCoord d,
        (M * Y a * M) i i) P :=
      integrable_finsetSum Finset.univ fun i _ => hentryint i i
    refine h1.congr (Filter.Eventually.of_forall fun a => ?_)
    rfl
  have htrval : ∫ a, Matrix.trace (M * Y a * M) ∂P = Matrix.trace D := by
    have h1 : ∫ a, (∑ i : BlockCoord d, (M * Y a * M) i i) ∂P =
        ∑ i : BlockCoord d, ∫ a, (M * Y a * M) i i ∂P :=
      integral_finsetSum Finset.univ fun i _ => hentryint i i
    have h0 : ∫ a, Matrix.trace (M * Y a * M) ∂P =
        ∫ a, (∑ i : BlockCoord d, (M * Y a * M) i i) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => rfl)
    rw [h0, h1]
    have h2 : ∀ i : BlockCoord d,
        ∫ a, (M * Y a * M) i i ∂P = D i i := by
      intro i
      rw [← hZavg]
      exact (entry_integral hZint i i).symm
    rw [Finset.sum_congr rfl fun i _ => h2 i]
    rfl
  have hDpsd : D.PosSemidef := by
    have hmean := Recurrence.toFullBlockMat_adaptedMean_le hstat hgrid hlk hkt
      hintk hintt
    have hdiff := Matrix.le_iff.mp hmean
    have h := hdiff.conjTranspose_mul_mul_same M
    rw [hMsym] at h
    exact h
  have hDr0 : 0 ≤ blockSize (blockSub (adaptedMean P q k)
      (adaptedMean P q t)) F :=
    PortableHistory.blockSize_nonneg
      (isSymmetricBlockMat_blockSub
        (Recurrence.isSymmetricBlockMat_adaptedMean P q k)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)) hFsym hFpd
  have hDnorm : blockSize (blockSub (adaptedMean P q k)
      (adaptedMean P q t)) F = ‖D‖ := by
    rw [PortableHistory.blockSize_eq_norm
      (isSymmetricBlockMat_blockSub
        (Recurrence.isSymmetricBlockMat_adaptedMean P q k)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)) hFsym hFpd,
      Recurrence.toFullBlockMat_normalizedBlock, Transport.toFullBlockMat_blockSub,
      ← hMdef, ← hDdef]
  have htrace_le : Matrix.trace D ≤ 2 * d * blockSize (blockSub
      (adaptedMean P q k) (adaptedMean P q t)) F := by
    have h := trace_le_card_mul_norm hDpsd
    have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
      simp [BlockCoord, Fintype.card_sum, two_mul]
    rw [hcard] at h
    rw [hDnorm]
    exact h
  set g : CoeffSpace d → ℝ := fun a =>
    blockSize (Response.diagonalWeakAverageDefect q k t F a)
      (blockIdentity d) with hgdef
  set Dr : ℝ := blockSize (blockSub (adaptedMean P q k)
    (adaptedMean P q t)) F with hDrdef
  have hpath : ∀ a, g a ≤ Matrix.trace (M * Y a * M) := by
    intro a
    have hnorm : g a = ‖M * Y a * M‖ := by
      simp only [hgdef]
      rw [PortableHistory.blockSize_eq_norm
        (isSymmetricBlockMat_averageDefect' q k t F a)
        Response.isSymmetricBlockMat_blockIdentity
        Response.blockPosDef_blockIdentity,
        Recurrence.toFullBlockMat_normalizedBlock,
        toFullBlockMat_blockIdentity, inv_one, matSqrt_one'',
        Matrix.one_mul, Matrix.mul_one, hXfull a]
    rw [hnorm]
    exact norm_le_trace_of_posSemidef (hZpsd a)
  have hbs0 : ∀ a, 0 ≤ g a := fun a =>
    PortableHistory.blockSize_nonneg (isSymmetricBlockMat_averageDefect' q k t F a)
      Response.isSymmetricBlockMat_blockIdentity Response.blockPosDef_blockIdentity
  have hprod0 : (0 : ℝ) ≤ 2 * d * Dr :=
    mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * d) hDr0
  refine le_trans (le_rpow_inv_two_of_sq_le'
    (b := ENNReal.ofReal (2 * d * Dr)) ?_) (le_of_eq ?_)
  · have hsqrtm : AEStronglyMeasurable (fun a => Real.sqrt (g a)) P :=
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (aemeasurable_blockSize_averageDefect hq k t F).aestronglyMeasurable
    rw [eLpNorm_two_real_sq (fun a => Real.sqrt_nonneg _) hsqrtm]
    have hsq : ∀ a, Real.sqrt (g a) ^ 2 = g a := fun a =>
      Real.sq_sqrt (hbs0 a)
    rw [lintegral_congr fun a => congrArg ENNReal.ofReal (hsq a)]
    calc ∫⁻ a, ENNReal.ofReal (g a) ∂P ≤
        ∫⁻ a, ENNReal.ofReal (Matrix.trace (M * Y a * M)) ∂P :=
        lintegral_mono fun a => ENNReal.ofReal_le_ofReal (hpath a)
      _ = ENNReal.ofReal (∫ a, Matrix.trace (M * Y a * M) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal htrint
          (Filter.Eventually.of_forall fun a =>
            trace_nonneg_of_posSemidef (hZpsd a))).symm
      _ = ENNReal.ofReal (Matrix.trace D) := by rw [htrval]
      _ ≤ ENNReal.ofReal (2 * d * Dr) :=
        ENNReal.ofReal_le_ofReal htrace_le
  · rw [show Real.sqrt (2 * d * Dr) = (2 * d * Dr) ^ ((2 : ℝ)⁻¹) from by
      rw [Real.sqrt_eq_rpow, one_div]]
    rw [← ENNReal.ofReal_rpow_of_nonneg hprod0 (by norm_num)]

/-- **The rooted average sum by the mean drops alone.**  The `L²` norm of
the weighted rooted average-defect sum is bounded by the weighted roots of
the annealed mean drops — the sharp replacement for the crude per-cell
variance budget in the printed weak estimate. -/
theorem eLpNorm_diagonalWeakAverageSum_le_drops [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {t : ℤ} (H : ℕ)
    {rho : ℝ} (hstart : l ≤ t - (H : ℤ))
    (hintAll : ∀ k : ℤ, HasFiniteAdaptedMean P q k)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    eLpNorm
        (fun a => Response.diagonalWeakAverageSum q t H (1 / 2) rho F a) 2 P ≤
      ∑ j ∈ Finset.range (H + 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) *
          ENNReal.ofReal (Real.sqrt (2 * d *
            blockSize (blockSub (adaptedMean P q (t - (j : ℤ)))
              (adaptedMean P q t)) F)) := by
  classical
  have hfun : (fun a => Response.diagonalWeakAverageSum q t H (1 / 2) rho F a) =
      ∑ j ∈ Finset.range (H + 1),
        (fun a => (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
          Real.sqrt
            (blockSize
              (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
              (blockIdentity d))) := by
    funext a
    rw [Response.diagonalWeakAverageSum]
    rw [Finset.sum_apply]
  rw [hfun]
  refine le_trans
    (eLpNorm_sum_le (by norm_num)) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  have hjH : (j : ℤ) ≤ (H : ℤ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsmul : (fun a => (3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ)) *
      Real.sqrt
        (blockSize
          (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
          (blockIdentity d))) =
      ((3 : ℝ) ^ (-(1 / 2 - rho / 2) * (j : ℝ))) •
        fun a => Real.sqrt
          (blockSize
            (Response.diagonalWeakAverageDefect q (t - (j : ℤ)) t F a)
            (blockIdentity d)) := by
    funext a
    simp [smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal hw0]
  refine mul_le_mul' le_rfl ?_
  exact eLpNorm_sqrt_blockSize_averageDefect_le_drop hstat hgrid
    (by omega) (by omega) (hintAll _) (hintAll _) hFsym hFpd

end

end HCPolySupport.HighContrast.Quenched
