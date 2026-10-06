/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedColourIndependence
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.StationarityTransport
public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.Rosenthal.Corollaries

/-!
# High-contrast homogenization: Provider.Recurrence.ColourClassAveraging

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The independent-sum estimate on one colour class

`l.fixed.geometry.matrix.averaging` proves a matrix estimate by proving `4d²`
scalar ones, and each scalar one is a moment estimate for a sum of independent
centred random variables: the entries of the normalized centred responses
`X_i = R^{-1/2}(𝐀(U_i) - 𝐄[𝐀(U_i)])R^{-1/2}` over the cells of one colour class.

This file produces that scalar estimate.  Its analytic inputs are the moment
binders of the independent-sum inequality, and each is a consequence of data the
fixed-grid estimates already carry.

*Integrability of the `Q`-th powers.*  An entry of a normalized centred block is
dominated pointwise by the Schatten size of that block, so a finite `L^Q` norm of
the entry puts it in `L^Q`, and the `Q`-th power of its absolute value is then
integrable.

*Centring.*  The entries of the normalized centred response integrate to zero.
This is stationarity of the coefficient law read through the translation
invariance of the coarse block: the annealed block of an aligned adapted cell is
the adapted mean at that scale, which is the block the response is centred by.

*The uniform bound.*  The `Q`-th root of the `Q`-th absolute moment of an entry
is the real form of its `L^Q` norm, so a uniform bound on those norms is exactly
the uniform binder the inequality asks for.

With the three binders the uniform moment inequality for independent sums applies
to the colour class, and the square root of the cardinality of the class — the
fluctuation gain of the printed proof, before the average is normalized —
appears in the bound.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Symmetry and the entrywise comparison -/

/-- The centred coarse response of a cell is symmetric as soon as the centring
block is. -/
theorem isSymmetricBlockMat_coarseBlock_sub {U : Set (Vec d)} (a : CoeffSpace d)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) :
    IsSymmetricBlockMat (blockSub (coarseBlock U a) E) :=
  isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlockMatrix U (⇑a.1)) hE

/-- **An entry of a normalized block has `L^Q` norm at most the mixed norm of the
block.**  This is the entrywise spectral comparison of
`l.fixed.geometry.matrix.averaging` after the `L^Q` norm is taken. -/
theorem lqNorm_normalizedBlock_le_lqSchattenSize (P : Measure (CoeffSpace d)) {Q : ℝ}
    (hQ : 0 < Q) {A : CoeffSpace d → BlockMat d} (hA : ∀ a, IsSymmetricBlockMat (A a))
    (F : BlockMat d) (α β : BlockCoord d)
    (hmeas : AEStronglyMeasurable (fun a => toFullBlockMat (normalizedBlock (A a) F) α β) P) :
    lqNorm P Q (fun a => toFullBlockMat (normalizedBlock (A a) F) α β)
      ≤ lqSchattenSize P Q A F :=
  lqNorm_le_eLpNorm_schattenNorm P hQ (fun a => isSymmetricBlockMat_normalizedBlock (hA a)) α β
    hmeas

/-! ## The integrability binder -/

/-- **An entry of the normalized centred response lies in `L^Q`** as soon as its
`L^Q` norm is finite. -/
theorem memLp_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)} {Q : ℝ}
    {U : Set (Vec d)} (E F : BlockMat d)
    (α β : BlockCoord d)
    (hfin : lqNorm P Q
      (fun a => toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β) ≠ ⊤) :
    MemLp (fun a => toFullBlockMat (normalizedBlock (blockSub (coarseBlock U a) E) F) α β)
      (ENNReal.ofReal Q) P :=
  hfin.lt_top

/-- **The `Q`-th power of the absolute value of an `L^Q` variable is
integrable.**  This is the integrability binder of the independent-sum
inequality. -/
theorem integrable_abs_rpow_of_memLp {P : Measure (CoeffSpace d)} {Q : ℝ} (hQ : 0 < Q)
    {X : CoeffSpace d → ℝ} (hX : MemLp X (ENNReal.ofReal Q) P) :
    Integrable (fun a => |X a| ^ Q) P := by
  have h := hX.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hQ).ne' ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hQ.le] at h
  simpa only [Real.norm_eq_abs] using h

/-! ## The uniform binder -/

/-- **The uniform binder of the independent-sum inequality.**  The `Q`-th root of
the `Q`-th absolute moment is the real form of the `L^Q` norm, so a bound on the
latter is a bound on the former. -/
theorem rpow_inv_integral_abs_rpow_le_toReal {P : Measure (CoeffSpace d)} {Q : ℝ} (hQ : 0 < Q)
    {X : CoeffSpace d → ℝ} (hX : MemLp X (ENNReal.ofReal Q) P) {v : ℝ≥0∞} (hv : v ≠ ⊤)
    (hle : lqNorm P Q X ≤ v) :
    (∫ a, |X a| ^ Q ∂P) ^ Q⁻¹ ≤ v.toReal := by
  have hrepr := hX.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hQ).ne'
    ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hQ.le] at hrepr
  have hle' : ENNReal.ofReal ((∫ a, |X a| ^ Q ∂P) ^ Q⁻¹) ≤ v := by
    simp only [lqNorm, hrepr, Real.norm_eq_abs] at hle
    exact hle
  exact (ENNReal.ofReal_le_iff_le_toReal hv).mp hle'

/-! ## The centring binder -/

/-- **The entries of the normalized centred response of an aligned adapted cell
integrate to zero.**  The annealed block of an aligned cell is the adapted mean
at that scale, by the translation invariance of the coarse block under
stationarity of the coefficient law, and that mean is the block the response is
centred by. -/
theorem integral_toFullBlockMat_normalizedBlock_adaptedCellAt_eq_zero
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hj : l ≤ j) (hint : HasFiniteAdaptedMean P q j) (F : BlockMat d)
    (w : Fin d → ℤ) (α β : BlockCoord d) :
    ∫ a, toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β ∂P = 0 := by
  have hmeas : HasMeasurableCoarseBlock P (adaptedCell q j) :=
    fun γ δ => (hint γ δ).aestronglyMeasurable
  have hintw := hasIntegrableCoarseBlock_adaptedCellAt hP hq hj hint w
  have hint' : ∀ δ γ : BlockCoord d,
      Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) δ γ) P :=
    fun δ γ => by simpa only [blockMatEntry_eq_toFullBlockMat] using hintw δ γ
  have hmean : ∀ δ γ : BlockCoord d,
      ∫ a, toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) δ γ ∂P
        = toFullBlockMat (adaptedMean P q j) δ γ := by
    intro δ γ
    have h1 : ∫ a, blockMatEntry (coarseBlock (adaptedCellAt q j w) a) δ γ ∂P
        = blockMatEntry (annealedBlock P (adaptedCellAt q j w)) δ γ :=
      (blockMatEntry_annealedBlock P _ δ γ).symm
    rw [annealedBlock_adaptedCellAt_eq_adaptedMean hP hq hj hmeas w] at h1
    simpa only [blockMatEntry_eq_toFullBlockMat] using h1
  have hfun : (fun a => toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β)
      = fun a => ∑ γ : BlockCoord d, ∑ δ : BlockCoord d,
        matSqrt ((toFullBlockMat F)⁻¹) α δ * matSqrt ((toFullBlockMat F)⁻¹) γ β *
          (toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) δ γ
            - toFullBlockMat (adaptedMean P q j) δ γ) := by
    funext a
    rw [toFullBlockMat_normalizedBlock_apply]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ => by
      rw [toFullBlockMat_blockSub_apply]; ring
  have hterm : ∀ γ δ : BlockCoord d, Integrable (fun a =>
      matSqrt ((toFullBlockMat F)⁻¹) α δ * matSqrt ((toFullBlockMat F)⁻¹) γ β *
        (toFullBlockMat (coarseBlock (adaptedCellAt q j w) a) δ γ
          - toFullBlockMat (adaptedMean P q j) δ γ)) P :=
    fun γ δ => ((hint' δ γ).sub (integrable_const _)).const_mul _
  rw [hfun, integral_finsetSum _ fun γ _ => integrable_finsetSum _ fun δ _ => hterm γ δ]
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [integral_finsetSum _ fun δ _ => hterm γ δ]
  refine Finset.sum_eq_zero fun δ _ => ?_
  rw [integral_const_mul, integral_sub (hint' δ γ) (integrable_const _), integral_const,
    hmean δ γ]
  simp

/-! ## The independent-sum estimate -/

/-- **The scalar moment estimate of `l.fixed.geometry.matrix.averaging`**, in
the `ℝ≥0∞` form the mixed norm is written in: a finite sum of independent centred
real variables with `L^Q` norms at most `v` has `L^Q` norm at most a constant
depending on `Q` times the square root of the number of summands times `v`.  The
square root is the fluctuation gain of the printed proof. -/
theorem lqNorm_finsetSum_le_of_iIndepFun {ι : Type*} {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {Q : ℝ} (hQ : 2 ≤ Q) {v : ℝ≥0∞} (hv : v ≠ ⊤) (s : Finset ι)
    {Y : ι → CoeffSpace d → ℝ}
    (hindep : ProbabilityTheory.iIndepFun (fun u : {i : ι // i ∈ s} => Y u.1) P)
    (hmeas : ∀ i, Measurable (Y i)) (hmemLp : ∀ i ∈ s, MemLp (Y i) (ENNReal.ofReal Q) P)
    (hmean : ∀ i ∈ s, ∫ a, Y i a ∂P = 0) (hbd : ∀ i ∈ s, lqNorm P Q (Y i) ≤ v) :
    lqNorm P Q (fun a => ∑ i ∈ s, Y i a)
      ≤ ENNReal.ofReal
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            (Real.sqrt (s.card : ℝ) * v.toReal)) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hK0 : (0 : ℝ) ≤ v.toReal := ENNReal.toReal_nonneg
  have hconst : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine le_trans (le_of_eq ?_) zero_le
    simp [lqNorm]
  have : Nonempty {i : ι // i ∈ s} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  have hcard : (Finset.univ : Finset {i : ι // i ∈ s}).card = s.card := by
    rw [Finset.card_univ, Fintype.card_coe]
  have hsum : ∀ a : CoeffSpace d, ∑ u : {i : ι // i ∈ s}, Y u.1 a = ∑ i ∈ s, Y i a :=
    fun a => Finset.sum_coe_sort s fun i => Y i a
  have hros :=
    IndependentSums.integral_abs_finsetSum_rpow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero
      (μ := P) (X := fun u : {i : ι // i ∈ s} => Y u.1) Finset.univ_nonempty hQ hK0 hindep
      (fun u => hmeas u.1)
      (fun u _ => integrable_abs_rpow_of_memLp hQ0 (hmemLp u.1 u.2))
      (fun u _ => hmean u.1 u.2)
      (fun u _ => rpow_inv_integral_abs_rpow_le_toReal hQ0 (hmemLp u.1 u.2) hv (hbd u.1 u.2))
  rw [hcard] at hros
  simp only [hsum] at hros
  have hmemsum : MemLp (fun a => ∑ i ∈ s, Y i a) (ENNReal.ofReal Q) P :=
    memLp_finsetSum s fun i hi => hmemLp i hi
  have hrepr := hmemsum.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hQ0).ne'
    ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hQ0.le] at hrepr
  have hgoal : lqNorm P Q (fun a => ∑ i ∈ s, Y i a)
      = ENNReal.ofReal ((∫ a, |∑ i ∈ s, Y i a| ^ Q ∂P) ^ Q⁻¹) := by
    simpa only [Real.norm_eq_abs] using! hrepr
  rw [hgoal]
  refine ENNReal.ofReal_le_ofReal (le_trans hros ?_)
  have hN1 : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hNle : (s.card : ℝ) ^ Q⁻¹ ≤ Real.sqrt (s.card : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hone := one_div_le_one_div_of_le (zero_lt_two (α := ℝ)) hQ
    rw [one_div]
    simpa only [one_div] using hone
  have h1 : 2 * Q * ((s.card : ℝ) ^ Q⁻¹ * v.toReal)
      ≤ 2 * Q * (Real.sqrt (s.card : ℝ) * v.toReal) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNle hK0) (by positivity)
  have h2 : 4 * IndependentSums.rosenthalBennettIntegralConst *
        (Real.sqrt Q * (Real.sqrt (s.card : ℝ) * v.toReal))
      = 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q *
        (Real.sqrt (s.card : ℝ) * v.toReal) := by ring
  rw [h2]
  have h3 : (2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
      (Real.sqrt (s.card : ℝ) * v.toReal)
      = 2 * Q * (Real.sqrt (s.card : ℝ) * v.toReal) +
        4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q *
          (Real.sqrt (s.card : ℝ) * v.toReal) := by ring
  rw [h3]
  linarith only [h1]

/-! ## One colour class of a family of aligned adapted cells -/

/-- **The scalar moment estimate on one colour class of aligned adapted cells.**
The entries of the normalized centred responses of a same-colour family of
distinct aligned cells are independent and centred, so the uniform moment
inequality for independent sums applies, and the square root of the cardinality
of the class is the fluctuation gain it produces. -/
theorem lqNorm_sum_colourClass_le {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P) (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ}
    (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j)
    (hint : HasFiniteAdaptedMean P q j) (F : BlockMat d) {v : ℝ≥0∞} (hv : v ≠ ⊤)
    (Z : Finset (Fin d → ℤ)) (c : Fin d → ZMod 3) (α β : BlockCoord d)
    (hbd : ∀ w ∈ Z, lqNorm P Q (fun a => toFullBlockMat (normalizedBlock
      (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β) ≤ v) :
    lqNorm P Q (fun a => ∑ w ∈ Z.filter fun u => (fun i => ((u i : ZMod 3))) = c,
        toFullBlockMat (normalizedBlock
          (blockSub (coarseBlock (adaptedCellAt q j w) a) (adaptedMean P q j)) F) α β)
      ≤ ENNReal.ofReal
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            (Real.sqrt ((Z.filter fun u => (fun i => ((u i : ZMod 3))) = c).card : ℝ) *
              v.toReal)) := by
  have hmem : ∀ w ∈ Z.filter fun u => (fun i => ((u i : ZMod 3))) = c, w ∈ Z :=
    fun w hw => (Finset.mem_filter.mp hw).1
  refine lqNorm_finsetSum_le_of_iIndepFun hQ hv _
    (iIndepFun_toFullBlockMat_normalizedBlock_colourClass P hP hq hj Z c
      (adaptedMean P q j) F α β)
    (fun w => measurable_toFullBlockMat_normalizedBlock_adaptedCellAt
      (posDef_of_isRoundedGrid hq) j w (adaptedMean P q j) F α β)
    (fun w hw => memLp_toFullBlockMat_normalizedBlock_blockSub
      (U := adaptedCellAt q j w) _ F α β
      (lt_of_le_of_lt (hbd w (hmem w hw)) hv.lt_top).ne)
    (fun w hw => integral_toFullBlockMat_normalizedBlock_adaptedCellAt_eq_zero hPs hq hj hint
      F w α β)
    (fun w hw => hbd w (hmem w hw))

end

end Recurrence
end HighContrast
end HCPolySupport
