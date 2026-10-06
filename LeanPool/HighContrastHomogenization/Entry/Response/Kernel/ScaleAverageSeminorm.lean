/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.AnnealedBlockIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseBlockObjects
public import LeanPool.HighContrastHomogenization.Support.Deterministic.WeakNormInterfaces.Definitions

/-!
# High-contrast homogenization: Entry.Response.Kernel.ScaleAverageSeminorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scale-average seminorm and its positive-definiteness inputs

This file introduces the scale-average (Besov-type) seminorm `besovSeminorm t avg` used in the
diagonal weak-norm bound of AK.HC (2.130), together with its cell-average family, its summability
over scales, and the monotonicity of the associated ratio. It then supplies the positive-
definiteness facts the diagonal weak-norm (cell-average) estimate needs: the annealed adapted mean
and the block response mean are positive definite whenever the underlying coefficient sample is
integrable, and the recentred energies `respEhatMinus`/`respEhatPlus` are positive definite from
integrability or from a mean hypothesis, using that the response shear is a unit of the full block
matrix. The scale-average seminorm and these positive-definiteness facts are the inputs to the
response transfer of `p.response.transfer`.
-/

section
/-!
## HC bridge II: the scale-average seminorm (AK.HC (2.130))

The carrier is `besovSeminorm t avg` (`ResponseBlockObjects.lean`, real `tsum`); the
`ℝ≥0∞`-valued `adaptedWeakSeminorm q t s F` is the alternative.  The real carrier needs the
summability supplied below.  Paper `p.response.transfer`.

The pullback to the reference cube is in `ReferenceCubeAveragePullback.lean`; the diagonal
weak-norm primal bound is in `DiagonalDefectCarriers.lean` /
`DiagonalWeakNormBound.lean`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The cell-average family of a doubled field on the selected grid: depth `n`, label `w`
(old `blockCellAverage ∘ adaptedCellAtCenter`, `WeakNorm.lean`). -/
@[expose]
def cellAverageFamily (q : Mat d) (t : ℤ) (X : Vec d → BlockVec d) :
    ℕ → (Fin d → ℤ) → BlockVec d :=
  fun n w => cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) X

/-- The squared `L²(U_t)` mean of a doubled field. -/
@[expose]
def cellMeanSq (V : Set (Vec d)) (X : Vec d → BlockVec d) : ℝ :=
  volumeAverage V fun x => blockVecDot (X x) (X x)

/-! ## Summability and the Jensen/partition bound
(`p.response.transfer`: a constant `c` has `3^{-t/2}[c] = |c|/(1-3^{-1/2})`; the general
field is bounded the same way through Jensen on each cell and exact partition averaging,
`p.response.transfer`).  Old counterpart: the `ℝ≥0∞` sum needed no summability
(`WeakNorm.lean`); the real carrier does. -/

/-! ## HELPERS -/

omit [NeZero d] in
/-- Scalar Jensen for `volumeAverage`. -/
theorem volumeAverage_mul_self_le {V : Set (Vec d)} (hV : MeasurableSet V)
    (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) {g : Vec d → ℝ}
    (hg : IntegrableOn g V) (hg2 : IntegrableOn (fun x => g x * g x) V) :
    volumeAverage V g * volumeAverage V g ≤ volumeAverage V (fun x => g x * g x) := by
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hfin⟩
  set c := volumeAverage V g with hc
  have hconst : IntegrableOn (fun _ : Vec d => c * c) V := integrable_const _
  have hlin : IntegrableOn (fun x => (2 * c) * g x) V := hg.const_mul _
  have hd : IntegrableOn (fun x => g x * g x - (2 * c) * g x) V := hg2.sub hlin
  have hnn : 0 ≤ volumeAverage V (fun x => (g x - c) * (g x - c)) := by
    refine volumeAverage_nonneg_of_nonneg_on hV ?_
    intro x _
    exact mul_self_nonneg _
  have h2 : volumeAverage V (fun x => g x * g x - (2 * c) * g x)
      = volumeAverage V (fun x => g x * g x) - (2 * c) * c := by
    have hrw : (fun x => g x * g x - (2 * c) * g x)
        = (fun x => g x * g x) - ((2 * c) • g) := by
      funext x; simp [smul_eq_mul]
    rw [hrw, volumeAverage_sub hg2 (by simpa [smul_eq_mul] using! hlin), volumeAverage_smul]
  have heq : volumeAverage V (fun x => (g x - c) * (g x - c))
      = volumeAverage V (fun x => g x * g x) - c * c := by
    have h1 : (fun x => (g x - c) * (g x - c))
        = (fun x => g x * g x - (2 * c) * g x) + (fun _ => c * c) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [h1, volumeAverage_add hd hconst, volumeAverage_const hvol, h2]
    ring
  linarith only [heq, hnn]

omit [NeZero d] in
/-- Finite-family Jensen, junk-safe: non-integrable components contribute `0` on the left. -/
theorem sum_volumeAverage_mul_self_le {ι : Type*} [Fintype ι] {V : Set (Vec d)}
    (hV : MeasurableSet V) (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0)
    (g : ι → Vec d → ℝ)
    (hG : IntegrableOn (fun x => ∑ k, g k x * g k x) V) :
    ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      ≤ volumeAverage V (fun x => ∑ k, g k x * g k x) := by
  classical
  have : IsFiniteMeasure (volume.restrict V) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hfin⟩
  set s : Finset ι := Finset.univ.filter (fun k => IntegrableOn (g k) V) with hs
  have hmem : ∀ k ∈ s, IntegrableOn (g k) V := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hzero : ∀ k, k ∉ s → volumeAverage V (g k) = 0 := by
    intro k hk
    have hni : ¬ IntegrableOn (g k) V := by
      intro h; exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)
    unfold volumeAverage
    rw [integral_undef hni, mul_zero]
  have hL : ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = ∑ k ∈ s, volumeAverage V (g k) * volumeAverage V (g k) := by
    refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
    intro k _ hk
    rw [hzero k hk, mul_zero]
  have hptnn : ∀ (x : Vec d) (k : ι), g k x * g k x ≤ ∑ j, g j x * g j x := by
    intro x k
    exact Finset.single_le_sum (f := fun j => g j x * g j x)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
  have hsq : ∀ k ∈ s, IntegrableOn (fun x => g k x * g k x) V := by
    intro k hk
    have hgk := hmem k hk
    refine hG.mono' (hgk.aestronglyMeasurable.mul hgk.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _)]
    exact hptnn x k
  have hsInt : IntegrableOn (fun x => ∑ k ∈ s, g k x * g k x) V := by
    simpa [IntegrableOn] using
      (integrable_finsetSum (μ := volume.restrict V) s
        (fun k hk => (hsq k hk).integrable))
  calc ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = ∑ k ∈ s, volumeAverage V (g k) * volumeAverage V (g k) := hL
    _ ≤ ∑ k ∈ s, volumeAverage V (fun x => g k x * g k x) :=
        Finset.sum_le_sum (fun k hk =>
          volumeAverage_mul_self_le hV hfin hvol (hmem k hk) (hsq k hk))
    _ = volumeAverage V (fun x => ∑ k ∈ s, g k x * g k x) :=
        (volumeAverage_sum s (fun k x => g k x * g k x) hsq).symm
    _ ≤ volumeAverage V (fun x => ∑ k, g k x * g k x) := by
        refine volumeAverage_le_volumeAverage_of_le_on hV hsInt hG ?_
        intro x _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun j _ _ => mul_self_nonneg _)

omit [NeZero d] in
/-- Jensen for the doubled cell average: `|(X)_V|² ≤ (|X|²)_V`. -/
theorem blockVecDot_cellAverage_self_le_cellMeanSq {V : Set (Vec d)} (hV : MeasurableSet V)
    (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) (X : Vec d → BlockVec d)
    (hX : IntegrableOn (fun x => blockVecDot (X x) (X x)) V) :
    blockVecDot (cellAverage V X) (cellAverage V X) ≤ cellMeanSq V X := by
  classical
  set g : (Fin d ⊕ Fin d) → Vec d → ℝ :=
    fun k x => Sum.elim (fun i => (X x).1 i) (fun i => (X x).2 i) k with hgdef
  have hsum : ∀ x : Vec d, ∑ k, g k x * g k x = blockVecDot (X x) (X x) := by
    intro x
    rw [Fintype.sum_sum_type]
    simp [hgdef, blockVecDot, vecDot]
  have hG : IntegrableOn (fun x => ∑ k, g k x * g k x) V := by
    simpa only [hsum] using hX
  have hmain := sum_volumeAverage_mul_self_le hV hfin hvol g hG
  have hR : volumeAverage V (fun x => ∑ k, g k x * g k x) = cellMeanSq V X := by
    unfold cellMeanSq
    exact congrArg (volumeAverage V) (funext hsum)
  have hLhs : ∑ k, volumeAverage V (g k) * volumeAverage V (g k)
      = blockVecDot (cellAverage V X) (cellAverage V X) := by
    rw [Fintype.sum_sum_type]
    simp [hgdef, blockVecDot, vecDot, cellAverage]
  rw [hLhs, hR] at hmain
  exact hmain

/-! ## GEOMETRY.  `standardCell_subset_centeredCube_of_mem_triadicIndexBox` and
`adaptedCellAtCenter_subset_adaptedCell` are imported from
`HCPoly/Entry/Response/Core/ScalarMaximizerExistence.lean`. -/

omit [NeZero d] in
theorem card_triadicIndexBox (n : ℕ) : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := by
  classical
  have hone : 1 ≤ (3 : ℕ) ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hdvd : 2 ∣ (3 : ℕ) ^ n - 1 := by
    have hodd : Odd ((3 : ℕ) ^ n) := Odd.pow (by decide)
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  have hIcc : (Finset.Icc (-(((3 ^ n - 1) / 2 : ℕ) : ℤ)) (((3 ^ n - 1) / 2 : ℕ) : ℤ)).card
      = (3 : ℕ) ^ n := by
    rw [Int.card_Icc]
    have h2 : 2 * ((3 ^ n - 1) / 2 : ℕ) = (3 : ℕ) ^ n - 1 := Nat.mul_div_cancel' hdvd
    omega
  have hc : (triadicIndexBox d n).card = ((3 : ℕ) ^ n) ^ d := by
    unfold triadicIndexBox
    rw [Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hIcc)]
    simp
  rw [hc]
  push_cast
  ring

omit [NeZero d] in
theorem isOpen_adaptedCell_of_isUnit {q : Mat d} (hq : IsUnit q) (j : ℤ) :
    IsOpen (HighContrast.adaptedCell q j) := by
  have h0 : HighContrast.adaptedCellTranslate q j 0 = HighContrast.adaptedCell q j := by
    ext x; simp [HighContrast.adaptedCellTranslate]
  rw [← h0]
  exact Geometry.isOpen_adaptedCellTranslate hq j 0

omit [NeZero d] in
theorem isOpen_adaptedCellAtCenter_of_isUnit {q : Mat d} (hq : IsUnit q) (j : ℤ) (w : Fin d → ℤ) :
    IsOpen (adaptedCellAtCenter q j w) :=
  Geometry.isOpen_adaptedCellTranslate hq j _

/-! ## The scale-term average bound -/

omit [NeZero d] in
/-- Each scale term is bounded by the `L²(U_t)` mean: Jensen on cells + exact partition
of `U_t` by the `3^{nd}` depth-`n` cells. -/
theorem avsum_cellAverageFamily_sq_le (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) (n : ℕ) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w) ≤
      cellMeanSq (HighContrast.adaptedCell q t) X := by
  classical
  set U : Set (Vec d) := HighContrast.adaptedCell q t with hU
  set f : Vec d → ℝ := fun x => blockVecDot (X x) (X x) with hf
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    have : f x = (∑ i, (X x).1 i * (X x).1 i) + ∑ i, (X x).2 i * (X x).2 i := by
      simp [hf, blockVecDot, vecDot]
    rw [this]
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  have hdet : |q.det| ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det q).mp hq
    exact abs_ne_zero.mpr (IsUnit.ne_zero this)
  have hUmeas : MeasurableSet U := (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hUreal : (volume U).toReal = |q.det| * ((3 : ℝ) ^ t) ^ d :=
    Geometry.volume_adaptedCell_toReal q t
  have hUfin : volume U ≠ ⊤ := by
    rw [hU, Geometry.volume_adaptedCell]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hUpos : 0 < (volume U).toReal := by
    rw [hUreal]
    have h1 : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hXint : IntegrableOn f U := (memLp_one_iff_integrable.mp hX)
  -- per-cell data
  set V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter q (t - (n : ℤ)) w with hV
  have hVmeas : ∀ w, MeasurableSet (V w) := fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq _
    w).measurableSet
  have hVreal : ∀ w, (volume (V w)).toReal = |q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
    intro w
    rw [hV, Geometry.volume_adaptedCellAtCenter]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
  have hVfin : ∀ w, volume (V w) ≠ ⊤ := fun w => Geometry.volume_adaptedCellAtCenter_ne_top q _ w
  have hVpos : ∀ w, 0 < (volume (V w)).toReal := by
    intro w
    rw [hVreal w]
    have h1 : 0 < |q.det| := abs_pos.mpr (by
      have := (Matrix.isUnit_iff_isUnit_det q).mp hq
      exact IsUnit.ne_zero this)
    positivity
  have hsub : ∀ w ∈ triadicIndexBox d n, V w ⊆ U := by
    intro w hw
    exact adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVint : ∀ w ∈ triadicIndexBox d n, IntegrableOn f (V w) :=
    fun w hw => hXint.mono_set (hsub w hw)
  -- Step 1: Jensen on each cell
  have hJ : ∀ w ∈ triadicIndexBox d n,
      blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)
        ≤ (volume (V w)).toReal⁻¹ * ∫ x in V w, f x := by
    intro w hw
    have := blockVecDot_cellAverage_self_le_cellMeanSq (V := V w) (hVmeas w) (hVfin w)
      (ne_of_gt (hVpos w)) X (hVint w hw)
    simpa [cellAverageFamily, cellMeanSq, volumeAverage, hV, hf] using this
  -- Step 2: sum of the integrals
  have hdisj : Set.Pairwise (↑(triadicIndexBox d n) : Set (Fin d → ℤ))
      (Function.onFun Disjoint V) := by
    intro a _ b _ hab
    exact Geometry.adaptedCellAtCenter_disjoint_of_ne hq _ hab
  have hunion : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x
      = ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x :=
    integral_biUnion_finset _ (fun w _ => hVmeas w) hdisj hVint
  have hUsub : (⋃ w ∈ triadicIndexBox d n, V w) ⊆ U := by
    refine Set.iUnion₂_subset ?_
    intro w hw
    exact hsub w hw
  have hmono : ∫ x in (⋃ w ∈ triadicIndexBox d n, V w), f x ≤ ∫ x in U, f x := by
    refine setIntegral_mono_set hXint ?_ (LE.le.eventuallyLE hUsub)
    filter_upwards with x using hfnn x
  have hsumle : ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x ≤ ∫ x in U, f x := by
    rw [← hunion]; exact hmono
  -- Step 3: arithmetic
  have hNcard : ((triadicIndexBox d n).card : ℝ) = ((3 : ℝ) ^ n) ^ d := card_triadicIndexBox n
  have hNpos : (0 : ℝ) < ((triadicIndexBox d n).card : ℝ) := by
    rw [hNcard]; positivity
  have hprod : ((triadicIndexBox d n).card : ℝ) * (volume (V 0)).toReal = (volume U).toReal := by
    rw [hNcard, hVreal 0, hUreal]
    have h3 : (3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ)) = (3 : ℝ) ^ t := by
      rw [show ((3 : ℝ) ^ n) = (3 : ℝ) ^ ((n : ℤ)) from (zpow_natCast (3 : ℝ) n).symm,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring_nf
    calc ((3 : ℝ) ^ n) ^ d * (|q.det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d)
        = |q.det| * ((3 : ℝ) ^ n * (3 : ℝ) ^ (t - (n : ℤ))) ^ d := by rw [mul_pow]; ring
      _ = |q.det| * ((3 : ℝ) ^ t) ^ d := by rw [h3]
  have hVconst : ∀ w, (volume (V w)).toReal = (volume (V 0)).toReal := by
    intro w; rw [hVreal w, hVreal 0]
  calc (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ((volume (V 0)).toReal⁻¹ * ∫ x in V w, f x) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (le_of_lt (inv_pos.mpr hNpos))
        intro w hw
        have := hJ w hw
        rwa [hVconst w] at this
    _ = ((((triadicIndexBox d n).card : ℝ)) * (volume (V 0)).toReal)⁻¹ *
          ∑ w ∈ triadicIndexBox d n, ∫ x in V w, f x := by
        rw [← Finset.mul_sum, mul_inv]
        ring
    _ ≤ ((((triadicIndexBox d n).card : ℝ)) * (volume (V 0)).toReal)⁻¹ * ∫ x in U, f x := by
        refine mul_le_mul_of_nonneg_left hsumle ?_
        rw [hprod]
        exact le_of_lt (inv_pos.mpr hUpos)
    _ = cellMeanSq U X := by
        rw [hprod]
        rfl

/-! ## The geometric majorant -/

omit [NeZero d] in
theorem three_rpow_scale_split (t : ℤ) (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2)
      = (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

omit [NeZero d] in
theorem besovRatio_lt_one : (3 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

omit [NeZero d] in
theorem besovRatio_nonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ)) :=
  Real.rpow_nonneg (by norm_num) _

omit [NeZero d] in
/-- The geometric majorant of the scale terms (`avsum_cellAverageFamily_sq_le` +
monotonicity of `sqrt`). -/
theorem besov_term_le (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
  have hA : Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) :=
    Real.sqrt_le_sqrt (avsum_cellAverageFamily_sq_le q hq t X hX n)
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ((t : ℝ) / 2)
    have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := pow_nonneg besovRatio_nonneg n
    exact mul_nonneg this h2
  rw [three_rpow_scale_split t n]
  calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n *
          Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) :=
        mul_le_mul_of_nonneg_left hA h1
    _ = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X) *
          ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n := by ring

/-! ## Summability of the scale-term series -/

omit [NeZero d] in
/-- The series defining `besovSeminorm` is summable for an `L²(U_t)` field. -/
theorem summable_besov_cellAverageFamily (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (X : Vec d → BlockVec d) (hX : MemLp (fun x => blockVecDot (X x) (X x)) 1
      (volume.restrict (HighContrast.adaptedCell q t))) :
    Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot (cellAverageFamily q t X n w) (cellAverageFamily q t X n w)) := by
  refine Summable.of_nonneg_of_le (fun n => ?_)
    (fun n => besov_term_le q hq t X hX n)
    ((summable_geometric_of_lt_one besovRatio_nonneg besovRatio_lt_one).mul_left
      ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt (cellMeanSq (HighContrast.adaptedCell q t) X)))
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Positive definiteness of the annealed adapted mean from integrability alone

Every step of the cell-average estimate that consumes the response sample needs
`(toFullBlockMat (respMean P jStar F t)).PosDef`, and that reduces by definition to
`(toFullBlockMat (adaptedMean P (respGrid jStar F) t)).PosDef`.  The tree previously obtained
this only from `Annealed.adaptedMean_posDef`, which carries the whole coarse-ellipticity
bundle; but the pathwise positivity of the coarse block uses nothing beyond `IsUnit q`, and the
only genuinely missing input is the law-integrability of the coarse block.  The two theorems
below isolate that input, in the shape of the determinant bound
`1 ≤ (toFullBlockMat (adaptedMean P q j)).det`.

`IsProbabilityMeasure P` is not positivity content: it is the hypothesis under which the tree
proves `blockPosDef_annealedBlock` (its expectation argument ends in `measure_univ = 1`), and
`blockPosDef_coarseBlock_adapted` hides no ellipticity hypothesis — the local uniform
ellipticity is carried by `CoeffSpace d` itself, and the only extra ingredient is `IsUnit q`,
which the statement's hypothesis records.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean
  blockPosDef_annealedBlock coarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The adapted annealed mean is positive definite as soon as its coarse block is
law-integrable: `IsUnit q` supplies the pathwise positivity, and the expectation of an
integrable family of positive blocks is positive. -/
theorem adaptedMean_posDef_of_integrable {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (hint : HasIntegrableCoarseBlock P (HighContrast.adaptedCell q j)) :
    (toFullBlockMat (adaptedMean P q j)).PosDef := by
  let U := HighContrast.adaptedCell q j
  have hp (a : CoeffSpace d) : Book.Ch02.BlockPosDef (coarseBlock U a) := by
    simpa [U, HighContrast.adaptedCellTranslate] using
      Annealed.blockPosDef_coarseBlock_adapted q hq j 0 a
  exact posDef_toFullBlockMat (isSymmetricBlockMat_annealedBlock P U)
    (blockPosDef_annealedBlock hint hp)

/-- The response mean inherits the same positive definiteness, since `respMean` and `respCell`
are `adaptedMean` and `HighContrast.adaptedCell` at the selected grid. -/
theorem respMean_posDef_of_integrable {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respMean P jStar F t)).PosDef := by
  simpa only [respMean, respCell] using
    adaptedMean_posDef_of_integrable (P := P) hgrid t hint

end

end HCPolySupport.HighContrast.Multiscale
end

section
open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The block shear `⟨1, 0, c, 1⟩` written in flat `fromBlocks` form.  It is lower
unitriangular, so its determinant is `1`. -/
private theorem toFullBlockMat_shear_eq_fromBlocks (c : Mat d) :
    toFullBlockMat (⟨1, 0, c, 1⟩ : BlockMat d) = Matrix.fromBlocks (1 : Mat d) 0 c 1 := by
  ext (i | i) (j | j) <;> rfl

/-- The response shear `G = ⟨1, 0, respg F, 1⟩` is a unit for every `F`, with no hypothesis:
the shear by `-respg F` is a right inverse, so the determinant is a unit. -/
theorem isUnit_toFullBlockMat_respG (F : BlockMat d) :
    IsUnit (toFullBlockMat (respG F)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse
      (B := toFullBlockMat (⟨1, 0, -(respg F), 1⟩ : BlockMat d)) ?_)
  rw [respG, toFullBlockMat_shear_eq_fromBlocks, toFullBlockMat_shear_eq_fromBlocks,
    Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, add_neg_cancel,
    Matrix.fromBlocks_one]

/-- The doubling `D = diag(Id, -Id)` written in flat `fromBlocks` form. -/
private theorem toFullBlockMat_blockD_eq_fromBlocks :
    toFullBlockMat (blockD d) = Matrix.fromBlocks (1 : Mat d) 0 0 (-1) := by
  ext (i | i) (j | j) <;> rfl

/-- The doubling `D = diag(Id, -Id)` is its own inverse, hence a unit. -/
private theorem isUnit_toFullBlockMat_blockD : IsUnit (toFullBlockMat (blockD d)) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse (B := toFullBlockMat (blockD d)) ?_)
  rw [toFullBlockMat_blockD_eq_fromBlocks, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.fromBlocks_one,
    Matrix.one_mul]

/-- Congruence by a unit preserves positive definiteness: conjugating a positive definite
matrix by an invertible matrix keeps it positive definite (`p.response.transfer`). -/
theorem blockCongr_posDef {G E : BlockMat d} (hG : IsUnit (toFullBlockMat G))
    (hE : (toFullBlockMat E).PosDef) : (toFullBlockMat (blockCongr G E)).PosDef := by
  rw [blockCongr, toFullBlockMat_ofFullBlockMat]
  have h := hE.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hG)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The negative response sample `Ehat^- = Gᵗ E_t G` is positive definite as soon as the
mean `E_t` is, since the shear `G` is a unit (`p.response.transfer`). -/
theorem respEhatMinus_posDef_of_mean {P : Measure (CoeffSpace d)} {jStar : ℕ}
    {F : BlockMat d} {t : ℤ} (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
  blockCongr_posDef (isUnit_toFullBlockMat_respG F) hE

/-- The positive response sample `Ehat^+ = D Ehat^- D` is positive definite as soon as the
mean is, since the doubling `D` is a unit (`p.response.transfer`). -/
theorem respEhatPlus_posDef_of_mean {P : Measure (CoeffSpace d)} {jStar : ℕ}
    {F : BlockMat d} {t : ℤ} (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
  blockCongr_posDef isUnit_toFullBlockMat_blockD (respEhatMinus_posDef_of_mean hE)

/-- **The response sample is positive definite as soon as the coarse block is law-integrable.**
Composing the congruence step with `respMean_posDef_of_integrable`, the positive definiteness
that the recent-head chain asks of `Ê⁻` rests on exactly two things a caller can hold: the unit
selected grid that the cell-average estimate already carries, and the integrability of the coarse
block under the law.  Neither stationarity, nor the coarse-ellipticity bundle, nor a dimension
bound is used. -/
theorem respEhatMinus_posDef_of_integrable [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
  respEhatMinus_posDef_of_mean (respMean_posDef_of_integrable hgrid t hint)

/-- The adjoint twin of `respEhatMinus_posDef_of_integrable`. -/
theorem respEhatPlus_posDef_of_integrable [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {jStar : ℕ} {F : BlockMat d}
    (hgrid : IsUnit (respGrid jStar F)) (t : ℤ)
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    (toFullBlockMat (respEhatPlus P jStar F t)).PosDef :=
  respEhatPlus_posDef_of_mean (respMean_posDef_of_integrable hgrid t hint)

end

end HCPolySupport.HighContrast.Multiscale
end
