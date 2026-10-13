/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier
public import LeanPool.HighContrastHomogenization.Support.Geometry.OriginCubeBoundaryPush
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The genuine lower-infinite cutoff

This file defines the manuscript cutoff only on `CutoffSample`, the public
carrier on which every descending local-control series is summable.  Thus the
occurrence of `tsum` below is never used with its nonsummable semantics: the
carrier supplies the convergence proof needed at each point and on every
origin-centred cube.

The field is built entrywise from the literal series
`sum_{r >= 0} j_(m-r)`.  Local uniform convergence makes that field continuous,
so it is a genuine `RegCoeffField`; it is not a finite floor or a default value.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The matrix-valued lower-infinite shell series at one physical point. -/
def cutoffValue (m : ℤ) (omega : CutoffSample d) (x : Vec d) : Mat d :=
  fun i j => ∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j

private theorem exists_mem_openOriginCube (x : Vec d) :
    ∃ ell : ℤ, x ∈ openCubeSet (originCube d ell) := by
  let R : ℝ := 2 * ∑ i : Fin d, |x i|
  have hpow : ∀ᶠ n : ℕ in atTop, R < (3 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop R
  obtain ⟨n, hn⟩ := hpow.exists
  refine ⟨(n : ℤ), ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hle : |x i| ≤ ∑ k : Fin d, |x k| := by
    exact Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ i)
  have habs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    calc
      |x i| ≤ ∑ k : Fin d, |x k| := hle
      _ = (1 / 2 : ℝ) * R := by dsimp [R]; ring
      _ < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
        exact mul_lt_mul_of_pos_left hn (by norm_num)
  have hpow_int : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := by
    simp
  rw [hpow_int]
  constructor
  · calc
      (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n = -((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by ring
      _ < -|x i| := neg_lt_neg habs
      _ ≤ x i := neg_abs_le _
  · exact (le_abs_self _).trans_lt habs

private theorem continuous_finiteLowerCutoff_entry (m : ℤ) (q : ℕ)
    (omega : ShellSeq d) (i j : Fin d) :
    Continuous (fun x : Vec d => finiteLowerCutoff m q omega x i j) := by
  have hfun : (fun x : Vec d => finiteLowerCutoff m q omega x i j) =
      fun x => ∑ r ∈ Finset.range q, omega (m - (r : ℤ)) x i j := by
    funext x
    exact finiteLowerCutoff_apply_entry_eq_sum_range_desc m q omega x i j
  rw [hfun]
  exact continuous_finsetSum _ fun r _ =>
    ((continuous_apply j).comp
      ((continuous_apply i).comp (omega (m - (r : ℤ))).1.1.continuous))

theorem continuous_cutoffValue_entry (m : ℤ) (omega : CutoffSample d)
    (i j : Fin d) :
    Continuous (fun x : Vec d => cutoffValue m omega x i j) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨ell, hx⟩ := exists_mem_openOriginCube x
  have hlim := lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry
    omega.2 ell m i j
  have hcont : ContinuousOn
      (fun x : Vec d => cutoffValue m omega x i j)
      (openCubeSet (originCube d ell)) := by
    exact hlim.continuousOn <|
      (Filter.Eventually.of_forall fun q =>
        (continuous_finiteLowerCutoff_entry m q omega.1 i j).continuousOn).frequently
  exact (hcont x hx).continuousAt ((isOpen_openCubeSet (originCube d ell)).mem_nhds hx)

/-- The actual lower-infinite cutoff `k_m = sum_{n <= m} j_n`, defined only
on the convergent cutoff carrier. -/
def cutoff (m : ℤ) (omega : CutoffSample d) : RegCoeffField d where
  toFun := cutoffValue m omega
  entry_measurable := fun i j =>
    (continuous_cutoffValue_entry m omega i j).measurable
  entry_locInt := fun i j =>
    (continuous_cutoffValue_entry m omega i j).locallyIntegrable

@[simp]
theorem cutoff_apply_entry (m : ℤ) (omega : CutoffSample d) (x : Vec d)
    (i j : Fin d) :
    cutoff m omega x i j = ∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j :=
  rfl

theorem continuous_cutoff_entry (m : ℤ) (omega : CutoffSample d) (i j : Fin d) :
    Continuous (fun x : Vec d => cutoff m omega x i j) :=
  continuous_cutoffValue_entry m omega i j

theorem measurable_cutoff_apply_entry (m : ℤ) (x : Vec d) (i j : Fin d) :
    Measurable (fun omega : CutoffSample d => cutoff m omega x i j) := by
  apply measurable_of_tendsto_metrizable
  · intro q
    exact (measurable_apply_entry x i j).comp
      ((measurable_finiteLowerCutoff m q).comp measurable_subtype_coe)
  · rw [tendsto_pi_nhds]
    intro omega
    obtain ⟨ell, hx⟩ := exists_mem_openOriginCube x
    simpa only [cutoff_apply_entry] using!
      (lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry omega.2 ell m i j).tendsto_at hx

private theorem measurable_shell_entry_uncurried (n : ℤ) (i j : Fin d) :
    Measurable (fun p : CutoffSample d × Vec d => p.1.1 n p.2 i j) := by
  have hshell : Measurable (fun p : CutoffSample d × Vec d => p.1.1 n) :=
    (measurable_pi_apply _).comp (measurable_subtype_coe.comp measurable_fst)
  have heval : Measurable (fun q : Algsuperdiff.Frozen.Assumptions.ShellField d × Vec d =>
      q.1 q.2 i j) := by
    have hcont : Continuous (fun q : Algsuperdiff.Frozen.Assumptions.ShellField d × Vec d =>
        q.1 q.2 i j) := by
      have hvalue : Continuous
          (fun q : Algsuperdiff.Frozen.Assumptions.ShellField d × Vec d => q.1 q.2) :=
        ContinuousEval.continuous_eval.comp
          (((continuous_subtype_val.comp continuous_fst).fst).prodMk continuous_snd)
      exact (continuous_apply j).comp ((continuous_apply i).comp hvalue)
    exact hcont.measurable
  exact heval.comp (hshell.prodMk measurable_snd)

private theorem measurable_finiteLowerCutoff_apply_entry_uncurried (m : ℤ) (q : ℕ)
    (i j : Fin d) :
    Measurable (fun p : CutoffSample d × Vec d => finiteLowerCutoff m q p.1.1 p.2 i j) := by
  have hfun : (fun p : CutoffSample d × Vec d => finiteLowerCutoff m q p.1.1 p.2 i j) =
      fun p => ∑ r ∈ Finset.range q, p.1.1 (m - (r : ℤ)) p.2 i j := by
    funext p
    exact finiteLowerCutoff_apply_entry_eq_sum_range_desc m q p.1.1 p.2 i j
  rw [hfun]
  exact Finset.measurable_sum _ fun r _ =>
    measurable_shell_entry_uncurried (m - (r : ℤ)) i j

private theorem measurable_cutoff_apply_entry_uncurried (m : ℤ) (i j : Fin d) :
    Measurable (fun p : CutoffSample d × Vec d => cutoff m p.1 p.2 i j) := by
  apply measurable_of_tendsto_metrizable
  · intro q
    exact measurable_finiteLowerCutoff_apply_entry_uncurried m q i j
  · rw [tendsto_pi_nhds]
    intro p
    obtain ⟨ell, hp⟩ := exists_mem_openOriginCube p.2
    simpa only [cutoff_apply_entry] using!
      (lowerTailGood_tendstoUniformlyOn_finiteLowerCutoff_entry p.1.2 ell m i j).tendsto_at hp

private theorem measurable_entryTestR_cutoff (m : ℤ) (i j : Fin d)
    (phi : Vec d → ℝ) (hphi : IsProbeR phi) :
    Measurable (fun omega : CutoffSample d => entryTestR i j phi (cutoff m omega)) := by
  have hintegrand : Measurable (fun p : CutoffSample d × Vec d =>
      cutoff m p.1 p.2 i j * phi p.2) :=
    (measurable_cutoff_apply_entry_uncurried m i j).mul
      (hphi.measurable.comp measurable_snd)
  have hintegral : StronglyMeasurable (fun omega : CutoffSample d =>
      ∫ x, cutoff m omega x i j * phi x ∂volume) :=
    hintegrand.stronglyMeasurable.integral_prod_right'
  exact hintegral.measurable

/-- The lower-infinite cutoff is measurable for CoarseGraining's full regular-field
sigma-algebra, including both pointwise and compactly-supported entry-test
generators.  The entry-test integrals are genuinely integrable by the
`RegCoeffField` carrier; the displayed measurability proof uses their jointly
measurable integrands, not a totalized off-carrier series. -/
theorem measurable_cutoff (m : ℤ) :
    Measurable (fun omega : CutoffSample d => cutoff m omega) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro x i j
    exact measurable_cutoff_apply_entry m x i j
  · intro i j phi hphi
    exact measurable_entryTestR_cutoff m i j phi hphi

private theorem summable_cutoff_entry (m : ℤ) (omega : CutoffSample d)
    (x : Vec d) (i j : Fin d) :
    Summable (fun r : ℕ => omega.1 (m - (r : ℤ)) x i j) := by
  obtain ⟨ell, hx⟩ := exists_mem_openOriginCube x
  refine (lowerTailGood_summable omega.2 ell m).of_norm_bounded fun r => ?_
  simpa only [Real.norm_eq_abs] using
    abs_entry_le_localCubeControl ell (omega.1 (m - (r : ℤ))) hx i j

theorem cutoff_skew (m : ℤ) (omega : CutoffSample d) (x : Vec d) :
    (cutoff m omega x).transpose = -cutoff m omega x := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.neg_apply, cutoff_apply_entry]
  calc
    (∑' r : ℕ, omega.1 (m - (r : ℤ)) x j i) =
        ∑' r : ℕ, -omega.1 (m - (r : ℤ)) x i j := by
      apply tsum_congr
      intro r
      exact Algsuperdiff.Frozen.Assumptions.ShellField.skew_entry
        (omega.1 (m - (r : ℤ))) x j i
    _ = -(∑' r : ℕ, omega.1 (m - (r : ℤ)) x i j) := by
      rw [tsum_neg]

private theorem sub_natCast_toNat_eq_of_le {n m : ℤ} (hnm : n ≤ m) :
    m - ((m - n).toNat : ℤ) = n := by
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm)]
  ring

/-- The exact finite-increment identity for the lower-infinite cutoffs.  This is
the carrier equality equivalent to `k_m - k_n = sum_(n,m] j_k`; phrasing it
without subtraction preserves CoarseGraining's additive regular-field carrier. -/
theorem cutoff_add_finiteShellIncrement (omega : CutoffSample d) {n m : ℤ}
    (hnm : n ≤ m) :
    cutoff n omega + finiteShellIncrement omega.1 n m = cutoff m omega := by
  apply RegCoeffField.ext
  intro x
  ext i j
  let L : ℕ := (m - n).toNat
  have hL : m - (L : ℤ) = n := by
    simpa [L] using sub_natCast_toNat_eq_of_le hnm
  have hfinite : finiteShellIncrement omega.1 n m x i j =
      ∑ r ∈ Finset.range L, omega.1 (m - (r : ℤ)) x i j := by
    rw [← hL]
    change finiteLowerCutoff m L omega.1 x i j = _
    exact finiteLowerCutoff_apply_entry_eq_sum_range_desc m L omega.1 x i j
  have hsum := summable_cutoff_entry m omega x i j
  have htail : (fun r : ℕ => omega.1 (m - ((r + L : ℕ) : ℤ)) x i j) =
      fun r : ℕ => omega.1 (n - (r : ℤ)) x i j := by
    funext r
    have hcast : ((r + L : ℕ) : ℤ) = (r : ℤ) + (L : ℤ) := by norm_num
    have hindex : m - ((r + L : ℕ) : ℤ) = n - (r : ℤ) := by
      rw [hcast]
      calc
        m - ((r : ℤ) + (L : ℤ)) = (m - (L : ℤ)) - (r : ℤ) := by ring
        _ = n - (r : ℤ) := by rw [hL]
    rw [hindex]
  rw [RegCoeffField.add_apply, Matrix.add_apply, cutoff_apply_entry,
    hfinite, cutoff_apply_entry]
  rw [← htail]
  rw [add_comm]
  exact hsum.sum_add_tsum_nat_add L

/-- Pointwise subtraction form of the finite-increment identity:
`k_m - k_n = sum_(n,m] j_k`. -/
theorem cutoff_sub_cutoff_eq_finiteShellIncrement (omega : CutoffSample d)
    {n m : ℤ} (hnm : n ≤ m) (x : Vec d) :
    cutoff m omega x - cutoff n omega x = finiteShellIncrement omega.1 n m x := by
  have h := congrArg (fun a : RegCoeffField d => a x)
    (cutoff_add_finiteShellIncrement omega hnm)
  change cutoff n omega x + finiteShellIncrement omega.1 n m x = cutoff m omega x at h
  ext i j
  have hentry := congrFun (congrFun h i) j
  change cutoff m omega x i j - cutoff n omega x i j =
    finiteShellIncrement omega.1 n m x i j
  apply sub_eq_iff_eq_add.mpr
  simpa only [Matrix.add_apply, add_comm] using hentry.symm

/-- The coefficient cutoff `a_m = nu I + k_m`. -/
def coefficientCutoff (nu : ℝ) (m : ℤ) (omega : CutoffSample d) : RegCoeffField d :=
  RegCoeffField.constRegCoeffField (nu • (1 : Mat d)) + cutoff m omega

@[simp]
theorem coefficientCutoff_apply (nu : ℝ) (m : ℤ) (omega : CutoffSample d)
    (x : Vec d) :
    coefficientCutoff nu m omega x = nu • (1 : Mat d) + cutoff m omega x :=
  rfl

/-- The actual coefficient cutoff is measurable for CoarseGraining's full
regular-coefficient-field sigma-algebra. -/
theorem measurable_coefficientCutoff (nu : ℝ) (m : ℤ) :
    Measurable (fun omega : CutoffSample d => coefficientCutoff nu m omega) := by
  exact measurable_const.add (measurable_cutoff m)

/-- The symmetric part of the actual coefficient cutoff is exactly `nu I`.
This is a pointwise identity, not an added ellipticity hypothesis. -/
theorem symmPart_coefficientCutoff (nu : ℝ) (m : ℤ) (omega : CutoffSample d)
    (x : Vec d) :
    symmPart (coefficientCutoff nu m omega x) = nu • (1 : Mat d) := by
  have hskew := cutoff_skew m omega x
  ext i j
  have hskew_entry : cutoff m omega x j i = -cutoff m omega x i j := by
    have := congrFun (congrFun hskew i) j
    simpa using this
  simp only [symmPart, coefficientCutoff_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [hskew_entry]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.one_apply, ite_eq_left]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [Matrix.one_apply, ite_eq_right hij, ite_eq_right hji]
    ring

end

end Algsuperdiff.Section3.Cutoff
