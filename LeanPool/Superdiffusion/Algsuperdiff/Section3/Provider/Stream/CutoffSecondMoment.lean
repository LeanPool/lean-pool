/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Probability.Independence.Integration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Ellipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.P4UpperMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.GeometricSums
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.ShellSecondMoment

/-!
# CutoffSecondMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The pointwise second moment of the stream matrix `k_m`

ABK26 computes, in the proof of `e.km.kn.L2.bound`,

`⨍ j_k(x) : j_{k'}(x) dx = 0` in expectation for `k ≠ k'`

from independence and mean zero, and then sums the diagonal terms with the exact
normalization `E[‖j_k(x)‖_F²] = c⁺ (log 3) 3^{2γk}` of `ShellSecondMoment`.
This module carries out that computation and then sends `n → -∞`, which is how
the source obtains the estimates for `k_m` itself ("note that we can obtain
estimates for `k_m` by sending `n → -∞`").

## Route for the infinite-sum/expectation interchange

The lower-infinite sum is exchanged with the expectation by *dominated
convergence*, not by a bare `tsum` manipulation.  On the public carrier
`CutoffSample` the proved envelope `cutoffLocalControl ell m` dominates every
entry of every finite lower truncation and of the limit
(`abs_cutoff_entry_le_cutoffLocalControl`), and all of its natural moments are
finite (`integrable_cutoffLocalControl_pow`).  Hence `(d²) ·
(cutoffLocalControl ell m)²` is an integrable dominating function for the whole
approximating sequence, and no new carrier A is required.

## Main results

* `integral_frobeniusMass_shellFinsetSum`: the finite orthogonal expansion
  `E[‖∑_{k ∈ s} j_k(x)‖_F²] = ∑_{k ∈ s} 3^{2γk} c⁺ log 3`.
* `integral_frobeniusMass_finiteShellIncrement`: the same for the increment
  `k_m - k_n`.
* `integral_frobeniusMass_cutoff`: the limit form
  `E[‖k_m(x)‖_F²] = c⁺ K_γ 3^{2γm} / 2`.

## References

* ABK26, `e.km.L2.expectation`.
* ABK26 (the `n → -∞` remark).
* ABK26, `e.km.kn.L2.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Pointwise algebra of the Frobenius mass -/

/-- The Frobenius mass of a finite sum of matrices, expanded into all pairwise
Frobenius pairings. -/
private theorem matrixFrobeniusNormSq_finset_sum (s : Finset ℤ) (A : ℤ → Mat d) :
    matrixFrobeniusNormSq (∑ k ∈ s, A k) =
      ∑ k ∈ s, ∑ k' ∈ s, ∑ i : Fin d, ∑ l : Fin d, A k i l * A k' i l := by
  have hstep : ∀ i l : Fin d,
      (∑ k ∈ s, A k) i l ^ 2 = ∑ k ∈ s, ∑ k' ∈ s, A k i l * A k' i l := by
    intro i l
    rw [Matrix.sum_apply, sq, Finset.sum_mul_sum]
  show (∑ i : Fin d, ∑ l : Fin d, (∑ k ∈ s, A k) i l ^ 2) = _
  calc (∑ i : Fin d, ∑ l : Fin d, (∑ k ∈ s, A k) i l ^ 2)
      = ∑ i : Fin d, ∑ l : Fin d, ∑ k ∈ s, ∑ k' ∈ s, A k i l * A k' i l :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun l _ => hstep i l
    _ = ∑ i : Fin d, ∑ k ∈ s, ∑ l : Fin d, ∑ k' ∈ s, A k i l * A k' i l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i : Fin d, ∑ l : Fin d, ∑ k' ∈ s, A k i l * A k' i l :=
        Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i : Fin d, ∑ k' ∈ s, ∑ l : Fin d, A k i l * A k' i l :=
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ s, ∑ k' ∈ s, ∑ i : Fin d, ∑ l : Fin d, A k i l * A k' i l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- A uniform entry bound gives a Frobenius mass bound. -/
theorem matrixFrobeniusNormSq_le_of_abs_entry_le {A : Mat d} {C : ℝ}
    (h : ∀ i l : Fin d, |A i l| ≤ C) :
    matrixFrobeniusNormSq A ≤ (d : ℝ) ^ 2 * C ^ 2 := by
  show (∑ i : Fin d, ∑ l : Fin d, A i l ^ 2) ≤ _
  calc (∑ i : Fin d, ∑ l : Fin d, A i l ^ 2)
      ≤ ∑ _i : Fin d, ∑ _l : Fin d, C ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => ?_
        exact sq_le_sq' (abs_le.mp (h i l)).1 (abs_le.mp (h i l)).2
    _ = (d : ℝ) ^ 2 * C ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## Measurability helpers -/

/-- One scalar entry of one shell value is measurable on the sequence
carrier. -/
private theorem measurable_shellSeq_entry (k : ℤ) (x : Vec d) (i l : Fin d) :
    Measurable (fun omega : ShellSeq d => (omega k) x i l) :=
  (ShellField.measurable_eval_entry x i l).comp (measurable_pi_apply k)

/-- The Frobenius mass of a finite shell sum is measurable. -/
private theorem measurable_frobeniusMass_finsetSum (s : Finset ℤ) (x : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      matrixFrobeniusNormSq (∑ k ∈ s, (omega k) x)) := by
  show Measurable fun omega : ShellSeq d =>
    ∑ i : Fin d, ∑ l : Fin d, (∑ k ∈ s, (omega k) x) i l ^ 2
  refine Finset.univ.measurable_sum fun i _ =>
    Finset.univ.measurable_sum fun l _ => ?_
  have hentry : Measurable
      (fun omega : ShellSeq d => (∑ k ∈ s, (omega k) x) i l) := by
    simp only [Matrix.sum_apply]
    exact Finset.measurable_sum s fun k _ => measurable_shellSeq_entry k x i l
  exact hentry.pow_const 2

/-! ## The pairwise Frobenius pairing of two shells -/

/-- The Frobenius pairing `j_k(x) : j_{k'}(x)` as a real observable. -/
def shellPairing (x : Vec d) (k k' : ℤ) (omega : ShellSeq d) : ℝ :=
  ∑ i : Fin d, ∑ l : Fin d, (omega k) x i l * (omega k') x i l

private theorem integrable_shell_entry_mul (M : ABKModel d) (x : Vec d) (k k' : ℤ)
    (i l : Fin d) :
    Integrable (fun omega : ShellSeq d => (omega k) x i l * (omega k') x i l)
      M.P.toMeasure :=
  (memLp_two_shell_entry M k x i l).integrable_mul
    (memLp_two_shell_entry M k' x i l)

private theorem integrable_shellPairing (M : ABKModel d) (x : Vec d) (k k' : ℤ) :
    Integrable (shellPairing x k k') M.P.toMeasure := by
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => ?_
  exact integrable_shell_entry_mul M x k k' i l

/-- Distinct shells are independent and mean zero, so their Frobenius pairing
has vanishing expectation.  This is ABK26's cross-term cancellation. -/
private theorem integral_shellPairing_of_ne (M : ABKModel d) (x : Vec d)
    {k k' : ℤ} (hne : k ≠ k') :
    ∫ omega : ShellSeq d, shellPairing x k k' omega ∂M.P.toMeasure = 0 := by
  have hindep : ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => omega k) (fun omega : ShellSeq d => omega k')
      M.P.toMeasure := M.shellPrefix.independent.indepFun hne
  show (∫ omega : ShellSeq d,
    ∑ i : Fin d, ∑ l : Fin d, (omega k) x i l * (omega k') x i l
    ∂M.P.toMeasure) = 0
  rw [integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun l _ => integrable_shell_entry_mul M x k k' i l]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun l _ => integrable_shell_entry_mul M x k k' i l]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hentry : ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => (omega k) x i l)
      (fun omega : ShellSeq d => (omega k') x i l) M.P.toMeasure :=
    hindep.comp (ShellField.measurable_eval_entry x i l)
      (ShellField.measurable_eval_entry x i l)
  rw [hentry.integral_fun_mul_eq_mul_integral
    (measurable_shellSeq_entry k x i l).aestronglyMeasurable
    (measurable_shellSeq_entry k' x i l).aestronglyMeasurable,
    integral_shell_entry_at_point_eq_zero M k x i l, zero_mul]

/-- The diagonal Frobenius pairing is the shell second moment. -/
private theorem integral_shellPairing_self (M : ABKModel d) (x : Vec d) (k : ℤ) :
    ∫ omega : ShellSeq d, shellPairing x k k omega ∂M.P.toMeasure =
      (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  rw [← integral_shellFrobeniusMass M k x]
  refine integral_congr_ae ?_
  filter_upwards with omega
  show (∑ i : Fin d, ∑ l : Fin d, (omega k) x i l * (omega k) x i l) =
    ∑ i : Fin d, ∑ l : Fin d, (omega k) x i l ^ 2
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun l _ => (sq (((omega k) x) i l)).symm

/-! ## The finite orthogonal expansion -/

/-- The exact second moment of a finite sum of shells at one point:
independence and mean zero kill every off-diagonal term, and the diagonal is
summed by the `c⁺` normalization.  This is the deterministic content of the
first two lines of ABK26's `e.km.kn.L2.bound` computation. -/
theorem integral_frobeniusMass_shellFinsetSum (M : ABKModel d) (s : Finset ℤ)
    (x : Vec d) :
    ∫ omega : ShellSeq d, matrixFrobeniusNormSq (∑ k ∈ s, (omega k) x)
        ∂M.P.toMeasure =
      ∑ k ∈ s, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  have hexpand : ∀ omega : ShellSeq d,
      matrixFrobeniusNormSq (∑ k ∈ s, (omega k) x) =
        ∑ k ∈ s, ∑ k' ∈ s, shellPairing x k k' omega :=
    fun omega => matrixFrobeniusNormSq_finset_sum s (fun k => (omega k) x)
  calc ∫ omega : ShellSeq d, matrixFrobeniusNormSq (∑ k ∈ s, (omega k) x)
        ∂M.P.toMeasure
      = ∫ omega : ShellSeq d, ∑ k ∈ s, ∑ k' ∈ s, shellPairing x k k' omega
          ∂M.P.toMeasure := by
        exact integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ k ∈ s, ∑ k' ∈ s,
          ∫ omega : ShellSeq d, shellPairing x k k' omega ∂M.P.toMeasure := by
        rw [integral_finsetSum _ fun k _ =>
          integrable_finsetSum _ fun k' _ => integrable_shellPairing M x k k']
        exact Finset.sum_congr rfl fun k _ =>
          integral_finsetSum _ fun k' _ => integrable_shellPairing M x k k'
    _ = ∑ k ∈ s, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.sum_eq_single_of_mem k hk
          (fun k' _ hk' => integral_shellPairing_of_ne M x (Ne.symm hk')),
          integral_shellPairing_self M x k]

/-- ABK26's exact second moment for the stream increment `k_m - k_n`. -/
theorem integral_frobeniusMass_finiteShellIncrement (M : ABKModel d) (n m : ℤ)
    (x : Vec d) :
    ∫ omega : ShellSeq d,
        matrixFrobeniusNormSq (finiteShellIncrement omega n m x) ∂M.P.toMeasure =
      ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  rw [← integral_frobeniusMass_shellFinsetSum M (Finset.Ioc n m) x]
  refine integral_congr_ae ?_
  filter_upwards with omega
  rw [finiteShellIncrement_apply]
  rfl

/-! ## Transport to the public cutoff carrier -/

/-- Integrals of shell-sequence observables are unchanged by the passage to the
full-measure cutoff carrier. -/
theorem integral_cutoffSampleLaw_comp_val (M : ABKModel d) {f : ShellSeq d → ℝ}
    (hf : Measurable f) :
    ∫ omega : CutoffSample d, f omega.1 ∂(cutoffSampleLaw M).toMeasure =
      ∫ omega : ShellSeq d, f omega ∂M.P.toMeasure := by
  conv_rhs => rw [← map_cutoffSampleLaw_val M]
  exact (integral_map measurable_subtype_coe.aemeasurable
    hf.aestronglyMeasurable).symm

/-! ## The lower-infinite limit -/

/-- Every point of `ℝ^d` lies in some origin-centred open triadic cube.

This restates the private helper `exists_mem_openOriginCube` of
`Section3/Cutoff/Limit.lean`, which is not exported; the proof is the same
elementary Archimedean argument. -/
theorem exists_mem_openCubeSet_originCube (x : Vec d) :
    ∃ ell : ℤ, x ∈ openCubeSet (originCube d ell) := by
  have hpow : ∀ᶠ n : ℕ in atTop, 2 * ∑ i : Fin d, |x i| < (3 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℝ) < 3 by norm_num)).eventually_gt_atTop _
  obtain ⟨n, hn⟩ := hpow.exists
  refine ⟨(n : ℤ), ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hle : |x i| ≤ ∑ k : Fin d, |x k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (x k)) (Finset.mem_univ i)
  have habs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    have hhalf : (1 / 2 : ℝ) * (2 * ∑ k : Fin d, |x k|) < (1 / 2 : ℝ) * (3 : ℝ) ^ n :=
      mul_lt_mul_of_pos_left hn (by norm_num)
    calc |x i| ≤ ∑ k : Fin d, |x k| := hle
      _ = (1 / 2 : ℝ) * (2 * ∑ k : Fin d, |x k|) := by ring
      _ < (1 / 2 : ℝ) * (3 : ℝ) ^ n := hhalf
  have hpow_int : (3 : ℝ) ^ ((n : ℤ)) = (3 : ℝ) ^ n := by simp
  rw [hpow_int]
  refine ⟨?_, (le_abs_self _).trans_lt habs⟩
  calc (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n = -((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by ring
    _ < -|x i| := neg_lt_neg habs
    _ ≤ x i := neg_abs_le _

/-- Every entry of every finite lower truncation is dominated by the proved cutoff
envelope. -/
private theorem abs_finiteLowerCutoff_entry_le_cutoffLocalControl (ell m : ℤ)
    (q : ℕ) (omega : CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) (i l : Fin d) :
    |finiteLowerCutoff m q omega.1 x i l| ≤ cutoffLocalControl ell m omega := by
  rw [finiteLowerCutoff_apply_entry_eq_sum_range_desc]
  calc |∑ r ∈ Finset.range q, omega.1 (m - (r : ℤ)) x i l|
      ≤ ∑ r ∈ Finset.range q, |omega.1 (m - (r : ℤ)) x i l| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range q, localCubeControl ell (omega.1 (m - (r : ℤ))) :=
        Finset.sum_le_sum fun r _ =>
          abs_entry_le_localCubeControl ell (omega.1 (m - (r : ℤ))) hx i l
    _ ≤ ∑' r : ℕ, localCubeControl ell (omega.1 (m - (r : ℤ))) :=
        (summable_cutoffLocalControl ell m omega).sum_le_tsum _
          (fun r _ => localCubeControl_nonneg ell (omega.1 (m - (r : ℤ))))
    _ = cutoffLocalControl ell m omega := rfl

/-- The finite lower truncations converge to the genuine cutoff in Frobenius
mass, pointwise on the public carrier. -/
private theorem tendsto_frobeniusMass_finiteLowerCutoff (ell m : ℤ)
    (omega : CutoffSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ell)) :
    Tendsto (fun q : ℕ => matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x))
      atTop (nhds (matrixFrobeniusNormSq (cutoff m omega x))) := by
  have hentry : ∀ i l : Fin d,
      Tendsto (fun q : ℕ => finiteLowerCutoff m q omega.1 x i l) atTop
        (nhds (cutoff m omega x i l)) := by
    intro i l
    have hsum : Summable (fun r : ℕ => omega.1 (m - (r : ℤ)) x i l) := by
      refine (summable_cutoffLocalControl ell m omega).of_norm_bounded fun r => ?_
      simpa only [Real.norm_eq_abs] using
        abs_entry_le_localCubeControl ell (omega.1 (m - (r : ℤ))) hx i l
    simpa only [finiteLowerCutoff_apply_entry_eq_sum_range_desc,
      cutoff_apply_entry] using hsum.hasSum.tendsto_sum_nat
  show Tendsto (fun q : ℕ =>
    ∑ i : Fin d, ∑ l : Fin d, finiteLowerCutoff m q omega.1 x i l ^ 2) atTop
    (nhds (∑ i : Fin d, ∑ l : Fin d, cutoff m omega x i l ^ 2))
  exact tendsto_finsetSum _ fun i _ =>
    tendsto_finsetSum _ fun l _ => (hentry i l).pow 2

/-- The exact geometric value of the finite lower truncation's second
moment. -/
private theorem integral_frobeniusMass_finiteLowerCutoff (M : ABKModel d) (m : ℤ)
    (q : ℕ) (x : Vec d) :
    ∫ omega : CutoffSample d,
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x)
        ∂(cutoffSampleLaw M).toMeasure =
      ∑ k ∈ Finset.Ioc (m - (q : ℤ)) m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  have hrewrite : ∀ omega : ShellSeq d,
      matrixFrobeniusNormSq (finiteLowerCutoff m q omega x) =
        matrixFrobeniusNormSq (∑ k ∈ Finset.Ioc (m - (q : ℤ)) m, (omega k) x) := by
    intro omega
    rw [finiteLowerCutoff_apply]
    rfl
  rw [integral_cutoffSampleLaw_comp_val M
    (f := fun omega : ShellSeq d =>
      matrixFrobeniusNormSq (finiteLowerCutoff m q omega x))
    (by
      have := measurable_frobeniusMass_finsetSum (d := d)
        (Finset.Ioc (m - (q : ℤ)) m) x
      simpa only [hrewrite] using this)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrewrite),
    integral_frobeniusMass_shellFinsetSum M (Finset.Ioc (m - (q : ℤ)) m) x]

/-- The closed form of ABK26's geometric partial sum, in the shape used by the
`n → -∞` limit. -/
private theorem sum_Ioc_frobenius_closed_form (M : ABKModel d) {n m : ℤ}
    (hnm : n ≤ m) :
    ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) =
      Disorder.cstarPlus M * Kgamma M.gamma / 2 *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
          (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) := by
  have hkey := two_mul_log_three_mul_sum_Ioc_rpow M.shellPrefix.gamma_pos hnm
  have hlog : Real.log 3 *
      ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) =
        Kgamma M.gamma *
          ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
            (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) / 2 := by
    linarith [hkey]
  rw [← Finset.sum_mul]
  calc (∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) *
        (Disorder.cstarPlus M * Real.log 3)
      = Disorder.cstarPlus M *
          (Real.log 3 *
            ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by ring
    _ = Disorder.cstarPlus M *
          (Kgamma M.gamma *
            ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
              (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) / 2) := by rw [hlog]
    _ = Disorder.cstarPlus M * Kgamma M.gamma / 2 *
          ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
            (3 : ℝ) ^ (2 * M.gamma * (n : ℝ))) := by ring

/-- The lower geometric tail vanishes as the truncation depth grows. -/
private theorem tendsto_rpow_lower_scale (gamma : ℝ) (hgamma : 0 < gamma) (m : ℤ) :
    Tendsto (fun q : ℕ => (3 : ℝ) ^ (2 * gamma * ((m - (q : ℤ) : ℤ) : ℝ))) atTop
      (nhds 0) := by
  have hratio : (fun q : ℕ => (3 : ℝ) ^ (2 * gamma * ((m - (q : ℤ) : ℤ) : ℝ))) =
      fun q : ℕ => (3 : ℝ) ^ (2 * gamma * (m : ℝ)) *
        ((3 : ℝ) ^ (-(2 * gamma))) ^ q := by
    funext q
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(2 * gamma))) q,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [hratio]
  have hlt : (3 : ℝ) ^ (-(2 * gamma)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hnonneg : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * gamma)) :=
    Real.rpow_nonneg (by norm_num) _
  simpa using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt).const_mul
      ((3 : ℝ) ^ (2 * gamma * (m : ℝ)))

/-- ABK26's stream second moment at a single point, obtained from the finite
increments by sending `n → -∞`:

`E[ ‖k_m(x)‖_F² ] = c⁺ K_γ 3^{2γm} / 2`.

The interchange of the lower-infinite sum with the expectation is by dominated
convergence against `d² (cutoffLocalControl ell m)²`. -/
theorem integral_frobeniusMass_cutoff (M : ABKModel d) (m : ℤ) (x : Vec d) :
    ∫ omega : CutoffSample d, matrixFrobeniusNormSq (cutoff m omega x)
        ∂(cutoffSampleLaw M).toMeasure =
      Disorder.cstarPlus M * Kgamma M.gamma / 2 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
  obtain ⟨ell, hx⟩ := exists_mem_openCubeSet_originCube x
  have hmeas : ∀ q : ℕ, AEStronglyMeasurable
      (fun omega : CutoffSample d =>
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x))
      (cutoffSampleLaw M).toMeasure := by
    intro q
    have hrewrite : ∀ omega : ShellSeq d,
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega x) =
          matrixFrobeniusNormSq
            (∑ k ∈ Finset.Ioc (m - (q : ℤ)) m, (omega k) x) := by
      intro omega
      rw [finiteLowerCutoff_apply]
      rfl
    have hbase : Measurable (fun omega : ShellSeq d =>
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega x)) := by
      have := measurable_frobeniusMass_finsetSum (d := d)
        (Finset.Ioc (m - (q : ℤ)) m) x
      simpa only [hrewrite] using this
    exact (hbase.comp measurable_subtype_coe).aestronglyMeasurable
  have hdct : Tendsto
      (fun q : ℕ => ∫ omega : CutoffSample d,
        matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x)
        ∂(cutoffSampleLaw M).toMeasure)
      atTop (nhds (∫ omega : CutoffSample d,
        matrixFrobeniusNormSq (cutoff m omega x)
        ∂(cutoffSampleLaw M).toMeasure)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun omega : CutoffSample d =>
        (d : ℝ) ^ 2 * cutoffLocalControl ell m omega ^ 2)
      hmeas ((integrable_cutoffLocalControl_pow M ell m 2).const_mul _)
      (fun q => Filter.Eventually.of_forall fun omega => ?_)
      (Filter.Eventually.of_forall fun omega =>
        tendsto_frobeniusMass_finiteLowerCutoff ell m omega hx)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (matrixFrobeniusNormSq_nonneg
        (finiteLowerCutoff m q omega.1 x))]
    exact matrixFrobeniusNormSq_le_of_abs_entry_le fun i l =>
      abs_finiteLowerCutoff_entry_le_cutoffLocalControl ell m q omega hx i l
  have hvalue : ∀ q : ℕ, ∫ omega : CutoffSample d,
      matrixFrobeniusNormSq (finiteLowerCutoff m q omega.1 x)
      ∂(cutoffSampleLaw M).toMeasure =
        Disorder.cstarPlus M * Kgamma M.gamma / 2 *
          ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
            (3 : ℝ) ^ (2 * M.gamma * ((m - (q : ℤ) : ℤ) : ℝ))) := by
    intro q
    rw [integral_frobeniusMass_finiteLowerCutoff M m q x,
      sum_Ioc_frobenius_closed_form M (by omega : m - (q : ℤ) ≤ m)]
  have hgeo : Tendsto
      (fun q : ℕ => Disorder.cstarPlus M * Kgamma M.gamma / 2 *
        ((3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) -
          (3 : ℝ) ^ (2 * M.gamma * ((m - (q : ℤ) : ℤ) : ℝ)))) atTop
      (nhds (Disorder.cstarPlus M * Kgamma M.gamma / 2 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) := by
    have h := (tendsto_const_nhds (x := (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))
      (f := atTop (α := ℕ))).sub
      (tendsto_rpow_lower_scale M.gamma M.shellPrefix.gamma_pos m)
    simpa using h.const_mul (Disorder.cstarPlus M * Kgamma M.gamma / 2)
  refine tendsto_nhds_unique ?_ hgeo
  simpa only [hvalue] using hdct

end

end Algsuperdiff.Section3.Provider.Stream
