/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessGeneral
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIntegralProcessLocalMartingale
public import LeanPool.MathFin.Probability.Support.DoobContinuous

/-!
# Continuous modification of the general-integrand Itô process (the gate)

The first pathwise-regularity result for the **general** integrand: a continuous
modification of the `L²`-valued process `t ↦ itoProcessCLM T t φ` on a finite
horizon `[0,T]`.

B1b (`ItoIntegralProcessGeneral`) built the general-integrand Itô integral as an
`Lp ℝ 2 μ`-valued process — adapted, an `L²` martingale, `L²`-continuous in `t`,
but with no honest sample paths. B3 (`ItoIntegralProcessLocalMartingale`) gave
pathwise continuity only for the **simple** integrand. This file closes the gap:
approximate `φ` by simple processes `Vₙ` (density, B1b); each `Vₙ ● B` has
continuous paths (B3); Degenne's continuous-time weak-type maximal inequality
(`maximal_ineq_norm`) + Borel–Cantelli on a fast subsequence make `(Vₙ ● B)`
a.s.-uniformly Cauchy on `[0,T]`, so the uniform limit `itoContinuousMod` is
pathwise continuous (`itoContinuousMod_continuousOn`) and equals `(φ ● B)_t` a.e.
at every `t ≤ T` (a **modification**, `itoContinuousMod_modification`), bundled by
`exists_continuous_modification_itoProcess`.

This continuous modification is the *input* the localized stochastic calculus
consumes: the `IsLocalMartingale` packaging is an explicit follow-on (Degenne's
`Martingale.IsLocalMartingale` needs paths càdlàg for **every** `ω`, which for the
general integrand requires an augmented filtration — the "usual conditions" — that
`natFiltration` does not carry; B3 sidesteps this because the *simple* process is
continuous and adapted for every `ω`). It is **not** proved here.

## Coherence

Pure consumption + assembly. Degenne's general càdlàg modification, `cadlagModif` in
`StochasticIntegral/Quasimartingale/CadlagModificationBanach.lean`, has no `sorry` at our pin, but
it is a modification only for a right-continuous filtration, and adapted only if that filtration is
also complete: the usual conditions, which `natFiltration` does not carry. So this result is not a
duplicate, and the `L²`-continuity + Doob route yields a genuinely **continuous** (not merely
càdlàg) version. Nothing of the isometry, density, or martingale property is reproved — the maximal
inequality is Degenne's, the continuous approximants are B3's, the density is B1b's.

See `docs/superpowers/specs/2026-06-26-ito-continuous-modification-design.md`.

## Main definitions

* `itoContinuousMod`: the pathwise limit process, for each `t, ω` the limit (if it exists) of the
  approximating simple integrals `(Vₙ ● B)_t ω` along `approxSeq`, junk off the convergence set.

## Main results

* `itoSimpleProcess_maximal_weak`: the weak-type maximal bound
  `ε · μ{ε ≤ sup_{i ≤ T} ‖(V ● B)_i‖} ≤ ∫_{that set} ‖(V ● B)_T‖` for the elementary Itô integral.
* `itoSimpleProcess_maximal_prob`: for a `T`-bounded simple process `V` and `ε > 0`, the
  probability that the running maximum of `(V ● B)` over `[0,T]` reaches `ε` is at most
  `ε⁻¹ · ‖simpleAssemblyHorizon V‖`.
* `approxSeq`: every predictable integrand `φ` has a fast approximating sequence of `T`-bounded
  simple processes, with `‖simpleAssemblyHorizon Vₙ − φ‖ ≤ 2⁻ⁿ`.
* `ae_eventually_sup_lt`: for such a fast approximating sequence `Vₙ` (and continuous Brownian
  paths), almost surely the running maximum of the consecutive difference `(Vₙ − Vₙ₊₁) ● B` over
  `[0,T]` is eventually below `(3/4)ⁿ`.
* `itoContinuousMod_modification`: for every `t ≤ T`, `itoContinuousMod φ t` agrees almost
  everywhere with `itoProcessCLM T t φ`.
* `itoContinuousMod_continuousOn`: almost every path of `itoContinuousMod φ` is continuous on
  `[0,T]`.
* `exists_continuous_modification_itoProcess`: there is a process agreeing almost everywhere with
  `itoProcessCLM T t φ` at every `t ≤ T`, with almost surely continuous paths on `[0,T]`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 7

## Tags

continuous modification, Itô integral, Doob maximal inequality, Borel–Cantelli, stochastic integral,
sample paths, MSC 60H05, MSC 60G44, MSC 60G07
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MathFin
namespace ItoIntegralProcessContinuousModification

open ItoIntegralL2 ItoIntegralCLM ItoIntegralProcess ItoIntegralProcessGeneral

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)

include hB

/-! ## Phase 1 — the maximal estimate -/

/-- **Continuous-time weak-type maximal bound** for the elementary Itô integral.
The process `t ↦ (V ● B)_t` is a continuous `L²` martingale (B1a's martingale
property + B3's path continuity), so Degenne's continuous-time maximal inequality
`maximal_ineq_norm` applies directly at `n := T`, where `⨆ i : Set.Iic T` is the
running supremum over the whole interval `[0,T]`. -/
theorem itoSimpleProcess_maximal_weak (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ (natFiltration hBmeas)) (T : ℝ≥0) (ε : ℝ) :
    ε • μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖}
      ≤ ∫ ω in {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V i ω‖},
          ‖itoSimpleProcess hBmeas V T ω‖ ∂μ :=
  maximal_ineq_norm (itoSimpleProcess_isMartingale hB hBmeas V) ε T
    (fun ω _ ↦ (itoSimpleProcess_pathContinuous hBmeas hBcont V ω).continuousWithinAt)

/-- **Chebyshev form** of the maximal bound, with the `L²` terminal norm on the right. For a
`T`-bounded simple process `V`, the probability that the running maximum of `(V ● B)` over `[0,T]`
reaches `ε` is at most `ε⁻¹ · ‖simpleAssemblyHorizon V‖`: combine the weak bound with
`∫_S ‖(V●B)_T‖ ≤ ∫ ‖(V●B)_T‖ ≤ ‖(V●B)_T‖_{L²}` (set-integral monotonicity + `L¹ ≤ L²` on the
probability space) and the terminal Itô isometry `‖(V●B)_T‖_{L²} = ‖simpleAssemblyHorizon V‖`. -/
theorem itoSimpleProcess_maximal_prob (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (T : ℝ≥0) (V : TBoundedSP T hBmeas) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖}
      ≤ ε⁻¹ * ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖ := by
  set f := itoSimpleProcess hBmeas V.val T
  set S := {ω | ε ≤ ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas V.val i ω‖}
  have hf : MemLp f 2 μ := memLp_itoSimpleProcess hB hBmeas V.val T
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hweak := itoSimpleProcess_maximal_weak hB hBmeas hBcont V.val T ε
  -- ∫_S ‖f‖ ≤ ∫ ‖f‖
  have hsub : ∫ ω in S, ‖f ω‖ ∂μ ≤ ∫ ω, ‖f ω‖ ∂μ :=
    setIntegral_le_integral hfi.norm (ae_of_all _ fun ω ↦ norm_nonneg _)
  -- ∫ ‖f‖ ≤ ‖f‖_{L²} = ‖itoSimpleProcessLp V T‖
  have hL2 : ∫ ω, ‖f ω‖ ∂μ ≤ ‖itoSimpleProcessLp hB hBmeas V.val T‖ := by
    rw [itoSimpleProcessLp, Lp.norm_toLp,
      ← ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_eNorm hfi,
      ← eLpNorm_one_eq_lintegral_eNorm hfi.aestronglyMeasurable]
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  -- terminal Itô isometry on the simple embedding
  have hterm : ‖itoSimpleProcessLp hB hBmeas V.val T‖ =
      ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖ := by
    rw [← itoProcessCLM_simpleAssemblyHorizon hB T T hBmeas V,
      itoProcessCLM_norm_terminal hB T hBmeas]
  -- assemble: ε * μ.real S ≤ ‖simpleAssemblyHorizon V‖, then divide by ε > 0
  rw [smul_eq_mul] at hweak
  have hchain : ε * μ.real S ≤ ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖ :=
    hweak.trans (hsub.trans (hL2.trans_eq hterm))
  calc μ.real S = ε⁻¹ * (ε * μ.real S) := by
        rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ ε⁻¹ * ‖simpleAssemblyHorizon (μ := μ) T hBmeas V‖ :=
        mul_le_mul_of_nonneg_left hchain (inv_nonneg.mpr hε.le)

/-! ## Phase 2 — approximating subsequence, Borel–Cantelli, continuous limit -/

omit hB in
/-- **Fast approximating subsequence.** By density of the simple-process
embedding (`simpleAssemblyHorizon_denseRange`), every predictable integrand `φ` is
approximated by `T`-bounded simple processes `Vₙ` with
`‖simpleAssemblyHorizon Vₙ − φ‖ ≤ 2⁻ⁿ`. -/
theorem approxSeq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∃ V : ℕ → TBoundedSP T hBmeas,
      ∀ n, ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
  have hd := simpleAssemblyHorizon_denseRange (μ := μ) T hBmeas
  have hex : ∀ n : ℕ, ∃ V : TBoundedSP T hBmeas,
      ‖simpleAssemblyHorizon (μ := μ) T hBmeas V - φ‖ ≤ (2⁻¹ : ℝ) ^ n := by
    intro n
    obtain ⟨V, hV⟩ := hd.exists_dist_lt φ (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ n)
    exact ⟨V, by rw [← dist_eq_norm, dist_comm]; exact hV.le⟩
  choose V hV using hex
  exact ⟨V, hV⟩

omit hB in
/-- The elementary process Itô integral is **subtractive** in the simple
process (from B1a's `itoSimpleProcess_add` / `_neg`). -/
lemma itoSimpleProcess_sub (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration hBmeas)) (t : ℝ≥0) :
    itoSimpleProcess hBmeas (V - W) t
      = itoSimpleProcess hBmeas V t - itoSimpleProcess hBmeas W t := by
  rw [sub_eq_add_neg, itoSimpleProcess_add, itoSimpleProcess_neg, ← sub_eq_add_neg]

/-- **Summable maximal tail.** For the fast subsequence `V` (`approxSeq`), the
probabilities that the running max of the consecutive difference
`(Vₙ − Vₙ₊₁) ● B` over `[0,T]` reaches `εₙ := (3/4)ⁿ` are summable: each is
`≤ εₙ⁻¹ · ‖simpleAssemblyHorizon (Vₙ − Vₙ₊₁)‖ ≤ εₙ⁻¹ · 2·2⁻ⁿ = 2·(2/3)ⁿ`. The choice
`εₙ = (3/4)ⁿ ∈ (2⁻¹, 1)ⁿ` makes both `Σ εₙ⁻¹·2⁻ⁿ` and `Σ εₙ` converge. -/
theorem summable_maximal_tail (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    Summable (fun n ↦ μ.real {ω | (3 / 4 : ℝ) ^ n ≤
      ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖}) := by
  refine Summable.of_nonneg_of_le (fun n ↦ measureReal_nonneg) (fun n ↦ ?_)
    ((summable_geometric_of_lt_one (r := 2 / 3) (by norm_num) (by norm_num)).mul_left 2)
  -- per-term: μ.real {…} ≤ 2 * (2/3)ⁿ
  refine (itoSimpleProcess_maximal_prob hB hBmeas hBcont T (V n - V (n + 1))
    (ε := (3 / 4 : ℝ) ^ n) (by positivity)).trans ?_
  have hnorm : ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n - V (n + 1))‖ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
    rw [map_sub]
    calc ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n)
          - simpleAssemblyHorizon (μ := μ) T hBmeas (V (n + 1))‖
        ≤ ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - φ‖
            + ‖φ - simpleAssemblyHorizon (μ := μ) T hBmeas (V (n + 1))‖ := by
          have h := norm_add_le (simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - φ)
            (φ - simpleAssemblyHorizon (μ := μ) T hBmeas (V (n + 1)))
          simpa using h
      _ ≤ (2⁻¹ : ℝ) ^ n + (2⁻¹ : ℝ) ^ (n + 1) := by
          gcongr
          · exact hV n
          · rw [norm_sub_rev]; exact hV (n + 1)
      _ ≤ 2 * (2⁻¹ : ℝ) ^ n := by
          rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) n]
  calc ((3 / 4 : ℝ) ^ n)⁻¹ * ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n - V (n + 1))‖
      ≤ ((3 / 4 : ℝ) ^ n)⁻¹ * (2 * (2⁻¹ : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 2 * (2 / 3 : ℝ) ^ n := by
        rw [← inv_pow, mul_comm (2 : ℝ) ((2⁻¹ : ℝ) ^ n), ← mul_assoc, ← mul_pow,
          show ((3 / 4 : ℝ)⁻¹ * 2⁻¹) = 2 / 3 from by norm_num, mul_comm]

/-- **A.s. eventual smallness (Borel–Cantelli).** Since the maximal tail is
summable, for almost every `ω` the running maximum of the consecutive difference
`(Vₙ − Vₙ₊₁) ● B` over `[0,T]` is eventually below `(3/4)ⁿ`. This is the pathwise
input to the uniform-Cauchy argument. -/
theorem ae_eventually_sup_lt (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (V : ℕ → TBoundedSP T hBmeas)
    (hV : ∀ n, ‖simpleAssemblyHorizon (μ := μ) T hBmeas (V n) - φ‖ ≤ (2⁻¹ : ℝ) ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      (⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖) < (3 / 4 : ℝ) ^ n := by
  set A : ℕ → Set Ω := fun n ↦ {ω | (3 / 4 : ℝ) ^ n ≤
    ⨆ i : Set.Iic T, ‖itoSimpleProcess hBmeas (V n - V (n + 1)).val i ω‖} with hA
  have hconv : (∑' n, μ (A n)) ≠ ∞ := by
    have heq : ∀ n, μ (A n) = ENNReal.ofReal (μ.real (A n)) :=
      fun n ↦ (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ measureReal_nonneg)
      (summable_maximal_tail hB T hBmeas hBcont φ V hV)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hconv] with ω hω
  filter_upwards [hω] with n hn
  rwa [hA, Set.mem_ofPred_eq, not_le] at hn

/-! ## Phase 3 — continuous limit, modification, capstone -/

omit hB in
/-- **The running-max keystone.** For `i ≤ T`, the value `‖(W ● B)_i ω‖` is
bounded by the running maximum over `[0,T]`. The supremum is genuine (not the
junk value of an unbounded family): `(W ● B)_· ω` is continuous (B3) and `[0,T]`
is compact, so the family is bounded above. This unlocks the pointwise control of
consecutive differences. -/
lemma norm_le_iSup_Iic (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (W : SimpleProcess ℝ (natFiltration hBmeas)) (ω : Ω) {i : ℝ≥0} (hi : i ≤ T) :
    ‖itoSimpleProcess hBmeas W i ω‖
      ≤ ⨆ j : Set.Iic T, ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ := by
  have hcont : Continuous fun j : Set.Iic T ↦ ‖itoSimpleProcess hBmeas W (j : ℝ≥0) ω‖ :=
    (continuous_norm.comp (itoSimpleProcess_pathContinuous hBmeas hBcont W ω)).comp
      continuous_subtype_val
  have hIic : (Set.Iic T : Set ℝ≥0) = Set.Icc 0 T := by
    ext x; simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
  have : CompactSpace (Set.Iic T) := isCompact_iff_compactSpace.mp (hIic ▸ isCompact_Icc)
  exact le_ciSup (isCompact_range hcont).bddAbove ⟨i, hi⟩

omit hB in
/-- The pathwise limit process: for each `t, ω` the limit (if it exists) of the
approximating simple integrals `(Vₙ ● B)_t ω`, junk off the convergence set. The
subsequence `Vₙ` is `approxSeq`'s choice for `φ`. -/
noncomputable def itoContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω

/-- **Pointwise a.s. convergence.** For almost every `ω` and every `t ≤ T`, the
approximating sequence `(Vₙ ● B)_t ω` converges to `itoContinuousMod φ t ω`. The
consecutive distances are eventually `< (3/4)ⁿ` (a.s., uniformly in `t ≤ T`, by
`ae_eventually_sup_lt` + the running-max keystone + linearity), hence summable,
so the sequence is Cauchy in the complete space `ℝ`. -/
theorem itoContinuousMod_tendsto (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0, t ≤ T →
      Tendsto (fun n ↦ itoSimpleProcess hBmeas ((approxSeq T hBmeas φ).choose n).val t ω) atTop
        (𝓝 (itoContinuousMod T hBmeas φ t ω)) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [ae_eventually_sup_lt hB T hBmeas hBcont φ V hV] with ω hω
  intro t ht
  have hcauchy : CauchySeq (fun n ↦ itoSimpleProcess hBmeas (V n).val t ω) := by
    apply cauchySeq_of_summable_dist
    obtain ⟨N, hN⟩ := eventually_atTop.mp hω
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n ↦ dist_nonneg) (fun n ↦ ?_)
      (f := fun n ↦ (3 / 4 : ℝ) ^ (n + N)) ?_
    · rw [dist_eq_norm]
      have hcoe : ((V (n + N) - V (n + N + 1)).val : SimpleProcess ℝ (natFiltration hBmeas))
          = (V (n + N)).val - (V (n + N + 1)).val := rfl
      have hlin : itoSimpleProcess hBmeas (V (n + N)).val t ω
            - itoSimpleProcess hBmeas (V (n + N + 1)).val t ω
          = itoSimpleProcess hBmeas (V (n + N) - V (n + N + 1)).val t ω := by
        rw [hcoe]
        exact (congrFun (itoSimpleProcess_sub hBmeas (V (n + N)).val (V (n + N + 1)).val t) ω).symm
      rw [hlin]
      exact (norm_le_iSup_Iic T hBmeas hBcont (V (n + N) - V (n + N + 1)).val ω ht).trans
        (hN (n + N) (Nat.le_add_left N n)).le
    · simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  simpa only [itoContinuousMod, hVdef] using hcauchy.tendsto_limUnder

/-- **The modification (Task 7).** For every `t ≤ T`, the pathwise limit `itoContinuousMod φ t`
agrees almost everywhere with the `L²` process value `itoProcessCLM T t φ`. Two convergences to
compare: `Fₙ → itoContinuousMod` a.e. (pointwise, above) and `Fₙ → itoProcessCLM T t φ` in measure
(from the `L²` convergence
`itoSimpleProcessLp Vₙ t = itoProcessCLM T t (simpleAssemblyHorizon Vₙ) → itoProcessCLM T t φ`, via
the bridge + CLM continuity). In-measure limits are a.e.-unique. -/
theorem itoContinuousMod_modification (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) {t : ℝ≥0} (ht : t ≤ T) :
    (fun ω ↦ itoContinuousMod T hBmeas φ t ω) =ᵐ[μ] itoProcessCLM hB T t hBmeas φ := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  set F : ℕ → Ω → ℝ := fun n ω ↦ itoSimpleProcess hBmeas (V n).val t ω
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) μ :=
    fun n ↦ (memLp_itoSimpleProcess hB hBmeas (V n).val t).aestronglyMeasurable
  -- (a) F → itoContinuousMod a.e. ⟹ in measure
  have hmeasG : TendstoInMeasure μ F atTop (fun ω ↦ itoContinuousMod T hBmeas φ t ω) := by
    refine tendstoInMeasure_of_tendsto_ae hFmeas ?_
    filter_upwards [itoContinuousMod_tendsto hB T hBmeas hBcont φ] with ω hω using hω t ht
  -- (b) F → ⇑(itoProcessCLM T t φ) in measure, from L² convergence
  have hsa : Tendsto (fun n ↦ simpleAssemblyHorizon (μ := μ) T hBmeas (V n)) atTop (𝓝 φ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n ↦ norm_nonneg _) hV
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hLp : Tendsto (fun n ↦ itoSimpleProcessLp hB hBmeas (V n).val t) atTop
      (𝓝 (itoProcessCLM hB T t hBmeas φ)) := by
    have hrw : (fun n ↦ itoSimpleProcessLp hB hBmeas (V n).val t)
        = fun n ↦ itoProcessCLM hB T t hBmeas (simpleAssemblyHorizon (μ := μ) T hBmeas (V n)) :=
      funext fun n ↦ (itoProcessCLM_simpleAssemblyHorizon hB T t hBmeas (V n)).symm
    rw [hrw]
    exact ((itoProcessCLM hB T t hBmeas).continuous.tendsto φ).comp hsa
  have heLp : Tendsto (fun n ↦ eLpNorm (F n - ⇑(itoProcessCLM hB T t hBmeas φ)) 2 μ)
      atTop (𝓝 0) := by
    refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F
      (fun n ↦ memLp_itoSimpleProcess hB hBmeas (V n).val t)
      (⇑(itoProcessCLM hB T t hBmeas φ)) (Lp.memLp _)).mp ?_
    simp only [Lp.toLp_coeFn]
    exact hLp
  have hmeasH : TendstoInMeasure μ F atTop (⇑(itoProcessCLM hB T t hBmeas φ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) heLp
  exact tendstoInMeasure_ae_unique hmeasG hmeasH

omit hB in
/-- Consecutive-difference bound combining linearity with the running-max keystone:
for `t ≤ T`, `‖(Vₐ ● B)_t − (Vₐ₊₁ ● B)_t‖` is at most the running max of
`(Vₐ − Vₐ₊₁) ● B` over `[0,T]`. -/
lemma consecutive_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω) (V : ℕ → TBoundedSP T hBmeas)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) (a : ℕ) :
    ‖itoSimpleProcess hBmeas (V a).val t ω - itoSimpleProcess hBmeas (V (a + 1)).val t ω‖
      ≤ ⨆ j : Set.Iic T, ‖itoSimpleProcess hBmeas (V a - V (a + 1)).val (j : ℝ≥0) ω‖ := by
  have hcoe : ((V a - V (a + 1)).val : SimpleProcess ℝ (natFiltration hBmeas))
      = (V a).val - (V (a + 1)).val := rfl
  rw [show itoSimpleProcess hBmeas (V a).val t ω - itoSimpleProcess hBmeas (V (a + 1)).val t ω
        = itoSimpleProcess hBmeas (V a - V (a + 1)).val t ω from by
      rw [hcoe]; exact (congrFun (itoSimpleProcess_sub hBmeas (V a).val (V (a + 1)).val t) ω).symm]
  exact norm_le_iSup_Iic T hBmeas hBcont (V a - V (a + 1)).val ω ht

/-- **Pathwise continuity (the rest of Task 6).** For almost every `ω`, the pathwise limit
`t ↦ itoContinuousMod φ t ω` is continuous on `[0,T]`. The approximating continuous paths
`(Vₙ ● B)_· ω` (B3) converge to it *uniformly* on `[0,T]`: the running max gives
`‖itoContinuousMod φ t ω − (Vₙ ● B)_t ω‖ ≤ 4·(3/4)ⁿ` for all `t ≤ T` once `n` is large (geometric
tail of the consecutive differences, uniform in `t`). A uniform limit of continuous functions is
continuous. -/
theorem itoContinuousMod_continuousOn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ itoContinuousMod T hBmeas φ t ω) (Set.Icc 0 T) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [ae_eventually_sup_lt hB T hBmeas hBcont φ V hV,
    itoContinuousMod_tendsto hB T hBmeas hBcont φ] with ω hω htends
  rw [show (Set.Icc 0 T : Set ℝ≥0) = Set.Iic T from by
    ext x; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have huniform : TendstoUniformlyOn (fun n t ↦ itoSimpleProcess hBmeas (V n).val t ω)
      (fun t ↦ itoContinuousMod T hBmeas φ t ω) atTop (Set.Iic T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htend0 : Tendsto (fun n ↦ 4 * (3 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 4 * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    filter_upwards [eventually_ge_atTop N, htend0.eventually_lt_const hε] with n hn hnε
    intro t ht
    rw [Set.mem_Iic] at ht
    rw [dist_comm]
    -- the uniform bound: dist (fₙ t ω) (X t ω) ≤ 4·(3/4)ⁿ
    have htendsto : Tendsto (fun k ↦ itoSimpleProcess hBmeas (V (k + n)).val t ω) atTop
        (𝓝 (itoContinuousMod T hBmeas φ t ω)) := (htends t ht).comp (tendsto_add_atTop_nat n)
    have hstep : ∀ k, dist (itoSimpleProcess hBmeas (V (k + n)).val t ω)
        (itoSimpleProcess hBmeas (V (k + 1 + n)).val t ω) ≤ (3 / 4 : ℝ) ^ n * (3 / 4 : ℝ) ^ k := by
      intro k
      rw [show k + 1 + n = (k + n) + 1 from by ring, dist_eq_norm]
      refine (consecutive_norm_le T hBmeas hBcont V ω ht (k + n)).trans ?_
      exact (hN (k + n) (hn.trans (Nat.le_add_left n k))).le.trans
        (le_of_eq (by rw [pow_add]; ring))
    have h0 :=
      dist_le_of_le_geometric_of_tendsto₀ (3 / 4) ((3 / 4 : ℝ) ^ n) (by norm_num) hstep htendsto
    simp only [zero_add] at h0
    refine lt_of_le_of_lt (h0.trans (le_of_eq ?_)) hnε
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 from by norm_num]; ring
  have hcont : ∀ᶠ n in atTop,
      ContinuousOn (fun t ↦ itoSimpleProcess hBmeas (V n).val t ω) (Set.Iic T) :=
    Eventually.of_forall fun n ↦
      (itoSimpleProcess_pathContinuous hBmeas hBcont (V n).val ω).continuousOn
  exact huniform.continuousOn hcont.frequently

/-! ## Phase 4 — the headline existence theorem (the gate) -/

/-- **The continuous modification of the general-integrand Itô process on `[0,T]`
exists (the gate).** There is a process `X : ℝ≥0 → Ω → ℝ` that (i) agrees almost
everywhere with the `L²` process value `itoProcessCLM T t φ` at every `t ≤ T` — a
**modification** — and (ii) has almost-surely continuous paths on `[0,T]`. This is
the first pathwise-regularity result for the general integrand, and the
localization gateway for the unbounded-coefficient Itô calculus. -/
theorem exists_continuous_modification_itoProcess (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure (μ := μ) T hBmeas)) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, t ≤ T → X t =ᵐ[μ] itoProcessCLM hB T t hBmeas φ) ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc 0 T)) :=
  ⟨itoContinuousMod T hBmeas φ,
    fun _ ht ↦ itoContinuousMod_modification hB T hBmeas hBcont φ ht,
    itoContinuousMod_continuousOn hB T hBmeas hBcont φ⟩

end ItoIntegralProcessContinuousModification
end MathFin
