/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main
public import LeanPool.RareSubtreePatterns.ExtremesAnalysis.Rary
public import LeanPool.RareSubtreePatterns.Extremes.Ineqs
public import LeanPool.RareSubtreePatterns.Declumping.Conditioned
public import LeanPool.RareSubtreePatterns.Applications.CompleteArySC
public import LeanPool.RareSubtreePatterns.Bridge.Microscopic
public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof

/-!
# Theorem `thm:max_string`: the maximal complete non-fringe `r`-ary height

Source lines 475–521 (statement), 2800–2897 (proof, inventory P20). The target is the reviewed
statement `PoissonDeclumping.MaxStringStatement` of `Statements/Main.lean`. The final theorem
`maxString_of` takes Theorems `thm:PoissonApproximation` and `thm:PoissonApproximation2` as
hypotheses of exactly their reviewed statement types (`PoissonApproximationStatement`,
`PoissonApproximation2Statement`); everything else is proved from the hypothesis
`InStableDomain μ` (through `Stable.stableToolkit`).

All marks are `G_k = 1{H_{r,k} ≺ ·}` (`Embeds (completeTree r k)`), with
`π_k = μ_1^k` (`r = 1`) or `μ_r^{(r^k-1)/(r-1)}` (`r ≥ 2`), and the cutoff is
`M_n = max 1 ⌊n^{1-η}⌋₊` with `η = (1 - 1/α)/2` (correction F11). All limits run along
admissible sizes.

* (i) `maxString_unary_of` (`μ_1 > 0`): level `k_n = (⌊t_n^* + t⌋ + 1).toNat` (the level may be
  nonpositive for finitely many `n`; `{H_1 ≤ ⌊t_n^* + t⌋} = {N_{k_n} = 0}` holds for every `n`,
  `setOf_natCast_le_eq`). Raw (S) by Lemma `lem:S_rary`(i) (`k_n = O(log n)`), declumped (C) by
  Lemma `lem:C_rary` with `B = {d | d ≠ 1}`, `c_B = 1 - μ_1` (`cB_ne_one`), propagation
  (`propagatesOutside_completeTree_one`), `n π_{k_n}` bounded; Theorem
  `thm:PoissonApproximation2`(i) gives the declumped Poisson approximation, Corollary `cor:SM`(iii)
  the vanishing root mark (`π_{k_n} = O(1/n)`), Lemma `lem:declump_to_raw` the raw zero event
  (this is the paper's Corollary `cor:declump_zero`), and the exact lattice identity
  `n (1 - μ_1) μ_1^{⌊t_n^*+t⌋+1} = μ_1^{t+1-{t_n^*+t}}` the limit.
* (ii) `maxString_rary_of` (`r ≥ 2`, `μ_r > 0`): the thresholds `eq:threshold_rary`.
  Upper (`tendsto_le_maxCompleteHeight_zero`): Markov (Lemma `lem:ineqs`) with
  `E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` (Corollary `cor:SM`(ii)). Lower
  (`tendsto_le_maxCompleteHeight_one`): Theorem `thm:PoissonApproximation`(ii) with (M) from
  Corollary `cor:SM`(i) and (C) from Lemma `lem:S_rary`(ii) — **correction F8**: the source cites
  Corollary `cor:Non-fringe Poisson`(ii), whose uniform pair hypothesis is not established; the
  summed pair bound of Lemma `lem:S_rary`(ii) is exactly Assumption (C) of Theorem
  `thm:PoissonApproximation`. The two-point set is handled without the paper's split at
  `θ_n = 1/2`: `J_n = {a_n, a_n + 1}` with `a_n = twoPointLow t_n^{**}`, `n π_{a_n} → ∞`,
  `n π_{a_n+2} → 0` (`ExtremesAnalysis.rary_twoPoint_thresholds`), and
  `P(H_r ∈ J_n) ≥ P(H_r ≥ a_n) - P(H_r ≥ a_n + 2)`; the interior phase uses the levels `m_n`,
  `m_n + 1`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping
namespace Extremes

open PlaneTree

/-- `c_B = 1 - μ_1` for `B = {d | d ≠ 1}` (criticality: `∑ j μ_j = 1`). -/
theorem cB_ne_one {μ : PMF ℕ} (hc : IsCritical μ) : cB μ {d | d ≠ 1} = 1 - μ 1 := by
  classical
  have h := ENNReal.tsum_eq_add_tsum_ite (f := fun j : ℕ => (j : ℝ≥0∞) * μ j) 1
  have hc' : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1 := hc
  rw [hc'] at h
  have hcB : cB μ {d | d ≠ 1} = ∑' x : ℕ, ite (x = 1) 0 ((x : ℝ≥0∞) * μ x) := by
    refine tsum_congr fun j => ?_
    by_cases hj : j = 1
    · simp [hj]
    · rw [Set.indicator_of_mem (show j ∈ {d : ℕ | d ≠ 1} from hj), ite_eq_right hj]
  rw [hcB]
  refine ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top μ 1) ?_
  rw [add_comm, h, Nat.cast_one, one_mul]
  congr 1
  exact tsum_congr fun x => by split_ifs <;> rfl

/-- `0 < μ_r < 1` in real form, for `μ_r > 0` and `μ_r ≠ 1`. -/
theorem pmf_toReal_mem_Ioo {μ : PMF ℕ} {r : ℕ} (h0 : 0 < μ r) (h1 : μ r ≠ 1) :
    0 < (μ r).toReal ∧ (μ r).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos h0.ne' (PMF.apply_ne_top μ r), ?_⟩
  have hlt : μ r < 1 := lt_of_le_of_ne (PMF.coe_le_one μ r) h1
  have := (ENNReal.toReal_lt_toReal (PMF.apply_ne_top μ r) ENNReal.one_ne_top).2 hlt
  simpa using this

/-- Propagation for the unary marks: if a child of a vertex of outdegree `1` carries a unary
chain of height `k`, so does the vertex. -/
theorem propagatesOutside_completeTree_one (k : ℕ) :
    PropagatesOutside {d | d ≠ 1} (Embeds (completeTree 1 k)) := by
  intro T U hU hGU hdeg
  have hdeg' : T.rootDegree = 1 := by
    simpa only [Set.mem_ofPred_eq, not_not] using hdeg
  refine embeds_completeTree_of_succ le_rfl ((embeds_completeTree_succ_iff le_rfl k T).2
    ⟨hdeg', fun V hV => ?_⟩)
  obtain ⟨W, hW⟩ := List.length_eq_one_iff.1 (show T.children.length = 1 from hdeg')
  rw [hW, List.mem_singleton] at hU hV
  rw [hV, ← hU]
  exact hGU

/-- The cutoff exponent `η = (1 - 1/α)/2 ∈ (0, 1 - 1/α)`. -/
theorem cutoff_exponent {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) :
    (0 < (1 - 1 / α) / 2 ∧ (1 - 1 / α) / 2 < 1 - 1 / α) ∧ (1 - 1 / α) / 2 < 1 := by
  have h1 := hT.rho_lt_one
  have h0 := hT.rho_pos
  refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- `{H_r(T) ≤ m} = {N_{(m+1).toNat}(T) = 0}` for every integer `m` (`r ≥ 1`). -/
theorem setOf_natCast_le_eq {r : ℕ} (hr : 1 ≤ r) (m : ℤ) :
    {T : PlaneTree | ((maxCompleteHeight r T : ℕ) : ℤ) ≤ m} =
      {T | markCount (Embeds (completeTree r (m + 1).toNat)) T = 0} := by
  ext T
  simp only [Set.mem_ofPred_eq, ExtremesAnalysis.natCast_le_iff_not_toNat_le,
    le_maxCompleteHeight_iff_markCount_pos hr, not_lt, Nat.le_zero]

/-- **Theorem `thm:max_string`(i)** (source lines 477–485, proof 2808–2850), conditional on
Theorem `thm:PoissonApproximation2` (`PoissonApproximation2Statement`, its part (i)). -/
theorem maxString_unary_of (h2 : PoissonApproximation2Statement) (μ : PMF ℕ)
    (hμ : InStableDomain μ) (hμ1 : 0 < μ 1) :
    LatticeGumbel μ (maxCompleteHeight 1) (μ 1).toReal (tStar (μ 1).toReal) := by
  obtain ⟨α, a, hSD⟩ := hμ
  have hT := Stable.stableToolkit hSD
  obtain ⟨hq0, hq1⟩ := pmf_toReal_mem_Ioo hμ1 hT.nondegenerate
  have hlt : μ 1 < 1 := lt_of_le_of_ne (PMF.coe_le_one μ 1) hT.nondegenerate
  set q := (μ 1).toReal with hq
  obtain ⟨hη, hη1⟩ := cutoff_exponent hT
  set η := (1 - 1 / α) / 2 with hη_def
  have hM : IsCutoff (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) :=
    Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  intro t
  set k : ℕ → ℕ := fun n => (⌊tStar q n + t⌋ + 1).toNat with hk_def
  set G : ℕ → PlaneTree → Prop := fun j => Embeds (completeTree 1 j) with hG_def
  set B : Set ℕ := {d | d ≠ 1} with hB_def
  -- `π_k = μ_1^k`
  have hπ : ∀ n, markProb μ G k n = q ^ k n := fun n =>
    bienayme_real_embeds_completeTree_one hT.critical hT.nondegenerate (k n)
  -- Assumption (S) for the raw marks (Lemma `lem:S_rary`(i), `k_n = O(log n)`)
  have hlev : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (k n : ℝ) ≤ (n : ℝ) ^ δ :=
    fun δ hδ => Eventually.filter_mono hl (ExtremesAnalysis.unaryLevel_le_rpow hq0 hq1
      (a := Real.log (1 - q)) (fun n => rfl) t δ hδ)
  have hS : StructuralMicroscopic μ a G k (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) :=
    Applications.lem_S_rary_i_one hT hη hlev
  -- Assumption (C) for the declumped marks (Lemma `lem:C_rary`)
  have hC : NonClustering μ (fun j => declumpedMark B (G j)) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) :=
    Applications.lem_C_rary hT.critical hT.nondegenerate 1 k _ hM.isLittleO
  -- `c_B = 1 - μ_1`
  have hcB : cB μ B = 1 - μ 1 := cB_ne_one hT.critical
  have hcB0 : 0 < cB μ B := by rw [hcB]; exact tsub_pos_of_lt hlt
  have hcBtop : cB μ B < ∞ := by
    rw [hcB]; exact lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top
  have hcBreal : (cB μ B).toReal = 1 - q := by
    rw [hcB, ENNReal.toReal_sub_of_le hlt.le ENNReal.one_ne_top, ENNReal.toReal_one]
  -- `n π_{k_n}` is bounded
  obtain ⟨K, hK⟩ := ExtremesAnalysis.tStar_exists_eventually_mul_le hq0 hq1 t
  have hbdd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C :=
    ⟨K, (hK.filter_mono hl).mono fun n hn => by rw [hπ]; exact hn⟩
  -- Theorem `thm:PoissonApproximation2`(i): the declumped count is close to `Po(c_B n π)`
  have htv := (h2 μ α a hSD G k _ hM B hcB0 hcBtop hS hC).1 hbdd
  -- the root is marked with vanishing probability (`π_{k_n} = O(1/n)`)
  have hO : markProb μ G k =O[admissibleSizes μ] (fun n => 1 / (n : ℝ)) := by
    obtain ⟨C, hC⟩ := hbdd
    refine IsBigO.of_bound C ?_
    filter_upwards [hC, hl (eventually_ge_atTop 1)] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hp0 : 0 ≤ markProb μ G k n := measureReal_nonneg
    rw [Real.norm_of_nonneg hp0,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n),
      mul_one_div, le_div_iff₀ hn0, mul_comm]
    exact hn
  have hroot := Bridge.conditioned_mark_tendsto_zero hT hM hS hO
  -- Lemma `lem:declump_to_raw`
  have hmain := conditioned_declump_to_raw μ B (fun n => G (k n))
    (fun n => Real.toNNReal ((cB μ B).toReal * ((n : ℝ) * markProb μ G k n)))
    (fun n => propagatesOutside_completeTree_one (k n)) hroot htv
  have hexp := (ExtremesAnalysis.tStar_tendsto_exp_sub hq0 hq1 t).mono_left hl
  have hsum := (show Tendsto _ (admissibleSizes μ) _ from hmain).add hexp
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  have hrate : ((Real.toNNReal ((cB μ B).toReal * ((n : ℝ) * markProb μ G k n)) : ℝ≥0) : ℝ) =
      (1 - q) * ((n : ℝ) * q ^ k n) := by
    rw [Real.coe_toNNReal _ (by rw [hcBreal, hπ]; have := hq1.le; positivity), hcBreal, hπ]
  simp only [hrate]
  rw [setOf_natCast_le_eq le_rfl]
  ring

/-! ### Theorem `thm:max_string`(ii): thresholds -/

/-- `{H_r(T) ≥ k} = {N_k(T) ≥ 1}` (`r ≥ 1`), in the real form used by Lemma `lem:ineqs`. -/
theorem le_maxCompleteHeight_iff_one_le {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) (k : ℕ) :
    ((k : ℤ) ≤ ((maxCompleteHeight r T : ℕ) : ℤ)) ↔
      (1 : ℝ) ≤ (markCount (Embeds (completeTree r k)) T : ℝ) := by
  rw [Nat.cast_le, le_maxCompleteHeight_iff_markCount_pos hr, Nat.one_le_cast,
    Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- At an admissible size, `∫⁻ N(𝒯^n) = ENNReal.ofReal (E[N(𝒯^n)])`. -/
theorem lintegral_markCount_eq_ofReal {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n)
    (G : PlaneTree → Prop) :
    ∫⁻ T, ENNReal.ofReal (markCount G T : ℝ) ∂conditioned μ n =
      ENNReal.ofReal (∫ T, (markCount G T : ℝ) ∂conditioned μ n) := by
  have := Cyclic.isProbabilityMeasure_uniformFringeLaw hn
  simp only [ENNReal.ofReal_natCast]
  rw [Cyclic.lintegral_markCount_conditioned, Cyclic.integral_markCount_conditioned,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Upper threshold** (first implication of `eq:threshold_rary`, source lines 2860–2872): if
`r^{k_n} = n^{o(1)}` and `n π_{k_n} → 0` along admissible sizes, then
`P(H_r(𝒯^n) ≥ k_n) → 0`. Lemma `lem:ineqs` (first half, Markov) with
`E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}` (Lemma `lem:S_rary`(i) and Corollary `cor:SM`(ii)). -/
theorem tendsto_le_maxCompleteHeight_zero {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (hT : StableToolkit μ α a) {r : ℕ} (hr : 2 ≤ r) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (r : ℝ) ^ k n ≤ (n : ℝ) ^ δ)
    (hπ : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => Embeds (completeTree r j)) k n)
      (admissibleSizes μ) (𝓝 0)) :
    Tendsto (fun n => (conditioned μ n).real {T | k n ≤ maxCompleteHeight r T})
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨hη, hη1⟩ := cutoff_exponent hT
  have hM := Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  have hS := Applications.lem_S_rary_i_of_two_le hT hr hη hk
  have hE := (Bridge.integral_markCount_isEquivalent hT hM hS).symm.tendsto_nhds hπ
  have hE' : Tendsto (fun n => ∫⁻ T, ENNReal.ofReal
      (markCount (Embeds (completeTree r (k n))) T : ℝ) ∂conditioned μ n)
      (admissibleSizes μ) (𝓝 0) := by
    have h := (ENNReal.tendsto_ofReal hE)
    rw [ENNReal.ofReal_zero] at h
    refine h.congr' ?_
    filter_upwards [PlaneTree.eventually_admissible μ] with n hn
    exact (lintegral_markCount_eq_ofReal hn _).symm
  have h := tendsto_zero_of_tendsto_lintegral_zero (Ω := fun _ : ℕ => PlaneTree)
    (P := fun n => conditioned μ n) (admissibleSizes μ)
    (fun _ T => ((maxCompleteHeight r T : ℕ) : ℤ))
    (fun n T => (markCount (Embeds (completeTree r (k n))) T : ℝ)) (fun n => (k n : ℤ))
    (fun _ => Measurable.of_discrete)
    (fun n T => le_maxCompleteHeight_iff_one_le (by omega) T (k n)) hE'
  refine h.congr fun n => ?_
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, Nat.cast_le]

/-- **Lower threshold** (second implication of `eq:threshold_rary`, source lines 2860–2872,
with correction F8): if `μ_r > 0`, `r^{k_n} = n^{o(1)}` and `n π_{k_n} → ∞` along admissible sizes,
then `P(H_r(𝒯^n) ≥ k_n) → 1`. Assumption (M) comes from (S) (Lemma `lem:S_rary`(i) and
Corollary `cor:SM`(i)), Assumption (C) from the summed pair bound (Lemma `lem:S_rary`(ii)), and
`N_{k_n}(𝒯^n) → ∞` in probability from Theorem `thm:PoissonApproximation`(ii). -/
theorem tendsto_le_maxCompleteHeight_one (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {r : ℕ}
    (hr : 2 ≤ r) (hμr : 0 < μ r) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (r : ℝ) ^ k n ≤ (n : ℝ) ^ δ)
    (hπ : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => Embeds (completeTree r j)) k n)
      (admissibleSizes μ) atTop) :
    Tendsto (fun n => (conditioned μ n).real {T | k n ≤ maxCompleteHeight r T})
      (admissibleSizes μ) (𝓝 1) := by
  obtain ⟨hη, hη1⟩ := cutoff_exponent hT
  have hM := Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  have hS := Applications.lem_S_rary_i_of_two_le hT hr hη hk
  have hMic := Bridge.microscopic_of_structural hT hM hS
  have hC := Applications.lem_S_rary_ii hT.critical hT.nondegenerate (by omega) hμr
    hM.isLittleO hπ
  have h0 := ((h1 μ hμ (fun j => Embeds (completeTree r j)) k ⟨_, hM, hMic, hC⟩).2 hπ).2 0
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [PlaneTree.eventually_admissible μ] with n hn
  have := conditioned_isProbabilityMeasure hn
  have hset : {T | k n ≤ maxCompleteHeight r T} =
      {T | markCount (Embeds (completeTree r (k n))) T ≤ 0}ᶜ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, le_maxCompleteHeight_iff_markCount_pos
      (show 1 ≤ r by omega), not_le]
  rw [hset, probReal_compl_eq_one_sub MeasurableSet.of_discrete]

/-- Localization from two thresholds: if `P(E_n) → 1` and `P(F_n) → 0` along admissible sizes,
then `P(E_n \ F_n) → 1`. -/
theorem tendsto_diff_one {μ : PMF ℕ} {E F : ℕ → Set PlaneTree}
    (hE : Tendsto (fun n => (conditioned μ n).real (E n)) (admissibleSizes μ) (𝓝 1))
    (hF : Tendsto (fun n => (conditioned μ n).real (F n)) (admissibleSizes μ) (𝓝 0)) :
    Tendsto (fun n => (conditioned μ n).real (E n \ F n)) (admissibleSizes μ) (𝓝 1) := by
  have hlow := hE.sub hF
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [PlaneTree.eventually_admissible μ] with n hn
    have := conditioned_isProbabilityMeasure hn
    have h : (conditioned μ n).real (E n) ≤
        (conditioned μ n).real (E n \ F n) + (conditioned μ n).real (F n) := by
      refine (measureReal_mono (?_ : E n ⊆ (E n \ F n) ∪ F n)).trans (measureReal_union_le _ _)
      intro T hT
      by_cases hF : T ∈ F n
      · exact Or.inr hF
      · exact Or.inl ⟨hT, hF⟩
    linarith
  · filter_upwards [PlaneTree.eventually_admissible μ] with n hn
    have := conditioned_isProbabilityMeasure hn
    exact measureReal_le_one

/-- **Theorem `thm:max_string`(ii)** (source lines 486–501, proof 2851–2897), conditional on
Theorem `thm:PoissonApproximation` (`PoissonApproximationStatement`, its part (ii)), which
replaces the paper's citation of Corollary `cor:Non-fringe Poisson`(ii) (correction F8). -/
theorem maxString_rary_of (h1 : PoissonApproximationStatement) (μ : PMF ℕ)
    (hμ : InStableDomain μ) (r : ℕ) (hr : 2 ≤ r) (hμr : 0 < μ r) :
    TwoPointLocalization μ (maxCompleteHeight r) (tStarStar r (μ r).toReal) := by
  obtain ⟨α, a, hSD⟩ := id hμ
  have hT := Stable.stableToolkit hSD
  have hμr1 : μ r ≠ 1 := by
    intro h
    have hsupp := (PMF.apply_eq_one_iff μ r).1 h
    have h0 : (0 : ℕ) ∈ μ.support :=
      (PMF.mem_support_iff μ 0).2 (hT.critical.apply_zero_ne_zero hT.nondegenerate)
    rw [hsupp, Set.mem_singleton_iff] at h0
    omega
  obtain ⟨hq0, hq1⟩ := pmf_toReal_mem_Ioo hμr hμr1
  set q := (μ r).toReal with hq
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hπ : ∀ (k : ℕ → ℕ) (n : ℕ),
      markProb μ (fun j => Embeds (completeTree r j)) k n = q ^ ((r ^ k n - 1) / (r - 1)) :=
    fun k n => bienayme_real_embeds_completeTree_of_two_le hT.critical hT.nondegenerate hr (k n)
  obtain ⟨hlev1, hlev2, hlev3⟩ := ExtremesAnalysis.rary_levels_le_rpow hr hq0 hq1
  constructor
  · -- two-point localization, with `J_n = {a_n, a_n + 1}`, `a_n = twoPointLow t_n^{**}`
    obtain ⟨hlow, hup⟩ := ExtremesAnalysis.rary_twoPoint_thresholds hr hq0 hq1 hl
    have hA := tendsto_le_maxCompleteHeight_one h1 hμ hT hr hμr
      (k := fun n => (ExtremesAnalysis.twoPointLow (tStarStar r q n)).toNat)
      (fun δ hδ => (hlev1 δ hδ).filter_mono hl) (hlow.congr fun n => by rw [hπ])
    have hB := tendsto_le_maxCompleteHeight_zero hT hr
      (k := fun n => (ExtremesAnalysis.twoPointLow (tStarStar r q n) + 2).toNat)
      (fun δ hδ => (hlev2 δ hδ).filter_mono hl) (hup.congr fun n => by rw [hπ])
    refine (tendsto_diff_one hA hB).congr fun n => ?_
    congr 1
    ext T
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, ExtremesAnalysis.natCast_mem_twoPointSet_iff]
  · -- interior phase
    rintro ⟨δ, hδ, hθ⟩
    obtain ⟨hlow, hup⟩ := ExtremesAnalysis.rary_interior_thresholds hr hq0 hq1 hl hδ hθ
    have hA := tendsto_le_maxCompleteHeight_one h1 hμ hT hr hμr
      (k := fun n => (⌊tStarStar r q n⌋).toNat)
      (fun δ hδ => (hlev3 0 (by norm_num) δ hδ).filter_mono hl |>.mono fun n hn => by
        simpa only [add_zero] using hn) (hlow.congr fun n => by rw [hπ])
    have hB := tendsto_le_maxCompleteHeight_zero hT hr
      (k := fun n => (⌊tStarStar r q n⌋ + 1).toNat)
      (fun δ hδ => (hlev3 1 (by norm_num) δ hδ).filter_mono hl) (hup.congr fun n => by rw [hπ])
    refine (tendsto_diff_one hA hB).congr fun n => ?_
    congr 1
    ext T
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, ExtremesAnalysis.natCast_eq_iff]

/-- **Theorem `thm:max_string`** (source lines 475–501), conditional on Theorems
`thm:PoissonApproximation` and `thm:PoissonApproximation2` (the reviewed statements
`PoissonApproximationStatement` and `PoissonApproximation2Statement`). -/
theorem maxString_of (h1 : PoissonApproximationStatement)
    (h2 : PoissonApproximation2Statement) : MaxStringStatement :=
  fun μ hμ => ⟨maxString_unary_of h2 μ hμ, fun r hr hμr => maxString_rary_of h1 μ hμ r hr hμr⟩

end Extremes
end PoissonDeclumping
