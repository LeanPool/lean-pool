/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main
public import LeanPool.RareSubtreePatterns.ExtremesAnalysis.LeafHeightLevels
public import LeanPool.RareSubtreePatterns.Applications.LeafHeightSC

import LeanPool.RareSubtreePatterns.Bridge.Microscopic
import LeanPool.RareSubtreePatterns.Declumping.Conditioned
import LeanPool.RareSubtreePatterns.Patterns.Complete
import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
import LeanPool.RareSubtreePatterns.RootDeclumping.Lemma51
import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex

/-!
# Theorem `thm:max_lh`: the maximum leaf-height

Source: statement lines 533–586, proof lines 3253–3387 (inventory T1.4, P24). Marks
`G_k(T) = 1{λ_∅(T) ≥ k}`, raw counts `N_k(T) = ∑_{v ∈ T} G_k(T_v)` (`markCount`), declumped marks
`Ĝ_k = RootDeclumping.lhDeclumpedMark μ k` (degree set `B = {j ≥ κ + 1}`), `π_k = P(λ_∅(𝒯) ≥ k)`,
`c = 1 - κ μ_κ` (`LeafHeight.cConst μ`). The cutoff is `M_n = max 1 ⌊n^{1-η}⌋₊` with
`η = (1 - 1/α)/2 ∈ (0, 1 - 1/α)`.

The final theorem takes Theorems `thm:PoissonApproximation2` and `thm:max_string` (the paper's own
results, proved elsewhere) as hypotheses of their reviewed statement types:

* `maxLeafHeight_of_approx2_maxString : PoissonApproximation2Statement → MaxStringStatement →
  MaxLeafHeightStatement`, and `maxLeafHeight_of`, the same with an (unused) extra hypothesis
  `PoissonApproximationStatement`.

The three cases are separate exports:

* `maxLeafHeight_unary` (**(i)**, `μ_1 > 0`, source lines 3298–3326): `C_μ = leafC μ`; the levels
  `h_n = ⌊k_n^* + t⌋ + 1` satisfy (S) (`Applications.lem_S_lh`, levels from
  `ExtremesAnalysis.lh_unary_inputs`), the declumped marks satisfy (C) (`Applications.lem_C_lh`),
  `n π_{h_n}` is bounded, so Theorem `thm:PoissonApproximation2` gives the declumped Poisson
  approximation with parameter `c_B n π_{h_n}`, `c_B = 1 - μ_1`; the leaf-height marks propagate
  through parents of degree `1` (`propagatesOutside_of_kappa_eq_one`), the root mark vanishes
  (`Bridge.conditioned_mark_tendsto_zero`), and Lemma `lem:declump_to_raw`
  (`PlaneTree.conditioned_declump_to_raw`) transfers to `P(N_{h_n}(𝒯^n) = 0) = P(λ(𝒯^n) ≤ ⌊k_n^* +
    t⌋)`.
* `maxLeafHeight_superexp_of_cConst_pos` (**(ii)**, `μ_1 = 0`, `c > 0`, source lines 3328–3383):
  `eq:threshold_lh` is `tendsto_conditioned_le_leafHeight_zero` (first moment, Corollary
  `cor:SM`(ii), Markov) and `tendsto_conditioned_le_leafHeight_one` (Theorem
  `thm:PoissonApproximation2`, divergent part, and `N̂_h ≥ 1 ⇒ N_h ≥ 1 ⇔ λ ≥ h`); these are the two
  halves of Lemma `lem:ineqs`, proved here directly for the conditioned laws (probability measures
  only at admissible sizes). The levels and the thresholds are those of
  `ExtremesAnalysis.lh_twoPoint_thresholds` and `ExtremesAnalysis.lh_interior_thresholds`.
* `maxLeafHeight_of_cConst_eq_zero` (**(ii)**, `c = 0`, source lines 3274–3296): `λ = H_κ` almost
  surely under `𝒯^n` and `k_n^{**} = t_n^{**}` (`ExtremesAnalysis.lh_center_eq_tStarStar`), so the
  claim is Theorem `thm:max_string`(ii) with `r = κ`.

## Departures

* The paper's case split at `θ_n = 1/2` is replaced by the single lower level
  `ExtremesAnalysis.twoPointLow k_n^{**}` (`J_n = [a_n, a_n + 2)`), and integer levels are turned
  into natural mark indices by `Int.toNat` (`{H ≤ m} = {(m+1).toNat ≤ H}ᶜ` for every integer `m`),
  so negative floors and small `n` need no separate treatment.
* Theorem `thm:PoissonApproximation` is not needed: Theorem `thm:PoissonApproximation2` (with
  Lemma `lem:declump_to_raw` in case (i)) covers both the bounded and the divergent regime.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping
namespace MaxLeafHeight

open PlaneTree LeafHeight RootDeclumping

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- Markov's inequality for a count under the conditioned law (any `n`):
`P(N(𝒯^n) ≥ 1) ≤ E[N(𝒯^n)]`. -/
theorem conditioned_real_markCount_pos_le (μ : PMF ℕ) (n : ℕ) (G : PlaneTree → Prop) :
    (conditioned μ n).real {T | 0 < markCount G T} ≤
      ∫ T, (markCount G T : ℝ) ∂conditioned μ n := by
  have hle : conditioned μ n {T | 0 < markCount G T} ≤
      ∫⁻ T, (markCount G T : ℝ≥0∞) ∂conditioned μ n := by
    rw [← lintegral_indicator_one MeasurableSet.of_discrete]
    refine lintegral_mono fun T => ?_
    by_cases hT : 0 < markCount G T
    · rw [Set.indicator_of_mem (show T ∈ {T | 0 < markCount G T} from hT), Pi.one_apply]
      exact Nat.one_le_cast.mpr hT
    · rw [Set.indicator_of_notMem (show T ∉ {T | 0 < markCount G T} from hT)]
      exact bot_le
  have hfin : ∫⁻ T, (markCount G T : ℝ≥0∞) ∂conditioned μ n ≠ ∞ := by
    rw [Cyclic.lintegral_markCount_conditioned]
    have : IsFiniteMeasure (uniformFringeLaw μ n) := by
      unfold uniformFringeLaw
      infer_instance
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_ne_top _ _)
  have hint : ∫ T, (markCount G T : ℝ) ∂conditioned μ n =
      (∫⁻ T, (markCount G T : ℝ≥0∞) ∂conditioned μ n).toReal := by
    rw [← integral_toReal Measurable.of_discrete.aemeasurable
      (Filter.Eventually.of_forall fun _ => ENNReal.natCast_lt_top _)]
    simp only [ENNReal.toReal_natCast]
  rw [hint, measureReal_def]
  exact ENNReal.toReal_mono hfin hle

/-- Along `admissibleSizes μ`, the sizes are eventually admissible. -/
theorem eventually_admissible_sizes (μ : PMF ℕ) :
    ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
  mem_inf_of_right (mem_principal_self _)

/-- `{λ(T) ≥ h}` is the event that the raw leaf-height count is positive. -/
theorem setOf_le_leafHeight_eq (h : ℕ) :
    {T : PlaneTree | h ≤ leafHeight T} =
      {T | 0 < markCount (fun U => h ≤ rootLeafHeight U) T} := by
  ext T
  exact le_leafHeight_iff_markCount_pos h T

/-- Upper half of `eq:threshold_lh` (source lines 3343–3356): under (S) along the levels `h_n`,
`n π_{h_n} → 0` implies `P(λ(𝒯^n) ≥ h_n) → 0` (Corollary `cor:SM`(ii) and the first half of
Lemma `lem:ineqs`, i.e. Markov's inequality for `N_{h_n}(𝒯^n)`). -/
theorem tendsto_conditioned_le_leafHeight_zero (hT : StableToolkit μ α a) {h M : ℕ → ℕ}
    (hM : IsCutoff M) (hS : StructuralMicroscopic μ a (fun j T => j ≤ rootLeafHeight T) h M)
    (h0 : Tendsto (fun n : ℕ => (n : ℝ) * (bienayme μ).real {T | h n ≤ rootLeafHeight T})
      (admissibleSizes μ) (𝓝 0)) :
    Tendsto (fun n => (conditioned μ n).real {T | h n ≤ leafHeight T}) (admissibleSizes μ)
      (𝓝 0) := by
  have hE := (Bridge.integral_markCount_isEquivalent hT hM hS).symm.tendsto_nhds h0
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hE
  rw [setOf_le_leafHeight_eq]
  exact conditioned_real_markCount_pos_le μ n _

/-- Lower half of `eq:threshold_lh` (source lines 3343–3356): if `c > 0`, under (S) along the
levels `h_n`, `n π_{h_n} → ∞` implies `P(λ(𝒯^n) ≥ h_n) → 1` (Theorem `thm:PoissonApproximation2`,
divergent part, gives `N̂_{h_n}(𝒯^n) → ∞` in probability, with (C) from Lemma `lem:C_lh`; then
the second half of Lemma `lem:ineqs`, since `N̂_h ≥ 1 ⇒ N_h ≥ 1 ⇔ λ ≥ h`). -/
theorem tendsto_conditioned_le_leafHeight_one (h2 : PoissonApproximation2Statement)
    (hD : StableDomain μ α a) (hcpos : 0 < cConst μ) {h M : ℕ → ℕ} (hM : IsCutoff M)
    (hS : StructuralMicroscopic μ a (fun j T => j ≤ rootLeafHeight T) h M)
    (hinf : Tendsto (fun n : ℕ => (n : ℝ) * (bienayme μ).real {T | h n ≤ rootLeafHeight T})
      (admissibleSizes μ) atTop) :
    Tendsto (fun n => (conditioned μ n).real {T | h n ≤ leafHeight T}) (admissibleSizes μ)
      (𝓝 1) := by
  have hc := hD.critical
  have h1 := hD.nondegenerate
  have hB0 : 0 < cB μ (lhDegrees μ) :=
    (cB_pos_iff hc _).2 (by rw [cBReal_lhDegrees hc]; exact hcpos)
  have hBtop : cB μ (lhDegrees μ) < ∞ := (cB_ne_top hc _).lt_top
  have hC : NonClustering μ
      (fun j => declumpedMark (lhDegrees μ) (fun T => j ≤ rootLeafHeight T)) h M :=
    Applications.lem_C_lh_of_isCutoff hc h1 hcpos h hM
  have hdecl := (h2 μ α a hD (fun j T => j ≤ rootLeafHeight T) h M hM (lhDegrees μ) hB0 hBtop
    hS hC).2 hinf 0
  have hlow : ∀ᶠ n in admissibleSizes μ, 1 - (conditioned μ n).real
      {T | markCount (declumpedMark (lhDegrees μ) (fun T => h n ≤ rootLeafHeight T)) T ≤ 0} ≤
      (conditioned μ n).real {T | h n ≤ leafHeight T} := by
    filter_upwards [eventually_admissible_sizes μ] with n hn
    have := conditioned_isProbabilityMeasure hn
    rw [← probReal_compl_eq_one_sub MeasurableSet.of_discrete]
    refine measureReal_mono fun T hT => ?_
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hT
    exact (le_leafHeight_iff_markCount_pos _ _).2 (declumped_count_pos_imp_raw_count_pos hT)
  have hup : ∀ᶠ n in admissibleSizes μ, (conditioned μ n).real {T | h n ≤ leafHeight T} ≤ 1 := by
    filter_upwards [eventually_admissible_sizes μ] with n hn
    have := conditioned_isProbabilityMeasure hn
    exact measureReal_le_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds hlow hup
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdecl

/-- Two thresholds give the localization on `[lo, hi)`: if `P(H(𝒯^n) ≥ lo_n) → 1` and
`P(H(𝒯^n) ≥ hi_n) → 0`, then `P(lo_n ≤ H(𝒯^n) < hi_n) → 1`. -/
theorem tendsto_le_and_not_le {l : Filter ℕ} (hl : ∀ᶠ n in l, Admissible μ n)
    (H : PlaneTree → ℕ) {lo hi : ℕ → ℕ}
    (hlo : Tendsto (fun n => (conditioned μ n).real {T | lo n ≤ H T}) l (𝓝 1))
    (hhi : Tendsto (fun n => (conditioned μ n).real {T | hi n ≤ H T}) l (𝓝 0)) :
    Tendsto (fun n => (conditioned μ n).real {T | lo n ≤ H T ∧ ¬ hi n ≤ H T}) l (𝓝 1) := by
  have hlow : ∀ n, (conditioned μ n).real {T | lo n ≤ H T} -
      (conditioned μ n).real {T | hi n ≤ H T} ≤
      (conditioned μ n).real {T | lo n ≤ H T ∧ ¬ hi n ≤ H T} := by
    intro n
    have hsub : {T | lo n ≤ H T} ⊆ {T | lo n ≤ H T ∧ ¬ hi n ≤ H T} ∪ {T | hi n ≤ H T} := by
      intro T hT
      by_cases hh : hi n ≤ H T
      · exact Or.inr hh
      · exact Or.inl ⟨hT, hh⟩
    have := (measureReal_mono (μ := conditioned μ n) hsub).trans (measureReal_union_le _ _)
    linarith
  have hup : ∀ᶠ n in l, (conditioned μ n).real {T | lo n ≤ H T ∧ ¬ hi n ≤ H T} ≤ 1 := by
    filter_upwards [hl] with n hn
    have := conditioned_isProbabilityMeasure hn
    exact measureReal_le_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds
    (Eventually.of_forall hlow) hup
  simpa using hlo.sub hhi

/-- Propagation for `κ = 1` (source lines 3317–3319): with `B = {j ≥ 2}`, a vertex with a child
`U` with `λ_∅(U) ≥ k` and degree outside `B` has degree one, hence `λ_∅ ≥ k + 1 ≥ k`. -/
theorem propagatesOutside_of_kappa_eq_one (hκ : kappa μ = 1) (k : ℕ) :
    PropagatesOutside (lhDegrees μ) (fun T => k ≤ rootLeafHeight T) := by
  intro T U hU hGU hdeg
  simp only [lhDegrees, hκ, Set.mem_ofPred_eq, not_le, rootDegree] at hdeg
  have hlen : T.children.length = 1 := by
    have := List.length_pos_of_mem hU
    omega
  obtain ⟨V, hV⟩ := List.length_eq_one_iff.mp hlen
  rw [hV, List.mem_singleton] at hU
  subst hU
  have := (succ_le_rootLeafHeight_iff k T).2 ⟨by simp [hV], fun W hW => by
    rw [hV, List.mem_singleton] at hW
    rw [hW]
    exact hGU⟩
  omega

/-- Statistics that agree almost surely under every `𝒯^n` have the same two-point
localization. -/
theorem twoPointLocalization_congr {H H' : PlaneTree → ℕ} {x : ℕ → ℝ}
    (hH : ∀ n, ∀ᵐ T ∂conditioned μ n, H T = H' T) :
    TwoPointLocalization μ H x ↔ TwoPointLocalization μ H' x := by
  have key : ∀ (n : ℕ) (P : ℕ → Prop),
      (conditioned μ n).real {T | P (H T)} = (conditioned μ n).real {T | P (H' T)} := by
    intro n P
    refine measureReal_congr ?_
    filter_upwards [hH n] with T hT
    rw [hT]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.congr fun n => key n (fun z => ((z : ℕ) : ℤ) ∈ twoPointSet (x n)),
      fun hθ => (h2 hθ).congr fun n => key n (fun z => ((z : ℕ) : ℤ) = ⌊x n⌋)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.congr fun n => (key n (fun z => ((z : ℕ) : ℤ) ∈ twoPointSet (x n))).symm,
      fun hθ => (h2 hθ).congr fun n => (key n (fun z => ((z : ℕ) : ℤ) = ⌊x n⌋)).symm⟩


/-- An exponent `η ∈ (0, 1 - 1/α)` (namely `η = (1 - 1/α)/2`) for the cutoff
`M_n = max 1 ⌊n^{1-η}⌋₊` of the proof (source lines 3259–3261). -/
theorem exists_eta (hT : StableToolkit μ α a) :
    ∃ η : ℝ, (0 < η ∧ η < 1 - 1 / α) ∧ η < 1 := by
  obtain ⟨hα1, -⟩ := hT.alpha_mem
  have h0 : 0 < 1 / α := by positivity
  have h1 : 1 / α < 1 := by rw [div_lt_one (by linarith)]; exact hα1
  exact ⟨(1 - 1 / α) / 2, ⟨by linarith, by linarith⟩, by linarith⟩

/-- `p_n = O(1/n)` from an eventual bound on `n p_n`, for nonnegative `p`. -/
theorem isBigO_of_eventually_mul_le {l : Filter ℕ} (hl : l ≤ atTop) {p : ℕ → ℝ}
    (hp : ∀ n, 0 ≤ p n) {K : ℝ} (hK : ∀ᶠ n : ℕ in l, (n : ℝ) * p n ≤ K) :
    p =O[l] (fun n => 1 / (n : ℝ)) := by
  refine IsBigO.of_bound K ?_
  filter_upwards [hK, hl (eventually_ge_atTop 1)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.norm_of_nonneg (hp n), Real.norm_of_nonneg (by positivity), mul_one_div,
    le_div_iff₀ hnpos]
  linarith

/-- **Theorem `thm:max_lh`(i)** (source lines 536–543, 562–566; proof 3298–3326): if `μ_1 > 0`,
`C_μ = lim P(λ_∅(𝒯) ≥ j)/μ_1^j > 0` exists, and with
`k_n^* = (log n + log((1 - μ_1) C_μ))/log(1/μ_1)`, for every real `t`,
`P(λ(𝒯^n) ≤ ⌊k_n^* + t⌋) - exp(-μ_1^{t + 1 - {k_n^* + t}}) → 0` along admissible sizes. -/
theorem maxLeafHeight_unary (h2 : PoissonApproximation2Statement) (hD : StableDomain μ α a)
    (hpos : 0 < μ 1) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun j : ℕ => (PlaneTree.bienayme μ).real {T | j ≤ T.rootLeafHeight} /
        (μ 1).toReal ^ j) atTop (𝓝 C) ∧
      LatticeGumbel μ PlaneTree.leafHeight (μ 1).toReal (fun n : ℕ =>
        (Real.log n + Real.log ((1 - (μ 1).toReal) * C)) / Real.log (1 / (μ 1).toReal)) := by
  have hT := Stable.stableToolkit hD
  have hc := hD.critical
  have h1 := hD.nondegenerate
  obtain ⟨hC, hlim, -⟩ := lem_ell_asymp_i_tree hc h1 hpos
  refine ⟨leafC μ, hC, hlim, fun t => ?_⟩
  set x : ℕ → ℝ := fun n => (Real.log n + Real.log ((1 - (μ 1).toReal) * leafC μ)) /
    Real.log (1 / (μ 1).toReal) with hx
  obtain ⟨hexp, ⟨K, hK⟩, hlev⟩ := ExtremesAnalysis.lh_unary_inputs hc h1 hpos (x := x)
    (fun n => rfl) t
  set h : ℕ → ℕ := fun n => (⌊x n + t⌋ + 1).toNat with hh
  set G : ℕ → PlaneTree → Prop := fun j T => j ≤ rootLeafHeight T with hG
  obtain ⟨η, hη, hη1⟩ := exists_eta hT
  set M : ℕ → ℕ := fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ with hMdef
  have hM : IsCutoff M := Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  have hκ : kappa μ = 1 := kappa_eq_one hpos
  have hS : StructuralMicroscopic μ a G h M :=
    Applications.lem_S_lh hT hη (fun _ δ hδ => (hlev δ hδ).filter_mono inf_le_left)
      (fun h2κ => by omega)
  have hcpos : 0 < cConst μ := cConst_pos_of_pos h1 hpos
  have hB0 : 0 < cB μ (lhDegrees μ) :=
    (cB_pos_iff hc _).2 (by rw [cBReal_lhDegrees hc]; exact hcpos)
  have hBtop : cB μ (lhDegrees μ) < ∞ := (cB_ne_top hc _).lt_top
  have hcB : (cB μ (lhDegrees μ)).toReal = 1 - (μ 1).toReal := by
    rw [← cBReal_eq_toReal_cB, cBReal_lhDegrees hc, cConst, hκ]
    simp [mass]
  have hCl : NonClustering μ (fun j => declumpedMark (lhDegrees μ) (G j)) h M :=
    Applications.lem_C_lh_of_isCutoff hc h1 hcpos h hM
  have hK' : ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G h n ≤ K :=
    hK.filter_mono inf_le_left
  have htv := (h2 μ α a hD G h M hM (lhDegrees μ) hB0 hBtop hS hCl).1 ⟨K, hK'⟩
  have hO : markProb μ G h =O[admissibleSizes μ] (fun n => 1 / (n : ℝ)) :=
    isBigO_of_eventually_mul_le inf_le_left (fun n => measureReal_nonneg) hK'
  have hroot := Bridge.conditioned_mark_tendsto_zero hT hM hS hO
  have hraw := PlaneTree.conditioned_declump_to_raw μ (lhDegrees μ) (fun n => G (h n))
    (fun n : ℕ => Real.toNNReal ((cB μ (lhDegrees μ)).toReal * ((n : ℝ) * markProb μ G h n)))
    (fun n => propagatesOutside_of_kappa_eq_one hκ (h n)) hroot htv
  have key := hraw.add (hexp.mono_left inf_le_left)
  rw [add_zero] at key
  refine key.congr fun n => ?_
  have hset : {T : PlaneTree | ((leafHeight T : ℕ) : ℤ) ≤ ⌊x n + t⌋} =
      {T | markCount (G (h n)) T = 0} := by
    ext T
    simp only [Set.mem_ofPred_eq, ExtremesAnalysis.natCast_le_iff_not_toNat_le,
      le_leafHeight_iff_markCount_pos, hG, hh, Nat.pos_iff_ne_zero, not_not]
  have hrate : ((Real.toNNReal ((cB μ (lhDegrees μ)).toReal * ((n : ℝ) * markProb μ G h n)) :
      ℝ≥0) : ℝ) = (1 - (μ 1).toReal) * ((n : ℝ) *
        (bienayme μ).real {T | (⌊x n + t⌋ + 1).toNat ≤ T.rootLeafHeight}) := by
    have hnn : 0 ≤ (cB μ (lhDegrees μ)).toReal * ((n : ℝ) * markProb μ G h n) :=
      mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg n) measureReal_nonneg)
    rw [Real.coe_toNNReal _ hnn, hcB]
    rfl
  simp only [hset, hrate]
  ring

/-- **Theorem `thm:max_lh`(ii), case `c = 1 - κ μ_κ > 0`** (source lines 545–558; proof
3328–3383): for `μ_1 = 0` and `k_n^{**} = log_κ log n - log_κ log(1/D_μ)`,
`P(λ(𝒯^n) ∈ J_n) → 1`, and `P(λ(𝒯^n) = ⌊k_n^{**}⌋) → 1` in the interior phase. -/
theorem maxLeafHeight_superexp_of_cConst_pos (h2 : PoissonApproximation2Statement)
    (hD : StableDomain μ α a) (h0 : μ 1 = 0) (hcpos : 0 < cConst μ) {x : ℕ → ℝ}
    (hx : ∀ n, x n = Real.logb (kappa μ) (Real.log n) -
      Real.logb (kappa μ) (Real.log (1 / leafD μ))) :
    TwoPointLocalization μ PlaneTree.leafHeight x := by
  have hT := Stable.stableToolkit hD
  have hc := hD.critical
  have h1 := hD.nondegenerate
  have hκ2 : 2 ≤ kappa μ := two_le_kappa hc h1 h0
  obtain ⟨η, hη, hη1⟩ := exists_eta hT
  set M : ℕ → ℕ := fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ with hMdef
  have hM : IsCutoff M := Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  have hSof : ∀ h : ℕ → ℕ, (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      (kappa μ : ℝ) ^ h n ≤ (n : ℝ) ^ δ) →
      StructuralMicroscopic μ a (fun j T => j ≤ rootLeafHeight T) h M := fun h hlev =>
    Applications.lem_S_lh hT hη (fun hκ1 => by omega)
      (fun _ δ hδ => (hlev δ hδ).filter_mono inf_le_left)
  obtain ⟨hlo, hhi, hfl⟩ := ExtremesAnalysis.lh_levels_le_rpow hc h1 h0 hx
  have hadm := eventually_admissible_sizes μ
  constructor
  · obtain ⟨hinf, hzero⟩ := ExtremesAnalysis.lh_twoPoint_thresholds hc h1 h0 hx
      (l := admissibleSizes μ) inf_le_left
    have hA := tendsto_conditioned_le_leafHeight_one h2 hD hcpos hM (hSof _ hlo) hinf
    have hB := tendsto_conditioned_le_leafHeight_zero hT hM (hSof _ hhi) hzero
    refine (tendsto_le_and_not_le hadm leafHeight hA hB).congr fun n => ?_
    congr 1
    ext T
    exact (ExtremesAnalysis.natCast_mem_twoPointSet_iff (x n) (leafHeight T)).symm
  · rintro ⟨δ, hδ, hθ⟩
    obtain ⟨hinf, hzero⟩ := ExtremesAnalysis.lh_interior_thresholds hc h1 h0 hx
      (l := admissibleSizes μ) inf_le_left hδ hθ
    have hlev0 : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        (kappa μ : ℝ) ^ (⌊x n⌋).toNat ≤ (n : ℝ) ^ δ := fun δ hδ => by
      simpa using hfl 0 (by norm_num) δ hδ
    have hA := tendsto_conditioned_le_leafHeight_one h2 hD hcpos hM (hSof _ hlev0) hinf
    have hB := tendsto_conditioned_le_leafHeight_zero hT hM (hSof _ (hfl 1 (by norm_num))) hzero
    refine (tendsto_le_and_not_le hadm leafHeight hA hB).congr fun n => ?_
    congr 1
    ext T
    exact (ExtremesAnalysis.natCast_eq_iff (leafHeight T) ⌊x n⌋).symm

/-- **Theorem `thm:max_lh`(ii), case `c = 0`** (source lines 3274–3296): the law is supported
on `{0, κ}`, `λ = H_κ` almost surely and `k_n^{**} = t_n^{**}`, so this is Theorem
`thm:max_string`(ii) with `r = κ`. -/
theorem maxLeafHeight_of_cConst_eq_zero (h3 : MaxStringStatement) (hμ : InStableDomain μ)
    (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (hc0 : cConst μ = 0) {x : ℕ → ℝ}
    (hx : ∀ n, x n = Real.logb (kappa μ) (Real.log n) -
      Real.logb (kappa μ) (Real.log (1 / leafD μ))) :
    TwoPointLocalization μ PlaneTree.leafHeight x := by
  have hκ2 := (two_le_kappa_of_cConst_eq_zero hc h1 hc0).1
  have H := (h3 μ hμ).2 (kappa μ) hκ2 (kappa_mem hc h1).2
  have hxeq : x = tStarStar (kappa μ) (μ (kappa μ)).toReal :=
    funext fun n => by rw [hx, ExtremesAnalysis.lh_center_eq_tStarStar hc h1 hc0]
  rw [hxeq, twoPointLocalization_congr
    (ae_conditioned_leafHeight_eq_maxCompleteHeight hc h1 hc0)]
  exact H

/-- **Theorem `thm:max_lh`** (source lines 533–586), from Theorems `thm:PoissonApproximation2` and
`thm:max_string`. -/
theorem maxLeafHeight_of_approx2_maxString (h2 : PoissonApproximation2Statement)
    (h3 : MaxStringStatement) : MaxLeafHeightStatement := by
  intro μ hμ
  obtain ⟨α, a, hD⟩ := id hμ
  have hc := hD.critical
  have h1 := hD.nondegenerate
  refine ⟨fun hpos => maxLeafHeight_unary h2 hD hpos, fun h0 => ?_⟩
  intro κ
  have hκ : κ = kappa μ := (kappa_eq_sInf_two h0).symm
  clear_value κ
  subst hκ
  obtain ⟨-, hD0, hD1, hDlim, -⟩ := lem_ell_asymp_ii_tree hc h1 h0
  refine ⟨leafD μ, hD0, hD1, hDlim, ?_⟩
  rcases (cConst_nonneg hc).eq_or_lt with hc0 | hcpos
  · exact maxLeafHeight_of_cConst_eq_zero h3 hμ hc h1 hc0.symm fun n => rfl
  · exact maxLeafHeight_superexp_of_cConst_pos h2 hD h0 hcpos fun n => rfl

/-- **Theorem `thm:max_lh`**, from Theorems `thm:PoissonApproximation2` and `thm:max_string` as
hypotheses (the unconditional form is `PoissonDeclumping.maxLeafHeight`). Theorem
`thm:PoissonApproximation` is not used (the proof goes through Theorem
`thm:PoissonApproximation2` and Theorem `thm:max_string`). -/
theorem maxLeafHeight_of (_h1 : PoissonApproximationStatement)
    (h2 : PoissonApproximation2Statement) (h3 : MaxStringStatement) : MaxLeafHeightStatement :=
  maxLeafHeight_of_approx2_maxString h2 h3


end MaxLeafHeight
end PoissonDeclumping
