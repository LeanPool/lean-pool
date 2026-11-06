/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.ForestEstimates
public import LeanPool.RareSubtreePatterns.Bridge.CriterionM
public import LeanPool.RareSubtreePatterns.Setup.Marks

import LeanPool.RareSubtreePatterns.RegularVariation.Karamata
import LeanPool.RareSubtreePatterns.RegularVariation.Consequences
import LeanPool.RareSubtreePatterns.Bienayme.Normalization
import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex

/-!
# Consequences of Assumption (S): Lemma `lem:consequenceM` and Corollary `cor:SM`

Work package WP3 of the bridge plan. Source lines 1182–1251 (Lemma 3.6, proof step P04) and
1256–1365 (Corollary 3.7, proof step P05). Notation: `𝒯 ~ bienayme μ`, `P_k = P(· | G_k(𝒯) = 1)`
(`cond`), `Ψ_m(x) = walkProb μ m x`, `supWalk μ m = sup_x Ψ_m(x)`.

## The decomposition of Assumption (S)

A decomposition `ρ` (`Skeleton`) is a law of `(𝒯, C, 𝒯^{(1)}, …, 𝒯^{(L)})` with first marginal
`P_k`, conditionally i.i.d. trees given `(C, L)` and `|𝒯| = C + ∑ |𝒯^{(i)}|`.
`lintegral_skeleton` is the resulting forest formula
`E[h(C, L, ∑ |𝒯^{(i)}|)] = ∑_{c, ℓ} P(C = c, L = ℓ) ∑_q P(|𝒢_ℓ| = q) h(c, ℓ, q)`, and
`lintegral_skeleton_le` compares with `E[L]`; the empty forest `ℓ = 0` needs no special
treatment there.

## Main statements

* `consequenceM_tail` (**Lemma `lem:consequenceM`, first assertion**):
  `P_{k_n}(|𝒯| > M_n/4) → 0`.
* `consequenceM_weighted` (**second assertion, numerator form**, correction F3): for every
  `ε > 0`, eventually, uniformly over a time shift `j ≤ 1` and an endpoint selector `e`,
  `a_n E_{k_n}[Ψ_{n-j-|𝒯|}(e(𝒯)) 1{|𝒯| > M_n/4}] ≤ ε`; `consequenceM_weighted_sup` is the
  `sup_x` form and `consequenceM_weighted_div` the paper's form (division by `Ψ_n(-1)`).
  The paper's step "`Ψ_{n-c}(-1) ∼ Ψ_n(-1)` uniformly for `c ≤ M_n/8`" fails in the periodic case
  (`Ψ_{n-c}(-1) = 0` when `d ∤ c`); the proof instead applies the numerator forest estimate
  `forest_weighted_tail_sup_le` at time `N = n - j - c ≥ n/2` and uses `a_n ≤ C a_N`.
* `microscopic_of_large`: Assumption (M) from `o(π_n)` bounds on large marked trees, before and
  after bridge weighting (the assembly of source lines 1286–1311).
* `microscopic_of_structural` (**Corollary `cor:SM`(i)**): (S) implies (M), same cutoff.
* `integral_markCount_isEquivalent` (**Corollary `cor:SM`(ii)**):
  `E[#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}] ∼ n π_n`.
* `conditioned_mark_tendsto_zero` (**Corollary `cor:SM`(iii)**): `π_n = O(1/n)` implies
  `P(G_{k_n}(𝒯^n) = 1) → 0`.

Null marks (`π_n = 0`, where (S) gives no decomposition) are handled by `cond` of a null event
being `0` (correction F13).
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped ENNReal Topology

namespace PoissonDeclumping.Bridge

open PlaneTree

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### Forests of i.i.d. trees: sums over tuples and lists -/

/-- `∑_{(t_1..t_L)} ∏ w(t_i) H(∑ |t_i|) = ∑_q P(|𝒢_L| = q) H(q)`. -/
theorem tsum_prod_weight_mul (μ : PMF ℕ) (L : ℕ) (H : ℕ → ℝ≥0∞) :
    ∑' f : Fin L → PlaneTree, (∏ i, weight μ (f i)) * H (∑ i, (f i).vertexCount) =
      ∑' q, forestSizeWeight μ L q * H q := by
  simp only [forestSizeWeight, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun f => ?_
  rw [tsum_eq_single (∑ i, (f i).vertexCount)]
  · rw [ite_eq_left rfl]
  · intro q hq
    rw [ite_eq_right (Ne.symm hq), zero_mul]

/-- Lists of trees grouped by length: `∑_{ts} ∏ w(t_i) Φ(|ts|, ∑ |t_i|) = ∑_L ∑_q P(|𝒢_L| = q)
  Φ(L, q)`. -/
theorem tsum_list_prod_weight_mul (μ : PMF ℕ) (Φ : ℕ → ℕ → ℝ≥0∞) :
    ∑' ts : List PlaneTree, (ts.map (weight μ)).prod * Φ ts.length (ts.map vertexCount).sum =
      ∑' L, ∑' q, forestSizeWeight μ L q * Φ L q := by
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun L => ?_
  rw [← tsum_prod_weight_mul]
  refine tsum_congr fun f => ?_
  simp only [List.equivSigmaTuple_symm_apply, List.map_ofFn, List.prod_ofFn, List.length_ofFn,
    List.sum_ofFn]
  rfl

/-! ### Integrals over a decomposition `ρ` -/

/-- Integrating a function of `(C, L)` against any measure on `PlaneTree × ℕ × List PlaneTree`. -/
theorem lintegral_core_length (ρ : Measure (PlaneTree × ℕ × List PlaneTree))
    (g : ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ ω, g ω.2.1 ω.2.2.length ∂ρ =
      ∑' c, ∑' L, ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * g c L := by
  have hm : Measurable fun ω : PlaneTree × ℕ × List PlaneTree => (ω.2.1, ω.2.2.length) :=
    Measurable.of_discrete
  have h := lintegral_map (μ := ρ) (f := fun p : ℕ × ℕ => g p.1 p.2) Measurable.of_discrete hm
  rw [← h, lintegral_countable', ENNReal.tsum_prod']
  refine tsum_congr fun c => tsum_congr fun L => ?_
  rw [Measure.map_apply hm (MeasurableSet.singleton _), mul_comm]
  congr 2
  ext ω
  simp [Prod.ext_iff]

/-- **The conditional forest structure** of a decomposition (Assumption (S), source lines
1196–1202): for every `h(c, ℓ, q)`,
`E[h(C, L, ∑_{i ≤ L} |𝒯^{(i)}|)] = ∑_{c, ℓ} P(C = c, L = ℓ) ∑_q P(|𝒢_ℓ| = q) h(c, ℓ, q)`. -/
theorem lintegral_skeleton {G : PlaneTree → Prop} {ρ : Measure (PlaneTree × ℕ × List PlaneTree)}
    (hρ : Skeleton μ G ρ) (h : ℕ → ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ ω, h ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum ∂ρ =
      ∑' c, ∑' L, ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} *
        ∑' q, forestSizeWeight μ L q * h c L q := by
  have hm : Measurable fun ω : PlaneTree × ℕ × List PlaneTree => ω.2 := Measurable.of_discrete
  have h1 := lintegral_map (μ := ρ)
    (f := fun p : ℕ × List PlaneTree => h p.1 p.2.length (p.2.map vertexCount).sum)
    Measurable.of_discrete hm
  rw [← h1, lintegral_countable', ENNReal.tsum_prod']
  refine tsum_congr fun c => ?_
  have h2 : ∀ ts : List PlaneTree, (ρ.map fun ω => ω.2) {(c, ts)} =
      ρ {ω | ω.2.1 = c ∧ ω.2.2.length = ts.length} * (ts.map (weight μ)).prod := by
    intro ts
    rw [Measure.map_apply hm (MeasurableSet.singleton _), ← hρ.conditionally_iid]
    congr 1
    ext ω
    simp [Prod.ext_iff]
  simp_rw [h2]
  have h3 := tsum_list_prod_weight_mul μ
    (fun L q => ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * h c L q)
  have h4 : ∀ L, ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} *
      ∑' q, forestSizeWeight μ L q * h c L q =
      ∑' q, forestSizeWeight μ L q * (ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * h c L q) := by
    intro L
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by ring
  simp_rw [h4]
  rw [← h3]
  exact tsum_congr fun ts => by ring

/-- Comparison: if `∑_q P(|𝒢_ℓ| = q) h(c, ℓ, q) ≤ K ℓ` for all `c, ℓ`, then
`E[h(C, L, ∑ |𝒯^{(i)}|)] ≤ K E[L]` (the empty forest `ℓ = 0` contributes only through the
hypothesis at `ℓ = 0`). -/
theorem lintegral_skeleton_le {G : PlaneTree → Prop}
    {ρ : Measure (PlaneTree × ℕ × List PlaneTree)} (hρ : Skeleton μ G ρ)
    (h : ℕ → ℕ → ℕ → ℝ≥0∞) (K : ℝ≥0∞)
    (hK : ∀ c L, ∑' q, forestSizeWeight μ L q * h c L q ≤ K * L) :
    ∫⁻ ω, h ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum ∂ρ ≤
      K * ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ := by
  rw [lintegral_skeleton hρ, lintegral_core_length ρ (fun _ L => (L : ℝ≥0∞)),
    ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun c => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun L => ?_
  calc ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * ∑' q, forestSizeWeight μ L q * h c L q
      ≤ ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * (K * L) := by gcongr; exact hK c L
    _ = K * (ρ {ω | ω.2.1 = c ∧ ω.2.2.length = L} * L) := by ring

/-- Under a decomposition, a function of the size of the marked tree integrates as a function of
`C + ∑_{i ≤ L} |𝒯^{(i)}|` (source line 1198). -/
theorem lintegral_cond_vertexCount {G : PlaneTree → Prop}
    {ρ : Measure (PlaneTree × ℕ × List PlaneTree)} (hρ : Skeleton μ G ρ) (ψ : ℕ → ℝ≥0∞) :
    ∫⁻ T, ψ T.vertexCount ∂cond (bienayme μ) {T | G T} =
      ∫⁻ ω, ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ∂ρ := by
  rw [← hρ.law_tree, lintegral_map Measurable.of_discrete measurable_fst]
  exact lintegral_congr_ae (hρ.size_eq.mono fun ω hω => by simp only [hω])

/-! ### Core estimates for one decomposition -/

/-- `a_M ≤ C a_{⌊M/8⌋}` and `a_n ≤ C a_N` for `n ≤ 2N` (regular variation). -/
theorem exists_comparison (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 < C ∧ (∀ M : ℕ, 8 ≤ M → a M ≤ C * a (M / 8)) ∧
      ∀ n N : ℕ, 1 ≤ N → n ≤ 2 * N → a n ≤ C * a N := by
  obtain ⟨C₁, hC₁, h₁⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le 16
  obtain ⟨C₂, hC₂, h₂⟩ := hT.regularlyVarying.exists_le_mul_of_le_mul hT.monotone hT.pos
    hT.rho_pos.le 2
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun M hM => ?_, fun n N hN hnN => ?_⟩
  · have hm : 1 ≤ M / 8 := by omega
    have h := h₁ (M / 8) M hm (by
      have : M ≤ 16 * (M / 8) := by omega
      exact_mod_cast this)
    exact h.trans (by gcongr; exacts [(hT.pos _ hm).le, le_max_left _ _])
  · have h := h₂ N n hN (by exact_mod_cast hnN)
    exact h.trans (by gcongr; exacts [(hT.pos _ hN).le, le_max_right _ _])

/-- **Unweighted core estimate** (proof of `lem:consequenceM`, source lines 1208–1224): for a
decomposition `ρ` of `P(· | G(𝒯) = 1)` and `M ≥ 8`,
`P(|𝒯| > M/4 | G(𝒯) = 1) ≤ P(C > M/8) + (C' / a_M) E[L]`. -/
theorem cond_vertexCount_gt_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : PlaneTree → Prop) (ρ : Measure (PlaneTree × ℕ × List PlaneTree)),
      Skeleton μ G ρ → ∀ M : ℕ, 8 ≤ M →
      cond (bienayme μ) {T | G T} {T | (M : ℝ) / 4 < T.vertexCount} ≤
        ρ {ω | 1 / 8 * (M : ℝ) < ω.2.1} +
          ENNReal.ofReal (C / a M) * ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ := by
  obtain ⟨Ct, hCt, htail⟩ := forestSizeWeight_tail_le_ofReal hT
  obtain ⟨Cc, hCc, hcM, -⟩ := exists_comparison hT
  refine ⟨Ct * Cc, by positivity, fun G ρ hρ M hM => ?_⟩
  set m := M / 8 with hmdef
  have hm : 1 ≤ m := by omega
  have ham : 0 < a m := hT.pos m hm
  have haM : 0 < a M := hT.pos M (by omega)
  have hmR : (m : ℝ) ≤ (M : ℝ) / 8 := by
    rw [hmdef]
    exact_mod_cast Nat.cast_div_le
  set ψ : ℕ → ℝ≥0∞ := {t : ℕ | (M : ℝ) / 4 < t}.indicator 1 with hψ
  have hset : cond (bienayme μ) {T | G T} {T | (M : ℝ) / 4 < T.vertexCount} =
      ∫⁻ T, ψ T.vertexCount ∂cond (bienayme μ) {T | G T} := by
    rw [← lintegral_indicator_one MeasurableSet.of_discrete]
    rfl
  rw [hset, lintegral_cond_vertexCount hρ]
  have hpt : ∀ ω : PlaneTree × ℕ × List PlaneTree,
      ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ≤
        {ω : PlaneTree × ℕ × List PlaneTree | 1 / 8 * (M : ℝ) < ω.2.1}.indicator 1 ω +
          (Set.Ioi m).indicator 1 (ω.2.2.map vertexCount).sum := by
    intro ω
    by_cases h1 : (M : ℝ) / 4 < ((ω.2.1 + (ω.2.2.map vertexCount).sum : ℕ) : ℝ)
    · rw [hψ, Set.indicator_of_mem (show _ ∈ {t : ℕ | (M : ℝ) / 4 < t} from h1)]
      by_cases h2 : 1 / 8 * (M : ℝ) < ω.2.1
      · rw [Set.indicator_of_mem (show ω ∈ {ω : PlaneTree × ℕ × List PlaneTree |
          1 / 8 * (M : ℝ) < ω.2.1} from h2)]
        exact le_self_add
      · have h3 : m < (ω.2.2.map vertexCount).sum := by
          rw [Nat.cast_add] at h1
          have : (m : ℝ) < ((ω.2.2.map vertexCount).sum : ℕ) := by
            push Not at h2
            linarith
          exact_mod_cast this
        rw [Set.indicator_of_mem (show (ω.2.2.map vertexCount).sum ∈ Set.Ioi m from h3)]
        exact le_add_self
    · rw [hψ, Set.indicator_of_notMem (show _ ∉ {t : ℕ | (M : ℝ) / 4 < t} from h1)]
      exact zero_le
  calc ∫⁻ ω, ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ∂ρ
      ≤ ∫⁻ ω, ({ω : PlaneTree × ℕ × List PlaneTree | 1 / 8 * (M : ℝ) < ω.2.1}.indicator 1 ω +
          (Set.Ioi m).indicator 1 (ω.2.2.map vertexCount).sum) ∂ρ := lintegral_mono hpt
    _ = ρ {ω | 1 / 8 * (M : ℝ) < ω.2.1} +
          ∫⁻ ω, (fun _ _ q => (Set.Ioi m).indicator (1 : ℕ → ℝ≥0∞) q) ω.2.1 ω.2.2.length
            (ω.2.2.map vertexCount).sum ∂ρ := by
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_indicator_one MeasurableSet.of_discrete]
    _ ≤ _ := by
        gcongr
        refine lintegral_skeleton_le hρ (fun _ _ q => (Set.Ioi m).indicator (1 : ℕ → ℝ≥0∞) q)
          (ENNReal.ofReal (Ct * Cc / a M)) fun c L => ?_
        have h1 : ∑' q, forestSizeWeight μ L q * (Set.Ioi m).indicator (1 : ℕ → ℝ≥0∞) q =
            ∑' q, (Set.Ioi m).indicator (forestSizeWeight μ L) q := by
          refine tsum_congr fun q => ?_
          by_cases hq : q ∈ Set.Ioi m
          · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
        rw [h1]
        refine (htail L m hm).trans ?_
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        rw [div_mul_eq_mul_div, div_le_div_iff₀ ham haM]
        have := hcM M hM
        rw [← hmdef] at this
        have h2 : Ct * L * a M ≤ Ct * L * (Cc * a m) := by gcongr
        nlinarith

/-- **Bridge-weighted core estimate** (proof of `lem:consequenceM`, source lines 1226–1250, in
numerator form, correction F3): for a decomposition `ρ` of `P(· | G(𝒯) = 1)`, `M ≥ 8`,
`n ≥ 2M` and a time shift `j ≤ 1`,
`E[sup_x Ψ_{n-j-|𝒯|}(x) 1{|𝒯| > M/4} | G(𝒯) = 1] ≤ P(C > M/8) + C' E[L] / (a_M a_n)`.
On `{C ≤ M/8}` the forest has more than `M/8` vertices and the forest estimate is applied at time
`N = n - j - C ≥ n/2` (no ratio `Ψ_{n-c}(-1)/Ψ_n(-1)` is used). -/
theorem lintegral_cond_supWalk_le (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : PlaneTree → Prop) (ρ : Measure (PlaneTree × ℕ × List PlaneTree)),
      Skeleton μ G ρ → ∀ M n j : ℕ, 8 ≤ M → j ≤ 1 → 2 * M ≤ n →
      ∫⁻ T, ENNReal.ofReal ({T : PlaneTree | (M : ℝ) / 4 < T.vertexCount}.indicator
          (fun T => supWalk μ ((n : ℤ) - j - T.vertexCount)) T) ∂cond (bienayme μ) {T | G T} ≤
        ρ {ω | 1 / 8 * (M : ℝ) < ω.2.1} +
          ENNReal.ofReal (C / (a M * a n)) * ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ := by
  obtain ⟨Cw, hCw, hw⟩ := forestSizeWeight_weighted_tail_le_ofReal hT
  obtain ⟨Cc, hCc, hcM, hcn⟩ := exists_comparison hT
  refine ⟨Cw * Cc * Cc, by positivity, fun G ρ hρ M n j hM hj hn => ?_⟩
  set m := M / 8 with hmdef
  have hm : 1 ≤ m := by omega
  have ham : 0 < a m := hT.pos m hm
  have haM : 0 < a M := hT.pos M (by omega)
  have han : 0 < a n := hT.pos n (by omega)
  have hmR : (m : ℝ) ≤ (M : ℝ) / 8 := by
    rw [hmdef]
    exact_mod_cast Nat.cast_div_le
  set ψ : ℕ → ℝ≥0∞ := fun t => ENNReal.ofReal ({t : ℕ | (M : ℝ) / 4 < t}.indicator
    (fun t => supWalk μ ((n : ℤ) - j - t)) t) with hψ
  have hset : (fun T : PlaneTree => ENNReal.ofReal ({T : PlaneTree | (M : ℝ) / 4 <
      T.vertexCount}.indicator (fun T => supWalk μ ((n : ℤ) - j - T.vertexCount)) T)) =
      fun T => ψ T.vertexCount := rfl
  rw [hset, lintegral_cond_vertexCount hρ]
  set h₂ : ℕ → ℕ → ℕ → ℝ≥0∞ := fun c _ q => if 8 * c ≤ M then (Set.Ioi m).indicator
    (fun q => ENNReal.ofReal (supWalk μ (((n - j - c : ℕ) : ℤ) - q))) q else 0 with hh₂
  have hpt : ∀ ω : PlaneTree × ℕ × List PlaneTree,
      ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ≤
        {ω : PlaneTree × ℕ × List PlaneTree | 1 / 8 * (M : ℝ) < ω.2.1}.indicator 1 ω +
          h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum := by
    intro ω
    set c := ω.2.1
    set q := (ω.2.2.map vertexCount).sum
    by_cases h2 : 1 / 8 * (M : ℝ) < c
    · rw [Set.indicator_of_mem (show ω ∈ {ω : PlaneTree × ℕ × List PlaneTree |
        1 / 8 * (M : ℝ) < ω.2.1} from h2), Pi.one_apply]
      refine le_trans ?_ le_self_add
      simp only [hψ]
      refine ENNReal.ofReal_le_one.2 ?_
      by_cases h1 : c + q ∈ {t : ℕ | (M : ℝ) / 4 < t}
      · rw [Set.indicator_of_mem h1]
        exact supWalk_le_one μ _
      · rw [Set.indicator_of_notMem h1]
        exact zero_le_one
    · push Not at h2
      have h8 : 8 * c ≤ M := by
        have : ((8 * c : ℕ) : ℝ) ≤ M := by push_cast; linarith
        exact_mod_cast this
      refine le_trans ?_ le_add_self
      by_cases h1 : c + q ∈ {t : ℕ | (M : ℝ) / 4 < t}
      · have h1' : (M : ℝ) / 4 < ((c + q : ℕ) : ℝ) := h1
        rw [Nat.cast_add] at h1'
        have h3 : m < q := by
          have : (m : ℝ) < (q : ℝ) := by linarith
          exact_mod_cast this
        simp only [hψ, hh₂]
        rw [Set.indicator_of_mem h1, ite_eq_left h8,
          Set.indicator_of_mem (show q ∈ Set.Ioi m from h3)]
        have hcast : (n : ℤ) - j - ((c + q : ℕ) : ℤ) = ((n - j - c : ℕ) : ℤ) - q := by
          have : j + c ≤ n := by omega
          push_cast [Nat.sub_sub, this]
          ring
        rw [hcast]
      · simp only [hψ]
        rw [Set.indicator_of_notMem h1, ENNReal.ofReal_zero]
        exact zero_le
  calc ∫⁻ ω, ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ∂ρ
      ≤ ∫⁻ ω, ({ω : PlaneTree × ℕ × List PlaneTree | 1 / 8 * (M : ℝ) < ω.2.1}.indicator 1 ω +
          h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum) ∂ρ := lintegral_mono hpt
    _ = ρ {ω | 1 / 8 * (M : ℝ) < ω.2.1} +
          ∫⁻ ω, h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum ∂ρ := by
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_indicator_one MeasurableSet.of_discrete]
    _ ≤ _ := by
        gcongr
        refine lintegral_skeleton_le hρ h₂ _ fun c L => ?_
        by_cases h8 : 8 * c ≤ M
        · set N := n - j - c with hN
          have hN1 : 1 ≤ N := by omega
          have h2m : 2 * m ≤ N := by omega
          have haN : 0 < a N := hT.pos N hN1
          have h1 : ∑' q, forestSizeWeight μ L q * h₂ c L q =
              ∑' q, (Set.Ioi m).indicator (fun q => forestSizeWeight μ L q *
                ENNReal.ofReal (supWalk μ ((N : ℤ) - q))) q := by
            refine tsum_congr fun q => ?_
            simp only [hh₂, ite_eq_left h8]
            by_cases hq : q ∈ Set.Ioi m
            · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
            · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
          rw [h1]
          refine (hw L m N hm h2m).trans ?_
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hA := hcM M hM
          rw [← hmdef] at hA
          have hB := hcn n N hN1 (by omega)
          have h3 : a M * a n ≤ (Cc * a m) * (Cc * a N) :=
            mul_le_mul hA hB han.le (by positivity)
          have h4 : Cw * L * (a M * a n) ≤ Cw * L * ((Cc * a m) * (Cc * a N)) := by gcongr
          nlinarith
        · have h1 : ∑' q, forestSizeWeight μ L q * h₂ c L q = 0 := by
            simp [hh₂, ite_eq_right h8]
          rw [h1]
          exact zero_le

/-! ### Lemma `lem:consequenceM` -/

/-- A nonnegative function that is eventually below every `ε > 0` tends to `0`. -/
theorem tendsto_zero_of_forall_eventually_le {ι : Type*} {l : Filter ι} {f : ι → ℝ}
    (h0 : ∀ i, 0 ≤ f i) (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, f i ≤ ε) : Tendsto f l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun b hb => Eventually.of_forall fun i => lt_of_lt_of_le hb (h0 i), fun b hb => ?_⟩
  filter_upwards [h (b / 2) (by positivity)] with i hi
  linarith

/-- Turning a bound `X ≤ P + (K / A) E` with `E / A ≤ δ` into `X ≤ P + K δ` in `ℝ`. -/
theorem toReal_le_add_of_le_add_div {X P E : ℝ≥0∞} {K A δ : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hδ : 0 ≤ δ) (hP : P ≠ ∞) (hX : X ≤ P + ENNReal.ofReal (K / A) * E)
    (hE : E / ENNReal.ofReal A ≤ ENNReal.ofReal δ) :
    X.toReal ≤ P.toReal + K * δ := by
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hA).ne' ENNReal.ofReal_ne_top] at hE
  have h1 : ENNReal.ofReal (K / A) * E ≤ ENNReal.ofReal (K * δ) := by
    calc ENNReal.ofReal (K / A) * E ≤ ENNReal.ofReal (K / A) *
          (ENNReal.ofReal δ * ENNReal.ofReal A) := by gcongr
      _ = ENNReal.ofReal (K / A * (δ * A)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hδ]
      _ = ENNReal.ofReal (K * δ) := by congr 1; field_simp
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hP]
  exact hX.trans (by gcongr)

/-- Eventual facts on a cutoff along admissible sizes: `M_n ≥ 8`, `2 M_n ≤ n`, `a_n ≥ 1`. -/
theorem eventually_cutoff_facts (hT : StableToolkit μ α a) {M : ℕ → ℕ} (hM : IsCutoff M) :
    ∀ᶠ n in admissibleSizes μ, 8 ≤ M n ∧ 2 * M n ≤ n ∧ 1 ≤ a n := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have h2 : ∀ᶠ n in atTop, 2 * M n ≤ n := by
    filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((2 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  filter_upwards [hl (hM.tendsto_atTop.eventually_ge_atTop 8), hl h2,
    hl (hT.tendsto_atTop.eventually_ge_atTop 1)] with n h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Lemma `lem:consequenceM`, first assertion** (source lines 1182–1224, P04): under
Assumption (S), `P(|𝒯| > M_n/4 | G_{k_n}(𝒯) = 1) → 0` along admissible sizes. -/
theorem consequenceM_tail (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M) :
    Tendsto (fun n => (cond (bienayme μ) {T | G (k n) T}).real
      {T | (M n : ℝ) / 4 < T.vertexCount}) (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨ρ, hρ, hS1, hS2⟩ := hS
  obtain ⟨C, hC0, hC⟩ := cond_vertexCount_gt_le hT
  refine tendsto_zero_of_forall_eventually_le (fun n => measureReal_nonneg) fun ε hε => ?_
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hCδ : C * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  filter_upwards [eventually_cutoff_facts hT hM,
    (hS1 (1 / 8) (by norm_num)).eventually (ge_mem_nhds (half_pos hε)),
    hS2.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ0))] with n hfacts h1 h2
  obtain ⟨hM8, -, ha1⟩ := hfacts
  by_cases hπ : bienayme μ {T | G (k n) T} = 0
  · rw [cond_eq_zero_of_meas_eq_zero hπ, measureReal_zero_apply]
    exact hε.le
  have hsk := hρ (k n) (pos_iff_ne_zero.2 hπ)
  have := hsk.isProbabilityMeasure
  have haM : 0 < a (M n) := hT.pos _ (by omega)
  have hb := toReal_le_add_of_le_add_div hC0 haM hδ0.le (measure_ne_top _ _)
    (hC (G (k n)) (ρ (k n)) hsk (M n) hM8) h2
  rw [← measureReal_def, ← measureReal_def] at hb
  have hρle : (ρ (k n)).real {ω | 1 / 8 * (M n : ℝ) < ω.2.1} ≤
      a n * (ρ (k n)).real {ω | 1 / 8 * (M n : ℝ) < ω.2.1} :=
    le_mul_of_one_le_left measureReal_nonneg ha1
  linarith

/-- **Lemma `lem:consequenceM`, second assertion, `sup_x` form** (source lines 1226–1250):
under Assumption (S), uniformly in a time shift `j ≤ 1`,
`a_n E[sup_x Ψ_{n-j-|𝒯|}(x) 1{|𝒯| > M_n/4} | G_{k_n}(𝒯) = 1] → 0` along admissible sizes. -/
theorem consequenceM_weighted_sup (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ, ∀ j : ℕ, j ≤ 1 →
      a n * ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - j - T.vertexCount)) T
          ∂cond (bienayme μ) {T | G (k n) T} ≤ ε := by
  obtain ⟨ρ, hρ, hS1, hS2⟩ := hS
  obtain ⟨C, hC0, hC⟩ := lintegral_cond_supWalk_le hT
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hCδ : C * δ ≤ ε / 2 := by
    rw [hδ, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  filter_upwards [eventually_cutoff_facts hT hM,
    (hS1 (1 / 8) (by norm_num)).eventually (ge_mem_nhds (half_pos hε)),
    hS2.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ0))] with n hfacts h1 h2 j hj
  obtain ⟨hM8, h2M, ha1⟩ := hfacts
  have han : 0 < a n := by linarith
  by_cases hπ : bienayme μ {T | G (k n) T} = 0
  · rw [cond_eq_zero_of_meas_eq_zero hπ, integral_zero_measure, mul_zero]
    exact hε.le
  have hsk := hρ (k n) (pos_iff_ne_zero.2 hπ)
  have := hsk.isProbabilityMeasure
  have haM : 0 < a (M n) := hT.pos _ (by omega)
  have hX := hC (G (k n)) (ρ (k n)) hsk (M n) n j hM8 hj h2M
  rw [show C / (a (M n) * a n) = C / a n / a (M n) by rw [div_div, mul_comm]] at hX
  have hb := toReal_le_add_of_le_add_div (by positivity) haM hδ0.le (measure_ne_top _ _) hX h2
  rw [← measureReal_def] at hb
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun T => Set.indicator_nonneg
    (fun T _ => supWalk_nonneg μ _) T) Measurable.of_discrete.aestronglyMeasurable]
  have hρle : (ρ (k n)).real {ω | 1 / 8 * (M n : ℝ) < ω.2.1} * a n ≤ ε / 2 := by
    rw [mul_comm]; exact h1
  calc a n * (∫⁻ T, ENNReal.ofReal ({T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - j - T.vertexCount)) T)
          ∂cond (bienayme μ) {T | G (k n) T}).toReal
      ≤ a n * ((ρ (k n)).real {ω | 1 / 8 * (M n : ℝ) < ω.2.1} + C / a n * δ) :=
        mul_le_mul_of_nonneg_left hb han.le
    _ = (ρ (k n)).real {ω | 1 / 8 * (M n : ℝ) < ω.2.1} * a n + C * δ := by
        field_simp
    _ ≤ ε := by linarith

/-- **Lemma `lem:consequenceM`, second assertion, numerator form** (source lines 1226–1250;
plan WP3.3, correction F3): under Assumption (S), for every `ε > 0`, eventually along admissible
sizes, for every time shift `j ≤ 1` and every endpoint selector `e`,
`a_n E[Ψ_{n-j-|𝒯|}(e(𝒯)) 1{|𝒯| > M_n/4} | G_{k_n}(𝒯) = 1] ≤ ε`. Dividing by
`Ψ_n(-1) ≥ c / a_n` gives the paper's form at `j = 0`. -/
theorem consequenceM_weighted (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ, ∀ j : ℕ, j ≤ 1 → ∀ e : PlaneTree → ℤ,
      a n * ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => walkProb μ ((n : ℤ) - j - T.vertexCount) (e T)) T
          ∂cond (bienayme μ) {T | G (k n) T} ≤ ε := by
  intro ε hε
  filter_upwards [consequenceM_weighted_sup hT hM hS ε hε, eventually_cutoff_facts hT hM]
    with n hn hfacts j hj e
  obtain ⟨-, -, ha1⟩ := hfacts
  refine le_trans ?_ (hn j hj)
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine integral_mono_of_nonneg (Eventually.of_forall fun T => Set.indicator_nonneg
    (fun T _ => walkProb_nonneg μ _ _) T) ?_ (Eventually.of_forall fun T =>
      Set.indicator_le_indicator (walkProb_le_supWalk μ _ _))
  refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
    (Eventually.of_forall fun T => ?_)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_trans (by norm_num) (Set.indicator_nonneg (fun T _ => supWalk_nonneg μ _) T)
  · by_cases hT' : T ∈ {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}
    · rw [Set.indicator_of_mem hT']
      exact supWalk_le_one μ _
    · rw [Set.indicator_of_notMem hT']
      exact zero_le_one

/-- **Lemma `lem:consequenceM`, second assertion, the paper's form** (source line 1189,
  `eq:record`):
under Assumption (S),
`E[sup_x Ψ_{n-|𝒯|}(x) / Ψ_n(-1) 1{|𝒯| > M_n/4} | G_{k_n}(𝒯) = 1] → 0` along admissible sizes
(at admissible `n`, `Ψ_n(-1) ≥ c / a_n > 0`). -/
theorem consequenceM_weighted_div (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M) :
    Tendsto (fun n => ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - T.vertexCount) / walkProb μ n (-1)) T
          ∂cond (bienayme μ) {T | G (k n) T}) (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hnn : ∀ n, 0 ≤ ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
      (fun T => supWalk μ ((n : ℤ) - T.vertexCount) / walkProb μ n (-1)) T
        ∂cond (bienayme μ) {T | G (k n) T} := fun n =>
    integral_nonneg fun T => Set.indicator_nonneg (fun T _ => div_nonneg (supWalk_nonneg μ _)
      (walkProb_nonneg μ _ _)) T
  refine tendsto_zero_of_forall_eventually_le hnn fun ε hε => ?_
  filter_upwards [consequenceM_weighted_sup hT hM hS (ε * c) (by positivity), hadm,
    eventually_cutoff_facts hT hM] with n hn hadmn hfacts
  obtain ⟨-, -, ha1⟩ := hfacts
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => not_admissible_zero μ (h0 ▸ hadmn)
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadmn
  have han : 0 < a n := by linarith
  have hinv : (walkProb μ n (-1))⁻¹ ≤ a n / c := by
    rw [inv_le_comm₀ hψ (by positivity), inv_div]
    exact hlow n hn1 hψ
  have h0 := hn 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, sub_zero] at h0
  have heq : ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
      (fun T => supWalk μ ((n : ℤ) - T.vertexCount) / walkProb μ n (-1)) T
        ∂cond (bienayme μ) {T | G (k n) T} =
      (walkProb μ n (-1))⁻¹ * ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - T.vertexCount)) T ∂cond (bienayme μ) {T | G (k n) T} := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun T => ?_)
    by_cases hT' : T ∈ {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}
    · change _ = (walkProb μ n (-1))⁻¹ * _
      rw [Set.indicator_of_mem hT', Set.indicator_of_mem hT', div_eq_inv_mul]
    · change _ = (walkProb μ n (-1))⁻¹ * _
      rw [Set.indicator_of_notMem hT', Set.indicator_of_notMem hT', mul_zero]
  rw [heq]
  have hI0 : 0 ≤ ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
      (fun T => supWalk μ ((n : ℤ) - T.vertexCount)) T ∂cond (bienayme μ) {T | G (k n) T} :=
    integral_nonneg fun T => Set.indicator_nonneg (fun T _ => supWalk_nonneg μ _) T
  calc _ ≤ a n / c * ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - T.vertexCount)) T ∂cond (bienayme μ) {T | G (k n) T} :=
        mul_le_mul_of_nonneg_right hinv hI0
    _ = (a n * ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
        (fun T => supWalk μ ((n : ℤ) - T.vertexCount)) T
          ∂cond (bienayme μ) {T | G (k n) T}) / c := by ring
    _ ≤ ε * c / c := by gcongr
    _ = ε := by field_simp

/-! ### Corollary `cor:SM` -/

/-- `ν(s ∩ t) = ν(s) ν(t | s)` in `ℝ`, for a finite measure on plane trees. -/
theorem measureReal_inter_eq_mul_condReal (ν : Measure PlaneTree) [IsFiniteMeasure ν]
    (s t : Set PlaneTree) : ν.real (s ∩ t) = ν.real s * (cond ν s).real t := by
  rw [cond_real_apply_of_discrete]
  by_cases h : ν.real s = 0
  · rw [h, zero_mul]
    exact le_antisymm (h ▸ measureReal_mono Set.inter_subset_left) measureReal_nonneg
  · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- `∫ 1_s f dν = ν(s) ∫ f dν(· | s)` in `ℝ`, for a finite measure on plane trees. -/
theorem integral_indicator_eq_mul_integral_cond (ν : Measure PlaneTree) [IsFiniteMeasure ν]
    (s : Set PlaneTree) (f : PlaneTree → ℝ) :
    ∫ T, s.indicator f T ∂ν = ν.real s * ∫ T, f T ∂cond ν s := by
  rw [integral_cond_eq _ MeasurableSet.of_discrete]
  by_cases h : ν.real s = 0
  · have h' : ν s = 0 := (measureReal_eq_zero_iff).1 h
    rw [h, zero_mul, integral_indicator MeasurableSet.of_discrete,
      Measure.restrict_eq_zero.2 h', integral_zero_measure]
  · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-- **Assembly of Assumption (M)** from bounds on large marked trees (the argument of source
lines 1286–1311, in numerator form): if `P(G_{k_n}(𝒯), |𝒯| > M_n) = o(π_n)` and
`a_n E[1{G_{k_n}(𝒯), |𝒯| > M_n} Ψ_{n-|𝒯|}(0)] = o(π_n)` along admissible sizes, then (M)
holds. Small trees are handled by the uniform ratio limit
(`eventually_abs_uniformFringeLaw_real_sub_le`), large ones by Corollary `cor:cyclicshift` and
`Ψ_n(-1) ≥ c / a_n`. -/
theorem microscopic_of_large (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M)
    (h1 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      (bienayme μ).real {T | G (k n) T ∧ M n < T.vertexCount} ≤ ε * markProb μ G k n)
    (h2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      a n * ∫ T, {T | G (k n) T ∧ M n < T.vertexCount}.indicator
        (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ ≤
          ε * markProb μ G k n) :
    Microscopic μ G k M := by
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  set p : ℕ → ℝ := markProb μ G k with hpdef
  have hp0 : ∀ n, 0 ≤ p n := fun n => measureReal_nonneg
  -- large fringe trees: `P(G(𝒯^n_{U_n}), |𝒯^n_{U_n}| > M_n) ≤ ε π_n`
  have hlarge : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} ≤ ε * p n := by
    intro ε hε
    filter_upwards [h2 (ε * c) (by positivity), hadm] with n hn hadmn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => not_admissible_zero μ (h0 ▸ hadmn)
    have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadmn
    have han : 0 < a n := hT.pos n hn1
    have hinv : (walkProb μ n (-1))⁻¹ ≤ a n / c := by
      rw [inv_le_comm₀ hψ (by positivity), inv_div]
      exact hlow n hn1 hψ
    rw [Cyclic.uniformFringeLaw_real_eq]
    have hI0 : 0 ≤ ∫ T, {T | G (k n) T ∧ M n < T.vertexCount}.indicator
        (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ :=
      integral_nonneg fun T => Set.indicator_nonneg (fun T _ => walkProb_nonneg μ _ _) T
    calc (walkProb μ n (-1))⁻¹ * ∫ T, {T | G (k n) T ∧ M n < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ
        ≤ a n / c * ∫ T, {T | G (k n) T ∧ M n < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ :=
          mul_le_mul_of_nonneg_right hinv hI0
      _ = (a n * ∫ T, {T | G (k n) T ∧ M n < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ) / c := by ring
      _ ≤ ε * c * p n / c := by gcongr
      _ = ε * p n := by field_simp
  -- `|P(G(𝒯^n_{U_n})) - π_n| ≤ ε π_n`
  have hmain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      |(uniformFringeLaw μ n).real {T | G (k n) T} - p n| ≤ ε * p n := by
    intro ε hε
    filter_upwards [eventually_abs_uniformFringeLaw_real_sub_le hT hM.isLittleO (half_pos hε),
      hlarge (ε / 4) (by positivity), h1 (ε / 4) (by positivity), hadm] with n hs hlg hbig hadmn
    have := Cyclic.isProbabilityMeasure_uniformFringeLaw hadmn
    have hs' := hs (fun T => G (k n) T ∧ T.vertexCount ≤ M n) (fun T hT => hT.2)
    have hU := measureReal_split_vertexCount (uniformFringeLaw μ n) (G (k n)) (M n)
    have hP := measureReal_split_vertexCount (bienayme μ) (G (k n)) (M n)
    have hPle : (bienayme μ).real {T | G (k n) T ∧ T.vertexCount ≤ M n} ≤ p n :=
      measureReal_mono (fun T hT => hT.1)
    have hU0 : 0 ≤ (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} :=
      measureReal_nonneg
    have hP0 : 0 ≤ (bienayme μ).real {T | G (k n) T ∧ M n < T.vertexCount} :=
      measureReal_nonneg
    have hp' : p n = (bienayme μ).real {T | G (k n) T} := rfl
    have hPle' : ε / 2 * (bienayme μ).real {T | G (k n) T ∧ T.vertexCount ≤ M n} ≤
        ε / 2 * p n := mul_le_mul_of_nonneg_left hPle (by positivity)
    rw [abs_le] at hs' ⊢
    constructor <;> nlinarith [hs'.1, hs'.2]
  refine ⟨?_, ?_⟩
  · refine isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [hmain ε hε] with n hn
    rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp0 n)]
    exact hn
  · refine tendsto_zero_of_forall_eventually_le (fun n => measureReal_nonneg) fun ε hε => ?_
    filter_upwards [hmain (1 / 2) one_half_pos, hlarge (ε / 2) (half_pos hε)] with n hn hlg
    rw [cond_real_apply_of_discrete, ← Set.ofPred_and]
    rcases (hp0 n).eq_or_lt with hp | hp
    · have h0 : (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} = 0 :=
        le_antisymm (by rw [← hp, mul_zero] at hlg; exact hlg) measureReal_nonneg
      rw [h0, mul_zero]
      exact hε.le
    · rw [abs_le] at hn
      have hupos : 0 < (uniformFringeLaw μ n).real {T | G (k n) T} := by linarith [hn.1]
      rw [inv_mul_le_iff₀ hupos]
      nlinarith [hn.1]

/-- **Corollary `cor:SM`(i)** (source lines 1256–1311, P05): Assumption (S) implies
Assumption (M) along `(k_n)` with respect to the same cutoff `(M_n)`. -/
theorem microscopic_of_structural (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M) :
    Microscopic μ G k M := by
  have hsub : ∀ n, {T : PlaneTree | M n < T.vertexCount} ⊆
      {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount} := by
    intro n T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    have h1 : ((M n : ℕ) : ℝ) < (T.vertexCount : ℝ) := by exact_mod_cast hT
    have h2 : (0 : ℝ) ≤ M n := Nat.cast_nonneg _
    linarith
  refine microscopic_of_large hT hM (fun ε hε => ?_) (fun ε hε => ?_)
  · filter_upwards [(consequenceM_tail hT hM hS).eventually (ge_mem_nhds hε)] with n hn
    rw [Set.ofPred_and, measureReal_inter_eq_mul_condReal, mul_comm]
    refine mul_le_mul_of_nonneg_right ((measureReal_mono (hsub n)).trans hn) measureReal_nonneg
  · filter_upwards [consequenceM_weighted hT hM hS ε hε, eventually_cutoff_facts hT hM]
      with n hn hfacts
    obtain ⟨-, -, ha1⟩ := hfacts
    have hn0 := hn 0 (Nat.zero_le _) (fun _ => 0)
    simp only [Nat.cast_zero, sub_zero] at hn0
    rw [Set.ofPred_and, ← Set.indicator_indicator, integral_indicator_eq_mul_integral_cond]
    have hmono : ∫ T, {T : PlaneTree | M n < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
          ∂cond (bienayme μ) {T | G (k n) T} ≤
        ∫ T, {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
          ∂cond (bienayme μ) {T | G (k n) T} := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun T => Set.indicator_nonneg
        (fun T _ => walkProb_nonneg μ _ _) T) ?_ (Eventually.of_forall fun T =>
          Set.indicator_le_indicator_of_subset (hsub n) (fun T => walkProb_nonneg μ _ _) T)
      refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
        (Eventually.of_forall fun T => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg
        (fun T _ => walkProb_nonneg μ _ _) T)]
      by_cases hT' : T ∈ {T : PlaneTree | (M n : ℝ) / 4 < T.vertexCount}
      · rw [Set.indicator_of_mem hT']
        exact walkProb_le_one μ _ _
      · rw [Set.indicator_of_notMem hT']
        exact zero_le_one
    have han : 0 ≤ a n := by linarith
    calc a n * ((bienayme μ).real {T | G (k n) T} * ∫ T, {T : PlaneTree | M n <
      T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
          ∂cond (bienayme μ) {T | G (k n) T})
        = markProb μ G k n * (a n * ∫ T, {T : PlaneTree | M n < T.vertexCount}.indicator
          (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T
          ∂cond (bienayme μ) {T | G (k n) T}) := by rw [markProb]; ring
      _ ≤ markProb μ G k n * ε := by
          refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hmono han).trans hn0)
            measureReal_nonneg
      _ = ε * markProb μ G k n := mul_comm _ _

/-- **Corollary `cor:SM`(ii)** (source lines 1305–1311): under Assumption (S),
`E[#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}] ∼ n π_n` along admissible sizes. -/
theorem integral_markCount_isEquivalent (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hS : StructuralMicroscopic μ a G k M) :
    IsEquivalent (admissibleSizes μ)
      (fun n => ∫ T, (markCount (G (k n)) T : ℝ) ∂conditioned μ n)
      (fun n => (n : ℝ) * markProb μ G k n) := by
  have h := (microscopic_of_structural hT hM hS).1
  have h2 := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := admissibleSizes μ)).mul h
  refine h2.congr_left (Eventually.of_forall fun n => ?_)
  simp only [Pi.mul_apply, Cyclic.integral_markCount_conditioned]

/-- **Local core estimate** (proof of `cor:SM`(iii), source lines 1330–1353): for a
decomposition `ρ` of `P(· | G(𝒯) = 1)` and `n ≥ 1`,
`P(|𝒯| = n | G(𝒯) = 1) ≤ P(C > n/2) + K E[L] / (n a_n)`. On `{C ≤ n/2}` the forest must have
exactly `n - C ≥ n/2` vertices, and `P(|𝒢_ℓ| = n - c) ≤ C ℓ / ((n - c) a_{n-c})`; the empty forest
contributes nothing since `n - c ≥ 1`. -/
theorem cond_vertexCount_eq_le (hT : StableToolkit μ α a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : PlaneTree → Prop) (ρ : Measure (PlaneTree × ℕ × List PlaneTree)),
      Skeleton μ G ρ → ∀ n : ℕ, 1 ≤ n →
      cond (bienayme μ) {T | G T} {T | T.vertexCount = n} ≤
        ρ {ω | (n : ℝ) / 2 < ω.2.1} +
          ENNReal.ofReal (K / (n * a n)) * ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂ρ := by
  obtain ⟨C₀, hC₀, hloc⟩ := forestSizeWeight_toReal_le hT
  obtain ⟨Cc, hCc, -, hcn⟩ := exists_comparison hT
  refine ⟨2 * C₀ * Cc, by positivity, fun G ρ hρ n hn => ?_⟩
  have han : 0 < a n := hT.pos n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set ψ : ℕ → ℝ≥0∞ := {t : ℕ | t = n}.indicator 1 with hψ
  have hset : cond (bienayme μ) {T | G T} {T | T.vertexCount = n} =
      ∫⁻ T, ψ T.vertexCount ∂cond (bienayme μ) {T | G T} := by
    rw [← lintegral_indicator_one MeasurableSet.of_discrete]
    rfl
  rw [hset, lintegral_cond_vertexCount hρ]
  set h₂ : ℕ → ℕ → ℕ → ℝ≥0∞ := fun c _ q => if 2 * c ≤ n ∧ c + q = n then 1 else 0 with hh₂
  have hpt : ∀ ω : PlaneTree × ℕ × List PlaneTree,
      ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ≤
        {ω : PlaneTree × ℕ × List PlaneTree | (n : ℝ) / 2 < ω.2.1}.indicator 1 ω +
          h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum := by
    intro ω
    by_cases h1 : ω.2.1 + (ω.2.2.map vertexCount).sum = n
    · rw [hψ, Set.indicator_of_mem (show _ ∈ {t : ℕ | t = n} from h1)]
      by_cases h2 : (n : ℝ) / 2 < ω.2.1
      · rw [Set.indicator_of_mem (show ω ∈ {ω : PlaneTree × ℕ × List PlaneTree |
          (n : ℝ) / 2 < ω.2.1} from h2)]
        exact le_self_add
      · push Not at h2
        have h3 : 2 * ω.2.1 ≤ n := by
          have : ((2 * ω.2.1 : ℕ) : ℝ) ≤ n := by push_cast; linarith
          exact_mod_cast this
        simp only [hh₂]
        rw [ite_eq_left ⟨h3, h1⟩]
        exact le_add_self
    · rw [hψ, Set.indicator_of_notMem (show _ ∉ {t : ℕ | t = n} from h1)]
      exact zero_le
  calc ∫⁻ ω, ψ (ω.2.1 + (ω.2.2.map vertexCount).sum) ∂ρ
      ≤ ∫⁻ ω, ({ω : PlaneTree × ℕ × List PlaneTree | (n : ℝ) / 2 < ω.2.1}.indicator 1 ω +
          h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum) ∂ρ := lintegral_mono hpt
    _ = ρ {ω | (n : ℝ) / 2 < ω.2.1} +
          ∫⁻ ω, h₂ ω.2.1 ω.2.2.length (ω.2.2.map vertexCount).sum ∂ρ := by
        rw [lintegral_add_left Measurable.of_discrete,
          lintegral_indicator_one MeasurableSet.of_discrete]
    _ ≤ _ := by
        gcongr
        refine lintegral_skeleton_le hρ h₂ _ fun c L => ?_
        by_cases h2 : 2 * c ≤ n
        · have h1 : ∑' q, forestSizeWeight μ L q * h₂ c L q = forestSizeWeight μ L (n - c) := by
            rw [tsum_eq_single (n - c)]
            · simp only [hh₂]
              rw [ite_eq_left ⟨h2, by omega⟩, mul_one]
            · intro q hq
              simp only [hh₂]
              rw [ite_eq_right (by omega), mul_zero]
          rw [h1, ← ENNReal.ofReal_toReal (forestSizeWeight_ne_top μ L (n - c)),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ((hloc L (n - c) (by omega)).trans ?_)
          have hnc : 1 ≤ n - c := by omega
          have hanc : 0 < a (n - c) := hT.pos _ hnc
          have hB := hcn n (n - c) hnc (by omega)
          have hncR : (n : ℝ) ≤ 2 * ((n - c : ℕ) : ℝ) := by
            have : n ≤ 2 * (n - c) := by omega
            exact_mod_cast this
          have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h3 : (n : ℝ) * a n ≤ (2 * ((n - c : ℕ) : ℝ)) * (Cc * a (n - c)) :=
            mul_le_mul hncR hB han.le (by positivity)
          have h4 : C₀ * L * ((n : ℝ) * a n) ≤
              C₀ * L * ((2 * ((n - c : ℕ) : ℝ)) * (Cc * a (n - c))) := by gcongr
          nlinarith
        · have h1 : ∑' q, forestSizeWeight μ L q * h₂ c L q = 0 := by
            refine ENNReal.tsum_eq_zero.2 fun q => ?_
            simp only [hh₂]
            rw [ite_eq_right (fun h => h2 h.1), mul_zero]
          rw [h1]
          exact zero_le

/-- **Corollary `cor:SM`(iii)** (source lines 1258–1260, 1313–1364): under Assumption (S), if
`π_n = O(1/n)` along admissible sizes, then the root of `𝒯^n` is marked with vanishing
probability, `P(G_{k_n}(𝒯^n) = 1) → 0`. The proof writes
`P(G_{k_n}(𝒯^n) = 1) = π_n P_{k_n}(|𝒯| = n) / P(|𝒯| = n)`, uses `P(|𝒯| = n) ≥ c / (n a_n)`
(`tree_size_asymp`) and the local core estimate `cond_vertexCount_eq_le`; null marks
(`π_n = 0`) and empty forests are covered (correction F13). -/
theorem conditioned_mark_tendsto_zero (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hS : StructuralMicroscopic μ a G k M)
    (hO : markProb μ G k =O[admissibleSizes μ] (fun n => 1 / (n : ℝ))) :
    Tendsto (fun n => (conditioned μ n).real {T | G (k n) T}) (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨ρ, hρ, hS1, hS2⟩ := hS
  obtain ⟨K, hK0, hK⟩ := cond_vertexCount_eq_le hT
  obtain ⟨c, _C, hc, hasymp⟩ := tree_size_asymp hT
  obtain ⟨B, hB⟩ := hO.bound
  obtain ⟨C₅, hC₅, hlin⟩ := hT.regularlyVarying.exists_le_mul hT.monotone hT.pos hT.rho_pos.le
    hT.rho_lt_one
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  set B' : ℝ := max B 1 with hB'
  have hB'1 : 1 ≤ B' := le_max_right _ _
  refine tendsto_zero_of_forall_eventually_le (fun n => measureReal_nonneg) fun ε hε => ?_
  set η : ℝ := ε * c / (2 * B') with hη
  set δ : ℝ := ε * c / (2 * B' * (K * C₅ + 1)) with hδ
  have hη0 : 0 < η := by positivity
  have hδ0 : 0 < δ := by positivity
  filter_upwards [eventually_cutoff_facts hT hM, hB, hadm,
    (hS1 1 one_pos).eventually (ge_mem_nhds hη0),
    hS2.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hδ0))] with n hfacts hBn hadmn h1 h2
  obtain ⟨hM8, h2M, ha1⟩ := hfacts
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have han : 0 < a n := by linarith
  have haM : 0 < a (M n) := hT.pos _ (by omega)
  have haMn : a (M n) ≤ a n := hT.monotone (by omega)
  have hanl : a n ≤ C₅ * n := hlin n hn1
  -- `π_n ≤ B' / n`
  have hπ : markProb μ G k n ≤ B' / n := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ markProb μ G k n from measureReal_nonneg),
      abs_of_pos (show (0 : ℝ) < 1 / n by positivity)] at hBn
    calc markProb μ G k n ≤ B * (1 / n) := hBn
      _ ≤ B' * (1 / n) := by gcongr; exact le_max_left _ _
      _ = B' / n := by ring
  have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
  -- the formula `P(G(𝒯^n)) = P(|𝒯| = n)⁻¹ π_n P(|𝒯| = n | G(𝒯) = 1)`
  have hform : (conditioned μ n).real {T | G (k n) T} =
      ((bienayme μ).real {T | T.vertexCount = n})⁻¹ * (markProb μ G k n *
        (cond (bienayme μ) {T | G (k n) T}).real {T | T.vertexCount = n}) := by
    rw [conditioned, cond_real_apply_of_discrete, Set.inter_comm,
      measureReal_inter_eq_mul_condReal]
    rfl
  obtain ⟨hlow, -⟩ := hasymp n hn1 hadmn
  have hPpos : 0 < (bienayme μ).real {T | T.vertexCount = n} :=
    lt_of_lt_of_le (by positivity) hlow
  have hinv : ((bienayme μ).real {T | T.vertexCount = n})⁻¹ ≤ n * a n / c := by
    rw [inv_le_comm₀ hPpos (by positivity), inv_div]
    exact hlow
  by_cases hπz : bienayme μ {T | G (k n) T} = 0
  · rw [hform, cond_eq_zero_of_meas_eq_zero hπz, measureReal_zero_apply, mul_zero, mul_zero]
    exact hε.le
  have hsk := hρ (k n) (pos_iff_ne_zero.2 hπz)
  have := hsk.isProbabilityMeasure
  have hX := hK (G (k n)) (ρ (k n)) hsk n hn1
  rw [show K / (n * a n) = K * a (M n) / (n * a n) / a (M n) by field_simp] at hX
  have hb := toReal_le_add_of_le_add_div (by positivity) haM hδ0.le (measure_ne_top _ _) hX h2
  rw [← measureReal_def, ← measureReal_def] at hb
  have hsub : (ρ (k n)).real {ω | (n : ℝ) / 2 < ω.2.1} ≤
      (ρ (k n)).real {ω | 1 * (M n : ℝ) < ω.2.1} := by
    refine measureReal_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : ((2 * M n : ℕ) : ℝ) ≤ n := by exact_mod_cast h2M
    push_cast at this
    linarith
  set r := (ρ (k n)).real {ω | 1 * (M n : ℝ) < ω.2.1} with hr
  have hr0 : 0 ≤ r := measureReal_nonneg
  set Y := (cond (bienayme μ) {T | G (k n) T}).real {T | T.vertexCount = n} with hY
  have hY0 : 0 ≤ Y := measureReal_nonneg
  have hY : Y ≤ r + K * a (M n) / (n * a n) * δ := hb.trans (by gcongr)
  rw [hform]
  have e1 : n * a n / c * (markProb μ G k n * r) ≤ ε / 2 := by
    have : n * a n / c * (markProb μ G k n * r) = (n * markProb μ G k n) * (a n * r) / c := by
      ring
    rw [this, div_le_iff₀ hc]
    have hnπ : (n : ℝ) * markProb μ G k n ≤ B' := by
      rw [le_div_iff₀ hnR] at hπ; linarith
    calc (n : ℝ) * markProb μ G k n * (a n * r) ≤ B' * η :=
          mul_le_mul hnπ h1 (by positivity) (by positivity)
      _ = ε / 2 * c := by rw [hη]; field_simp
  have e2 : n * a n / c * (markProb μ G k n * (K * a (M n) / (n * a n) * δ)) ≤ ε / 2 := by
    have : n * a n / c * (markProb μ G k n * (K * a (M n) / (n * a n) * δ)) =
        markProb μ G k n * K * a (M n) * δ / c := by
      field_simp
    rw [this, div_le_iff₀ hc]
    have h3 : markProb μ G k n * a (M n) ≤ B' * C₅ := by
      calc markProb μ G k n * a (M n) ≤ B' / n * (C₅ * n) :=
            mul_le_mul hπ (haMn.trans hanl) haM.le (by positivity)
        _ = B' * C₅ := by field_simp
    calc markProb μ G k n * K * a (M n) * δ = K * (markProb μ G k n * a (M n)) * δ := by ring
      _ ≤ K * (B' * C₅) * δ := by gcongr
      _ ≤ ε / 2 * c := by
          rw [hδ]
          have hden : 0 < 2 * B' * (K * C₅ + 1) := by positivity
          rw [mul_div_assoc', div_le_iff₀ hden]
          have : K * (B' * C₅) * (ε * c) ≤ ε / 2 * c * (2 * B' * (K * C₅ + 1)) := by
            have hε2 : 0 ≤ ε * c * B' := by positivity
            nlinarith
          linarith
  calc ((bienayme μ).real {T | T.vertexCount = n})⁻¹ * (markProb μ G k n * Y)
      ≤ n * a n / c * (markProb μ G k n * (r + K * a (M n) / (n * a n) * δ)) := by
        refine mul_le_mul hinv ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (hY.trans (by linarith [hsub])) hπ0
    _ = n * a n / c * (markProb μ G k n * r) +
          n * a n / c * (markProb μ G k n * (K * a (M n) / (n * a n) * δ)) := by ring
    _ ≤ ε := by linarith

end PoissonDeclumping.Bridge
