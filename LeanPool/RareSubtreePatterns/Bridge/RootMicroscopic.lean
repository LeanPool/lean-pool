/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.Microscopic
public import LeanPool.RareSubtreePatterns.RootDeclumping.Lemma51


/-!
# Inherited microscopicity for declumped marks: Lemma `lem:root_declumping`(iii)

Work package WP3.5 of the bridge plan. Source lines 2197–2299 (Lemma 5.1, proof step P16).
Parts (i), (ii) and the parent formula are in `RootDeclumping/ParentFormula.lean` and
`RootDeclumping/Lemma51.lean`; this file proves part (iii).

Notation: `Ghat = declumpedMark B G` (root degree in `B` and some marked child), `D` the root
degree, `𝒢_ℓ` a forest of `ℓ` independent Bienaymé trees, `c_B = cB μ B`.

## Main statements

* `lintegral_declumped_le` (branching property and union bound over the marked child):
  `E[1{Ghat(𝒯)} Φ(|𝒯|)] ≤ ∑_{d ∈ B} d μ_d E[1{G(𝒯)} ∑_q P(|𝒢_{d-1}| = q) Φ(1 + |𝒯| + q)]`, and
  `lintegral_declumped_le_of_bound`, its form under a pointwise bound `A(t) + κ(d)`.
* `tsum_forestSizeWeight_mul_walkProb` (`eq:parent_convolution`):
  `∑_q P(|𝒢_ℓ| = q) Ψ_{N-q}(0) = Ψ_N(-ℓ) ≤ sup_x Ψ_N(x)`.
* `forest_bound_unweighted`, `forest_bound_weighted` (`eq:parent_forest` with the truncation by
  `1`): for a marked child `t` and `d ≥ 1`, the other `d - 1` children contribute at most
  `1{|t| > M/4} (sup_x Ψ_{n-1-|t|}(x)) + (K / a_n) min(1, d / a_{⌊M/2⌋})`.
* `tendsto_tsum_min_div`: `∑_{d ∈ B} d μ_d min(1, d / a_{m_n}) → 0` (dominated convergence).
* `microscopic_declumped` (**Lemma `lem:root_declumping`(iii)**): (S) for `(G_k)` and
  `c_B ∈ (0, ∞)` imply (M) for `(Ghat_k)` with the same cutoff.

Departure from the paper (periodic case, correction F3): the bridge-weighted estimate is used in
numerator form with the time shift `j = 1` of `consequenceM_weighted_sup`, instead of "replacing
`n` by `n - 1`" in a ratio with `Ψ_{n-1}(-1)` (which vanishes for `d ≥ 2` at admissible `n`);
the denominator `Ψ_n(-1) ≥ c / a_n` enters only in `microscopic_of_large`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped ENNReal Topology

namespace PoissonDeclumping.Bridge

open PlaneTree

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### The branching decomposition at a marked child -/

/-- `E[f(𝒯)] = ∑_T w(T) f(T)`. -/
theorem lintegral_bienayme_eq_tsum (μ : PMF ℕ) (f : PlaneTree → ℝ≥0∞) :
    ∫⁻ T, f T ∂bienayme μ = ∑' T, weight μ T * f T := by
  rw [lintegral_countable']
  exact tsum_congr fun T => by rw [bienayme_apply_singleton, mul_comm]

/-- Decomposition of `∑_T w(T) F(T)` according to the root degree and the children. -/
theorem tsum_weight_mul_eq_sigma (μ : PMF ℕ) (F : PlaneTree → ℝ≥0∞) :
    ∑' T, weight μ T * F T =
      ∑' d, ∑' f : Fin d → PlaneTree, μ d * (∏ i, weight μ (f i)) * F (node (List.ofFn f)) := by
  rw [← equivSigma.symm.tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun d => tsum_congr fun f => ?_
  rw [equivSigma_symm_apply, weight_node_ofFn]

/-- Separating the `i`-th child: for `F` depending on the `i`-th tree and the others,
`∑_{f : Fin (d+1) → 𝕋} F(f_i, (f_j)_{j ≠ i}) = ∑_t ∑_g F(t, g)`. -/
theorem tsum_pi_succAbove (d : ℕ) (i : Fin (d + 1))
    (F : PlaneTree → (Fin d → PlaneTree) → ℝ≥0∞) :
    ∑' f : Fin (d + 1) → PlaneTree, F (f i) (fun j => f (i.succAbove j)) =
      ∑' t, ∑' g, F t g := by
  rw [← (Fin.insertNthEquiv (fun _ => PlaneTree) i).tsum_eq, ← ENNReal.tsum_prod]
  refine tsum_congr fun p => ?_
  simp [Fin.insertNthEquiv]

/-- **Branching property at a marked child** (source lines 2236–2240, 2247–2251): for the `i`-th
child among `d + 1`, `∑_f ∏_j w(f_j) 1{G(f_i)} Φ(1 + ∑_j |f_j|) =
E[1{G(𝒯)} ∑_q P(|𝒢_d| = q) Φ(1 + |𝒯| + q)]`: the other `d` children form an independent forest. -/
theorem tsum_child_mark (μ : PMF ℕ) (d : ℕ) (i : Fin (d + 1)) (G : PlaneTree → Prop)
    (Φ : ℕ → ℝ≥0∞) :
    ∑' f : Fin (d + 1) → PlaneTree, (∏ j, weight μ (f j)) *
        ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount)) =
      ∫⁻ t, {t | G t}.indicator
        (fun t => ∑' q, forestSizeWeight μ d q * Φ (1 + t.vertexCount + q)) t ∂bienayme μ := by
  set F : PlaneTree → (Fin d → PlaneTree) → ℝ≥0∞ := fun t g => weight μ t *
    {t | G t}.indicator 1 t *
      ((∏ j, weight μ (g j)) * Φ (1 + t.vertexCount + ∑ j, (g j).vertexCount)) with hF
  have h1 : ∀ f : Fin (d + 1) → PlaneTree, (∏ j, weight μ (f j)) *
      ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount)) =
      F (f i) (fun j => f (i.succAbove j)) := by
    intro f
    simp only [hF]
    rw [Fin.prod_univ_succAbove _ i, Fin.sum_univ_succAbove _ i, add_assoc]
    ring
  rw [tsum_congr h1, tsum_pi_succAbove d i F]
  rw [lintegral_bienayme_eq_tsum]
  refine tsum_congr fun t => ?_
  rw [ENNReal.tsum_mul_left, tsum_prod_weight_mul μ d (fun q => Φ (1 + t.vertexCount + q))]
  by_cases ht : t ∈ {t | G t}
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, Pi.one_apply, mul_one]
  · simp [Set.indicator_of_notMem ht]

/-- **The declumped mark and its marked children** (source lines 2236–2241, union bound over the
marked child): `E[1{Ghat(𝒯)} Φ(|𝒯|)] ≤ ∑_{d ∈ B} d μ_d E[1{G(𝒯)} ∑_q P(|𝒢_{d-1}| = q) Φ(1 + |𝒯| +
  q)]`. -/
theorem lintegral_declumped_le (μ : PMF ℕ) (B : Set ℕ) (G : PlaneTree → Prop)
    (Φ : ℕ → ℝ≥0∞) :
    ∫⁻ T, {T | declumpedMark B G T}.indicator (fun T => Φ T.vertexCount) T ∂bienayme μ ≤
      ∑' d, B.indicator (fun d => (d : ℝ≥0∞) * μ d * ∫⁻ t, {t | G t}.indicator
        (fun t => ∑' q, forestSizeWeight μ (d - 1) q * Φ (1 + t.vertexCount + q)) t
          ∂bienayme μ) d := by
  rw [lintegral_bienayme_eq_tsum, tsum_weight_mul_eq_sigma]
  refine ENNReal.tsum_le_tsum fun d => ?_
  have hv : ∀ f : Fin d → PlaneTree,
      (node (List.ofFn f)).vertexCount = 1 + ∑ j, (f j).vertexCount := by
    intro f
    rw [vertexCount_node, List.map_ofFn, List.sum_ofFn, add_comm]
    rfl
  by_cases hd : d ∈ B
  · rw [Set.indicator_of_mem hd]
    rcases d with _ | d
    · refine (le_of_eq (ENNReal.tsum_eq_zero.2 fun f => ?_)).trans zero_le
      rw [Set.indicator_of_notMem, mul_zero]
      rintro ⟨-, U, hU, -⟩
      simp at hU
    · have hpt : ∀ f : Fin (d + 1) → PlaneTree,
          μ (d + 1) * (∏ j, weight μ (f j)) * {T | declumpedMark B G T}.indicator
            (fun T => Φ T.vertexCount) (node (List.ofFn f)) ≤
          ∑ i : Fin (d + 1), μ (d + 1) * ((∏ j, weight μ (f j)) *
            ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount))) := by
        intro f
        by_cases hG : node (List.ofFn f) ∈ {T | declumpedMark B G T}
        · rw [Set.indicator_of_mem hG, hv]
          obtain ⟨-, U, hU, hGU⟩ := hG
          rw [children_node, List.mem_ofFn] at hU
          obtain ⟨i₀, rfl⟩ := hU
          refine le_trans ?_ (Finset.single_le_sum (f := fun i : Fin (d + 1) =>
            μ (d + 1) * ((∏ j, weight μ (f j)) *
              ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount))))
            (fun _ _ => zero_le) (Finset.mem_univ i₀))
          rw [Set.indicator_of_mem (show f i₀ ∈ {t | G t} from hGU), Pi.one_apply, one_mul,
            mul_assoc]
        · rw [Set.indicator_of_notMem hG, mul_zero]
          exact zero_le
      calc ∑' f : Fin (d + 1) → PlaneTree, μ (d + 1) * (∏ j, weight μ (f j)) *
            {T | declumpedMark B G T}.indicator (fun T => Φ T.vertexCount) (node (List.ofFn f))
          ≤ ∑' f : Fin (d + 1) → PlaneTree, ∑ i : Fin (d + 1), μ (d + 1) *
              ((∏ j, weight μ (f j)) *
                ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount))) :=
            ENNReal.tsum_le_tsum hpt
        _ = ∑ i : Fin (d + 1), μ (d + 1) * ∑' f : Fin (d + 1) → PlaneTree,
              (∏ j, weight μ (f j)) *
                ({t | G t}.indicator 1 (f i) * Φ (1 + ∑ j, (f j).vertexCount)) := by
            rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
            exact Finset.sum_congr rfl fun i _ => ENNReal.tsum_mul_left
        _ = _ := by
            simp_rw [tsum_child_mark]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.add_sub_cancel]
            ring
  · rw [Set.indicator_of_notMem hd]
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun f => ?_)
    rw [Set.indicator_of_notMem, mul_zero]
    rintro ⟨hB, -⟩
    simp only [rootDegree_node, List.length_ofFn] at hB
    exact hd hB

/-- `∫⁻ 1_s f dν = ν(s) ∫⁻ f dν(· | s)` for a finite measure on plane trees. -/
theorem lintegral_indicator_eq_mul_lintegral_cond (ν : Measure PlaneTree) [IsFiniteMeasure ν]
    (s : Set PlaneTree) (f : PlaneTree → ℝ≥0∞) :
    ∫⁻ t, s.indicator f t ∂ν = ν s * ∫⁻ t, f t ∂cond ν s := by
  rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    lintegral_indicator MeasurableSet.of_discrete]
  by_cases h : ν s = 0
  · rw [Measure.restrict_eq_zero.2 h, lintegral_zero_measure, h, zero_mul]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_mul]

/-- **Union bound over the marked child, with a pointwise forest bound** (source lines
2236–2241, 2247–2270): if for every `d ≥ 1` and every marked `t`,
`∑_q P(|𝒢_{d-1}| = q) Φ(1 + |t| + q) ≤ A(t) + κ(d)`, then
`E[1{Ghat(𝒯)} Φ(|𝒯|)] ≤ π (c_B E[A(𝒯) | G(𝒯) = 1] + ∑_{d ∈ B} d μ_d κ(d))`. -/
theorem lintegral_declumped_le_of_bound (μ : PMF ℕ) (B : Set ℕ) (G : PlaneTree → Prop)
    (Φ : ℕ → ℝ≥0∞) (A : PlaneTree → ℝ≥0∞) (κ : ℕ → ℝ≥0∞)
    (hb : ∀ d t, 1 ≤ d → G t →
      ∑' q, forestSizeWeight μ (d - 1) q * Φ (1 + t.vertexCount + q) ≤ A t + κ d) :
    ∫⁻ T, {T | declumpedMark B G T}.indicator (fun T => Φ T.vertexCount) T ∂bienayme μ ≤
      bienayme μ {T | G T} * (cB μ B * ∫⁻ t, A t ∂cond (bienayme μ) {T | G T} +
        ∑' d, B.indicator (fun d => (d : ℝ≥0∞) * μ d * κ d) d) := by
  refine (lintegral_declumped_le μ B G Φ).trans ?_
  have hterm : ∀ d, B.indicator (fun d => (d : ℝ≥0∞) * μ d * ∫⁻ t, {t | G t}.indicator
      (fun t => ∑' q, forestSizeWeight μ (d - 1) q * Φ (1 + t.vertexCount + q)) t
        ∂bienayme μ) d ≤
      bienayme μ {T | G T} * (B.indicator (fun j => (j : ℝ≥0∞) * μ j) d *
        ∫⁻ t, A t ∂cond (bienayme μ) {T | G T}) +
      bienayme μ {T | G T} * B.indicator (fun d => (d : ℝ≥0∞) * μ d * κ d) d := by
    intro d
    by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd, Set.indicator_of_mem hd]
      rcases Nat.eq_zero_or_pos d with rfl | hd1
      · simp
      have h1 : ∫⁻ t, {t | G t}.indicator
          (fun t => ∑' q, forestSizeWeight μ (d - 1) q * Φ (1 + t.vertexCount + q)) t
            ∂bienayme μ ≤ ∫⁻ t, {t | G t}.indicator (fun t => A t + κ d) t ∂bienayme μ := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ {t | G t}
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
          exact hb d t hd1 ht
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      have h2 : ∫⁻ t, {t | G t}.indicator (fun t => A t + κ d) t ∂bienayme μ =
          bienayme μ {T | G T} * (∫⁻ t, A t ∂cond (bienayme μ) {T | G T} +
            κ d * cond (bienayme μ) {T | G T} Set.univ) := by
        rw [lintegral_indicator_eq_mul_lintegral_cond, lintegral_add_right _ measurable_const,
          lintegral_const]
      rw [h2] at h1
      have hcond : cond (bienayme μ) {T | G T} Set.univ ≤ 1 := by
        rcases eq_zero_or_isProbabilityMeasure (cond (bienayme μ) {T | G T}) with h | h
        · rw [h]; simp
        · rw [measure_univ]
      calc (d : ℝ≥0∞) * μ d * ∫⁻ t, {t | G t}.indicator
            (fun t => ∑' q, forestSizeWeight μ (d - 1) q * Φ (1 + t.vertexCount + q)) t
              ∂bienayme μ
          ≤ (d : ℝ≥0∞) * μ d * (bienayme μ {T | G T} *
              (∫⁻ t, A t ∂cond (bienayme μ) {T | G T} + κ d * 1)) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd, Set.indicator_of_notMem hd]
      simp
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    mul_add]
  rfl

/-! ### Forest convolution and the `min(1, D / a_{M_n})` domination -/

/-- **Forest first-passage decomposition, `tsum` form** (source lines 2250–2255,
`eq:parent_convolution`): for every `N : ℤ`,
`∑_q P(|𝒢_ℓ| = q) Ψ_{N-q}(0) = Ψ_N(-ℓ)` (both sides vanish for `N < 0`). -/
theorem tsum_forestSizeWeight_mul_walkProb (μ : PMF ℕ) (ℓ : ℕ) (N : ℤ) :
    ∑' q, forestSizeWeight μ ℓ q * ENNReal.ofReal (walkProb μ (N - q) 0) =
      ENNReal.ofReal (walkProb μ N (-ℓ)) := by
  rcases lt_or_ge N 0 with hN | hN
  · rw [walkProb_of_neg μ hN, ENNReal.ofReal_zero]
    refine ENNReal.tsum_eq_zero.2 fun q => ?_
    rw [walkProb_of_neg μ (by omega), ENNReal.ofReal_zero, mul_zero]
  · obtain ⟨Nn, rfl⟩ := Int.eq_ofNat_of_zero_le hN
    rw [tsum_eq_sum (s := Finset.range (Nn + 1)) fun q hq => by
      rw [walkProb_of_neg μ (by simp at hq; omega), ENNReal.ofReal_zero, mul_zero],
      walkProb_neg_eq_sum, ENNReal.ofReal_sum_of_nonneg fun q _ =>
        mul_nonneg ENNReal.toReal_nonneg (walkProb_nonneg μ _ _)]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q ≤ Nn := by simp at hq; omega
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (forestSizeWeight_ne_top μ ℓ q)]
    congr 3
    push_cast [hq']
    ring

/-- The dominated-convergence step of source lines 2242–2245:
`∑_{d ∈ B} d μ_d min(1, d / a_{m_n}) → 0` whenever `m_n → ∞`. -/
theorem tendsto_tsum_min_div (hT : StableToolkit μ α a) (B : Set ℕ) {l : Filter ℕ}
    {m : ℕ → ℕ} (hm : Tendsto m l atTop) :
    Tendsto (fun n => ∑' d, B.indicator
      (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / a (m n))) d) l (𝓝 0) := by
  have h0 : (0 : ℝ) = ∑' _d : ℕ, (0 : ℝ) := tsum_zero.symm
  rw [h0]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun d => B.indicator (fun d => (d : ℝ) * LeafHeight.mass μ d) d)
    (RootDeclumping.summable_cB hT.critical B) (fun d => ?_) ?_
  · have ha : Tendsto (fun n => a (m n)) l atTop := hT.tendsto_atTop.comp hm
    have h1 : Tendsto (fun n => min 1 ((d : ℝ) / a (m n))) l (𝓝 (min 1 0)) :=
      tendsto_const_nhds.min (tendsto_const_nhds.div_atTop ha)
    rw [min_eq_right zero_le_one] at h1
    by_cases hd : d ∈ B
    · simp only [Set.indicator_of_mem hd]
      simpa using h1.const_mul ((d : ℝ) * LeafHeight.mass μ d)
    · simp only [Set.indicator_of_notMem hd]
      exact tendsto_const_nhds
  · filter_upwards [hm.eventually_ge_atTop 1] with n hn d
    have han : 0 < a (m n) := hT.pos _ hn
    by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd, Real.norm_eq_abs]
      have hmin0 : 0 ≤ min 1 ((d : ℝ) / a (m n)) := le_min zero_le_one (by positivity)
      have hdm : 0 ≤ (d : ℝ) * LeafHeight.mass μ d :=
        mul_nonneg (Nat.cast_nonneg d) (LeafHeight.mass_nonneg d)
      rw [abs_of_nonneg (mul_nonneg hdm hmin0)]
      exact mul_le_of_le_one_right hdm (min_le_left _ _)
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd, norm_zero]

/-- `min u₁ u₂ ≤ K min(1, y)` when `u₁ ≤ K` and `u₂ ≤ K y`. -/
theorem min_le_mul_min_one {u₁ u₂ K y : ℝ} (h1 : u₁ ≤ K) (h2 : u₂ ≤ K * y) :
    min u₁ u₂ ≤ K * min 1 y := by
  rcases le_total y 1 with hy | hy
  · rw [min_eq_right hy]
    exact (min_le_right _ _).trans h2
  · rw [min_eq_left hy, mul_one]
    exact (min_le_left _ _).trans h1

theorem le_ofReal_min {y : ℝ≥0∞} {u v : ℝ} (h1 : y ≤ ENNReal.ofReal u)
    (h2 : y ≤ ENNReal.ofReal v) : y ≤ ENNReal.ofReal (min u v) := by
  rcases min_choice u v with h | h <;> rw [h] <;> assumption

/-- **Unweighted forest bound at a marked child** (source lines 2236–2245): for `M ≥ 8`, `d ≥ 1`
and every tree `t`, `P(1 + |t| + |𝒢_{d-1}| > M) ≤ 1{|t| > M/4} + K min(1, d / a_{⌊M/2⌋})`:
if `|t| ≤ M/4` the other forest has more than `M/2` vertices. -/
theorem forest_bound_unweighted (hT : StableToolkit μ α a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ M : ℕ, 8 ≤ M → ∀ (d : ℕ) (t : PlaneTree), 1 ≤ d →
      ∑' q, forestSizeWeight μ (d - 1) q *
          {s : ℕ | M < s}.indicator (1 : ℕ → ℝ≥0∞) (1 + t.vertexCount + q) ≤
        {t : PlaneTree | (M : ℝ) / 4 < t.vertexCount}.indicator (1 : PlaneTree → ℝ≥0∞) t +
          ENNReal.ofReal (K * min 1 ((d : ℝ) / a (M / 2))) := by
  obtain ⟨Ct, hCt, htail⟩ := forestSizeWeight_tail_le_ofReal hT
  refine ⟨max Ct 1, le_max_right _ _, fun M hM d t hd => ?_⟩
  have hm : 1 ≤ M / 2 := by omega
  have ham : 0 < a (M / 2) := hT.pos _ hm
  have hle1 : ∑' q, forestSizeWeight μ (d - 1) q *
      {s : ℕ | M < s}.indicator (1 : ℕ → ℝ≥0∞) (1 + t.vertexCount + q) ≤ 1 := by
    refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) (tsum_forestSizeWeight_le_one μ (d - 1))
    refine mul_le_of_le_one_right zero_le ?_
    by_cases h : 1 + t.vertexCount + q ∈ {s : ℕ | M < s}
    · rw [Set.indicator_of_mem h, Pi.one_apply]
    · rw [Set.indicator_of_notMem h]; exact zero_le
  by_cases ht : t ∈ {t : PlaneTree | (M : ℝ) / 4 < t.vertexCount}
  · rw [Set.indicator_of_mem ht, Pi.one_apply]
    exact hle1.trans le_self_add
  · refine le_trans ?_ le_add_self
    have ht4 : 4 * t.vertexCount ≤ M := by
      simp only [Set.mem_ofPred_eq, not_lt] at ht
      have : ((4 * t.vertexCount : ℕ) : ℝ) ≤ M := by push_cast; linarith
      exact_mod_cast this
    have hle2 : ∑' q, forestSizeWeight μ (d - 1) q *
        {s : ℕ | M < s}.indicator (1 : ℕ → ℝ≥0∞) (1 + t.vertexCount + q) ≤
        ENNReal.ofReal (Ct * ((d - 1 : ℕ) : ℝ) / a (M / 2)) := by
      refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) (htail (d - 1) (M / 2) hm)
      by_cases h : 1 + t.vertexCount + q ∈ {s : ℕ | M < s}
      · have hq : q ∈ Set.Ioi (M / 2) := by
          simp only [Set.mem_ofPred_eq] at h
          simp only [Set.mem_Ioi]
          omega
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hq, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem h, mul_zero]; exact zero_le
    refine (le_ofReal_min (hle1.trans ENNReal.ofReal_one.ge) hle2).trans
      (ENNReal.ofReal_le_ofReal (min_le_mul_min_one (le_max_right _ _) ?_))
    have hd1 : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
    rw [mul_div_assoc', div_le_iff₀ ham, div_mul_cancel₀ _ ham.ne']
    exact mul_le_mul (le_max_left _ _) hd1 (Nat.cast_nonneg _) (by positivity)

/-- **Bridge-weighted forest bound at a marked child** (source lines 2247–2264,
`eq:parent_convolution`, `eq:parent_forest`, numerator form): for `M ≥ 8`, `n ≥ 2M`, `d ≥ 1` and
every tree `t`,
`E[Ψ_{n-1-|t|-|𝒢_{d-1}|}(0) 1{1 + |t| + |𝒢_{d-1}| > M}] ≤ 1{|t| > M/4} sup_x Ψ_{n-1-|t|}(x) +
(K / a_n) min(1, d / a_{⌊M/2⌋})`. The first term is the convolution bound, the second combines it
with the weighted forest tail (the other forest has more than `M/2` vertices). -/
theorem forest_bound_weighted (hT : StableToolkit μ α a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M n : ℕ, 8 ≤ M → 2 * M ≤ n → ∀ (d : ℕ) (t : PlaneTree), 1 ≤ d →
      ∑' q, forestSizeWeight μ (d - 1) q * ENNReal.ofReal ({s : ℕ | M < s}.indicator
          (fun s => walkProb μ ((n : ℤ) - s) 0) (1 + t.vertexCount + q)) ≤
        ENNReal.ofReal ({t : PlaneTree | (M : ℝ) / 4 < t.vertexCount}.indicator
          (fun t => supWalk μ ((n : ℤ) - 1 - t.vertexCount)) t) +
          ENNReal.ofReal (K / a n * min 1 ((d : ℝ) / a (M / 2))) := by
  obtain ⟨Cw, hCw, hw⟩ := forestSizeWeight_weighted_tail_le_ofReal hT
  obtain ⟨C₁, hC₁, hsup2⟩ := exists_supWalk_le_of_le_two_mul hT
  obtain ⟨Cc, hCc, -, hcn⟩ := exists_comparison hT
  refine ⟨max C₁ (Cw * Cc), le_max_of_le_left hC₁, fun M n hM hn d t hd => ?_⟩
  have hm : 1 ≤ M / 2 := by omega
  have ham : 0 < a (M / 2) := hT.pos _ hm
  have han : 0 < a n := hT.pos n (by omega)
  set N : ℤ := (n : ℤ) - 1 - t.vertexCount with hN
  have hcastq : ∀ q : ℕ, (n : ℤ) - ((1 + t.vertexCount + q : ℕ) : ℤ) = N - q := by
    intro q; push_cast; ring
  -- the convolution bound
  have hconv : ∑' q, forestSizeWeight μ (d - 1) q * ENNReal.ofReal ({s : ℕ | M < s}.indicator
      (fun s => walkProb μ ((n : ℤ) - s) 0) (1 + t.vertexCount + q)) ≤
      ENNReal.ofReal (supWalk μ N) := by
    calc _ ≤ ∑' q, forestSizeWeight μ (d - 1) q * ENNReal.ofReal (walkProb μ (N - q) 0) := by
          refine ENNReal.tsum_le_tsum fun q => mul_le_mul_right ?_ _
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← hcastq q]
          exact Set.indicator_le_self' (fun _ _ => walkProb_nonneg μ _ _) _
      _ = ENNReal.ofReal (walkProb μ N (-((d - 1 : ℕ) : ℤ))) :=
          tsum_forestSizeWeight_mul_walkProb μ (d - 1) N
      _ ≤ ENNReal.ofReal (supWalk μ N) := ENNReal.ofReal_le_ofReal (walkProb_le_supWalk μ _ _)
  by_cases ht : t ∈ {t : PlaneTree | (M : ℝ) / 4 < t.vertexCount}
  · rw [Set.indicator_of_mem ht]
    exact hconv.trans le_self_add
  · refine le_trans ?_ le_add_self
    have ht4 : 4 * t.vertexCount ≤ M := by
      simp only [Set.mem_ofPred_eq, not_lt] at ht
      have : ((4 * t.vertexCount : ℕ) : ℝ) ≤ M := by push_cast; linarith
      exact_mod_cast this
    set Nn : ℕ := n - 1 - t.vertexCount with hNn
    have hNN : N = (Nn : ℤ) := by
      rw [hN, hNn]
      have : 1 + t.vertexCount ≤ n := by omega
      push_cast [Nat.sub_sub, this]
      ring
    have hNn1 : 1 ≤ Nn := by omega
    have haNn : 0 < a Nn := hT.pos _ hNn1
    -- first bound: `sup_x Ψ_{n-1-|t|} ≤ C₁ / a_n`
    have hA : ∑' q, forestSizeWeight μ (d - 1) q * ENNReal.ofReal ({s : ℕ | M < s}.indicator
        (fun s => walkProb μ ((n : ℤ) - s) 0) (1 + t.vertexCount + q)) ≤
        ENNReal.ofReal (C₁ / a n) := by
      refine hconv.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hNN]
      exact hsup2 n Nn (by omega) hNn1 (by omega)
    -- second bound: the weighted forest tail beyond `M/2`
    have hB : ∑' q, forestSizeWeight μ (d - 1) q * ENNReal.ofReal ({s : ℕ | M < s}.indicator
        (fun s => walkProb μ ((n : ℤ) - s) 0) (1 + t.vertexCount + q)) ≤
        ENNReal.ofReal (Cw * ((d - 1 : ℕ) : ℝ) / (a (M / 2) * a Nn)) := by
      refine le_trans (ENNReal.tsum_le_tsum fun q => ?_) (hw (d - 1) (M / 2) Nn hm (by omega))
      by_cases h : 1 + t.vertexCount + q ∈ {s : ℕ | M < s}
      · have hq : q ∈ Set.Ioi (M / 2) := by
          simp only [Set.mem_ofPred_eq] at h
          simp only [Set.mem_Ioi]
          omega
        rw [Set.indicator_of_mem h, Set.indicator_of_mem hq]
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        rw [hcastq q, hNN]
        exact walkProb_le_supWalk μ _ _
      · rw [Set.indicator_of_notMem h, ENNReal.ofReal_zero, mul_zero]; exact zero_le
    refine (le_ofReal_min hA hB).trans
      (ENNReal.ofReal_le_ofReal (min_le_mul_min_one ?_ ?_))
    · exact div_le_div_of_nonneg_right (le_max_left _ _) han.le
    · have hd1 : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
      have hcomp : a n ≤ Cc * a Nn := hcn n Nn hNn1 (by omega)
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : Cw * ((d - 1 : ℕ) : ℝ) ≤ max C₁ (Cw * Cc) * d / Cc := by
        rw [le_div_iff₀ hCc]
        calc Cw * ((d - 1 : ℕ) : ℝ) * Cc = Cw * Cc * ((d - 1 : ℕ) : ℝ) := by ring
          _ ≤ max C₁ (Cw * Cc) * d :=
            mul_le_mul (le_max_right _ _) hd1 (Nat.cast_nonneg _) (le_max_of_le_left hC₁)
      have h2 : a n * a (M / 2) ≤ Cc * (a (M / 2) * a Nn) := by nlinarith
      calc Cw * ((d - 1 : ℕ) : ℝ) * (a n * a (M / 2))
          ≤ max C₁ (Cw * Cc) * d / Cc * (Cc * (a (M / 2) * a Nn)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = max C₁ (Cw * Cc) * d * (a (M / 2) * a Nn) := by field_simp

/-! ### Lemma `lem:root_declumping`(iii) -/

/-- `∑_{d ∈ B} d μ_d K min(1, d / x) = K ∑_{d ∈ B} d μ_d min(1, d / x)` (from `ℝ≥0∞` to `ℝ`). -/
theorem tsum_indicator_mul_ofReal_min (hc : IsCritical μ) (B : Set ℕ) {K x : ℝ} (hK : 0 ≤ K)
    (hx : 0 < x) :
    ∑' d, B.indicator (fun d => (d : ℝ≥0∞) * μ d * ENNReal.ofReal (K * min 1 ((d : ℝ) / x))) d =
      ENNReal.ofReal (K * ∑' d, B.indicator
        (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / x)) d) := by
  have hmin : ∀ d : ℕ, 0 ≤ min 1 ((d : ℝ) / x) := fun d => le_min zero_le_one (by positivity)
  have hnn : ∀ d, 0 ≤ B.indicator
      (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / x)) d := fun d =>
    Set.indicator_nonneg (fun d _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
      (LeafHeight.mass_nonneg d)) (hmin d)) d
  have hsum : Summable (fun d => B.indicator
      (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / x)) d) := by
    refine Summable.of_nonneg_of_le hnn (fun d => ?_) (RootDeclumping.summable_cB hc B)
    by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd]
      exact mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg d) (LeafHeight.mass_nonneg d))
        (min_le_left _ _)
    · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd]
  rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun d => mul_nonneg hK (hnn d))
    (hsum.mul_left K)]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ B
  · rw [Set.indicator_of_mem hd, Set.indicator_of_mem hd,
      show K * ((d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / x)) =
        (d : ℝ) * LeafHeight.mass μ d * (K * min 1 ((d : ℝ) / x)) by ring,
      ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg d) (LeafHeight.mass_nonneg d)),
      ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast, LeafHeight.mass,
      ENNReal.ofReal_toReal (μ.apply_ne_top d)]
  · rw [Set.indicator_of_notMem hd, Set.indicator_of_notMem hd, mul_zero, ENNReal.ofReal_zero]

/-- From `Y ≤ P (C X + y)` in `ℝ≥0∞` to `ℝ`. -/
theorem toReal_le_mul_add {Y P C X : ℝ≥0∞} {y : ℝ} (hP : P ≠ ∞) (hC : C ≠ ∞) (hX : X ≠ ∞)
    (hy : 0 ≤ y) (h : Y ≤ P * (C * X + ENNReal.ofReal y)) :
    Y.toReal ≤ P.toReal * (C.toReal * X.toReal + y) := by
  have hCX : C * X ≠ ∞ := ENNReal.mul_ne_top hC hX
  have hfin : P * (C * X + ENNReal.ofReal y) ≠ ∞ :=
    ENNReal.mul_ne_top hP (ENNReal.add_ne_top.2 ⟨hCX, ENNReal.ofReal_ne_top⟩)
  refine (ENNReal.toReal_mono hfin h).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hCX ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hy]

theorem indicator_indicator_vertexCount {β : Type*} [Zero β] (S : Set PlaneTree) (P : ℕ → Prop)
    (f : ℕ → β) (T : PlaneTree) :
    S.indicator (fun T => {s : ℕ | P s}.indicator f T.vertexCount) T =
      {T | T ∈ S ∧ P T.vertexCount}.indicator (fun T => f T.vertexCount) T := by
  by_cases h1 : T ∈ S <;> by_cases h2 : P T.vertexCount
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show T.vertexCount ∈ {s | P s} from h2),
      Set.indicator_of_mem (show T ∈ {T | T ∈ S ∧ P T.vertexCount} from ⟨h1, h2⟩)]
  · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (show T.vertexCount ∉ {s | P s} from h2),
      Set.indicator_of_notMem (show T ∉ {T | T ∈ S ∧ P T.vertexCount} from fun h => h2 h.2)]
  · rw [Set.indicator_of_notMem h1,
      Set.indicator_of_notMem (show T ∉ {T | T ∈ S ∧ P T.vertexCount} from fun h => h1 h.1)]
  · rw [Set.indicator_of_notMem h1,
      Set.indicator_of_notMem (show T ∉ {T | T ∈ S ∧ P T.vertexCount} from fun h => h1 h.1)]

theorem tsum_indicator_min_nonneg (B : Set ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ ∑' d, B.indicator
      (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / x)) d :=
  tsum_nonneg fun d => Set.indicator_nonneg (fun d _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (LeafHeight.mass_nonneg d))
      (le_min zero_le_one (by positivity))) d

/-- **Lemma `lem:root_declumping`(iii)** (source lines 2212–2214, 2231–2298, P16): if the raw
marks `(G_k)` satisfy Assumption (S) along `(k_n)` with respect to the cutoff `(M_n)` and
`c_B ∈ (0, ∞)`, then the declumped marks `Ghat_k = declumpedMark B G_k` satisfy Assumption (M)
along `(k_n)` with respect to the same cutoff. Periodic offspring laws are included: the paper's
"replace `n` by `n - 1`" (line 2286) is replaced by the numerator form of Lemma
`lem:consequenceM` with time shift `j = 1` (`consequenceM_weighted_sup`), so no `Ψ_{n-1}(-1)`
appears (correction F3). -/
theorem microscopic_declumped (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} {B : Set ℕ} (hS : StructuralMicroscopic μ a G k M) (hM : IsCutoff M)
    (hB0 : 0 < cB μ B) (hB1 : cB μ B < ∞) :
    Microscopic μ (fun j => declumpedMark B (G j)) k M := by
  have hc := hT.critical
  have hne := hT.nondegenerate
  have hbpos : 0 < RootDeclumping.bB μ B :=
    (RootDeclumping.bB_pos_iff_cBReal_pos hc B).2 ((RootDeclumping.cB_pos_iff hc B).1 hB0)
  set b := RootDeclumping.bB μ B with hbdef
  set cBR := (cB μ B).toReal with hcBR
  have hcBR0 : 0 ≤ cBR := ENNReal.toReal_nonneg
  have hcB_ne : cB μ B ≠ ∞ := hB1.ne
  have hdecl : ∀ n, b * markProb μ G k n ≤ markProb μ (fun j => declumpedMark B (G j)) k n :=
    fun n => RootDeclumping.bB_mul_le_declumped hc hne B (G (k n))
  obtain ⟨KU, hKU1, hU⟩ := forest_bound_unweighted hT
  obtain ⟨KW, hKW0, hW⟩ := forest_bound_weighted hT
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hm' : Tendsto (fun n => M n / 2) (admissibleSizes μ) atTop := by
    refine (tendsto_atTop.2 fun b => ?_).mono_left hl
    filter_upwards [hM.tendsto_atTop.eventually_ge_atTop (2 * b)] with n hn
    omega
  have hs := tendsto_tsum_min_div hT B hm'
  refine microscopic_of_large hT hM (fun ε hε => ?_) (fun ε hε => ?_)
  · -- unweighted: `P(Ghat(𝒯), |𝒯| > M_n) = o(π̂_n)` (`eq:parent_unweighted`)
    have hδ : 0 < b * ε / (2 * (cBR + 1)) := by positivity
    have hδ2 : 0 < b * ε / (2 * KU) := by have : 0 < KU := by linarith
                                          positivity
    filter_upwards [eventually_cutoff_facts hT hM,
      (consequenceM_tail hT hM hS).eventually (ge_mem_nhds hδ),
      hs.eventually (ge_mem_nhds hδ2)] with n hf hp hsn
    obtain ⟨hM8, -, -⟩ := hf
    have ham : 0 < a (M n / 2) := hT.pos _ (by omega)
    have hE := lintegral_declumped_le_of_bound μ B (G (k n))
      (fun s => {s : ℕ | M n < s}.indicator (1 : ℕ → ℝ≥0∞) s)
      (fun t => {t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}.indicator
        (1 : PlaneTree → ℝ≥0∞) t)
      (fun d => ENNReal.ofReal (KU * min 1 ((d : ℝ) / a (M n / 2))))
      (fun d t hd _ => hU (M n) hM8 d t hd)
    rw [tsum_indicator_mul_ofReal_min hc B (by linarith) ham,
      lintegral_indicator_one MeasurableSet.of_discrete] at hE
    simp_rw [indicator_indicator_vertexCount] at hE
    rw [show (fun T : PlaneTree => (1 : ℕ → ℝ≥0∞) T.vertexCount) = 1 from rfl,
      lintegral_indicator_one MeasurableSet.of_discrete] at hE
    have hR := toReal_le_mul_add (measure_ne_top _ _) hcB_ne (measure_ne_top _ _)
      (mul_nonneg (by linarith) (tsum_indicator_min_nonneg B _ ham.le)) hE
    rw [← measureReal_def, ← measureReal_def, ← measureReal_def] at hR
    change (bienayme μ).real {T | declumpedMark B (G (k n)) T ∧ M n < T.vertexCount} ≤ _
    have e1 : cBR * (cond (bienayme μ) {T | G (k n) T}).real
        {t | (M n : ℝ) / 4 < t.vertexCount} ≤ b * ε / 2 := by
      calc _ ≤ cBR * (b * ε / (2 * (cBR + 1))) := mul_le_mul_of_nonneg_left hp hcBR0
        _ ≤ b * ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            have : 0 ≤ b * ε := by positivity
            nlinarith
    have e2 : KU * ∑' d, B.indicator
        (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / a (M n / 2))) d ≤
        b * ε / 2 := by
      calc _ ≤ KU * (b * ε / (2 * KU)) := mul_le_mul_of_nonneg_left hsn (by linarith)
        _ = b * ε / 2 := by field_simp
    have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
    calc (bienayme μ).real {T | declumpedMark B (G (k n)) T ∧ M n < T.vertexCount}
        ≤ markProb μ G k n * (cBR * (cond (bienayme μ) {T | G (k n) T}).real
            {t | (M n : ℝ) / 4 < t.vertexCount} + KU * ∑' d, B.indicator
              (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / a (M n / 2))) d) := hR
      _ ≤ markProb μ G k n * (b * ε) := by gcongr; linarith
      _ ≤ ε * markProb μ (fun j => declumpedMark B (G j)) k n := by
          have := hdecl n
          nlinarith
  · -- bridge-weighted: `a_n E[1{Ghat(𝒯), |𝒯| > M_n} Ψ_{n-|𝒯|}(0)] = o(π̂_n)` (`eq:parent_bridge`)
    have hδ : 0 < b * ε / (2 * (cBR + 1)) := by positivity
    have hδ2 : 0 < b * ε / (2 * (KW + 1)) := by positivity
    filter_upwards [eventually_cutoff_facts hT hM,
      consequenceM_weighted_sup hT hM hS _ hδ,
      hs.eventually (ge_mem_nhds hδ2)] with n hf hw hsn
    obtain ⟨hM8, h2M, ha1⟩ := hf
    have han : 0 < a n := by linarith
    have ham : 0 < a (M n / 2) := hT.pos _ (by omega)
    have hw1 := hw 1 le_rfl
    simp only [Nat.cast_one] at hw1
    have hE := lintegral_declumped_le_of_bound μ B (G (k n))
      (fun s => ENNReal.ofReal ({s : ℕ | M n < s}.indicator
        (fun s => walkProb μ ((n : ℤ) - s) 0) s))
      (fun t => ENNReal.ofReal ({t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}.indicator
        (fun t => supWalk μ ((n : ℤ) - 1 - t.vertexCount)) t))
      (fun d => ENNReal.ofReal (KW / a n * min 1 ((d : ℝ) / a (M n / 2))))
      (fun d t hd _ => hW (M n) n hM8 h2M d t hd)
    rw [tsum_indicator_mul_ofReal_min hc B (by positivity) ham] at hE
    set W := ∫⁻ t, ENNReal.ofReal ({t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}.indicator
        (fun t => supWalk μ ((n : ℤ) - 1 - t.vertexCount)) t) ∂cond (bienayme μ) {T | G (k n) T}
      with hWdef
    have hWfin : W ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_ne_top (cond (bienayme μ) {T | G (k n) T}) Set.univ) ?_
      rw [← lintegral_one]
      refine lintegral_mono fun t => ENNReal.ofReal_le_one.2 ?_
      by_cases ht : t ∈ {t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}
      · rw [Set.indicator_of_mem ht]; exact supWalk_le_one μ _
      · rw [Set.indicator_of_notMem ht]; exact zero_le_one
    have hWreal : W.toReal = ∫ t, {t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}.indicator
        (fun t => supWalk μ ((n : ℤ) - 1 - t.vertexCount)) t ∂cond (bienayme μ) {T | G (k n) T} :=
          by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun T => Set.indicator_nonneg
        (fun T _ => supWalk_nonneg μ _) T) Measurable.of_discrete.aestronglyMeasurable]
    have hR := toReal_le_mul_add (measure_ne_top _ _) hcB_ne hWfin
      (mul_nonneg (by positivity) (tsum_indicator_min_nonneg B _ ham.le)) hE
    rw [← measureReal_def, hWreal] at hR
    -- the left-hand side
    change a n * ∫ T, {T | declumpedMark B (G (k n)) T ∧ M n < T.vertexCount}.indicator
      (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ ≤ _
    have hL : ∫ T, {T | declumpedMark B (G (k n)) T ∧ M n < T.vertexCount}.indicator
        (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) T ∂bienayme μ =
        (∫⁻ T, {T | declumpedMark B (G (k n)) T}.indicator (fun T => ENNReal.ofReal
          ({s : ℕ | M n < s}.indicator (fun s => walkProb μ ((n : ℤ) - s) 0) T.vertexCount)) T
            ∂bienayme μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun T => Set.indicator_nonneg
        (fun T _ => walkProb_nonneg μ _ _) T) Measurable.of_discrete.aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun T => ?_
      by_cases h1 : declumpedMark B (G (k n)) T <;> by_cases h2 : M n < T.vertexCount
      · rw [Set.indicator_of_mem (show T ∈ {T | declumpedMark B (G (k n)) T ∧
          M n < T.vertexCount} from ⟨h1, h2⟩), Set.indicator_of_mem
          (show T ∈ {T | declumpedMark B (G (k n)) T} from h1),
          Set.indicator_of_mem (show T.vertexCount ∈ {s : ℕ | M n < s} from h2)]
      · rw [Set.indicator_of_notMem (show T ∉ {T | declumpedMark B (G (k n)) T ∧
          M n < T.vertexCount} from fun h => h2 h.2), Set.indicator_of_mem
          (show T ∈ {T | declumpedMark B (G (k n)) T} from h1),
          Set.indicator_of_notMem (show T.vertexCount ∉ {s : ℕ | M n < s} from h2),
          ENNReal.ofReal_zero]
      · rw [Set.indicator_of_notMem (show T ∉ {T | declumpedMark B (G (k n)) T ∧
          M n < T.vertexCount} from fun h => h1 h.1), Set.indicator_of_notMem
          (show T ∉ {T | declumpedMark B (G (k n)) T} from h1), ENNReal.ofReal_zero]
      · rw [Set.indicator_of_notMem (show T ∉ {T | declumpedMark B (G (k n)) T ∧
          M n < T.vertexCount} from fun h => h1 h.1), Set.indicator_of_notMem
          (show T ∉ {T | declumpedMark B (G (k n)) T} from h1), ENNReal.ofReal_zero]
    rw [hL]
    set I := ∫ t, {t : PlaneTree | (M n : ℝ) / 4 < t.vertexCount}.indicator
        (fun t => supWalk μ ((n : ℤ) - 1 - t.vertexCount)) t ∂cond (bienayme μ) {T | G (k n) T}
    set sn := ∑' d, B.indicator
      (fun d => (d : ℝ) * LeafHeight.mass μ d * min 1 ((d : ℝ) / a (M n / 2))) d
    have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
    have hsn0 : 0 ≤ sn := tsum_indicator_min_nonneg B _ ham.le
    have e1 : cBR * (a n * I) ≤ b * ε / 2 := by
      calc _ ≤ cBR * (b * ε / (2 * (cBR + 1))) := mul_le_mul_of_nonneg_left hw1 hcBR0
        _ ≤ b * ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            have : 0 ≤ b * ε := by positivity
            nlinarith
    have e2 : KW * sn ≤ b * ε / 2 := by
      calc _ ≤ KW * (b * ε / (2 * (KW + 1))) := mul_le_mul_of_nonneg_left hsn hKW0
        _ ≤ b * ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            have : 0 ≤ b * ε := by positivity
            nlinarith
    calc a n * (∫⁻ T, {T | declumpedMark B (G (k n)) T}.indicator (fun T => ENNReal.ofReal
          ({s : ℕ | M n < s}.indicator (fun s => walkProb μ ((n : ℤ) - s) 0) T.vertexCount)) T
            ∂bienayme μ).toReal
        ≤ a n * (markProb μ G k n * (cBR * I + KW / a n * sn)) :=
          mul_le_mul_of_nonneg_left hR han.le
      _ = markProb μ G k n * (cBR * (a n * I) + KW * sn) := by field_simp
      _ ≤ markProb μ G k n * (b * ε) := by gcongr; linarith
      _ ≤ ε * markProb μ (fun j => declumpedMark B (G j)) k n := by
          have := hdecl n
          nlinarith

end PoissonDeclumping.Bridge
