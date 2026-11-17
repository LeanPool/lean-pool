/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.BridgeRemoval

import LeanPool.RareSubtreePatterns.Bridge.CriterionM
import LeanPool.RareSubtreePatterns.RegularVariation.Consequences

/-!
# Truncation: Lemma `lem:truncate` and Lemma `lem:pnqn`

Work package WP5 of the bridge plan. Source lines 1662–1696 (Lemma 4.4, `P09`) and 1732–1788
(Lemma 4.5, `P10`). Notation: `W_n^M = cyclicSum (G (k n)) M (List.ofFn ω)` under
`bridgeLaw μ n = P(· | S_n = -1)`, `q_n = qProb μ (G (k n)) (M n) n`,
`p_n = pProb μ (G (k n)) (M n)`, `π_n = markProb μ G k n`, `𝒯^n_{U_n} ~ uniformFringeLaw μ n`.
"`(n π_n)` bounded" is the hypothesis `∃ C, ∀ᶠ n in admissibleSizes μ, n π_n ≤ C` of
`PoissonApproximationStatement`.

## Main statements

* `tendsto_paperTVDist_cyclicSum_truncated` (**Lemma `lem:truncate`(i)**): under (M) and
  bounded `n π_n`, `d_TV(W_n^{M_n}, W_n^∞) → 0` along admissible sizes;
  `tendsto_paperTVDist_cyclicSum_markedCountLaw`: the same against `markedCountLaw μ G k n`.
* `tendsto_mul_qProb_sub_mul_markProb`, `tendsto_paperTVDist_poisson_qProb_markProb`
  (**Lemma `lem:truncate`(ii)**): `n q_n - n π_n → 0` and `d_TV(Po(n q_n), Po(n π_n)) → 0`.
* `eventually_abs_qProb_sub_markProb_le`, `isEquivalent_qProb_markProb`: `q_n ∼ π_n` under (M).
* `isLittleO_walkVecLaw_firstMarked_abs_sum_gt(_admissible)` (**Lemma `lem:pnqn`(i)**):
  `P(I_1^{(M_n)} = 1, |S_{M_n}| > r_n) = o(p_n)`, `r_n = √(a_{M_n} a_n)` (needs only the
  toolkit and the cutoff; marginal tightness replaces functional tightness, F6).
* `isEquivalent_pProb_qProb`, `isEquivalent_pProb_qProb_markProb` (**Lemma `lem:pnqn`(ii)**):
  `p_n ∼ q_n` (toolkit and cutoff only; ratio limit at compatible endpoints, F4) and `q_n ∼ π_n`
  (Assumption (M)).

Lemma `lem:truncate` needs neither the toolkit nor `IsCutoff`; `π_n = 0` is allowed throughout
(`IsEquivalent` and `cond` of a null event handle it, F13).
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- `ν(s ∩ t) = ν(s) ν(t | s)` in `ℝ`, also when `ν(s) = 0`. -/
theorem measureReal_inter_eq_mul_cond {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsFiniteMeasure ν] {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    ν.real (s ∩ t) = ν.real s * (cond ν s).real t := by
  rw [measureReal_def (μ := cond ν s), cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def, ← measureReal_def]
  by_cases h : ν.real s = 0
  · have : ν.real (s ∩ t) = 0 :=
      le_antisymm (h ▸ measureReal_mono Set.inter_subset_left) measureReal_nonneg
    rw [this, h, zero_mul]
  · field_simp

/-- `q = P(G(𝒯^n_{U_n}) = 1) (1 - P(|𝒯^n_{U_n}| > M | G(𝒯^n_{U_n}) = 1))`. -/
theorem qProb_eq_sub_mul_cond (μ : PMF ℕ) (G : PlaneTree → Prop) (M n : ℕ) :
    qProb μ G M n = (uniformFringeLaw μ n).real {T | G T} -
      (uniformFringeLaw μ n).real {T | G T} *
        (cond (uniformFringeLaw μ n) {T | G T}).real {T | M < T.vertexCount} := by
  rw [qProb_eq_uniformFringeLaw, ← measureReal_inter_eq_mul_cond _ MeasurableSet.of_discrete,
    measureReal_split_vertexCount (uniformFringeLaw μ n) G M, ← Set.ofPred_and]
  ring

/-- Under Assumption (M): `|q_n - π_n| ≤ ε π_n` eventually along admissible sizes (source lines
1694–1695: `q_n - π_n = (P(G(𝒯^n_{U_n}) = 1) - π_n) - P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| > M_n)`). -/
theorem eventually_abs_qProb_sub_markProb_le {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ,
      |qProb μ (G (k n)) (M n) n - markProb μ G k n| ≤ ε * markProb μ G k n := by
  set δ : ℝ := min (ε / 3) 1 with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε / 3 := min_le_left _ _
  filter_upwards [hmic.1.def hδ0, hmic.2.eventually (ge_mem_nhds hδ0)] with n h1 h2
  have hπ : 0 ≤ markProb μ G k n := measureReal_nonneg
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hπ] at h1
  set U := (uniformFringeLaw μ n).real {T | G (k n) T} with hU
  set t := (cond (uniformFringeLaw μ n) {T | G (k n) T}).real {T | M n < T.vertexCount}
  have ht0 : 0 ≤ t := measureReal_nonneg
  have hU0 : 0 ≤ U := measureReal_nonneg
  rw [qProb_eq_sub_mul_cond]
  have hUle : U ≤ 2 * markProb μ G k n := by
    rw [abs_le] at h1
    nlinarith
  have hUt : U * t ≤ 2 * markProb μ G k n * δ := mul_le_mul hUle h2 ht0 (by positivity)
  rw [abs_le] at h1 ⊢
  constructor <;> nlinarith [mul_nonneg hU0 ht0]

/-! ### Lemma `lem:truncate` -/

/-- **Lemma `lem:truncate`(i)** (source lines 1675–1693): under Assumption (M) and bounded
`n π_n`, `d_TV(W_n^{M_n}, W_n^n) → 0` under `P(· | S_n = -1)`, where `W_n^n = W_n^∞` is the full
count (`markedCountLaw_eq`). Proof: the coupling bound `d_TV ≤ n P(G(𝒯^n_{U_n}) = 1,
|𝒯^n_{U_n}| > M_n)` (`paperTVDist_cyclicSum_truncated_le`), which is `o(n π_n)` by (M). -/
theorem tendsto_paperTVDist_cyclicSum_truncated {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n => paperTVDist
      ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) (M n) (List.ofFn ω)))
      ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) ⊤ (List.ofFn ω))))
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hbd
  have hfun : ∀ n : ℕ, (fun ω : Fin n → ℤ => cyclicSum (G (k n)) ⊤ (List.ofFn ω)) =
      fun ω => cyclicSum (G (k n)) (n : ℕ∞) (List.ofFn ω) := by
    intro n
    funext ω
    unfold cyclicSum shiftIndicator
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (firstIndicator_of_length_le (by simp)).symm
  have hlim : Tendsto (fun n => 2 * C * (cond (uniformFringeLaw μ n) {T | G (k n) T}).real
      {T | M n < T.vertexCount}) (admissibleSizes μ) (𝓝 0) := by
    simpa using hmic.2.const_mul (2 * C)
  refine squeeze_zero' (Eventually.of_forall fun n => paperTVDist_nonneg _ _) ?_ hlim
  filter_upwards [hC, eventually_abs_qProb_sub_markProb_le hmic one_pos, hmic.1.def one_pos]
    with n hCn _ h1
  have hπ : 0 ≤ markProb μ G k n := measureReal_nonneg
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hπ, abs_le] at h1
  rw [hfun n]
  refine (paperTVDist_cyclicSum_truncated_le μ (G (k n)) (M n) n).trans ?_
  rw [Set.ofPred_and, measureReal_inter_eq_mul_cond _ MeasurableSet.of_discrete]
  set U := (uniformFringeLaw μ n).real {T | G (k n) T}
  set t := (cond (uniformFringeLaw μ n) {T | G (k n) T}).real {T | M n < T.vertexCount}
  have ht0 : 0 ≤ t := measureReal_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hUle : U ≤ 2 * markProb μ G k n := by linarith
  calc (n : ℝ) * (U * t) ≤ n * (2 * markProb μ G k n * t) := by gcongr
    _ = 2 * (n * markProb μ G k n) * t := by ring
    _ ≤ 2 * C * t := by gcongr

/-- **Lemma `lem:truncate`(i)**, with the law of the marked count `#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u)}`
(Lemma `lem:RW`, `markedCountLaw_eq`). -/
theorem tendsto_paperTVDist_cyclicSum_markedCountLaw {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hmic : Microscopic μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n => paperTVDist
      ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) (M n) (List.ofFn ω)))
      (markedCountLaw μ G k n)) (admissibleSizes μ) (𝓝 0) := by
  simpa only [markedCountLaw_eq] using tendsto_paperTVDist_cyclicSum_truncated hmic hbd

/-- **Lemma `lem:truncate`(ii)**, first half (source lines 1694–1696): `n q_n - n π_n → 0`. -/
theorem tendsto_mul_qProb_sub_mul_markProb {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n : ℕ => (n : ℝ) * qProb μ (G (k n)) (M n) n - n * markProb μ G k n)
      (admissibleSizes μ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hbd
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C' := max C 1 with hC'
  have hC'0 : 0 < C' := lt_max_of_lt_right one_pos
  filter_upwards [hC, eventually_abs_qProb_sub_markProb_le hmic
    (show 0 < ε / (2 * C') by positivity)] with n hCn hn
  have hπ : 0 ≤ markProb μ G k n := measureReal_nonneg
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.dist_eq, sub_zero, ← mul_sub, abs_mul, abs_of_nonneg hn0]
  have hnπ : (n : ℝ) * markProb μ G k n ≤ C' := hCn.trans (le_max_left _ _)
  calc (n : ℝ) * |qProb μ (G (k n)) (M n) n - markProb μ G k n|
      ≤ n * (ε / (2 * C') * markProb μ G k n) := by gcongr
    _ = ε / (2 * C') * (n * markProb μ G k n) := by ring
    _ ≤ ε / (2 * C') * C' := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- **Lemma `lem:truncate`(ii)** (source line 1696): `d_TV(Po(n q_n), Po(n π_n)) → 0`, via
`d_TV(Po(x), Po(y)) ≤ |x - y|`. -/
theorem tendsto_paperTVDist_poisson_qProb_markProb {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) :
    Tendsto (fun n : ℕ => paperTVDist
      (poissonMeasure (Real.toNNReal ((n : ℝ) * qProb μ (G (k n)) (M n) n)))
      (poissonMeasure (Real.toNNReal ((n : ℝ) * markProb μ G k n))))
      (admissibleSizes μ) (𝓝 0) := by
  refine tendsto_paperTVDist_poissonMeasure ?_
  refine (tendsto_mul_qProb_sub_mul_markProb hmic hbd).congr fun n => ?_
  have hq : 0 ≤ (n : ℝ) * qProb μ (G (k n)) (M n) n :=
    mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  have hπ : 0 ≤ (n : ℝ) * markProb μ G k n := mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  rw [Real.coe_toNNReal _ hq, Real.coe_toNNReal _ hπ]


/-! ### Lemma `lem:pnqn` -/

/-- `q_n ∼ π_n` under Assumption (M) (source lines 1778–1783, uniform-vertex representation). -/
theorem isEquivalent_qProb_markProb {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hmic : Microscopic μ G k M) :
    IsEquivalent (admissibleSizes μ) (fun n => qProb μ (G (k n)) (M n) n) (markProb μ G k) := by
  refine isLittleO_iff.2 fun ε hε => ?_
  filter_upwards [eventually_abs_qProb_sub_markProb_le hmic hε] with n hn
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ markProb μ G k n from measureReal_nonneg)]
  exact hn

/-- The walk lives on its lattice: `d ∣ S_m + m` almost surely (from `LatticeLocal.support`). -/
theorem ae_dvd_sum_add {d : ℕ} {L : ℝ} (hloc : LatticeLocal μ a d L) (m : ℕ) :
    ∀ᵐ b ∂walkVecLaw μ m, (d : ℤ) ∣ ∑ i, b i + m := by
  rw [ae_iff]
  have hsub : {b : Fin m → ℤ | ¬(d : ℤ) ∣ ∑ i, b i + m} ⊆
      ⋃ s : ℤ, {b : Fin m → ℤ | ¬(d : ℤ) ∣ s + m ∧ ∑ i, b i = s} :=
    fun b hb => Set.mem_iUnion.2 ⟨_, hb, rfl⟩
  refine measure_mono_null hsub (measure_iUnion_null fun s => ?_)
  by_cases hs : (d : ℤ) ∣ s + m
  · simp [hs]
  · have h0 : walkProb μ m s = 0 := by
      by_contra h
      exact hs (hloc.support m s h)
    rw [walkProb_natCast, measureReal_eq_zero_iff] at h0
    exact measure_mono_null (fun b hb => hb.2) h0

/-- A `{0,1}`-indicator takes values in `[0, 1]`. -/
theorem indicator_one_mem_Icc {X : Type*} (s : Set X) (x : X) :
    0 ≤ s.indicator (1 : X → ℝ) x ∧ s.indicator (1 : X → ℝ) x ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- A bounded real function of `(X_1, …, X_m)` is integrable. -/
theorem integrable_walkVecLaw_of_abs_le (μ : PMF ℕ) {m : ℕ} {f : (Fin m → ℤ) → ℝ} (C : ℝ)
    (h : ∀ b, |f b| ≤ C) : Integrable f (walkVecLaw μ m) :=
  Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable C
    (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact h b)

/-- **Lemma `lem:pnqn`(i)** (source lines 1747–1771), along `atTop`: with
`r_n = √(a_{M_n} a_n)`, `P(I_1^{(M_n)} = 1, |S_{M_n}| > r_n) = o(p_n)`. Only the cutoff
properties and marginal tightness (`tight`, correction F6) are used. -/
theorem isLittleO_walkVecLaw_firstMarked_abs_sum_gt (hT : StableToolkit μ α a)
    (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) {M : ℕ → ℕ} (hM : IsCutoff M) :
    (fun n => (walkVecLaw μ (M n)).real {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
        √(a (M n) * a n) < |((∑ i, ω i : ℤ) : ℝ)|}) =o[atTop]
      (fun n => pProb μ (G (k n)) (M n)) := by
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have haM : Tendsto (fun n => a (M n)) atTop atTop := hT.tendsto_atTop.comp hM.tendsto_atTop
  have hr : Tendsto (fun n => (√(a (M n) * a n) - 1) / a (M n)) atTop atTop := by
    have h1 : Tendsto (fun n => -(a (M n))⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp haM).neg
    refine (hsq.1.atTop_add h1).congr' (Eventually.of_forall fun n => ?_)
    dsimp only
    ring
  have hM1 : ∀ᶠ n in atTop, 1 ≤ M n := hM.tendsto_atTop.eventually_ge_atTop 1
  refine isLittleO_iff.2 fun ε hε => ?_
  filter_upwards [hT.eventually_walkLaw_tail_le hM1 hr hε] with n hn
  have hp : 0 ≤ pProb μ (G (k n)) (M n) := measureReal_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, abs_of_nonneg hp]
  refine (walkVecLaw_firstMarked_abs_sum_gt_le μ (G (k n)) (M n) _).trans ?_
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 (M n)))
      (fun j => {T : PlaneTree | G (k n) T ∧ T.vertexCount = j}) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr fun T hi hj => hij ?_
    rw [← hi.2, ← hj.2]
  have hsum : ∑ j ∈ Finset.Icc 1 (M n), (bienayme μ).real {T | G (k n) T ∧ T.vertexCount = j} ≤
      pProb μ (G (k n)) (M n) := by
    rw [← measureReal_biUnion_finset hdisj (fun _ _ => MeasurableSet.of_discrete), pProb_eq]
    refine measureReal_mono ?_
    intro T hT
    simp only [Set.mem_iUnion, Finset.mem_Icc, exists_prop] at hT
    obtain ⟨j, ⟨-, hj⟩, hG, rfl⟩ := hT
    exact ⟨hG, hj⟩
  calc ∑ j ∈ Finset.Icc 1 (M n), (bienayme μ).real {T | G (k n) T ∧ T.vertexCount = j} *
        (walkLaw μ (M n - j)).real {x : ℤ | √(a (M n) * a n) - 1 < |(x : ℝ)|}
      ≤ ∑ j ∈ Finset.Icc 1 (M n),
          (bienayme μ).real {T | G (k n) T ∧ T.vertexCount = j} * ε :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hn _ (Nat.sub_le _ _)) measureReal_nonneg
    _ = ε * ∑ j ∈ Finset.Icc 1 (M n),
          (bienayme μ).real {T | G (k n) T ∧ T.vertexCount = j} := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ ≤ ε * pProb μ (G (k n)) (M n) := mul_le_mul_of_nonneg_left hsum hε.le

/-- **Lemma `lem:pnqn`(i)** along admissible sizes. -/
theorem isLittleO_walkVecLaw_firstMarked_abs_sum_gt_admissible (hT : StableToolkit μ α a)
    (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) {M : ℕ → ℕ} (hM : IsCutoff M) :
    (fun n => (walkVecLaw μ (M n)).real {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
        √(a (M n) * a n) < |((∑ i, ω i : ℤ) : ℝ)|}) =o[admissibleSizes μ]
      (fun n => pProb μ (G (k n)) (M n)) :=
  (isLittleO_walkVecLaw_firstMarked_abs_sum_gt hT G k hM).mono inf_le_left

/-- **Lemma `lem:pnqn`(ii), first half** (source lines 1740–1775): `p_n ∼ q_n`, by the Markov
property at time `M_n`, the ratio limit `Ψ_{n-M_n}(-1 - S_{M_n}) / Ψ_n(-1) → 1` on
`{|S_{M_n}| ≤ r_n}` at compatible endpoints (correction F4: `S_{M_n} ≡ -M_n (mod d)` almost
surely), the bound `Ψ_{n-M_n}(·) / Ψ_n(-1) ≤ C`, and part (i). No assumption on the marks. -/
theorem isEquivalent_pProb_qProb (hT : StableToolkit μ α a) (G : ℕ → PlaneTree → Prop)
    (k : ℕ → ℕ) {M : ℕ → ℕ} (hM : IsCutoff M) :
    IsEquivalent (admissibleSizes μ) (fun n => pProb μ (G (k n)) (M n))
      (fun n => qProb μ (G (k n)) (M n) n) := by
  refine IsEquivalent.symm (isLittleO_iff.2 fun ε hε => ?_)
  obtain ⟨d, L, hloc⟩ := hT.lattice
  obtain ⟨C₁, hC₁, hle⟩ := hT.exists_le_div_of_le_two_mul
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hsq := hT.regularlyVarying.tendsto_sqrt_div hT.monotone hT.pos hT.rho_pos
    hM.tendsto_atTop hM.isLittleO
  have hz : (fun n => √(a (M n) * a n) + 1) =o[atTop] (fun n => a ((fun n : ℕ => n) n)) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn h
      exact absurd h (hT.pos n hn).ne'
    · have h1 : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hT.tendsto_atTop
      have h2 := hsq.2.add h1
      rw [add_zero] at h2
      refine h2.congr' (Eventually.of_forall fun n => ?_)
      simp only [add_div, one_div]
  have h2M : ∀ᶠ n in atTop, 2 * M n ≤ n := by
    filter_upwards [hM.isLittleO.bound (show (0 : ℝ) < 1 / 2 by norm_num)] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have : ((2 * M n : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  set C' : ℝ := C₁ / c with hC'
  have hC'0 : 0 ≤ C' := by positivity
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [hl (hT.eventually_abs_div_sub_one_le hloc (N := fun n => n) tendsto_id
      hM.isLittleO hz hε2),
    (isLittleO_walkVecLaw_firstMarked_abs_sum_gt_admissible hT G k hM).def
      (show 0 < ε / 2 / (C' + 1) by positivity),
    hl h2M, hl (eventually_ge_atTop 1), hadm] with n hratio htail h2Mn hn1 hadmn
  set r : ℝ := √(a (M n) * a n) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hMn : M n ≤ n := by omega
  have han : 0 < a n := hT.pos n hn1
  set ψ : ℝ := walkProb μ n (-1) with hψdef
  have hψ : 0 < ψ := (walkProb_neg_one_pos_iff μ n).2 hadmn
  have hψlow : c / a n ≤ ψ := hlow n hn1 hψ
  have hdn := dvd_sub_one_of_admissible hloc hadmn
  set H : List ℤ → Prop := FirstMarked (G (k n)) (M n) with hH
  set I : (Fin (M n) → ℤ) → ℝ := fun b => {b : Fin (M n) → ℤ | H (List.ofFn b)}.indicator 1 b
    with hI
  set J : (Fin (M n) → ℤ) → ℝ := fun b => {b : Fin (M n) → ℤ | H (List.ofFn b) ∧
    r < |((∑ i, b i : ℤ) : ℝ)|}.indicator 1 b with hJ
  set Ψ' : (Fin (M n) → ℤ) → ℝ := fun b => walkProb μ ((n - M n : ℕ) : ℤ) (-1 - ∑ i, b i)
    with hΨ'
  have hΨ'le : ∀ b, Ψ' b * ψ⁻¹ ≤ C' := by
    intro b
    have h1 : Ψ' b ≤ C₁ / a n := hle n (n - M n) hn1 (by omega) (by omega) _
    have h2 : ψ⁻¹ ≤ a n / c := by
      calc ψ⁻¹ ≤ (c / a n)⁻¹ := inv_anti₀ (by positivity) hψlow
        _ = a n / c := inv_div _ _
    calc Ψ' b * ψ⁻¹ ≤ C₁ / a n * (a n / c) :=
          mul_le_mul h1 h2 (inv_nonneg.2 hψ.le) (by positivity)
      _ = C' := by rw [hC']; field_simp
  have hI01 : ∀ b, 0 ≤ I b ∧ I b ≤ 1 := fun b => indicator_one_mem_Icc _ b
  have hJ01 : ∀ b, 0 ≤ J b ∧ J b ≤ 1 := fun b => indicator_one_mem_Icc _ b
  have hΨ'0 : ∀ b, 0 ≤ Ψ' b := fun b => walkProb_nonneg μ _ _
  -- the two integral representations
  have hq : qProb μ (G (k n)) (M n) n = ψ⁻¹ * ∫ b, I b * Ψ' b ∂walkVecLaw μ (M n) := by
    have h := cond_real_take μ hMn H (-1)
    simp only [hH, firstMarked_take_iff] at h
    rw [qProb, bridgeLaw]
    exact h
  have hp : pProb μ (G (k n)) (M n) = ∫ b, I b ∂walkVecLaw μ (M n) := by
    rw [pProb, hI, integral_indicator_one MeasurableSet.of_discrete]
  have htl : (walkVecLaw μ (M n)).real {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
      r < |((∑ i, ω i : ℤ) : ℝ)|} = ∫ b, J b ∂walkVecLaw μ (M n) := by
    rw [hJ, integral_indicator_one MeasurableSet.of_discrete]
  have hIΨ : Integrable (fun b => ψ⁻¹ * (I b * Ψ' b)) (walkVecLaw μ (M n)) := by
    refine integrable_walkVecLaw_of_abs_le μ C' fun b => ?_
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hψ.le) (mul_nonneg (hI01 b).1 (hΨ'0 b)))]
    calc ψ⁻¹ * (I b * Ψ' b) = I b * (Ψ' b * ψ⁻¹) := by ring
      _ ≤ 1 * C' := mul_le_mul (hI01 b).2 (hΨ'le b)
          (mul_nonneg (hΨ'0 b) (inv_nonneg.2 hψ.le)) zero_le_one
      _ = C' := one_mul _
  have hIint : Integrable I (walkVecLaw μ (M n)) :=
    integrable_walkVecLaw_of_abs_le μ 1 fun b => by rw [abs_of_nonneg (hI01 b).1]; exact (hI01 b).2
  have hJint : Integrable J (walkVecLaw μ (M n)) :=
    integrable_walkVecLaw_of_abs_le μ 1 fun b => by rw [abs_of_nonneg (hJ01 b).1]; exact (hJ01 b).2
  have hdiff : qProb μ (G (k n)) (M n) n - pProb μ (G (k n)) (M n) =
      ∫ b, (ψ⁻¹ * (I b * Ψ' b) - I b) ∂walkVecLaw μ (M n) := by
    rw [hq, hp, ← integral_const_mul, integral_sub hIΨ hIint]
  have hg : Integrable (fun b => ε / 2 * I b + (C' + 1) * J b) (walkVecLaw μ (M n)) :=
    (hIint.const_mul _).add (hJint.const_mul _)
  have hbound : ∀ᵐ b ∂walkVecLaw μ (M n),
      ‖ψ⁻¹ * (I b * Ψ' b) - I b‖ ≤ ε / 2 * I b + (C' + 1) * J b := by
    filter_upwards [ae_dvd_sum_add hloc (M n)] with b hb
    rw [Real.norm_eq_abs]
    by_cases hHb : H (List.ofFn b)
    · have hIb : I b = 1 := by
        simp only [hI]
        rw [Set.indicator_of_mem (show b ∈ {b : Fin (M n) → ℤ | H (List.ofFn b)} from hHb)]
        rfl
      have hcalc : ψ⁻¹ * (I b * Ψ' b) - I b = Ψ' b / ψ - 1 := by
        rw [hIb]; field_simp
      rw [hcalc]
      by_cases hS : r < |((∑ i, b i : ℤ) : ℝ)|
      · have hJb : J b = 1 := by
          simp only [hJ]
          rw [Set.indicator_of_mem (show b ∈ {b : Fin (M n) → ℤ | H (List.ofFn b) ∧
            r < |((∑ i, b i : ℤ) : ℝ)|} from ⟨hHb, hS⟩)]
          rfl
        rw [hIb, hJb]
        have h1 : Ψ' b / ψ ≤ C' := by rw [div_eq_mul_inv]; exact hΨ'le b
        have h2 : 0 ≤ Ψ' b / ψ := div_nonneg (hΨ'0 b) hψ.le
        rw [abs_le]
        constructor <;> linarith
      · have hS' : |((∑ i, b i : ℤ) : ℝ)| ≤ r := not_lt.1 hS
        have hdx : (d : ℤ) ∣ (-1 - ∑ i, b i) + ((n - M n : ℕ) : ℤ) := by
          have := Int.dvd_sub hdn hb
          convert this using 1
          push_cast [hMn]
          ring
        have hdy : (d : ℤ) ∣ (-1 : ℤ) + (n : ℤ) := by
          rwa [show (-1 : ℤ) + n = n - 1 by ring]
        have hx : |(((-1 - ∑ i, b i : ℤ)) : ℝ)| ≤ r + 1 := by
          push_cast
          rw [abs_le] at hS' ⊢
          push_cast at hS'
          constructor <;> linarith
        have hy : |(((-1 : ℤ)) : ℝ)| ≤ r + 1 := by simp; linarith
        have := hratio (M n) le_rfl (-1 - ∑ i, b i) (-1) hdx hdy hx hy
        have hJ0 := (hJ01 b).1
        calc |Ψ' b / ψ - 1| ≤ ε / 2 := this
          _ ≤ ε / 2 * I b + (C' + 1) * J b := by
            rw [hIb]; nlinarith
    · have hIb : I b = 0 := by
        simp only [hI]
        rw [Set.indicator_of_notMem (show b ∉ {b : Fin (M n) → ℤ | H (List.ofFn b)} from hHb)]
      have hJb : J b = 0 := by
        simp only [hJ]
        rw [Set.indicator_of_notMem (show b ∉ {b : Fin (M n) → ℤ | H (List.ofFn b) ∧
          r < |((∑ i, b i : ℤ) : ℝ)|} from fun h => hHb h.1)]
      rw [hIb, hJb]
      simp
  have hint : ∫ b, (ε / 2 * I b + (C' + 1) * J b) ∂walkVecLaw μ (M n) =
      ε / 2 * pProb μ (G (k n)) (M n) + (C' + 1) *
        (walkVecLaw μ (M n)).real {ω | FirstMarked (G (k n)) (M n) (List.ofFn ω) ∧
          r < |((∑ i, ω i : ℤ) : ℝ)|} := by
    rw [integral_add (hIint.const_mul _) (hJint.const_mul _), integral_const_mul,
      integral_const_mul, hp, htl]
  have hp0 : 0 ≤ pProb μ (G (k n)) (M n) := measureReal_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg,
    abs_of_nonneg hp0] at htail
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0, hdiff]
  calc |∫ b, (ψ⁻¹ * (I b * Ψ' b) - I b) ∂walkVecLaw μ (M n)|
      ≤ ∫ b, (ε / 2 * I b + (C' + 1) * J b) ∂walkVecLaw μ (M n) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hg hbound
    _ = _ := hint
    _ ≤ ε / 2 * pProb μ (G (k n)) (M n) +
        (C' + 1) * (ε / 2 / (C' + 1) * pProb μ (G (k n)) (M n)) := by gcongr
    _ = ε * pProb μ (G (k n)) (M n) := by field_simp; ring

/-- **Lemma `lem:pnqn`(ii)** (source lines 1732–1788): under Assumption (M), `p_n ∼ q_n ∼ π_n`
along admissible sizes. (`π_n = 0` is allowed: `IsEquivalent` then forces `p_n = q_n = 0`.) -/
theorem isEquivalent_pProb_qProb_markProb (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M) :
    IsEquivalent (admissibleSizes μ) (fun n => pProb μ (G (k n)) (M n))
        (fun n => qProb μ (G (k n)) (M n) n) ∧
      IsEquivalent (admissibleSizes μ) (fun n => qProb μ (G (k n)) (M n) n)
        (markProb μ G k) :=
  ⟨isEquivalent_pProb_qProb hT G k hM, isEquivalent_qProb_markProb hmic⟩

end PoissonDeclumping.Bridge
