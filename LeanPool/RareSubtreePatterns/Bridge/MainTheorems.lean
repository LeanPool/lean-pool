/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.ExtremeMeans
public import LeanPool.RareSubtreePatterns.Bridge.RootMicroscopic

import LeanPool.RareSubtreePatterns.Stable.ToolkitProof

/-!
# Assembly of Theorems `thm:PoissonApproximation` and `thm:PoissonApproximation2`

Work package WP7 (second half) of the bridge plan. Source lines 1555–1595 (strategy),
2092–2143 (proof of Theorem 1.1, step `P14`) and 2305–2330 (proof of Theorem 1.2).

The only ingredient not proved upstream of this file is Proposition `prop:b3bis` (P4.8,
`b_3 → 0`, endpoint-smoothing package). It enters as an explicit hypothesis: `hb3` in the
per-law theorems, `ErrorB3Statement` in the paper-level statements. Everything else is proved:
Lemma `lem:RW` (`markedCountLaw_eq`), Lemma `lem:truncate`, Proposition `prop:AGG`
(`exists_paperTVDist_cyclicSum_le_errorTerms`), Proposition `prop:b1`, Lemma `lem:boundb2`,
Lemma `lem:pnqn`, Lemma `lem:extreme_means` (`Bridge/ExtremeMeans.lean`), Lemma
`lem:root_declumping`(i)–(iii) and the toolkit derived from `(H_α)` (`Stable.stableToolkit`).

## Main statements

* `conditioned_real_markCount_mem`: Lemma `lem:RW` for events.
* `tendsto_paperTVDist_markedCountLaw_of_b3` (Theorem 1.1, bounded mean),
  `tendsto_bridgeLaw_abs_cyclicSum_length_div_sub_one` and `poissonApproximation_divergent`
  (Theorem 1.1, divergent mean: LLN and divergence in probability).
* `poissonApproximation_of_b3`: the two conclusions of `PoissonApproximationStatement` for one
  law with the toolkit, given (M), (C) and `hb3`.
* `poissonApproximation2_of_b3`: the two conclusions of `PoissonApproximation2Statement` for one
  law with the toolkit, given (S) for `G`, (C) for `Ghat` and `hb3` for `Ghat`.
* `ErrorB3Statement`, `poissonApproximationStatement_of_b3`,
  `poissonApproximation2Statement_of_b3`: the paper-level statements from Proposition
  `prop:b3bis`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-! ### Transfer between trees and the bridge -/

/-- Lemma `lem:RW` for events: for every set `S ⊆ ℕ`,
`P(#{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1} ∈ S) = P(W_n^n ∈ S | S_n = -1)`. -/
theorem conditioned_real_markCount_mem (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n : ℕ) (S : Set ℕ) :
    (conditioned μ n).real {T | markCount (G (k n)) T ∈ S} =
      (bridgeLaw μ n).real {ω | cyclicSum (G (k n)) n (List.ofFn ω) ∈ S} := by
  have h := congrArg (fun ν : Measure ℕ => ν.real S) (markedCountLaw_eq μ G k n)
  simp only [markedCountLaw] at h
  rw [measureReal_def, measureReal_def, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable S).measurableSet, Measure.map_apply (measurable_of_countable _)
    (Set.to_countable S).measurableSet] at h
  rw [measureReal_def, measureReal_def]
  refine h.trans ?_
  congr 2
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  unfold cyclicSum shiftIndicator
  rw [List.length_ofFn]
  refine Iff.of_eq (congrArg (· ∈ S) (Finset.sum_congr rfl fun i _ => ?_))
  exact (firstIndicator_of_length_le (by simp)).symm

/-! ### Theorem `thm:PoissonApproximation`, bounded mean -/

/-- **Theorem `thm:PoissonApproximation`(i)**, conditional on Proposition `prop:b3bis`
(source lines 2104–2121): if `(n π_n)` is bounded and `b_3 → 0` for every family of test
functions bounded by `1`, then `d_TV(N_n, Po(n π_n)) → 0`. Proof: Lemma `lem:RW` and Lemma
`lem:truncate`(i) (`W_n^n` vs `W_n^{M_n}`), Proposition `prop:AGG` with the cyclic
neighbourhoods (`exists_paperTVDist_cyclicSum_le_errorTerms`, test functions chosen for each
admissible `n`), `b_1, b_2 → 0` (Proposition `prop:b1`, Lemma `lem:boundb2`), `hb3`, and Lemma
`lem:truncate`(ii) (`Po(n q_n)` vs `Po(n π_n)`). -/
theorem tendsto_paperTVDist_markedCountLaw_of_b3 (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M)
    (hC : NonClustering μ G k M)
    (hbd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C)
    (hb3 : ∀ f : ℕ → ℕ → ℝ, (∀ n w, |f n w| ≤ 1) →
      Tendsto (fun n => errorB3 μ (G (k n)) (M n) n (f n)) (admissibleSizes μ) (𝓝 0)) :
    Tendsto (fun n : ℕ => paperTVDist (markedCountLaw μ G k n)
      (poissonMeasure (Real.toNNReal ((n : ℝ) * markProb μ G k n))))
      (admissibleSizes μ) (𝓝 0) := by
  have hAGG : ∀ n : ℕ, ∃ f : ℕ → ℝ, (∀ w, |f w| ≤ 1) ∧ (Admissible μ n → 1 ≤ n →
      paperTVDist ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) (M n) (List.ofFn ω)))
          (poissonMeasure (Real.toNNReal ((n : ℝ) * qProb μ (G (k n)) (M n) n))) ≤
        2 * (errorB1 μ (G (k n)) (M n) n + errorB2 μ (G (k n)) (M n) n +
          errorB3 μ (G (k n)) (M n) n f)) := by
    intro n
    by_cases h : Admissible μ n ∧ 0 < M n
    · obtain ⟨f, hf, hle⟩ := exists_paperTVDist_cyclicSum_le_errorTerms μ (G (k n)) h.1 h.2
      exact ⟨f, hf, fun _ _ => hle⟩
    · exact ⟨0, fun w => by simp, fun hn hn1 => absurd ⟨hn, hM.pos n hn1⟩ h⟩
  choose f hf hfle using hAGG
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hlim := (((tendsto_errorB1 hT hM hbd).add (tendsto_errorB2 hT hM hC hbd)).add
    (hb3 f fun n w => hf n w)).const_mul 2
  rw [add_zero, add_zero, mul_zero] at hlim
  have hW : Tendsto (fun n => paperTVDist
      ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) (M n) (List.ofFn ω)))
      (poissonMeasure (Real.toNNReal ((n : ℝ) * qProb μ (G (k n)) (M n) n))))
      (admissibleSizes μ) (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => paperTVDist_nonneg _ _) ?_ hlim
    filter_upwards [hadm, hl (eventually_ge_atTop 1)] with n hn hn1
    exact hfle n hn hn1
  have hT1 : Tendsto (fun n => paperTVDist (markedCountLaw μ G k n)
      ((bridgeLaw μ n).map (fun ω => cyclicSum (G (k n)) (M n) (List.ofFn ω))))
      (admissibleSizes μ) (𝓝 0) := by
    simpa only [paperTVDist_comm (markedCountLaw μ G k _)] using
      tendsto_paperTVDist_cyclicSum_markedCountLaw hmic hbd
  exact tendsto_paperTVDist_trans (tendsto_paperTVDist_trans hT1 hW)
    (tendsto_paperTVDist_poisson_qProb_markProb hmic hbd)

/-! ### Theorem `thm:PoissonApproximation`, divergent mean -/

/-- **Theorem `thm:PoissonApproximation`(ii), law of large numbers on the bridge** (source lines
2126–2139): if `n π_n → ∞`, then `W_n^n / (n π_n) → 1` in probability under `P(· | S_n = -1)`.
Proof: Lemma `lem:extreme_means`(ii) for `W_n^{M_n}`, and Markov's inequality for
`W_n^n - W_n^{M_n} ≥ 0`, whose bridge expectation is `n P(G(𝒯^n_{U_n}) = 1, |𝒯^n_{U_n}| > M_n)
= o(n π_n)` by (M) (`integral_cyclicSum_sub_truncated`). -/
theorem tendsto_bridgeLaw_abs_cyclicSum_length_div_sub_one (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M)
    (hC : NonClustering μ G k M)
    (hdiv : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (bridgeLaw μ n).real {ω | ε <
      |(cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
      (admissibleSizes μ) (𝓝 0) := by
  have he : 0 < ε / 2 := half_pos hε
  have h1 := tendsto_bridgeLaw_abs_cyclicSum_div_sub_one hT hM hmic hC hdiv he
  have h2 : Tendsto (fun n => 4 / ε * (cond (uniformFringeLaw μ n) {T | G (k n) T}).real
      {T | M n < T.vertexCount}) (admissibleSizes μ) (𝓝 0) := by
    simpa using hmic.2.const_mul (4 / ε)
  have hlim := h1.add h2
  rw [add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hlim
  filter_upwards [hdiv.eventually_gt_atTop 0, hmic.1.isLittleO.def one_pos] with n hnπ hU
  have hπ0 : 0 ≤ markProb μ G k n := measureReal_nonneg
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hπ0, abs_le] at hU
  set π : ℝ := markProb μ G k n with hπdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set U : ℝ := (uniformFringeLaw μ n).real {T | G (k n) T} with hUdef
  set t : ℝ := (cond (uniformFringeLaw μ n) {T | G (k n) T}).real {T | M n < T.vertexCount}
    with htdef
  have ht0 : 0 ≤ t := measureReal_nonneg
  have hU2 : U ≤ 2 * π := by linarith [hU.2]
  -- the event splits into a truncated deviation and a large truncation error
  have hsub : {ω : Fin n → ℤ | ε <
      |(cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|} ⊆
      {ω | ε / 2 < |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|} ∪
        {ω | ε / 2 * ((n : ℝ) * π) ≤ (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) -
          cyclicSum (G (k n)) (M n) (List.ofFn ω)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    set Wn : ℝ := (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) with hWn
    set WM : ℝ := (cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) with hWM
    have hsplit : Wn / ((n : ℝ) * π) - 1 =
        (WM / ((n : ℝ) * π) - 1) + (Wn - WM) / ((n : ℝ) * π) := by
      field_simp
      ring
    have hD : 0 ≤ Wn - WM := by
      rw [hWn, hWM, sub_nonneg, Nat.cast_le]
      exact cyclicSum_le_cyclicSum_length _ _ ω
    have hD' : (Wn - WM) / ((n : ℝ) * π) < ε / 2 := by
      rw [div_lt_iff₀ hnπ]
      linarith
    have := abs_add_le (WM / ((n : ℝ) * π) - 1) ((Wn - WM) / ((n : ℝ) * π))
    rw [← hsplit, abs_of_nonneg (div_nonneg hD hnπ.le)] at this
    linarith
  -- Markov's inequality for the truncation error
  have hDint : Integrable (fun ω : Fin n → ℤ => (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) -
      cyclicSum (G (k n)) (M n) (List.ofFn ω)) (bridgeLaw μ n) :=
    (integrable_cyclicSum_bridgeLaw μ _ _ n).sub (integrable_cyclicSum_bridgeLaw μ _ _ n)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := bridgeLaw μ n)
    (f := fun ω : Fin n → ℤ => (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) -
      cyclicSum (G (k n)) (M n) (List.ofFn ω)) (Eventually.of_forall fun ω => by
      simp only [Pi.zero_apply, sub_nonneg, Nat.cast_le]
      exact cyclicSum_le_cyclicSum_length _ _ ω) hDint (ε / 2 * ((n : ℝ) * π))
  rw [integral_cyclicSum_sub_truncated, Set.ofPred_and,
    measureReal_inter_eq_mul_cond _ MeasurableSet.of_discrete] at hmk
  have hmk' : (bridgeLaw μ n).real {ω | ε / 2 * ((n : ℝ) * π) ≤
      (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) - cyclicSum (G (k n)) (M n) (List.ofFn ω)} ≤
      4 / ε * t := by
    rw [← mul_le_mul_iff_of_pos_left (show 0 < ε / 2 * ((n : ℝ) * π) by positivity)]
    calc ε / 2 * ((n : ℝ) * π) * (bridgeLaw μ n).real {ω | ε / 2 * ((n : ℝ) * π) ≤
          (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) -
            cyclicSum (G (k n)) (M n) (List.ofFn ω)} ≤ (n : ℝ) * (U * t) := hmk
      _ ≤ (n : ℝ) * (2 * π * t) := by gcongr
      _ = ε / 2 * ((n : ℝ) * π) * (4 / ε * t) := by field_simp; ring
  calc (bridgeLaw μ n).real {ω | ε <
        |(cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|}
      ≤ (bridgeLaw μ n).real
          ({ω | ε / 2 < |(cyclicSum (G (k n)) (M n) (List.ofFn ω) : ℝ) / ((n : ℝ) * π) - 1|} ∪
          {ω | ε / 2 * ((n : ℝ) * π) ≤ (cyclicSum (G (k n)) n (List.ofFn ω) : ℝ) -
            cyclicSum (G (k n)) (M n) (List.ofFn ω)}) :=
        measureReal_mono hsub (measure_ne_top (bridgeLaw μ n) _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl hmk'

/-- **Theorem `thm:PoissonApproximation`(ii)** (source lines 2126–2142): under (M) and (C), if
`n π_n → ∞`, then `N_n / (n π_n) → 1` in probability and `N_n → ∞` in probability, where
`N_n = #{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}`. -/
theorem poissonApproximation_divergent (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M)
    (hC : NonClustering μ G k M)
    (hdiv : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
      {T | ε < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
      (admissibleSizes μ) (𝓝 0)) ∧
    (∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
      {T | PlaneTree.markCount (G (k n)) T ≤ K}) (admissibleSizes μ) (𝓝 0)) := by
  have hLLN : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
      {T | ε < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
      (admissibleSizes μ) (𝓝 0) := by
    intro ε hε
    refine (tendsto_bridgeLaw_abs_cyclicSum_length_div_sub_one hT hM hmic hC hdiv hε).congr
      fun n => ?_
    exact (conditioned_real_markCount_mem μ G k n
      {w | ε < |(w : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|}).symm
  refine ⟨hLLN, fun K => ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_
    (hLLN (1 / 2) one_half_pos)
  filter_upwards [hdiv.eventually_gt_atTop (2 * K)] with n hn
  have hpos : 0 < (n : ℝ) * markProb μ G k n :=
    lt_of_le_of_lt (by positivity) hn
  refine measureReal_mono (fun T (hT : PlaneTree.markCount (G (k n)) T ≤ K) => ?_)
    (measure_ne_top _ _)
  change 1 / 2 < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|
  have hK : (PlaneTree.markCount (G (k n)) T : ℝ) ≤ K := by exact_mod_cast hT
  have hlt : (PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) < 1 / 2 := by
    rw [div_lt_iff₀ hpos]
    linarith
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

/-- **Theorem `thm:PoissonApproximation`** (source lines 305–329, proof 2092–2143) for one
offspring law, conditional on Proposition `prop:b3bis`: the two conclusions of
`PoissonApproximationStatement` for `μ`, `G`, `k`, given the toolkit, a cutoff `M` with (M) and
(C), and the hypothesis `hb3` (`b_3 → 0` along admissible sizes whenever `(n π_n)` is bounded, for
every family of test functions bounded by `1`). -/
theorem poissonApproximation_of_b3 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) (hmic : Microscopic μ G k M) (hC : NonClustering μ G k M)
    (hb3 : (∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      ∀ f : ℕ → ℕ → ℝ, (∀ n w, |f n w| ≤ 1) →
        Tendsto (fun n => errorB3 μ (G (k n)) (M n) n (f n)) (admissibleSizes μ) (𝓝 0)) :
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist (markedCountLaw μ G k n)
        (poissonMeasure (Real.toNNReal ((n : ℝ) * markProb μ G k n))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | ε < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
        (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | PlaneTree.markCount (G (k n)) T ≤ K}) (admissibleSizes μ) (𝓝 0))) :=
  ⟨fun hbd => tendsto_paperTVDist_markedCountLaw_of_b3 hT hM hmic hC hbd (hb3 hbd),
    poissonApproximation_divergent hT hM hmic hC⟩

/-! ### Theorem `thm:PoissonApproximation2` -/

/-- **Theorem `thm:PoissonApproximation2`** (source lines 396–442, proof 2305–2330) for one
offspring law, conditional on Proposition `prop:b3bis` for the declumped marks
`Ghat_k = declumpedMark B G_k`: the two conclusions of `PoissonApproximation2Statement`. Proof:
Lemma `lem:root_declumping`(iii) (`microscopic_declumped`) gives (M) for `Ghat`; with (C) for
`Ghat`,
Theorem `thm:PoissonApproximation` applies to `Ghat`. If `(n π_n)` is bounded, then so is
`(n π̂_n)` and `n π̂_n - c_B n π_n → 0` (Lemma `lem:root_declumping`(i)), and
`d_TV(Po(n π̂_n), Po(c_B n π_n)) ≤ |n π̂_n - c_B n π_n|`; if `n π_n → ∞`, then `n π̂_n → ∞`
(Lemma `lem:root_declumping`(ii)) and the declumped count diverges in probability. -/
theorem poissonApproximation2_of_b3 (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) {B : Set ℕ} (hB0 : 0 < cB μ B) (hB1 : cB μ B < ∞)
    (hS : StructuralMicroscopic μ a G k M)
    (hC : NonClustering μ (fun j => PlaneTree.declumpedMark B (G j)) k M)
    (hb3 : (∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ,
        (n : ℝ) * markProb μ (fun j => PlaneTree.declumpedMark B (G j)) k n ≤ C) →
      ∀ f : ℕ → ℕ → ℝ, (∀ n w, |f n w| ≤ 1) →
        Tendsto (fun n => errorB3 μ (PlaneTree.declumpedMark B (G (k n))) (M n) n (f n))
          (admissibleSizes μ) (𝓝 0)) :
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist
        (markedCountLaw μ (fun j => PlaneTree.declumpedMark B (G j)) k n)
        (poissonMeasure (Real.toNNReal ((cB μ B).toReal * ((n : ℝ) * markProb μ G k n)))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      ∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | PlaneTree.markCount (PlaneTree.declumpedMark B (G (k n))) T ≤ K})
        (admissibleSizes μ) (𝓝 0)) := by
  have hmicD : Microscopic μ (fun j => PlaneTree.declumpedMark B (G j)) k M :=
    microscopic_declumped hT hS hM hB0 hB1
  obtain ⟨-, -, -, hbdd, hdivg⟩ :=
    RootDeclumping.lem_root_declumping hT.critical hT.nondegenerate G k B hB0
  have hT11 := poissonApproximation_of_b3 hT hM hmicD hC hb3
  refine ⟨fun hbd => ?_, fun hdiv K => (hT11.2 (hdivg hdiv)).2 K⟩
  have hlim := hbdd hbd
  have hbdD : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ,
      (n : ℝ) * markProb μ (fun j => PlaneTree.declumpedMark B (G j)) k n ≤ C := by
    obtain ⟨C, hC⟩ := hbd
    refine ⟨(cB μ B).toReal * C + 1, ?_⟩
    filter_upwards [hC, (Metric.tendsto_nhds.mp hlim) 1 one_pos] with n hn h1
    rw [Real.dist_eq, sub_zero, abs_lt] at h1
    have := mul_le_mul_of_nonneg_left hn (ENNReal.toReal_nonneg (a := cB μ B))
    linarith
  refine tendsto_paperTVDist_poissonMeasure_congr _ (hT11.1 hbdD) (hlim.congr fun n => ?_)
  have h1 : 0 ≤ (n : ℝ) * markProb μ (fun j => PlaneTree.declumpedMark B (G j)) k n :=
    mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  have h2 : 0 ≤ (cB μ B).toReal * ((n : ℝ) * markProb μ G k n) :=
    mul_nonneg ENNReal.toReal_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)
  rw [Real.coe_toNNReal _ h1, Real.coe_toNNReal _ h2]

/-! ### The paper's statements, conditional on Proposition `prop:b3bis` -/

/-- Proposition `prop:b3bis` (P4.8, source lines 1860–1995) in the form used by the assembly:
for every offspring law with the stable toolkit, every cutoff and marks with (M), if `(n π_n)` is
bounded then `b_3 → 0` along admissible sizes for every family of test functions bounded by `1`.
This is the export of the endpoint-smoothing package. -/
def ErrorB3Statement : Prop :=
  ∀ (μ : PMF ℕ) (α : ℝ) (a : ℕ → ℝ), StableToolkit μ α a →
    ∀ (G : ℕ → PlaneTree → Prop) (k M : ℕ → ℕ), IsCutoff M → Microscopic μ G k M →
      (∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      ∀ f : ℕ → ℕ → ℝ, (∀ n w, |f n w| ≤ 1) →
        Tendsto (fun n => errorB3 μ (G (k n)) (M n) n (f n)) (admissibleSizes μ) (𝓝 0)

/-- **Theorem `thm:PoissonApproximation`**, the paper's statement, from Proposition
`prop:b3bis` (`ErrorB3Statement`) and the stable toolkit derived from `(H_α)`. -/
theorem poissonApproximationStatement_of_b3 (hb3 : ErrorB3Statement) :
    PoissonApproximationStatement := by
  rintro μ ⟨α, a, hdom⟩ G k ⟨M, hM, hmic, hC⟩
  have hT := Stable.stableToolkit hdom
  exact poissonApproximation_of_b3 hT hM hmic hC (hb3 μ α a hT G k M hM hmic)

/-- **Theorem `thm:PoissonApproximation2`**, the paper's statement, from Proposition
`prop:b3bis` (`ErrorB3Statement`, applied to the declumped marks) and the stable toolkit derived
from `(H_α)`. -/
theorem poissonApproximation2Statement_of_b3 (hb3 : ErrorB3Statement) :
    PoissonApproximation2Statement := by
  intro μ α a hdom G k M hM B hB0 hB1 hS hC
  have hT := Stable.stableToolkit hdom
  have hmicD : Microscopic μ (fun j => PlaneTree.declumpedMark B (G j)) k M :=
    microscopic_declumped hT hS hM hB0 hB1
  exact poissonApproximation2_of_b3 hT hM hB0 hB1 hS hC
    (hb3 μ α a hT (fun j => PlaneTree.declumpedMark B (G j)) k M hM hmicD)

end PoissonDeclumping.Bridge
