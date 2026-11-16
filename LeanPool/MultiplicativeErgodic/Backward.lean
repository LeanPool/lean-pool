/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Uniqueness

/-!
# The backward characterisation of the fast spaces

For a witness to `mainres` and `i + 2 ≤ L`, almost surely
`E_0(ω) ⊕ ⋯ ⊕ E_i(ω) = R.backwardSpace ω λ_{i+1}`: the fast sum is exactly the set of vectors
with a backward history `x = y₀ ← y₁ ← ⋯` along `σ^{-n}ω` decaying at rate `λ_{i+1}`
(`Cocycle.IsOseledets.backward_characterisation`). Not in `proof_met.tex`; compare
Froyland--Lloyd--Quas, *A semi-invertible Oseledets theorem with applications to transfer operator
cocycles*, Lemma 20.

* `ae_eventually_exp_le_backward` — a density argument (as in Mañé's lemma, González-Tokman--Quas
  Lemma 15) turning forward growth into backward growth, with no integrability of the inverse.
* `Cocycle.ae_le_backwardSpace_of_growth` — fast vectors have fast-decaying histories.
* `Cocycle.IsLevel.eq_zero_of_mem_backwardSpace` — slow vectors have none (backward Kingman on
  the modified cocycle `𝓛 ∘ Q`).
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace
open scoped Topology

section Density

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] in
/-- A converging Birkhoff average, read as two-sided linear bounds on the Birkhoff sum. -/
theorem eventually_birkhoffSum_bounds {τ : Ω → Ω} {g : Ω → ℝ} {ω : Ω} {I ε : ℝ}
    (h : Tendsto (fun j : ℕ => birkhoffAverage ℝ τ g j ω) atTop (𝓝 I)) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, (I - ε) * j ≤ birkhoffSum τ g j ω ∧ birkhoffSum τ g j ω ≤ (I + ε) * j := by
  filter_upwards [h (Ioo_mem_nhds (by linarith : I - ε < I) (by linarith : I < I + ε)),
    eventually_ge_atTop 1] with j hj hj1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have heq : birkhoffAverage ℝ τ g j ω = birkhoffSum τ g j ω / j := by
    rw [birkhoffAverage, smul_eq_mul, inv_mul_eq_div]
  have hj' : I - ε < birkhoffSum τ g j ω / j ∧ birkhoffSum τ g j ω / j < I + ε := by
    rw [← heq]; exact hj
  rw [lt_div_iff₀ hjpos, div_lt_iff₀ hjpos] at hj'
  exact ⟨hj'.1.le, hj'.2.le⟩

/-- **Returns at a positive density.** For an ergodic `τ` and a set `G` of positive measure,
almost every orbit visits `G` in every window `[n, (1+η)n]` with `n` large. -/
theorem ae_eventually_exists_mem_window {τ : Ω → Ω} (hτ : Ergodic τ μ) {G : Set Ω}
    (hG : MeasurableSet G) (hGpos : μ G ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, n ≤ k ∧ (k : ℝ) ≤ (1 + η) * n ∧ τ^[k] ω ∈ G := by
  set f : Ω → ℝ := G.indicator (fun _ => (1 : ℝ)) with hf
  have hfm : Measurable f := measurable_const.indicator hG
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).indicator hG
  set p : ℝ := ∫ x, f x ∂μ with hp
  have hppos : 0 < p := by
    rw [hp, hf, integral_indicator hG, setIntegral_const, smul_eq_mul, mul_one]
    exact ENNReal.toReal_pos hGpos (measure_ne_top μ G)
  set ε : ℝ := p * η / (4 + 2 * η) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  filter_upwards [ae_tendsto_birkhoffAverage_of_ergodic hτ f hfm hfi] with ω hω
  have hb := eventually_birkhoffSum_bounds hω hεpos
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hb
  filter_upwards [eventually_ge_atTop (max J 1)] with n hn
  have hnJ : J ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  by_contra hno
  push Not at hno
  set K : ℕ := ⌊(1 + η) * n⌋₊ with hK
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnK : n ≤ K + 1 := by
    have : (n : ℝ) ≤ (1 + η) * n := by nlinarith
    have h2 : (n : ℝ) < K + 1 := lt_of_le_of_lt this (Nat.lt_floor_add_one _)
    exact_mod_cast h2.le
  have hK1 : (1 + η) * n < (K + 1 : ℕ) := by push_cast; exact Nat.lt_floor_add_one _
  -- no visit in `[n, K]`
  have hzero : ∑ t ∈ Finset.Ico n (K + 1), f (τ^[t] ω) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    have htK : (t : ℝ) ≤ (1 + η) * n := by
      have : t ≤ K := by omega
      calc (t : ℝ) ≤ K := by exact_mod_cast this
        _ ≤ (1 + η) * n := Nat.floor_le (by positivity)
    have := hno t ht.1 htK
    simp [hf, Set.indicator_of_notMem this]
  have hsum : birkhoffSum τ f (K + 1) ω = birkhoffSum τ f n ω := by
    rw [birkhoffSum, birkhoffSum, ← Finset.sum_range_add_sum_Ico _ hnK, hzero, add_zero]
  have h1 := (hJ (K + 1) (by omega)).1
  have h2 := (hJ n hnJ).2
  rw [hsum] at h1
  have h3 : (p - ε) * ((1 + η) * n) ≤ (p + ε) * n := by
    have hpe : 0 ≤ p - ε := by
      rw [hε]
      have : p * η / (4 + 2 * η) ≤ p := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    calc (p - ε) * ((1 + η) * n) ≤ (p - ε) * ((K + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hK1.le hpe
      _ ≤ _ := h1.trans h2
  have h4 : p * η ≤ ε * (2 + η) := by nlinarith
  rw [hε, div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h4
  have hpη : 0 < p * η := by positivity
  nlinarith

/-- **Backward growth from forward growth (the density argument).** `a n ζ` is a growth
statistic of an `n`-step window starting at `ζ`. Forward, `a n ζ ≥ e^{bn}` eventually for every
`b < c`. The windows ending at a fixed `ω` are related by
`a_k(τ^k ω) ≤ a_n(τ^n ω) · exp(∑_{t ∈ (n, k]} φ(τ^t ω))` for an integrable `φ ≥ 0` (for a cocycle
along `τ = σ⁻¹`, `φ = log⁺‖𝓛‖`). Then also `a_n(τ^n ω) ≥ e^{bn}` eventually, for every `b < c`.

The window times `τ^k ω` at which the forward bound has already kicked in by a fixed time `N`
have positive density, so for large `n` one lies in `[n, (1+η)n]`; the extra `k - n ≤ ηn` steps
cost at most `e^{(k-n)∫φ + o(n)}` by Birkhoff. This is the argument of Mañé's lemma on tempered
functions (González-Tokman--Quas, Lemma 15), and needs no integrability of `log a_1`. -/
theorem ae_eventually_exp_le_backward {τ : Ω → Ω} (hτ : Ergodic τ μ) (a : ℕ → Ω → ℝ)
    (ha : ∀ n, Measurable (a n)) {φ : Ω → ℝ} (hφm : Measurable φ) (hφ : Integrable φ μ)
    (hφ0 : ∀ ω, 0 ≤ φ ω) {c : ℝ}
    (hwin : ∀ᵐ ω ∂μ, ∀ n k : ℕ, n ≤ k →
      a k (τ^[k] ω) ≤ a n (τ^[n] ω) * Real.exp (∑ t ∈ Finset.Ioc n k, φ (τ^[t] ω)))
    (hfwd : ∀ᵐ ζ ∂μ, ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ a n ζ) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ a n (τ^[n] ω) := by
  -- a single rate suffices, then pass through the rationals
  suffices H : ∀ b : ℝ, b < c → ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, Real.exp (b * n) ≤ a n (τ^[n] ω) by
    have hQ : ∀ᵐ ω ∂μ, ∀ q : ℚ, (q : ℝ) < c →
        ∀ᶠ n : ℕ in atTop, Real.exp (q * n) ≤ a n (τ^[n] ω) := by
      rw [ae_all_iff]
      intro q
      by_cases hq : (q : ℝ) < c
      · filter_upwards [H q hq] with ω h _ using h
      · exact Eventually.of_forall fun ω h => absurd h hq
    filter_upwards [hQ] with ω hω b hb
    obtain ⟨q, hbq, hqc⟩ := exists_rat_btwn hb
    filter_upwards [hω q hqc] with n hn
    refine le_trans (Real.exp_le_exp.2 ?_) hn
    exact mul_le_mul_of_nonneg_right hbq.le (Nat.cast_nonneg n)
  intro b hb
  set δ : ℝ := (c - b) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set b' : ℝ := b + 2 * δ with hb'
  have hb'c : b' < c := by rw [hb', hδ]; linarith
  set I : ℝ := ∫ x, φ x ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg hφ0
  set η : ℝ := min 1 (δ / (2 * (|b'| + I + 1))) with hη
  have hηpos : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηb : (|b'| + I) * η ≤ δ / 2 := by
    have h1 : η ≤ δ / (2 * (|b'| + I + 1)) := min_le_right _ _
    have h2 : (|b'| + I) * η ≤ (|b'| + I + 1) * (δ / (2 * (|b'| + I + 1))) :=
      mul_le_mul (by linarith) h1 hηpos.le (by positivity)
    have h3 : (|b'| + I + 1) * (δ / (2 * (|b'| + I + 1))) = δ / 2 := by
      field_simp
    linarith
  set ε : ℝ := δ / 8 with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- the good sets
  set G : ℕ → Set Ω := fun N => {ζ | ∀ k : ℕ, N ≤ k → Real.exp (b' * k) ≤ a k ζ} with hG
  have hGm : ∀ N, MeasurableSet (G N) := by
    intro N
    have : G N = ⋂ k : ℕ, {ζ | N ≤ k → Real.exp (b' * k) ≤ a k ζ} := by
      ext ζ; simp [hG]
    rw [this]
    refine MeasurableSet.iInter fun k => ?_
    by_cases hk : N ≤ k
    · simpa [hk] using measurableSet_le measurable_const (ha k)
    · simp [hk]
  obtain ⟨N, hN⟩ : ∃ N, μ (G N) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hnull : μ (⋃ N, G N) = 0 := measure_iUnion_null hcon
    have hfull : ∀ᵐ ζ ∂μ, ζ ∈ ⋃ N, G N := by
      filter_upwards [hfwd] with ζ hζ
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hζ b' hb'c)
      exact Set.mem_iUnion.2 ⟨N, hN⟩
    have hc : μ (⋃ N, G N)ᶜ = 0 := ae_iff.1 hfull
    have := measure_union_null hnull hc
    rw [Set.union_compl_self, measure_univ] at this
    exact one_ne_zero this
  filter_upwards [ae_eventually_exists_mem_window hτ (hGm N) hN hηpos, hwin,
    ae_tendsto_birkhoffAverage_of_ergodic hτ φ hφm hφ] with ω hvis hw hB
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (eventually_birkhoffSum_bounds hB hεpos)
  filter_upwards [hvis, eventually_ge_atTop (max N (max J 1))] with n hk hn
  obtain ⟨k, hnk, hkη, hkG⟩ := hk
  have hNn : N ≤ n := le_trans (le_max_left _ _) hn
  have hJn : J ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hak : Real.exp (b' * k) ≤ a k (τ^[k] ω) := hkG k (le_trans hNn hnk)
  -- the Birkhoff estimate on `(n, k]`
  have hsumeq : ∑ t ∈ Finset.Ioc n k, φ (τ^[t] ω) =
      birkhoffSum τ φ (k + 1) ω - birkhoffSum τ φ (n + 1) ω := by
    rw [birkhoffSum, birkhoffSum, ← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ k + 1)]
    rw [add_sub_cancel_left, Finset.Ico_add_one_add_one_eq_Ioc]
  have hup := (hJ (k + 1) (by omega)).2
  have hlo := (hJ (n + 1) (by omega)).1
  set S := ∑ t ∈ Finset.Ioc n k, φ (τ^[t] ω) with hS
  have hSle : S ≤ I * ((k : ℝ) - n) + ε * ((k : ℝ) + n + 2) := by
    rw [hsumeq]; push_cast at hup hlo; nlinarith
  have hwn := hw n k hnk
  have hmain : Real.exp (b' * k - S) ≤ a n (τ^[n] ω) := by
    rw [Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]
    exact hak.trans hwn
  refine le_trans (Real.exp_le_exp.2 ?_) hmain
  -- arithmetic
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hkn : (n : ℝ) ≤ k := by exact_mod_cast hnk
  have hkn2 : (k : ℝ) - n ≤ η * n := by nlinarith
  have hab : -(|b'| * ((k : ℝ) - n)) ≤ b' * ((k : ℝ) - n) := by
    have := neg_abs_le b'
    nlinarith
  have hI2 : I * ((k : ℝ) - n) ≤ I * (η * n) := mul_le_mul_of_nonneg_left hkn2 hI0
  have hb2 : |b'| * ((k : ℝ) - n) ≤ |b'| * (η * n) := mul_le_mul_of_nonneg_left hkn2 (abs_nonneg _)
  have hηn : (|b'| + I) * η * n ≤ δ / 2 * n := by
    have := mul_le_mul_of_nonneg_right hηb (by positivity : (0 : ℝ) ≤ n)
    linarith
  have hkk : (k : ℝ) ≤ 2 * n := by nlinarith
  rw [hε] at hSle
  nlinarith
end Density

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- **Vectors with a fast-decaying backward history.** `x ∈ R.backwardSpace ω c` when `x` has
preimages `x = y₀ ← y₁ ← y₂ ← ⋯` along the backward orbit, `𝓛_{σ^{-(n+1)}ω} y_{n+1} = y_n`, with
`(1/n) log ‖y_n‖` eventually below `-b` for every real `b < c` — i.e. the history decays at rate
at least `c`. (`σ^{-n}ω` is written `σ.symm^[n] ω`.) -/
def Cocycle.backwardSpace (R : Cocycle Ω X) (ω : Ω) (c : EReal) : Submodule ℝ X where
  carrier := {x | ∃ y : ℕ → X, y 0 = x ∧
    (∀ n : ℕ, R.L ((R.σ.symm : Ω → Ω)^[n + 1] ω) (y (n + 1)) = y n) ∧
    ∀ b : ℝ, (b : EReal) < c → ∀ᶠ n : ℕ in atTop, ‖y n‖ ≤ Real.exp (-b * n)}
  zero_mem' := ⟨0, rfl, fun n => by simp, fun b _ =>
    Eventually.of_forall fun n => by simp only [Pi.zero_apply, norm_zero]; positivity⟩
  add_mem' := by
    rintro x x' ⟨y, hy0, hyL, hyr⟩ ⟨y', hy0', hyL', hyr'⟩
    refine ⟨y + y', by simp [hy0, hy0'], fun n => ?_, fun b hb => ?_⟩
    · change R.L _ (y (n + 1) + y' (n + 1)) = y n + y' n
      rw [map_add, hyL, hyL']
    obtain ⟨b', hbb', hb'c⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hbb : b < b' := by exact_mod_cast hbb'
    filter_upwards [hyr b' hb'c, hyr' b' hb'c,
      eventually_mul_exp_le_exp (a := -b') (b := -b) (c := 0) (D := 2)
        (by linarith)] with n h1 h2 h3
    rw [zero_add] at h3
    calc ‖(y + y') n‖ ≤ ‖y n‖ + ‖y' n‖ := norm_add_le _ _
      _ ≤ 2 * Real.exp (-b' * n) := by linarith
      _ ≤ _ := h3
  smul_mem' := by
    rintro r x ⟨y, hy0, hyL, hyr⟩
    refine ⟨r • y, by simp [hy0], fun n => ?_, fun b hb => ?_⟩
    · change R.L _ (r • y (n + 1)) = r • y n
      rw [map_smul, hyL]
    obtain ⟨b', hbb', hb'c⟩ := EReal.lt_iff_exists_real_btwn.1 hb
    have hbb : b < b' := by exact_mod_cast hbb'
    filter_upwards [hyr b' hb'c,
      eventually_mul_exp_le_exp (a := -b') (b := -b) (c := 0) (D := |r|) (by linarith)] with n h1 h3
    rw [zero_add] at h3
    calc ‖(r • y) n‖ = |r| * ‖y n‖ := by simp [norm_smul]
      _ ≤ |r| * Real.exp (-b' * n) := mul_le_mul_of_nonneg_left h1 (abs_nonneg r)
      _ ≤ _ := h3

/-- A faster required rate gives a smaller space. -/
theorem Cocycle.backwardSpace_anti (R : Cocycle Ω X) (ω : Ω) {c c' : EReal} (h : c' ≤ c) :
    R.backwardSpace ω c ≤ R.backwardSpace ω c' := by
  rintro x ⟨y, hy0, hyL, hyr⟩
  exact ⟨y, hy0, hyL, fun b hb => hyr b (lt_of_lt_of_le hb h)⟩

/-- `σ` undoes `σ⁻¹`. -/
theorem Cocycle.sigma_symm_iterate_succ (R : Cocycle Ω X) (n : ℕ) (ω : Ω) :
    R.σ ((R.σ.symm : Ω → Ω)^[n + 1] ω) = (R.σ.symm : Ω → Ω)^[n] ω := by
  rw [Function.iterate_succ_apply']
  exact R.σ.apply_symm_apply _

/-- `σ^j` undoes `σ^{-j}`. -/
theorem Cocycle.iterate_sigma_symm_iterate (R : Cocycle Ω X) (j n : ℕ) (ω : Ω) :
    (R.σ : Ω → Ω)^[j] ((R.σ.symm : Ω → Ω)^[j + n] ω) = (R.σ.symm : Ω → Ω)^[n] ω := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, show j + 1 + n = j + n + 1 by omega,
      R.sigma_symm_iterate_succ, ih]

/-- **The window inequality for norms.** The norm of the `j`-step cocycle arriving at
`σ^{-n}ω` is at most `exp ∑_{t ∈ (n, n+j]} log⁺‖𝓛_{σ^{-t}ω}‖`. -/
theorem Cocycle.norm_iterate_backward_le (R : Cocycle Ω X) (ω : Ω) (n j : ℕ) :
    ‖R.iterate j ((R.σ.symm : Ω → Ω)^[n + j] ω)‖ ≤ Real.exp (∑ t ∈ Finset.Ioc n (n + j),
      Real.log (max ‖R.L ((R.σ.symm : Ω → Ω)^[t] ω)‖ 1)) := by
  induction j with
  | zero =>
    simp only [add_zero, Finset.Ioc_self, Finset.sum_empty, Real.exp_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ j ih =>
    set ζ := (R.σ.symm : Ω → Ω)^[n + (j + 1)] ω with hζ
    have hσζ : (R.σ : Ω → Ω)^[1] ζ = (R.σ.symm : Ω → Ω)^[n + j] ω := by
      rw [Function.iterate_one, hζ, show n + (j + 1) = n + j + 1 by omega,
        R.sigma_symm_iterate_succ]
    have hsplit : R.iterate (j + 1) ζ = (R.iterate j ((R.σ.symm : Ω → Ω)^[n + j] ω)).comp
        (R.iterate 1 ζ) := by
      rw [← hσζ]; exact R.iterate_add j 1 ζ
    have h1 : ‖R.iterate 1 ζ‖ ≤ max ‖R.L ζ‖ 1 := by
      have : R.iterate 1 ζ = (R.L ζ).comp (ContinuousLinearMap.id ℝ X) := by
        change (R.L ((R.σ : Ω → Ω)^[0] ζ)).comp (R.iterate 0 ζ) = _; rfl
      rw [this]
      calc ‖(R.L ζ).comp (ContinuousLinearMap.id ℝ X)‖ ≤ ‖R.L ζ‖ * ‖ContinuousLinearMap.id ℝ X‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖R.L ζ‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ max ‖R.L ζ‖ 1 := by rw [mul_one]; exact le_max_left _ _
    rw [hsplit, show n + (j + 1) = n + j + 1 by omega,
      Finset.sum_Ioc_succ_top (by omega : n ≤ n + j), Real.exp_add,
      Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))]
    calc ‖(R.iterate j ((R.σ.symm : Ω → Ω)^[n + j] ω)).comp (R.iterate 1 ζ)‖
        ≤ ‖R.iterate j ((R.σ.symm : Ω → Ω)^[n + j] ω)‖ * ‖R.iterate 1 ζ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := by
          rw [hζ, show n + (j + 1) = n + j + 1 by omega] at h1
          exact mul_le_mul ih h1 (norm_nonneg _) (Real.exp_pos _).le

omit [StandardBorelSpace Ω] in
/-- **Growth along a moving subspace is measurable.** `ω ↦ g(A ω, E ω)` for strongly measurable
`A` and measurable `E : Ω → 𝒢_mX`: continuous in the subspace, measurable in `ω` for a fixed
subspace, hence jointly measurable (Carathéodory). -/
theorem measurable_growth_moving [SeparableSpace X] [BorelSpace X] {m : ℕ} [NeZero m]
    {A : Ω → X →L[ℝ] X} (hA : ∀ x : X, Measurable fun ω => A ω x)
    {E : Ω → GrassmannianFin X m} (hE : Measurable E) :
    Measurable fun ω => growth (A ω) ((E ω).1 : Submodule ℝ X) := by
  have := grassmannianFin_separable (X := X) m
  have : SecondCountableTopology (GrassmannianFin X m) :=
    UniformSpace.secondCountable_of_separable _
  set u : GrassmannianFin X m → Ω → ℝ := fun V ω => growth (A ω) (V.1 : Submodule ℝ X) with hu
  have hcont : ∀ ω, Continuous fun V => u V ω := fun ω =>
    (growth_continuous (X := X) m).comp
      (Continuous.prodMk continuous_const continuous_id :
        Continuous fun V : GrassmannianFin X m => (A ω, V))
  have hmeas : ∀ V, Measurable (u V) := by
    intro V
    refine measurable_growth_of_weak hA _ ?_
    have := V.2.1
    have hne : ((V.1 : Submodule ℝ X)) ≠ ⊥ := by
      intro h
      have := V.2.2
      rw [h, finrank_bot] at this
      exact NeZero.ne m this.symm
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨‖x‖⁻¹ • x, ?_, (V.1 : Submodule ℝ X).smul_mem _ hx⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hjoint : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable (u := u) hcont hmeas
  have heq : (fun ω => growth (A ω) ((E ω).1 : Submodule ℝ X)) =
      Function.uncurry u ∘ (fun ω => (E ω, ω)) := rfl
  rw [heq]
  exact hjoint.comp (hE.prodMk measurable_id)

/-- A backward history is carried back to its endpoint by the cocycle:
`𝓛^{(n)}_{σ^{-n}ω} y_n = y_0`. -/
theorem Cocycle.iterate_history (R : Cocycle Ω X) (ω : Ω) {y : ℕ → X}
    (hyL : ∀ n : ℕ, R.L ((R.σ.symm : Ω → Ω)^[n + 1] ω) (y (n + 1)) = y n) (n : ℕ) :
    R.iterate n ((R.σ.symm : Ω → Ω)^[n] ω) (y n) = y 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs : R.iterate (n + 1) ((R.σ.symm : Ω → Ω)^[n + 1] ω) =
        (R.iterate n ((R.σ.symm : Ω → Ω)^[n] ω)).comp
          (R.iterate 1 ((R.σ.symm : Ω → Ω)^[n + 1] ω)) := by
      have := R.iterate_add n 1 ((R.σ.symm : Ω → Ω)^[n + 1] ω)
      rwa [Function.iterate_one, R.sigma_symm_iterate_succ] at this
    have h1 : R.iterate 1 ((R.σ.symm : Ω → Ω)^[n + 1] ω) (y (n + 1)) =
        R.L ((R.σ.symm : Ω → Ω)^[n + 1] ω) (y (n + 1)) := rfl
    rw [hs, ContinuousLinearMap.comp_apply, h1, hyL, ih]

/-- **Fast vectors have fast-decaying histories** (the forward half of the backward
characterisation; cf. Froyland--Lloyd--Quas, Lemma 20). If an equivariant measurable family `E`
grows at rate `c` — `g(𝓛^{(n)}_ω, E(ω)) ≥ e^{bn}` eventually for each `b < c` — then a.e. every
`x ∈ E(ω)` has a history inside `E` decaying at rate `c`.

The history is built by choosing preimages inside `E`, which equivariance supplies. Its decay is
`‖y_n‖ ≤ ‖x‖ / g(𝓛^{(n)}_{σ^{-n}ω}, E(σ^{-n}ω))`, a *backward* growth bound; FLQ obtain it from
Kingman applied to the inverse cocycle on `E`, which needs `log⁺‖(𝓛|_E)^{-1}‖` integrable. Here it
comes from the forward bound by `ae_eventually_exp_le_backward`, which needs no such hypothesis. -/
theorem Cocycle.ae_le_backwardSpace_of_growth (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    {m : ℕ} [NeZero m] (E : Ω → GrassmannianFin X m) (hEm : Measurable E)
    (hEeq : ∀ᵐ ω ∂(R.μ), Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E ω).1 : Submodule ℝ X)
        = ((E (R.σ ω)).1 : Submodule ℝ X))
    {c : ℝ} (hEg : ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, b < c → ∀ᶠ n : ℕ in atTop,
        Real.exp (b * n) ≤ growth (R.iterate n ω) ((E ω).1 : Submodule ℝ X)) :
    ∀ᵐ ω ∂(R.μ), ((E ω).1 : Submodule ℝ X) ≤ R.backwardSpace ω c := by
  set τ : Ω → Ω := (R.σ.symm : Ω → Ω) with hτ
  have hτerg : Ergodic τ R.μ := R.ergodic.symm
  have hτmp : MeasurePreserving τ R.μ R.μ := hτerg.toMeasurePreserving
  -- equivariance at every point `σ^s (σ^{-k} ω)`
  have hall : ∀ᵐ ω ∂(R.μ), ∀ k s : ℕ,
      Submodule.map (R.L (R.σ^[s] (τ^[k] ω)) : X →ₗ[ℝ] X)
        ((E (R.σ^[s] (τ^[k] ω))).1 : Submodule ℝ X)
        = ((E (R.σ^[s + 1] (τ^[k] ω))).1 : Submodule ℝ X) := by
    rw [ae_all_iff]
    intro k
    exact (hτmp.iterate k).quasiMeasurePreserving.ae (R.ae_all_shift_equivariant E hEeq)
  set a : ℕ → Ω → ℝ := fun n ζ => growth (R.iterate n ζ) ((E ζ).1 : Submodule ℝ X) with hadef
  have ha : ∀ n, Measurable (a n) := fun n =>
    measurable_growth_moving (fun x => R.measurable_iterate_apply n x) hEm
  set φ : Ω → ℝ := fun ω => Real.log (max ‖R.L ω‖ 1) with hφdef
  have hφm : Measurable φ := Real.measurable_log.comp (R.measurable_norm_L.max measurable_const)
  have hφ0 : ∀ ω, 0 ≤ φ ω := fun ω => Real.log_nonneg (le_max_right _ _)
  have hwin : ∀ᵐ ω ∂(R.μ), ∀ n k : ℕ, n ≤ k →
      a k (τ^[k] ω) ≤ a n (τ^[n] ω) * Real.exp (∑ t ∈ Finset.Ioc n k, φ (τ^[t] ω)) := by
    filter_upwards [hall] with ω hω n k hnk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
    have hσ : (R.σ : Ω → Ω)^[j] (τ^[n + j] ω) = τ^[n] ω := by
      rw [add_comm n j]; exact R.iterate_sigma_symm_iterate j n ω
    have hsplit : R.iterate (n + j) (τ^[n + j] ω) =
        (R.iterate n (τ^[n] ω)).comp (R.iterate j (τ^[n + j] ω)) := by
      rw [← hσ]; exact R.iterate_add n j _
    have hmap : Submodule.map (R.iterate j (τ^[n + j] ω) : X →ₗ[ℝ] X)
        ((E (τ^[n + j] ω)).1 : Submodule ℝ X) = ((E (τ^[n] ω)).1 : Submodule ℝ X) := by
      rw [← hσ]; exact R.map_iterate_of_equivariant E _ (hω (n + j)) j
    change growth (R.iterate (n + j) (τ^[n + j] ω)) ((E (τ^[n + j] ω)).1 : Submodule ℝ X) ≤
      growth (R.iterate n (τ^[n] ω)) ((E (τ^[n] ω)).1 : Submodule ℝ X) * _
    rw [hsplit]
    have h1 := (growth_ineq (R.iterate j (τ^[n + j] ω)) (R.iterate n (τ^[n] ω))
      ((E (τ^[n + j] ω)).1 : Submodule ℝ X)).2
    rw [hmap] at h1
    calc _ ≤ ‖R.iterate j (τ^[n + j] ω)‖ *
          growth (R.iterate n (τ^[n] ω)) ((E (τ^[n] ω)).1 : Submodule ℝ X) :=
          h1.trans (min_le_left _ _)
      _ ≤ Real.exp (∑ t ∈ Finset.Ioc n (n + j), φ (τ^[t] ω)) *
          growth (R.iterate n (τ^[n] ω)) ((E (τ^[n] ω)).1 : Submodule ℝ X) :=
          mul_le_mul_of_nonneg_right (R.norm_iterate_backward_le ω n j) (growth_nonneg _ _)
      _ = _ := mul_comm _ _
  have hback := ae_eventually_exp_le_backward hτerg a ha hφm R.forwardIntegrable hφ0 hwin hEg
  filter_upwards [hback, hall] with ω hb hω x hx
  -- each backward step maps `E` onto `E`
  have hsurj : ∀ n : ℕ, ∀ v ∈ ((E (τ^[n] ω)).1 : Submodule ℝ X),
      ∃ u ∈ ((E (τ^[n + 1] ω)).1 : Submodule ℝ X), R.L (τ^[n + 1] ω) u = v := by
    intro n v hv
    have h := hω (n + 1) 0
    simp only [Function.iterate_zero, id_eq, zero_add, Function.iterate_one] at h
    rw [R.sigma_symm_iterate_succ] at h
    rw [← h] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact ⟨u, hu, rfl⟩
  choose! pre hpre using hsurj
  obtain ⟨y, hy0, hys⟩ : ∃ y : ℕ → X, y 0 = x ∧ ∀ n, y (n + 1) = pre n (y n) :=
    ⟨fun n => Nat.rec x (fun n yn => pre n yn) n, rfl, fun n => rfl⟩
  have hy : ∀ n, y n ∈ ((E (τ^[n] ω)).1 : Submodule ℝ X) := by
    intro n
    induction n with
    | zero => rw [hy0]; exact hx
    | succ n ih => rw [hys]; exact (hpre n (y n) ih).1
  have hyL : ∀ n : ℕ, R.L (τ^[n + 1] ω) (y (n + 1)) = y n := fun n => by
    rw [hys]; exact (hpre n (y n) (hy n)).2
  refine ⟨y, hy0, hyL, fun b hb' => ?_⟩
  have hbc : b < c := by exact_mod_cast hb'
  have hb'c : (b + c) / 2 < c := by linarith
  filter_upwards [hb ((b + c) / 2) hb'c,
    eventually_mul_exp_le_exp (a := -((b + c) / 2)) (b := -b) (c := 0) (D := ‖x‖) (by linarith)]
    with n hn h3
  rw [zero_add] at h3
  have hg := growth_mul_norm_le (R.iterate n (τ^[n] ω)) (hy n)
  rw [R.iterate_history ω hyL n, hy0] at hg
  have h4 : Real.exp ((b + c) / 2 * n) * ‖y n‖ ≤ ‖x‖ :=
    le_trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)) hg
  have h5 : ‖y n‖ ≤ ‖x‖ * Real.exp (-((b + c) / 2) * n) := by
    rw [show -((b + c) / 2) * (n : ℝ) = -((b + c) / 2 * n) by ring, Real.exp_neg,
      le_mul_inv_iff₀ (Real.exp_pos _)]
    linarith [mul_comm (Real.exp ((b + c) / 2 * n)) ‖y n‖]
  exact h5.trans h3

/-- **Slow vectors have no fast-decaying history** (the backward half). In the slow space
`V(ω) = {λ_ω ≤ λ_{l+2}}` of a level datum, a vector with a history decaying at rate `λ_{l+1}` is
zero. With `Q` the projection onto `V`, `v = Q_ω 𝓛^{(n)}_{σ^{-n}ω} y_n = 𝓛^{(n)}_{σ^{-n}ω} Q y_n`,
and the operator `𝓛^{(n)}_{σ^{-n}ω} Q_{σ^{-n}ω}` is the backward `n`-step cocycle of `𝓛 ∘ Q`,
whose norm grows at rate `χ'_1 = λ_{l+2} < λ_{l+1}` by backward Kingman
(`ae_tendsto_chi_backward`). -/
theorem Cocycle.IsLevel.eq_zero_of_mem_backwardSpace (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] {lam : ℕ → EReal} (hlam : ∀ i, ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i)
    {l : ℕ} {D : LevelData Ω X} (hD : R.IsLevel lam l D) :
    ∀ᵐ ω ∂(R.μ), ∀ v ∈ ((D.V ω).1.1 : Submodule ℝ X), v ∈ R.backwardSpace ω (lam l) → v = 0 := by
  classical
  obtain ⟨A, C, hA, hApos, hC⟩ := R.exists_bounded_set hD.Q_meas
  let R' : Cocycle Ω X := R.modify D.Q hD.Q_meas A hA C hC
  obtain ⟨lamL, hlamL⟩ := hD.lam_real
  have hgapR : ∀ᵐ ω ∂(R.μ), ∀ᶠ n : ℕ in atTop, ‖(R.iterate n ω).comp (D.Q ω)‖ <
      growth (R.iterate n ω) ((D.F ω).1 : Submodule ℝ X) := by
    obtain ⟨b1, hb1, hb1'⟩ := EReal.lt_iff_exists_real_btwn.1 hD.lam_gap
    obtain ⟨b2, hb2, hb2'⟩ := EReal.lt_iff_exists_real_btwn.1 hb1'
    have hb12 : b1 < b2 := by exact_mod_cast hb2
    filter_upwards [hD.slow_rate, hD.F_growth] with ω hs hF
    filter_upwards [eventually_lt_exp_of_tendsto hb1 hs, hF b2 hb2'] with n h1 h2
    refine lt_of_lt_of_le h1 (le_trans ?_ h2)
    rw [mul_comm]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb12.le (Nat.cast_nonneg _))
  have hχ := R.chi_modify (fun ω => ((D.F ω).1 : Submodule ℝ X)) D.V D.Q hD.Q_meas hA hApos hC
    hD.Q_idem hD.Q_range hD.Q_ker hD.Q_equiv hD.Q_temp hgapR
  -- the top exponent of `𝓛'` is `λ_{l+2}`
  have hchi1 : ∀ᵐ ω ∂(R.μ), R'.chi 1 ω = lam (l + 1) := by
    filter_upwards [hχ, hD.lambdaIdx_eq, hlam (l + 1)] with ω h1 h2 h3
    rw [h1 1 le_rfl, ← h3]
    change R.chi (D.M + 1) ω = R.chi (R.lambdaIdx (l + 1) ω) ω
    rw [h2]
  have hback : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal ‖R'.iterate n ((R.σ.symm : Ω → Ω)^[n] ω)‖ / (n : EReal)) atTop (𝓝 (R'.chi 1 ω)) := by
    filter_upwards [R'.ae_tendsto_chi_backward 1] with ω h
    simp only [bernsteinNumber_one, zIter_neg_natCast] at h
    exact h
  set τ : Ω → Ω := (R.σ.symm : Ω → Ω) with hτ
  have hτerg : Ergodic τ R.μ := R.ergodic.symm
  have hτmp : MeasurePreserving τ R.μ R.μ := hτerg.toMeasurePreserving
  have horbQ := R.ae_forall_iterate (hD.Q_idem.and hD.Q_equiv)
  have hallQ : ∀ᵐ ω ∂(R.μ), ∀ k i : ℕ,
      (D.Q (R.σ^[i] (τ^[k] ω))).comp (D.Q (R.σ^[i] (τ^[k] ω))) = D.Q (R.σ^[i] (τ^[k] ω)) ∧
      (D.Q (R.σ (R.σ^[i] (τ^[k] ω)))).comp (R.L (R.σ^[i] (τ^[k] ω))) =
        (R.L (R.σ^[i] (τ^[k] ω))).comp (D.Q (R.σ^[i] (τ^[k] ω))) := by
    rw [ae_all_iff]
    intro k
    exact (hτmp.iterate k).quasiMeasurePreserving.ae horbQ
  have hvisit : ∀ᵐ ω ∂(R.μ), ∃ k : ℕ, τ^[k + 1] ω ∈ A := by
    filter_upwards [hτmp.quasiMeasurePreserving.ae (ae_exists_mem_iterate hτerg hA hApos)]
      with ω ⟨k, hk⟩
    exact ⟨k, by rwa [Function.iterate_succ_apply]⟩
  have hQfix : ∀ᵐ ω ∂(R.μ), ∀ v ∈ ((D.V ω).1.1 : Submodule ℝ X), D.Q ω v = v := by
    filter_upwards [hD.Q_range, hD.Q_idem] with ω hr hid v hv
    rw [← hr] at hv
    obtain ⟨z, rfl⟩ := hv
    exact congrArg (fun T : X →L[ℝ] X => T z) hid
  filter_upwards [hback, hchi1, hallQ, hvisit, hQfix] with ω hb hc hQ hv hfix v hvV hvB
  obtain ⟨y, hy0, hyL, hyr⟩ := hvB
  obtain ⟨k, hk⟩ := hv
  -- `v = 𝓛'^{(n)}_{σ^{-n}ω} y_n` for all `n > k`
  have hrep : ∀ n : ℕ, k + 1 ≤ n → R'.iterate n (τ^[n] ω) (y n) = v := by
    intro n hn
    have hid : ∀ i : ℕ, (D.Q (R.σ^[i] (τ^[n] ω))).comp (D.Q (R.σ^[i] (τ^[n] ω))) =
        D.Q (R.σ^[i] (τ^[n] ω)) := fun i => (hQ n i).1
    have hcomm : ∀ i : ℕ, (D.Q (R.σ^[i + 1] (τ^[n] ω))).comp (R.L (R.σ^[i] (τ^[n] ω))) =
        (R.L (R.σ^[i] (τ^[n] ω))).comp (D.Q (R.σ^[i] (τ^[n] ω))) := fun i => by
      rw [Function.iterate_succ_apply']; exact (hQ n i).2
    have hit := R.modify_iterate hD.Q_meas hA hC (τ^[n] ω) hid hcomm n
    have hvis : R.σ^[n - (k + 1)] (τ^[n] ω) ∈ A := by
      have := R.iterate_sigma_symm_iterate (n - (k + 1)) (k + 1) ω
      rw [show n - (k + 1) + (k + 1) = n by omega] at this
      rw [this]; exact hk
    have hR' : R'.iterate n (τ^[n] ω) = (R.iterate n (τ^[n] ω)).comp (D.Q (τ^[n] ω)) :=
      hit.2.1 (n - (k + 1)) (by omega) hvis
    have hσn : R.σ^[n] (τ^[n] ω) = ω := by
      have := R.iterate_sigma_symm_iterate n 0 ω
      simpa using this
    have hc1 := congrArg (fun T : X →L[ℝ] X => T (y n)) hit.1
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hσn] at hc1
    rw [hR', ContinuousLinearMap.comp_apply, ← hc1, R.iterate_history ω hyL n, hy0]
    exact hfix v hvV
  -- rates
  have hgap : lam (l + 1) < (lamL : EReal) := hlamL ▸ hD.lam_gap
  obtain ⟨b1, hb1, hb1L⟩ := EReal.lt_iff_exists_real_btwn.1 hgap
  have hb1L' : b1 < lamL := by exact_mod_cast hb1L
  set b : ℝ := (b1 + lamL) / 2 with hbdef
  have hbL : (b : EReal) < lam l := by rw [hlamL]; exact_mod_cast (by linarith : b < lamL)
  have hup : ∀ᶠ n : ℕ in atTop, ‖R'.iterate n (τ^[n] ω)‖ < Real.exp (b1 * n) := by
    rw [hc] at hb
    exact eventually_lt_exp_of_tendsto hb1 hb
  have hbound : ∀ᶠ n : ℕ in atTop, ‖v‖ ≤ Real.exp ((b1 - b) * n) := by
    filter_upwards [hup, hyr b hbL, eventually_ge_atTop (k + 1)] with n h1 h2 hn
    rw [← hrep n hn]
    calc ‖R'.iterate n (τ^[n] ω) (y n)‖ ≤ ‖R'.iterate n (τ^[n] ω)‖ * ‖y n‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp (b1 * n) * Real.exp (-b * n) :=
          mul_le_mul h1.le h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((b1 - b) * n) := by rw [← Real.exp_add]; ring_nf
  have hlim : Tendsto (fun n : ℕ => Real.exp ((b1 - b) * n)) atTop (𝓝 0) := by
    have hneg : b1 - b < 0 := by rw [hbdef]; linarith
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg hneg).2 tendsto_natCast_atTop_atTop)
  have hle : ‖v‖ ≤ 0 := ge_of_tendsto hlim hbound
  exact norm_le_zero_iff.1 hle

/-- **The backward characterisation of the fast spaces.** For any witness to `mainres` and any
`i` with `i + 2 ≤ L`, almost surely `E_0(ω) ⊕ ⋯ ⊕ E_i(ω)` is exactly the space of vectors having a
backward history `x = y₀ ← y₁ ← ⋯` along `σ^{-n}ω` that decays at rate `λ_{i+1}`
(`lam i`, in the paper's indexing): `limsup (1/n) log ‖y_n‖ ≤ -λ_{i+1}`.

This is not in `proof_met.tex`; it is the semi-invertible counterpart of the two-sided rates in
Oseledets' theorem (cf. Froyland--Lloyd--Quas, Lemma 20). The fast sum is contained in the
history space by `ae_le_backwardSpace_of_growth`; conversely, writing `x = f + v` along
`X = (⊕ E_j) ⊕ V_{i+1}`, the slow part `v` also has such a history, and is `0` by
`IsLevel.eq_zero_of_mem_backwardSpace`. -/
theorem Cocycle.IsOseledets.backward_characterisation (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] [CompleteSpace X]
    {L : ℕ∞} {lam : ℕ → EReal} {mdim : ℕ → ℕ} {E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1)}
    {V : ℕ → Ω → Submodule ℝ X} {P : ℕ → Ω → X →L[ℝ] X}
    (h : R.IsOseledets L lam mdim E V P) (i : ℕ) (hi : ((i + 2 : ℕ) : ℕ∞) ≤ L) :
    ∀ᵐ ω ∂(R.μ), (⨆ j ∈ Finset.range (i + 1), ((E j ω).1 : Submodule ℝ X)) =
      R.backwardSpace ω (lam i) := by
  obtain ⟨-, hlam, hL, -, hEm, -, -, hE, hdec⟩ := h
  choose c hc using R.exists_lambda_ae_eq
  have hlamc : ∀ j : ℕ, (j : ℕ∞) < L → lam j = c j := fun j hj => by
    obtain ⟨ω, h1, h2⟩ := ((hlam j hj).and (hc j)).exists
    rw [← h1, h2]
  have hlt0 : ∀ j : ℕ, ((j + 2 : ℕ) : ℕ∞) ≤ L → (j : ℕ∞) < L := fun j hj =>
    lt_of_lt_of_le (by exact_mod_cast (show j < j + 2 by omega)) hj
  have hlt1 : ∀ j : ℕ, ((j + 2 : ℕ) : ℕ∞) ≤ L → ((j + 1 : ℕ) : ℕ∞) < L := fun j hj =>
    lt_of_lt_of_le (by exact_mod_cast (show j + 1 < j + 2 by omega)) hj
  have hmono_le : ∀ j j' : ℕ, j' + 2 ≤ i + 2 → j ≤ j' → c j' ≤ c j := by
    intro j j' hj' hjj'
    induction j' with
    | zero => rw [Nat.le_zero.1 hjj']
    | succ j' ih =>
      rcases Nat.lt_or_eq_of_le hjj' with hlt | heq
      · have hprev : ((j' + 2 : ℕ) : ℕ∞) ≤ L :=
          le_trans (by exact_mod_cast (show j' + 2 ≤ i + 2 by omega)) hi
        have hm := (hL j').1 hprev
        obtain ⟨ω, h0, h1, h2⟩ := ((hc j').and ((hc (j' + 1)).and hm)).exists
        have hs := R.lambda_succ_lt ω h2
        rw [h0, h1] at hs
        exact hs.le.trans (ih (by omega) (by omega))
      · rw [heq]
  have hreal : ∀ j : ℕ, j ≤ i → ∃ r : ℝ, c j = r := by
    intro j hj
    have hj2 : ((j + 2 : ℕ) : ℕ∞) ≤ L :=
      le_trans (by exact_mod_cast (show j + 2 ≤ i + 2 by omega)) hi
    have hm := (hL j).1 hj2
    have hgap : c (j + 1) < c j := by
      obtain ⟨ω, h0, h1, h2⟩ := ((hc j).and ((hc (j + 1)).and hm)).exists
      have hs := R.lambda_succ_lt ω h2
      rwa [h0, h1] at hs
    have htop : c j < ⊤ := by
      obtain ⟨ω, h0, h1⟩ := ((hc 0).and R.ae_chi_one_lt_top).exists
      have : c 0 < ⊤ := by rw [← h0]; exact h1
      exact lt_of_le_of_lt (hmono_le 0 j (by omega) (Nat.zero_le j)) this
    exact ⟨(c j).toReal, (EReal.coe_toReal htop.ne (lt_of_le_of_lt bot_le hgap).ne').symm⟩
  -- each fast space lies in the history space
  have hfast : ∀ᵐ ω ∂(R.μ), ∀ j : ℕ, j ∈ Finset.range (i + 1) →
      ((E j ω).1 : Submodule ℝ X) ≤ R.backwardSpace ω (c i) := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ∈ Finset.range (i + 1)
    · have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hj2 : ((j + 2 : ℕ) : ℕ∞) ≤ L :=
        le_trans (by exact_mod_cast (show j + 2 ≤ i + 2 by omega)) hi
      obtain ⟨r, hr⟩ := hreal j hji
      have hA := hE j hj2
      rw [hlamc j (hlt0 j hj2), hr] at hA
      have hg : ∀ᵐ ω ∂(R.μ), ∀ b : ℝ, b < r → ∀ᶠ n : ℕ in atTop,
          Real.exp (b * n) ≤ growth (R.iterate n ω) ((E j ω).1 : Submodule ℝ X) := by
        filter_upwards [hA] with ω hω b hb
        filter_upwards [hω.2.2.2.eventually_const_lt (show (b : EReal) < r by exact_mod_cast hb),
          eventually_ge_atTop 1] with n hn hn1
        exact ((lt_logEReal_div_iff hn1 b).1 hn).le
      filter_upwards [R.ae_le_backwardSpace_of_growth (E j) (hEm j) (hA.mono fun ω h => h.2.1) hg]
        with ω hω _
      refine hω.trans (R.backwardSpace_anti ω ?_)
      rw [← hr]; exact hmono_le j i le_rfl hji
    · exact Eventually.of_forall fun ω h => absurd h hj
  have hmi : ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0 := (hL i).1 hi
  obtain ⟨D, hD⟩ := R.exists_isLevel hc i hmi
  filter_upwards [hfast, hdec i hi, hD.eq_zero_of_mem_backwardSpace R hc, hD.slow_char]
    with ω hle hd hz hchar
  rw [hlamc i (hlt0 i hi)]
  refine le_antisymm (iSup₂_le hle) fun x hx => ?_
  have hxs : x ∈ (⨆ j ∈ Finset.range (i + 1), ((E j ω).1 : Submodule ℝ X)) ⊔ V (i + 1) ω := by
    rw [hd.1.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨f, hf, v, hv, rfl⟩ := Submodule.mem_sup.1 hxs
  have hvB : v ∈ R.backwardSpace ω (c i) := by
    have := sub_mem hx (iSup₂_le hle hf)
    rwa [add_sub_cancel_left] at this
  have hvD : v ∈ ((D.V ω).1.1 : Submodule ℝ X) := by
    change v ∈ (((D.V ω).1.1 : Submodule ℝ X) : Set X)
    rw [hchar, ← hlamc (i + 1) (hlt1 i hi), ← hd.2.2.2.2.2]
    exact hv
  rw [hz v hvD hvB, add_zero]
  exact hf

end MultiplicativeErgodic
