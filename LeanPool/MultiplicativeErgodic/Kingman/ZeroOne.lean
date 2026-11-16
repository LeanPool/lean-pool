/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman.Basic

/-!
# The zero-one law for `liminf fₙ/n`

`liminfGE a q` is the set where `liminf aₙ ≥ q`, written unfolded so that measurability is a
plain countable-operations argument. Under an ergodic `σ` its measure is `0` or `1`, which is
what turns the liminf into a constant.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-!
## Set-level `liminf` thresholds

Both `kingman` and `balancedKingman` need the a.e.-constancy of `ω ↦ liminf aₙ(ω)` — for
`kingman` with `aₙ(ω) = f_n(ω)/n`, for `balancedKingman` with `aₙ(ω) = f_{2n}(σ⁻ⁿω)/(2n)`.
Forming that `liminf` as an honest `ℝ`-valued *function* is
awkward in Lean: `Filter.liminf` into `ℝ` carries `ConditionallyCompleteLattice` boundedness
side-conditions at every step, and escaping to `EReal` drags casting through the whole argument.

The lemmas below sidestep both by never forming a `liminf`-valued function at all. Instead
`liminfGE a q` is the *set* `{ω | liminf aₙ(ω) ≥ q}`, spelled out directly by its `ε`-`N`
definition. It is a countable `⋂/⋃/⋂` of preimages of open rays, hence measurable, and the
ergodic zero-one law applies to it verbatim. The threshold constant is then recovered as a
supremum over the (countably many) rational thresholds of full measure, in step (iii).
-/

/-- The set on which `liminf aₙ ≥ q`, written at the set level: for every rational `ε > 0`,
eventually `aₙ > q - ε`. Kept as an unfolded `∀ ε, ∃ N, ∀ n ≥ N` statement rather than a
`Filter.liminf` inequality so that measurability is a plain countable-operations argument and no
`ConditionallyCompleteLattice`/`EReal` bookkeeping is ever needed. -/
def liminfGE (a : ℕ → Ω → ℝ) (q : ℝ) : Set Ω :=
  {ω | ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → q - (ε : ℝ) < a n ω}

omit [MeasurableSpace Ω] in
/-- `liminfGE a` is antitone in the threshold: a larger `liminf` lower bound is a smaller set. -/
theorem liminfGE_antitone (a : ℕ → Ω → ℝ) : Antitone (liminfGE a) := by
  intro q q' hqq' ω hω ε hε
  obtain ⟨N, hN⟩ := hω ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  linarith

/-- `liminfGE a q` is measurable whenever each `aₙ` is: it is
`⋂_{ε > 0} ⋃_N ⋂_{n ≥ N} aₙ⁻¹(q - ε, ∞)`, a countable combination of preimages of open rays. -/
theorem measurableSet_liminfGE {a : ℕ → Ω → ℝ} (ha : ∀ n, Measurable (a n)) (q : ℝ) :
    MeasurableSet (liminfGE a q) := by
  have hrw : liminfGE a q =
      ⋂ ε ∈ {ε : ℚ | 0 < ε}, ⋃ N : ℕ, ⋂ n ∈ {n : ℕ | N ≤ n},
        (a n) ⁻¹' (Set.Ioi (q - (ε : ℝ))) := by
    ext ω
    simp only [liminfGE, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_Ioi]
  rw [hrw]
  refine MeasurableSet.biInter (Set.to_countable _) fun ε _ => ?_
  refine MeasurableSet.iUnion fun N => ?_
  exact MeasurableSet.biInter (Set.to_countable _) fun n _ => (ha n) measurableSet_Ioi

/-- **Ergodic zero-one law for the threshold sets.** If the threshold set is a.e. forward
invariant — only an a.e. *inclusion* `σ⁻¹(S) ⊆ S` is needed, which is exactly the shape the
caller (`balancedKingman`'s invariance step) produces from `hstep` — then it is null or conull.

The a.e.-inclusion form matters: that step gives the one-sided
`C_hat_{σ⁻¹ω} ≥ C_hat_ω`, so demanding
genuine invariance here would force extra work that
`Ergodic.ae_empty_or_univ_of_preimage_ae_le` makes unnecessary. -/
theorem measure_liminfGE_eq_zero_or_one {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {a : ℕ → Ω → ℝ} (ha : ∀ n, Measurable (a n)) (q : ℝ)
    (hinv : σ ⁻¹' (liminfGE a q) ≤ᵐ[μ] liminfGE a q) :
    μ (liminfGE a q) = 0 ∨ μ (liminfGE a q) = 1 := by
  rcases hσ.ae_empty_or_univ_of_preimage_ae_le
      (measurableSet_liminfGE ha q).nullMeasurableSet hinv with h | h
  · exact Or.inl (by rw [measure_congr h, measure_empty])
  · exact Or.inr (by rw [measure_congr h, measure_univ])

/-- The companion of `measure_liminfGE_eq_zero_or_one` for the *other* inclusion. Subadditivity
gives `liminf aₙ(σω) ≥ liminf aₙ(ω)`, i.e. `S ⊆ σ⁻¹ S` rather than `σ⁻¹ S ⊆ S`, so this is the
direction `kingman` actually produces. -/
theorem measure_liminfGE_eq_zero_or_one' {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {a : ℕ → Ω → ℝ} (ha : ∀ n, Measurable (a n)) (q : ℝ)
    (hinv : (liminfGE a q : Set Ω) ≤ᵐ[μ] σ ⁻¹' liminfGE a q) :
    μ (liminfGE a q) = 0 ∨ μ (liminfGE a q) = 1 := by
  rcases hσ.ae_empty_or_univ_of_ae_le_preimage
      (measurableSet_liminfGE ha q).nullMeasurableSet hinv with h | h
  · exact Or.inl (by rw [measure_congr h, measure_empty])
  · exact Or.inr (by rw [measure_congr h, measure_univ])

/-- **The liminf threshold sets are `σ`-forward-invariant.** From `f_{n+1}(ω) ≤ f_n(σω) + f_1(ω)`
we get `liminf f_n(σω)/n ≥ liminf f_n(ω)/n`, i.e. `S ⊆ σ⁻¹ S` for `S = {liminf ≥ q}`.

The `ε`-bookkeeping is delicate because the shift changes the denominator: the natural bound is
on `f_{n+1}(ω)/(n+1)` but what appears is `f_{n+1}(ω)/n`. Writing the latter as `A + A/n` with
`A = f_{n+1}(ω)/(n+1)` and using `A > q - ε/3` gives `A/n > (q - ε/3)/n`, which is eventually
`> -ε/3` whatever the sign of `q - ε/3`. -/
theorem SubadditiveFamily.liminfGE_le_preimage (μ : Measure Ω)
    (σ : Ω → Ω) (_hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (_hint : ∀ n, Integrable (f n) μ) (q : ℝ) :
    (liminfGE (fun n ω => f n ω / n) q : Set Ω)
      ≤ᵐ[μ] σ ⁻¹' liminfGE (fun n ω => f n ω / n) q := by
  filter_upwards with ω hmem
  simp only [liminfGE] at hmem ⊢
  intro ε hε
  have hε0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  -- pick the threshold at `ε/3`
  obtain ⟨ε', hε'pos, hε'lt⟩ : ∃ e : ℚ, 0 < e ∧ (e : ℝ) ≤ (ε : ℝ) / 3 :=
    ⟨ε / 3, by positivity, by push_cast; linarith⟩
  obtain ⟨N₀, hN₀⟩ := hmem ε' hε'pos
  set κ : ℝ := q - (ε' : ℝ) with hκ
  -- `f 1 ω / n → 0` and `κ / n → 0`
  have h1 : Tendsto (fun n : ℕ => f 1 ω / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun n : ℕ => κ / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp h1 ((ε : ℝ) / 3) (by positivity)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp h2 ((ε : ℝ) / 3) (by positivity)
  refine ⟨max (max N₀ N₁) (max N₂ 1), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right N₂ 1) (le_max_right _ _)) hn
  have hnN₀ : N₀ ≤ n + 1 := le_trans (le_trans (le_max_left N₀ N₁) (le_max_left _ _))
    (le_trans hn (Nat.le_succ n))
  have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_right N₀ N₁) (le_max_left _ _)) hn
  have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_left N₂ 1) (le_max_right _ _)) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn10 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- `A := f_{n+1}(ω)/(n+1) > κ`
  set A : ℝ := f (n + 1) ω / ((n : ℝ) + 1) with hA
  have hAκ : κ < A := by
    have h := hN₀ (n + 1) hnN₀
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring] at h
    exact h
  -- `f_{n+1}(ω)/n = A + A/n`, and `A/n > κ/n > -ε/3`
  have hsplit : f (n + 1) ω / (n : ℝ) = A + A / (n : ℝ) := by
    rw [hA]; field_simp
  have hAn : -((ε : ℝ) / 3) < A / (n : ℝ) := by
    rcases le_or_gt 0 κ with hκ0 | hκ0
    · have : 0 < A := lt_of_le_of_lt hκ0 hAκ
      have : 0 < A / (n : ℝ) := by positivity
      linarith [this, hε0]
    · have hlt : κ / (n : ℝ) < A / (n : ℝ) := by gcongr
      have := hN₂ n hnN₂
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      linarith [this.1, hlt]
  -- subadditivity: `f_n(σω) ≥ f_{n+1}(ω) - f_1(ω)`
  have hsub := hf.2 n 1 ω
  rw [show n + 1 = n + 1 from rfl, Function.iterate_one] at hsub
  have hf1 := hN₁ n hnN₁
  rw [Real.dist_eq, sub_zero, abs_lt] at hf1
  have hkey : q - (ε : ℝ) < f n (σ ω) / (n : ℝ) := by
    have hge : f (n + 1) ω / (n : ℝ) - f 1 ω / (n : ℝ) ≤ f n (σ ω) / (n : ℝ) := by
      rw [← sub_div]
      gcongr
      linarith [hsub]
    have : q - (ε : ℝ) < f (n + 1) ω / (n : ℝ) - f 1 ω / (n : ℝ) := by
      rw [hsplit]
      have : (ε' : ℝ) ≤ (ε : ℝ) / 3 := hε'lt
      linarith [hAκ, hAn, hf1.1, hf1.2]
    linarith
  exact hkey

/-- **Zero-one law for Kingman's liminf thresholds.** Combining `liminfGE_le_preimage` with
`measure_liminfGE_eq_zero_or_one'`: for every `q`, the set where `liminf f_n/n ≥ q` is null or
conull. This is the a.e.-constancy of `liminf f_n/n`, in the set form that avoids ever
constructing a `liminf`-valued function. -/
theorem SubadditiveFamily.measure_liminfGE_zero_or_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (hint : ∀ n, Integrable (f n) μ) (q : ℝ) :
    μ (liminfGE (fun n ω => f n ω / n) q) = 0
      ∨ μ (liminfGE (fun n ω => f n ω / n) q) = 1 :=
  measure_liminfGE_eq_zero_or_one' hσ (fun n => (hf.1 n).div_const _) q
    (hf.liminfGE_le_preimage μ σ hσ f hint q)

/-!
### Steele's good and bad sets

Fix a threshold `c` (in Steele's argument `c = G_M + ε`, where `G_M = max(-M, g)` truncates the
a.e.-constant `g = liminf f_n/n`). A point is *good* if some short block already achieves the
threshold, *bad* otherwise:

  `bad = {x | ∀ l, 1 ≤ l ≤ N → c·l < f_l x}`.

The greedy decomposition of `[0, n)` takes a good block wherever it can and a singleton at bad
positions, so what controls the error is the *density of bad times along the orbit* — and that is
Birkhoff applied to the indicator of `bad`.
-/

/-- Steele's bad set at scale `N` and threshold `c`: no block of length `≤ N` achieves `c`. -/
def SubadditiveFamily.badSet (f : ℕ → Ω → ℝ) (N : ℕ) (c : ℝ) : Set Ω :=
  {x | ∀ l : ℕ, 1 ≤ l → l ≤ N → c * l < f l x}

theorem SubadditiveFamily.measurableSet_badSet {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N : ℕ) (c : ℝ) :
    MeasurableSet (SubadditiveFamily.badSet f N c) := by
  have hrw : SubadditiveFamily.badSet f N c
      = ⋂ l ∈ Finset.Icc 1 N, {x | c * l < f l x} := by
    ext x
    simp only [SubadditiveFamily.badSet, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_Icc]
    exact ⟨fun h l hl => h l hl.1 hl.2, fun h l h1 h2 => h l ⟨h1, h2⟩⟩
  rw [hrw]
  exact MeasurableSet.biInter (Finset.countable_toSet _)
    (fun l _ => measurableSet_lt measurable_const (hf.1 l))

/-- **Density of bad times.** By Birkhoff applied to the indicator of the bad set, the fraction
of `k < n` with `σᵏx` bad converges a.e. to `μ(bad)`.

This is Steele's density-of-good-times step, and the ingredient that makes the greedy decomposition
pay: the good blocks cover all but a `μ(bad)` fraction of `[0, n)`,
up to the `N` positions at the end. -/
theorem SubadditiveFamily.ae_tendsto_badSet_density (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (N : ℕ) (c : ℝ) :
    ∀ᵐ x ∂μ, Tendsto
      (fun n : ℕ => birkhoffAverage ℝ σ (Set.indicator (SubadditiveFamily.badSet f N c) 1) n x)
      atTop (nhds (μ.real (SubadditiveFamily.badSet f N c))) := by
  have hmeas := hf.measurableSet_badSet N c
  have hind : Measurable (Set.indicator (SubadditiveFamily.badSet f N c) (1 : Ω → ℝ)) :=
    (measurable_one).indicator hmeas
  have hintg : Integrable (Set.indicator (SubadditiveFamily.badSet f N c) (1 : Ω → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hmeas
  have hval : ∫ x, Set.indicator (SubadditiveFamily.badSet f N c) (1 : Ω → ℝ) x ∂μ
      = μ.real (SubadditiveFamily.badSet f N c) := by
    rw [integral_indicator hmeas]
    simp
  have := ae_tendsto_birkhoffAverage_of_ergodic hσ
    (Set.indicator (SubadditiveFamily.badSet f N c) (1 : Ω → ℝ)) hind hintg
  rwa [hval] at this


/-- **A sub-invariant measurable function on an ergodic system is a.e. constant.**

Only `h ≤ h ∘ σ` is assumed, not equality: on a probability-preserving `σ` the two are the same
thing, because `{h > q} ⊆ σ⁻¹{h > q}` between sets of equal measure forces equality up to null
sets. This is the form the cocycle produces — `χ_k(ω) ≤ χ_k(σω)` comes from
`ρ_k(𝓛^{(n+1)}_ω) ≤ ρ_k(𝓛^{(n)}_{σω})‖𝓛_ω‖`, and the reverse inequality is *not* available for
a non-invertible `𝓛_ω`.

`EReal`-valued, since `χ_k` genuinely takes the value `⊥` for finite-rank cocycles. -/
theorem exists_ae_const_of_le_comp {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {h : Ω → EReal} (hm : Measurable h) (hle : ∀ ω, h ω ≤ h (σ ω)) :
    ∃ c : EReal, ∀ᵐ ω ∂μ, h ω = c := by
  classical
  set S : ℚ → Set Ω := fun q => h ⁻¹' Set.Ioi (((q : ℝ) : EReal)) with hS
  have hSm : ∀ q, MeasurableSet (S q) := fun q => hm measurableSet_Ioi
  have hsub : ∀ q, S q ⊆ σ ⁻¹' S q := fun q ω hω => lt_of_lt_of_le hω (hle ω)
  have hzo : ∀ q, μ (S q) = 0 ∨ μ (S q) = 1 := by
    intro q
    rcases hσ.ae_empty_or_univ_of_ae_le_preimage
        (MeasurableSet.nullMeasurableSet (hSm q)) (LE.le.eventuallyLE (hsub q)) with hq | hq
    · exact Or.inl (by rw [measure_congr hq, measure_empty])
    · exact Or.inr (by rw [measure_congr hq, measure_univ])
  -- off a null set, membership of `S q` is decided by `μ (S q)` alone
  have hBex : ∀ q : ℚ, ∃ E : Set Ω, μ E = 0 ∧ ∀ ω ∉ E, (ω ∈ S q ↔ μ (S q) ≠ 0) := by
    intro q
    by_cases hq : μ (S q) = 0
    · exact ⟨S q, hq, fun ω hω => by simp [hq, hω]⟩
    · refine ⟨(S q)ᶜ, ?_, fun ω hω => ?_⟩
      · have h1 : μ (S q) = 1 := (hzo q).resolve_left hq
        rw [measure_compl (hSm q) (measure_ne_top μ _), h1, measure_univ, tsub_self]
      · simp only [Set.mem_compl_iff, not_not] at hω
        simp [hω, hq]
  choose E hEnull hEiff using hBex
  set N : Set Ω := ⋃ q : ℚ, E q with hN
  have hNnull : μ N = 0 := measure_iUnion_null hEnull
  have hnot : ∀ ω ∉ N, ∀ q : ℚ, ω ∉ E q := fun ω hω q hc => hω (Set.mem_iUnion.2 ⟨q, hc⟩)
  have hkey : ∀ ω ∉ N, ∀ ω' ∉ N, h ω = h ω' := by
    intro ω hω ω' hω'
    have hiff : ∀ q : ℚ, (ω ∈ S q ↔ ω' ∈ S q) := fun q =>
      (hEiff q ω (hnot ω hω q)).trans (hEiff q ω' (hnot ω' hω' q)).symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
      exact absurd ((hiff q).2 hq2) (not_lt.2 hq1.le)
    · obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
      exact absurd ((hiff q).1 hq2) (not_lt.2 hq1.le)
  have hNne : ∃ ω₀, ω₀ ∉ N := by
    by_contra hcon
    rw [not_exists] at hcon
    have hu : N = Set.univ := Set.eq_univ_of_forall fun ω => not_not.1 (hcon ω)
    rw [hu, measure_univ] at hNnull
    exact one_ne_zero hNnull
  obtain ⟨ω₀, hω₀⟩ := hNne
  refine ⟨h ω₀, ?_⟩
  have hae : ∀ᵐ ω ∂μ, ω ∉ N := by
    rw [ae_iff]
    simpa using hNnull
  filter_upwards [hae] with ω hω
  exact hkey ω hω ω₀ hω₀

end MultiplicativeErgodic
