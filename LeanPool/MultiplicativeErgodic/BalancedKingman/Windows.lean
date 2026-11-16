/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.BalancedKingman.Vitali
public import LeanPool.MultiplicativeErgodic.MeasurableSelection
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Ingredients for the covering argument

The Vitali window endpoints `Λ₋`, `Λ₊`, their measurability, and the counting estimates that
bound `μ Λ₊` once every window radius is forced to be large.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-!
## Ingredients for the covering argument of `balancedKingman_of_integrable`

Three self-contained pieces the paper's `liminf ≥ C` argument (`proof_met.tex` lines 517-612)
needs before any of the covering combinatorics starts. They are stated separately because none
of them is specific to subadditive families.
-/

/-- **Absolute continuity of the integral.** For an `L¹` function `g` and `ε > 0` there is a
`δ > 0` such that `∫_s |g| ≤ ε` on every measurable `s` with `μ s ≤ δ`.

This is the paper's "since `f` is integrable, it is uniformly integrable and so there exists a
`δ > 0` such that if `P(A) < δ` then `∫_A f < ε`" — the step that lets the gaps left by the
Vitali cover contribute arbitrarily little. Mathlib states it as uniform integrability of the
one-element family (`unifIntegrable_const` at `p = 1`); the work here is unwinding `eLpNorm` into
a Bochner set-integral. -/
theorem exists_delta_setIntegral_abs_le {μ : Measure Ω} (g : Ω → ℝ) (hg : Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set Ω, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
      ∫ ω in s, |g ω| ∂μ ≤ ε := by
  have hmem : MemLp g 1 μ := memLp_one_iff_integrable.mpr hg
  obtain ⟨δ, hδ, h⟩ := hmem.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top
    (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨d, hd, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ δ := by
    by_cases htop : δ = ∞
    · exact ⟨1, zero_lt_one, by simp [htop]⟩
    · exact ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' htop,
        (ENNReal.ofReal_toReal htop).le⟩
  refine ⟨d, hd, fun s hs hμs => ?_⟩
  have hkey := h s hs.nullMeasurableSet (hμs.trans hdδ)
  rw [eLpNorm_one_eq_lintegral_enorm (hg.aestronglyMeasurable.indicator hs)] at hkey
  have h1 : ∫ ω in s, |g ω| ∂μ = ∫ ω, ‖s.indicator g ω‖ ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    funext ω
    by_cases hω : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  rw [h1, integral_norm_eq_lintegral_enorm (hg.aestronglyMeasurable.indicator hs)]
  calc (∫⁻ ω, ‖s.indicator g ω‖ₑ ∂μ).toReal
      ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono (by simp) hkey
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- The first forward time at which the orbit of `ω` meets `Λ` (junk value `0` if it never does).

This is the paper's `r₋`/`r₊`, which locate the start and end of the next interval of guaranteed
slow growth along the orbit. -/
noncomputable def hitTime (σ : Ω → Ω) (Λ : Set Ω) (ω : Ω) : ℕ := sInf {n : ℕ | σ^[n] ω ∈ Λ}

omit [MeasurableSpace Ω] in
theorem hitTime_spec {σ : Ω → Ω} {Λ : Set Ω} {ω : Ω} (h : ∃ n, σ^[n] ω ∈ Λ) :
    σ^[hitTime σ Λ ω] ω ∈ Λ :=
  Nat.sInf_mem h

omit [MeasurableSpace Ω] in
theorem hitTime_min {σ : Ω → Ω} {Λ : Set Ω} {ω : Ω} {k : ℕ} (hk : σ^[k] ω ∈ Λ) :
    hitTime σ Λ ω ≤ k :=
  Nat.sInf_le hk

omit [MeasurableSpace Ω] in
theorem hitTime_eq_zero_of_forall {σ : Ω → Ω} {Λ : Set Ω} {ω : Ω}
    (h : ∀ k : ℕ, σ^[k] ω ∉ Λ) : hitTime σ Λ ω = 0 := by
  change sInf {m : ℕ | σ^[m] ω ∈ Λ} = 0
  have hempty : {m : ℕ | σ^[m] ω ∈ Λ} = ∅ := by ext m; simpa using h m
  rw [hempty]
  simp

/-- The hitting time is measurable: `{hitTime = n}` is `{σⁿ ∈ Λ} ∩ ⋂_{k<n} {σᵏ ∉ Λ}` for `n ≥ 1`,
and for `n = 0` picks up the extra piece `⋂_k {σᵏ ∉ Λ}` where the junk value is returned. -/
theorem measurable_hitTime {σ : Ω → Ω} (hσm : Measurable σ) {Λ : Set Ω} (hΛ : MeasurableSet Λ) :
    Measurable (hitTime σ Λ) := by
  classical
  refine measurable_to_countable' (fun n => ?_)
  have hpre : ∀ k : ℕ, MeasurableSet ((σ^[k]) ⁻¹' Λ) := fun k => hΛ.preimage (hσm.iterate k)
  have hNm : MeasurableSet (⋂ k : ℕ, ((σ^[k]) ⁻¹' Λ)ᶜ) :=
    MeasurableSet.iInter fun k => (hpre k).compl
  have hGm : MeasurableSet
      (((σ^[n]) ⁻¹' Λ) ∩ ⋂ k : ℕ, ⋂ _ : k < n, ((σ^[k]) ⁻¹' Λ)ᶜ) :=
    (hpre n).inter (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hpre k).compl)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hchar : (hitTime σ Λ) ⁻¹' {0} = ((σ^[0]) ⁻¹' Λ) ∪ ⋂ k : ℕ, ((σ^[k]) ⁻¹' Λ)ᶜ := by
      ext ω
      constructor
      · intro h
        have h' : hitTime σ Λ ω = 0 := h
        by_cases hex : ∃ k, σ^[k] ω ∈ Λ
        · refine Or.inl ?_
          have hs := hitTime_spec hex
          rw [h'] at hs
          exact hs
        · refine Or.inr ?_
          simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
          exact not_exists.mp hex
      · intro h
        change hitTime σ Λ ω = 0
        rcases h with h | h
        · exact Nat.le_antisymm (hitTime_min h) (Nat.zero_le _)
        · simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage] at h
          exact hitTime_eq_zero_of_forall h
    rw [hchar]
    exact (hpre 0).union hNm
  · have hchar : (hitTime σ Λ) ⁻¹' {n}
        = ((σ^[n]) ⁻¹' Λ) ∩ ⋂ k : ℕ, ⋂ _ : k < n, ((σ^[k]) ⁻¹' Λ)ᶜ := by
      ext ω
      constructor
      · intro h
        have h' : hitTime σ Λ ω = n := h
        have hex : ∃ k, σ^[k] ω ∈ Λ := by
          by_contra hc
          rw [hitTime_eq_zero_of_forall (not_exists.mp hc)] at h'
          omega
        refine ⟨?_, ?_⟩
        · have hs := hitTime_spec hex
          rw [h'] at hs
          exact hs
        · simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
          intro k hk hmem
          exact absurd (hitTime_min hmem) (by rw [h']; omega)
      · rintro ⟨hmem, hmin⟩
        simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage] at hmin
        have hmem' : σ^[n] ω ∈ Λ := hmem
        change hitTime σ Λ ω = n
        refine le_antisymm (hitTime_min hmem') ?_
        by_contra hc
        rw [not_le] at hc
        exact hmin _ hc (hitTime_spec ⟨n, hmem'⟩)
    rw [hchar]
    exact hGm

/-- **Recurrence from ergodicity.** If `μ Λ ≠ 0` then a.e. orbit meets `Λ`.

The never-hitting set `N = ⋂ₙ σ⁻ⁿ(Λᶜ)` satisfies `N ⊆ σ⁻¹N`, so ergodicity makes it null or
conull; conull is impossible because `N` is disjoint from `Λ` (take `n = 0`). This is what makes
the paper's `r₋`, `r₊` "almost surely finite since `P(Λ_±) = P(A) > 0`". -/
theorem ae_exists_mem_iterate {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {Λ : Set Ω} (hΛm : MeasurableSet Λ) (hΛ : μ Λ ≠ 0) :
    ∀ᵐ ω ∂μ, ∃ n : ℕ, σ^[n] ω ∈ Λ := by
  set N : Set Ω := {ω | ∀ n : ℕ, σ^[n] ω ∉ Λ} with hN
  have hNeq : N = ⋂ n : ℕ, (σ^[n]) ⁻¹' Λᶜ := by
    ext ω; simp [hN, Set.mem_iInter]
  have hNm : MeasurableSet N := by
    rw [hNeq]
    exact MeasurableSet.iInter (fun n =>
      (hΛm.compl).preimage (hσ.toMeasurePreserving.measurable.iterate n))
  have hsub : (N : Set Ω) ≤ᵐ[μ] σ ⁻¹' N := by
    filter_upwards with ω hω
    intro n
    have := hω (n + 1)
    rwa [Function.iterate_succ_apply] at this
  rcases hσ.ae_empty_or_univ_of_ae_le_preimage hNm.nullMeasurableSet hsub with h | h
  · rw [ae_iff]
    have hset : {ω | ¬ ∃ n : ℕ, σ^[n] ω ∈ Λ} = N := by ext ω; simp [hN]
    rw [hset, measure_congr h, measure_empty]
  · exfalso
    refine hΛ ?_
    have hNfull : μ N = 1 := by rw [measure_congr h, measure_univ]
    have hsub2 : Λ ⊆ Nᶜ := fun x hx hxN => hxN 0 (by simpa using hx)
    have hle : μ Λ ≤ μ Nᶜ := measure_mono hsub2
    rw [measure_compl hNm (measure_ne_top μ _), hNfull, measure_univ, tsub_self] at hle
    exact nonpos_iff_eq_zero.mp hle

/-- **The cutoff estimate.** `μ{r ≥ N} → 0`, which is what lets the paper choose an `N` with
`P(r_± ≥ N) < ε/4`.

The sets `{N ≤ r}` are antitone with empty intersection — `hitTime` is `ℕ`-valued, so it is finite
at every point (the junk value `0` where the orbit never meets `Λ` sits *below* every `N ≥ 1`,
not above it) — so continuity from above applies. -/
theorem tendsto_measure_hitTime_ge (μ : Measure Ω) [IsFiniteMeasure μ] {σ : Ω → Ω}
    (hσm : Measurable σ) {Λ : Set Ω} (hΛ : MeasurableSet Λ) :
    Tendsto (fun N : ℕ => μ {ω | N ≤ hitTime σ Λ ω}) atTop (nhds 0) := by
  have hmeas : ∀ N : ℕ, NullMeasurableSet {ω | N ≤ hitTime σ Λ ω} μ := fun N =>
    ((measurable_hitTime hσm hΛ) measurableSet_Ici).nullMeasurableSet
  have hanti : Antitone (fun N : ℕ => {ω | N ≤ hitTime σ Λ ω}) := by
    intro a b hab ω hω
    exact le_trans hab hω
  have hempty : (⋂ N : ℕ, {ω | N ≤ hitTime σ Λ ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    refine ⟨hitTime σ Λ ω + 1, ?_⟩
    simp only [Set.mem_ofPred_eq, not_le]
    omega
  have h := tendsto_measure_iInter_atTop (μ := μ) hmeas hanti ⟨0, measure_ne_top μ _⟩
  rwa [hempty, measure_empty] at h

/-- The combined form the covering argument uses: when `Λ` is not null, a.e. `ω` really is sent
into `Λ` by its own hitting time. -/
theorem ae_mem_iterate_hitTime {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : Ω → Ω}
    (hσ : Ergodic σ μ) {Λ : Set Ω} (hΛm : MeasurableSet Λ) (hΛ : μ Λ ≠ 0) :
    ∀ᵐ ω ∂μ, σ^[hitTime σ Λ ω] ω ∈ Λ := by
  filter_upwards [ae_exists_mem_iterate hσ hΛm hΛ] with ω hω
  exact hitTime_spec hω

/-!
### The Vitali window endpoints `Λ₋`, `Λ₊`

`backwardVitali` hands back centres `A` and radii `jω`; the paper's `Λ_±` are the images of `A`
under the two endpoint maps. Their measurability is Lusin-Souslin (an injective measurable image
of a Borel set in a standard Borel space is Borel), with injectivity coming from disjointness of
the windows -- each endpoint lies in its own window. This is the second place
`[StandardBorelSpace Ω]` earns its keep, after `backwardVitali` itself.
-/

/-- Evaluating a `ℕ`-indexed measurable family at a measurable index stays measurable.

Used repeatedly: the greedy walk, the hitting times, and the window endpoints all have the shape
`ω ↦ g (k ω) ω` with `k` measurable and `ℕ`-valued. -/
theorem measurable_natIndex {β : Type*} [MeasurableSpace β] {k : Ω → ℕ} (hk : Measurable k)
    {g : ℕ → Ω → β} (hg : ∀ m, Measurable (g m)) : Measurable (fun ω => g (k ω) ω) :=
  measurable_glue hk hg

/-- The left and right endpoints of the Vitali windows, as maps. -/
noncomputable def leftEnd (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (ω : Ω) : Ω := zIter σ (-(jω ω : ℤ)) ω
/-- The right endpoint of a variable-radius orbit window. -/
noncomputable def rightEnd (σ : Ω ≃ᵐ Ω) (jω : Ω → ℕ) (ω : Ω) : Ω := zIter σ ((jω ω : ℤ)) ω

theorem measurable_leftEnd {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} (hj : Measurable jω) :
    Measurable (leftEnd σ jω) := by
  have : leftEnd σ jω = fun ω => (fun m ω => (σ.symm : Ω → Ω)^[m] ω) (jω ω) ω := by
    funext ω; rw [leftEnd, zIter_neg_natCast]
  rw [this]
  exact measurable_natIndex hj (fun m => σ.symm.measurable.iterate m)

theorem measurable_rightEnd {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} (hj : Measurable jω) :
    Measurable (rightEnd σ jω) := by
  have : rightEnd σ jω = fun ω => (fun m ω => (σ : Ω → Ω)^[m] ω) (jω ω) ω := by
    funext ω; rw [rightEnd, zIter_natCast]
  rw [this]
  exact measurable_natIndex hj (fun m => σ.measurable.iterate m)

section Endpoints
variable [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- Disjointness of the windows makes each endpoint map injective on `A`: the endpoint lies in
its own window, and distinct centres have disjoint windows. -/
theorem injOn_leftEnd {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hdisj : A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) :
    Set.InjOn (leftEnd σ jω) A := by
  intro x hx y hy hxy
  by_contra hne
  have hmemx : leftEnd σ jω x ∈ (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x) :=
    ⟨-(jω x : ℤ), ⟨le_refl _, by omega⟩, rfl⟩
  have hmemy : leftEnd σ jω x ∈ (fun i => zIter σ i y) '' Set.Icc (-(jω y : ℤ)) (jω y) := by
    rw [hxy]; exact ⟨-(jω y : ℤ), ⟨le_refl _, by omega⟩, rfl⟩
  exact Set.disjoint_left.mp (hdisj hx hy hne) hmemx hmemy

omit [StandardBorelSpace Ω] in
theorem injOn_rightEnd {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hdisj : A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) :
    Set.InjOn (rightEnd σ jω) A := by
  intro x hx y hy hxy
  by_contra hne
  have hmemx : rightEnd σ jω x ∈ (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x) :=
    ⟨(jω x : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
  have hmemy : rightEnd σ jω x ∈ (fun i => zIter σ i y) '' Set.Icc (-(jω y : ℤ)) (jω y) := by
    rw [hxy]; exact ⟨(jω y : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
  exact Set.disjoint_left.mp (hdisj hx hy hne) hmemx hmemy

/-- **`Λ₋` and `Λ₊` are measurable.** Lusin-Souslin: an injective measurable image of a Borel
set in a standard Borel space is Borel. This is the step the `[StandardBorelSpace Ω]` hypothesis
is actually for, beyond its role inside `backwardVitali`. -/
theorem measurableSet_leftEnd_image {σ : Ω ≃ᵐ Ω} {A : Set Ω} (hA : MeasurableSet A)
    {jω : Ω → ℕ} (hj : Measurable jω)
    (hdisj : A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) :
    MeasurableSet (leftEnd σ jω '' A) :=
  hA.image_of_measurable_injOn (measurable_leftEnd hj) (injOn_leftEnd hdisj)

theorem measurableSet_rightEnd_image {σ : Ω ≃ᵐ Ω} {A : Set Ω} (hA : MeasurableSet A)
    {jω : Ω → ℕ} (hj : Measurable jω)
    (hdisj : A.PairwiseDisjoint fun ω => (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) :
    MeasurableSet (rightEnd σ jω '' A) :=
  hA.image_of_measurable_injOn (measurable_rightEnd hj) (injOn_rightEnd hdisj)

end Endpoints

/-- A forward step from the left endpoint, in `zIter` coordinates. -/
theorem iterate_leftEnd {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} (k : ℕ) (ω : Ω) :
    (σ : Ω → Ω)^[k] (leftEnd σ jω ω) = zIter σ ((k : ℤ) - jω ω) ω := by
  rw [leftEnd, ← zIter_natCast σ k, ← zIter_add]
  congr 1

/-- Walking `2j` steps forward from the left endpoint lands exactly on the right endpoint. -/
theorem iterate_leftEnd_eq_rightEnd {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} (ω : Ω) :
    (σ : Ω → Ω)^[2 * jω ω] (leftEnd σ jω ω) = rightEnd σ jω ω := by
  rw [iterate_leftEnd, rightEnd]
  congr 1
  omega

/-- Every forward step of length `≤ 2j` from the left endpoint stays inside the window. -/
theorem iterate_leftEnd_mem_window {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} {k : ℕ} (ω : Ω)
    (hk : k ≤ 2 * jω ω) :
    (σ : Ω → Ω)^[k] (leftEnd σ jω ω)
      ∈ (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω) := by
  rw [iterate_leftEnd]
  exact ⟨(k : ℤ) - jω ω, ⟨by omega, by omega⟩, rfl⟩

/-- **The good block has length exactly `2j`.** From a left endpoint, the first forward return to
`Λ₊` is the matching right endpoint.

Two ingredients. Disjointness of the windows means no *other* window's right endpoint can lie in
this one, so an earlier return would have to be this window's own right endpoint; and injectivity
of the orbit then rules that out, since the right endpoint sits at coordinate `+j` and an earlier
return would put it at some `k - j < j`.

`hinj` holds almost everywhere: a point whose orbit is not injective is periodic, and
`periodic_null` shows the periodic points are null under ergodicity plus non-atomicity. -/
theorem hitTime_rightEnd_image {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω} (hωA : ω ∈ A)
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : Function.Injective fun i : ℤ => zIter σ i ω) :
    hitTime (σ : Ω → Ω) (rightEnd σ jω '' A) (leftEnd σ jω ω) = 2 * jω ω := by
  have hex : ∃ n, (σ : Ω → Ω)^[n] (leftEnd σ jω ω) ∈ rightEnd σ jω '' A :=
    ⟨2 * jω ω, by rw [iterate_leftEnd_eq_rightEnd]; exact ⟨ω, hωA, rfl⟩⟩
  refine le_antisymm (hitTime_min (by rw [iterate_leftEnd_eq_rightEnd]; exact ⟨ω, hωA, rfl⟩)) ?_
  by_contra hc
  rw [not_le] at hc
  obtain ⟨ω', hω'A, hω'eq⟩ := hitTime_spec hex
  -- the early return lies in this window ...
  have hin : (σ : Ω → Ω)^[hitTime (σ : Ω → Ω) (rightEnd σ jω '' A) (leftEnd σ jω ω)]
      (leftEnd σ jω ω) ∈ (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω) :=
    iterate_leftEnd_mem_window ω (by omega)
  -- ... and in `ω'`'s window, so the two windows meet and `ω' = ω`
  have hin' : (σ : Ω → Ω)^[hitTime (σ : Ω → Ω) (rightEnd σ jω '' A) (leftEnd σ jω ω)]
      (leftEnd σ jω ω) ∈ (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
    rw [← hω'eq, rightEnd]
    exact ⟨(jω ω' : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
  have hωω' : ω = ω' := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hωA hω'A hne) hin hin'
  subst hωω'
  rw [iterate_leftEnd, rightEnd] at hω'eq
  have hcoord := hinj hω'eq
  omega

/-- **Windows over a null set of centres are null.**

The point of this: `exists_good_windows` delivers goodness of the centres only *almost*
everywhere, but the covering argument meets `Λ₋` points along an orbit and needs goodness at
*every* one it meets. The fix is to shrink the centre set `A` to `A ∩ G` for a conull `G`, and
this lemma says that costs no coverage — each window is a finite set of orbit translates, so the
discarded part is contained in a countable union of translates of a null set. -/
theorem measure_iUnion_windows_of_null {μ : Measure Ω} (σ : Ω ≃ᵐ Ω) (hmp : MeasurePreserving
  (⇑σ) μ μ)
    {S : Set Ω} (hSm : MeasurableSet S) (hS : μ S = 0) (jω : Ω → ℕ) :
    μ (⋃ ω ∈ S, (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω)) = 0 := by
  refine measure_mono_null (fun x hx => ?_)
    (measure_iUnion_null (fun t : ℤ => by
      rw [measure_zIter_image σ hmp t hSm]; exact hS))
  obtain ⟨ω, hωS, hxω⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨i, -, hix⟩ := hxω
  exact Set.mem_iUnion.mpr ⟨i, ⟨ω, hωS, hix⟩⟩

/-- **The good-block value bound.** At a `Λ₋` point, the block that runs to the next `Λ₊` point
has `f` at most `q` times its length.

Stated with *pointwise* hypotheses on `A` rather than a.e. ones, deliberately: the walk meets
`Λ₋` points along an orbit and needs the bound at every one of them, not almost all. The caller
supplies this by shrinking `A` to its intersection with the conull set where
`exists_good_windows`' goodness and `ae_injective_zIter` both hold — which costs no coverage, by
`measure_iUnion_windows_of_null`. -/
theorem good_block_value {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {f : ℕ → Ω → ℝ} {q : ℝ}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hgood : ∀ ω ∈ A, 1 ≤ jω ω ∧ f (2 * jω ω) (zIter σ (-(jω ω : ℤ)) ω) < 2 * (jω ω) * q)
    (hinj : ∀ ω ∈ A, Function.Injective fun i : ℤ => zIter σ i ω)
    {x : Ω} (hx : x ∈ leftEnd σ jω '' A) :
    f (hitTime (σ : Ω → Ω) (rightEnd σ jω '' A) x) x
      ≤ q * (hitTime (σ : Ω → Ω) (rightEnd σ jω '' A) x : ℝ) := by
  obtain ⟨ω, hωA, rfl⟩ := hx
  rw [hitTime_rightEnd_image hωA hdisj (hinj ω hωA)]
  obtain ⟨-, hgq⟩ := hgood ω hωA
  change f (2 * jω ω) (zIter σ (-(jω ω : ℤ)) ω) ≤ q * ((2 * jω ω : ℕ) : ℝ)
  have hcast : (q : ℝ) * ((2 * jω ω : ℕ) : ℝ) = 2 * ((jω ω : ℕ) : ℝ) * q := by push_cast; ring
  rw [hcast]
  exact le_of_lt hgq

/-- The left and right endpoint sets are disjoint, given that every radius is positive: a common
point would force one window to meet another, hence to *be* the other, and then injectivity of
the orbit would give `-j = j`. This is what makes the first `Λ₊` hit from a `Λ₋` point strictly
positive, so the walk actually advances. -/
theorem disjoint_leftEnd_rightEnd {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hpos : ∀ ω ∈ A, 1 ≤ jω ω)
    (hinj : ∀ ω ∈ A, Function.Injective fun i : ℤ => zIter σ i ω) :
    Disjoint (leftEnd σ jω '' A) (rightEnd σ jω '' A) := by
  rw [Set.disjoint_left]
  rintro x ⟨ω, hωA, rfl⟩ ⟨ω', hω'A, hx'⟩
  have hin : leftEnd σ jω ω ∈ (fun i => zIter σ i ω) '' Set.Icc (-(jω ω : ℤ)) (jω ω) :=
    ⟨-(jω ω : ℤ), ⟨le_refl _, by omega⟩, rfl⟩
  have hin' : leftEnd σ jω ω ∈ (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
    rw [← hx', rightEnd]
    exact ⟨(jω ω' : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
  have hωω' : ω = ω' := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hωA hω'A hne) hin hin'
  subst hωω'
  rw [leftEnd, rightEnd] at hx'
  have := hinj ω hωA hx'
  have := hpos ω hωA
  omega

/-- **Covered means "forward-reachable from a left endpoint within `2j` steps".**

The windows are stated as two-sided `zIter` images, which is awkward to reason with along a
forward orbit. This recasts membership in purely forward terms, and is what lets the gap argument
locate the left endpoint of an offending window by *inverting `σ`* rather than by tracking signed
orbit positions. -/
theorem mem_iUnion_windows_iff {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {x : Ω} :
    x ∈ (⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω'))
      ↔ ∃ ω' ∈ A, ∃ m : ℕ, m ≤ 2 * jω ω' ∧ (σ : Ω → Ω)^[m] (leftEnd σ jω ω') = x := by
  constructor
  · intro hx
    obtain ⟨ω', hω'A, hmem⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨t, ht, htx⟩ := hmem
    refine ⟨ω', hω'A, (t + (jω ω' : ℤ)).toNat, ?_, ?_⟩
    · have h1 : t ≤ (jω ω' : ℤ) := ht.2
      omega
    · rw [iterate_leftEnd]
      have hcast : (((t + (jω ω' : ℤ)).toNat : ℤ)) = t + (jω ω' : ℤ) := by
        have : -(jω ω' : ℤ) ≤ t := ht.1
        omega
      rw [hcast, show t + (jω ω' : ℤ) - (jω ω' : ℤ) = t from by ring]
      exact htx
  · rintro ⟨ω', hω'A, m, hm, hmx⟩
    refine Set.mem_iUnion₂.mpr ⟨ω', hω'A, ?_⟩
    rw [iterate_leftEnd] at hmx
    exact ⟨(m : ℤ) - jω ω', ⟨by omega, by omega⟩, hmx⟩

/-- If a covered point sits at forward time `k` from `ω`, and the covering window's left endpoint
is not itself in the future of `ω`, then that left endpoint is at forward time `k - m`.

Only injectivity of `σ` is needed here — not injectivity of the whole orbit — because we invert
`σ^m` directly rather than comparing signed positions. -/
theorem leftEnd_at_earlier_time {σ : Ω ≃ᵐ Ω} {jω : Ω → ℕ} {ω ω' : Ω} {k m : ℕ}
    (hmk : m ≤ k) (h : (σ : Ω → Ω)^[m] (leftEnd σ jω ω') = (σ : Ω → Ω)^[k] ω) :
    leftEnd σ jω ω' = (σ : Ω → Ω)^[k - m] ω := by
  have hinjσ : Function.Injective ((σ : Ω → Ω)^[m]) := by
    have : Function.Injective (σ : Ω → Ω) := σ.injective
    exact Function.Injective.iterate this m
  refine hinjσ ?_
  rw [h, ← Function.iterate_add_apply]
  congr 1
  omega

/-- **Gap interiors are uncovered.** Strictly between a right endpoint at time `b` and the next
`Λ₋` hit, nothing lies in any window.

Note the strictness `b < k`: time `b` itself *is* covered — it is the right endpoint of its own
window — which is exactly the off-by-one the paper's `1_B` bound glosses over. The two cases below
are "the offending window opened at or before `b`" (then `σ^b ω` lies in it, so by disjointness it
*is* that window, forcing its offset to be `2j` and hence `m > 2j`, absurd) and "it opened after
`b`" (then its left endpoint is a `Λ₋` point strictly between `b` and `k`, contradicting
minimality of the hitting time). -/
theorem not_covered_of_gap {σ : Ω ≃ᵐ Ω} {A : Set Ω} {jω : Ω → ℕ} {ω : Ω}
    (hdisj : A.PairwiseDisjoint fun x => (fun i => zIter σ i x) '' Set.Icc (-(jω x : ℤ)) (jω x))
    (hinj : ∀ ω' ∈ A, Function.Injective fun i : ℤ => zIter σ i ω')
    {b k : ℕ} (hb : (σ : Ω → Ω)^[b] ω ∈ rightEnd σ jω '' A) (hbk : b < k)
    (hk : k < b + hitTime (σ : Ω → Ω) (leftEnd σ jω '' A) ((σ : Ω → Ω)^[b] ω)) :
    (σ : Ω → Ω)^[k] ω ∉
      ⋃ ω' ∈ A, (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
  intro hcov
  obtain ⟨ω', hω'A, m, hm, hmx⟩ := mem_iUnion_windows_iff.mp hcov
  rcases le_or_gt (k - b) m with hcase | hcase
  · -- the offending window already covers time `b`
    have hdle : m - (k - b) ≤ 2 * jω ω' := by omega
    have hdeq : (σ : Ω → Ω)^[m - (k - b)] (leftEnd σ jω ω') = (σ : Ω → Ω)^[b] ω := by
      refine (σ.injective.iterate (k - b)) ?_
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show (k - b) + (m - (k - b)) = m from by omega, show (k - b) + b = k from by omega]
      exact hmx
    obtain ⟨ω'', hω''A, hω''⟩ := hb
    have hmem1 : (σ : Ω → Ω)^[b] ω ∈
        (fun i => zIter σ i ω') '' Set.Icc (-(jω ω' : ℤ)) (jω ω') := by
      rw [← hdeq, iterate_leftEnd]
      exact ⟨((m - (k - b) : ℕ) : ℤ) - jω ω', ⟨by omega, by omega⟩, rfl⟩
    have hmem2 : (σ : Ω → Ω)^[b] ω ∈
        (fun i => zIter σ i ω'') '' Set.Icc (-(jω ω'' : ℤ)) (jω ω'') := by
      rw [← hω'', rightEnd]
      exact ⟨(jω ω'' : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
    have hωω' : ω' = ω'' := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hω'A hω''A hne) hmem1 hmem2
    subst hωω'
    have hright : (σ : Ω → Ω)^[2 * jω ω'] (leftEnd σ jω ω') = (σ : Ω → Ω)^[b] ω := by
      rw [iterate_leftEnd_eq_rightEnd]; exact hω''
    have hcoord : ((m - (k - b) : ℕ) : ℤ) - jω ω' = ((2 * jω ω' : ℕ) : ℤ) - (jω ω' : ℤ) := by
      refine hinj ω' hω'A ?_
      change zIter σ (((m - (k - b) : ℕ) : ℤ) - jω ω') ω'
        = zIter σ (((2 * jω ω' : ℕ) : ℤ) - jω ω') ω'
      rw [← iterate_leftEnd, ← iterate_leftEnd, hdeq, hright]
    omega
  · -- the offending window opened strictly after `b`, contradicting minimality
    have hmk : m ≤ k := by omega
    have hleft : leftEnd σ jω ω' = (σ : Ω → Ω)^[k - m] ω := leftEnd_at_earlier_time hmk hmx
    have hmemΛ : (σ : Ω → Ω)^[(k - m) - b] ((σ : Ω → Ω)^[b] ω) ∈ leftEnd σ jω '' A := by
      rw [← Function.iterate_add_apply, show (k - m) - b + b = k - m from by omega, ← hleft]
      exact ⟨ω', hω'A, rfl⟩
    have hmin := hitTime_min hmemΛ
    omega

/-- **Almost every two-sided orbit is injective.** If the orbit of `ω` revisits itself then `ω`
is periodic, and `periodic_null` makes the periodic points null under ergodicity plus
non-atomicity. This is what discharges the `hinj` hypothesis of `hitTime_rightEnd_image`. -/
theorem ae_injective_zIter [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (σ : Ω ≃ᵐ Ω) (hσ : Ergodic (⇑σ) μ) :
    ∀ᵐ ω ∂μ, Function.Injective (fun i : ℤ => zIter σ i ω) := by
  classical
  have hnull : μ (⋃ N : ℕ, {x : Ω | σ^[N + 1] x = x}) = 0 :=
    measure_iUnion_null (fun N => periodic_null μ σ hσ (N := N + 1) (by omega))
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  -- a repeat in the orbit gives a period
  have key : ∀ a b : ℤ, a < b → zIter σ a ω = zIter σ b ω →
      ω ∈ ⋃ N : ℕ, {x : Ω | σ^[N + 1] x = x} := by
    intro a b hlt heq
    have h1 : zIter σ (b - a) ω = ω := by
      have h := congrArg (zIter σ (-a)) heq
      rw [← zIter_add, ← zIter_add] at h
      rw [show -a + a = (0 : ℤ) from by ring, zIter_zero_apply] at h
      rw [show -a + b = b - a from by ring] at h
      exact h.symm
    obtain ⟨M, hMeq⟩ : ∃ M : ℕ, (M : ℤ) = b - a :=
      ⟨(b - a).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    change σ^[N + 1] ω = ω
    rw [← zIter_natCast σ (N + 1) ω, hMeq]
    exact h1
  simp only [Set.mem_ofPred_eq] at hω
  rw [Function.not_injective_iff] at hω
  obtain ⟨a, b, heq, hne⟩ := hω
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

omit [MeasurableSpace Ω] in
/-- Peeling one step off a hitting time. The hit-existence hypothesis is not decoration: without
it both sides collapse to the junk value `0` and the identity fails. -/
theorem hitTime_succ {σ : Ω → Ω} {Λ : Set Ω} {x : Ω} (hex : ∃ n, σ^[n] x ∈ Λ) (hx : x ∉ Λ) :
    hitTime σ Λ x = hitTime σ Λ (σ x) + 1 := by
  have hmem : σ^[hitTime σ Λ x] x ∈ Λ := hitTime_spec hex
  have hpos : 1 ≤ hitTime σ Λ x := by
    rcases Nat.eq_zero_or_pos (hitTime σ Λ x) with h0 | h
    · rw [h0] at hmem; simp only [Function.iterate_zero, id_eq] at hmem; exact absurd hmem hx
    · exact h
  -- the shifted orbit also hits `Λ`
  have hex' : ∃ n, σ^[n] (σ x) ∈ Λ := by
    refine ⟨hitTime σ Λ x - 1, ?_⟩
    have hrw : σ^[hitTime σ Λ x - 1] (σ x) = σ^[hitTime σ Λ x] x := by
      rw [← Function.iterate_succ_apply]
      congr 1
      omega
    rw [hrw]; exact hmem
  refine le_antisymm ?_ ?_
  · -- `hitTime x ≤ hitTime (σ x) + 1`
    refine hitTime_min ?_
    rw [Function.iterate_succ_apply]
    exact hitTime_spec hex'
  · -- `hitTime (σ x) + 1 ≤ hitTime x`
    have hle : hitTime σ Λ (σ x) ≤ hitTime σ Λ x - 1 := by
      refine hitTime_min ?_
      have hrw : σ^[hitTime σ Λ x - 1] (σ x) = σ^[hitTime σ Λ x] x := by
        rw [← Function.iterate_succ_apply]
        congr 1
        omega
      rw [hrw]; exact hmem
    omega

end MultiplicativeErgodic
