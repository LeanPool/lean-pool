/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.FTAP.FTAP

/-!
# No arbitrage is local: multi-period versus conditional one-period

The reduction step of the Dalang–Morton–Willinger theorem. For an adapted `F`-valued discounted
price `S` on a filtered probability space `(Ω, 𝓕, P)` with finite horizon `T`, the multi-period
`NoArbitrage 𝓕 P S T` of `FTAP.lean` (no bounded predictable strategy turns zero wealth into a
sure nonnegative, non-null gain) holds if and only if every one-period market conditional on
`𝓕 t` is arbitrage free: no `𝓕 t`-measurable position `θ` has an a.s. nonnegative gain
`⟪θ, S (t+1) − S t⟫` that is not a.s. zero (`NoArbitrageLocal`).

* `NoArbitrage ⇒ NoArbitrageLocal` needs no adaptedness: the position `θ` is truncated to the
  bounded `θ 1_{‖θ‖ ≤ n}` and held over `(t, t+1]` only; the gain vanishes on every truncation,
  hence a.s.
* `NoArbitrageLocal ⇒ NoArbitrage` is an induction on the horizon. If `V_T + g ≥ 0` with
  `g = ⟪φ_{T+1}, S_{T+1} − S_T⟫` and `V_T` the (`𝓕 T`-measurable) gain so far, the position
  `φ_{T+1} 1_{V_T<0}` has gain `≥ 0`, so it is a.s. zero and `V_T ≥ 0` a.s.; the induction
  hypothesis gives `V_T = 0`, and then `g ≥ 0` forces `g = 0`.

This is the first half of the multi-period FTAP on a general space; the conditional one-period
FTAP (the measurable-selection step) is not proved here.

## Main definitions

* `NoArbitrageAt`: no arbitrage in the one-period market of period `t` conditional on `𝓕 t`.
* `NoArbitrageLocal`: `NoArbitrageAt` for every period `t < T`.
* `singleStrategy`: the strategy holding `θ` over the single period `(t, t+1]`.
* `truncation`: `θ 1_{‖θ‖ ≤ n}`.

## Main results

* `noArbitrageLocal_of_noArbitrage`: multi-period no arbitrage gives the local one.
* `noArbitrage_of_noArbitrageLocal`: the local one gives the multi-period one (adapted price).
* `noArbitrage_iff_noArbitrageLocal`: the equivalence.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

no arbitrage, conditional no arbitrage, one-period reduction, predictable strategy,
Dalang–Morton–Willinger, JEL G13, MSC 91G20, MSC 60G42
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **No arbitrage in the conditional one-period market of period `t`.** Every `𝓕 t`-measurable
position `θ` (unbounded allowed) whose one-period gain `⟪θ, S (t+1) − S t⟫` is `P`-a.s. nonnegative
has a `P`-a.s. zero gain. -/
def NoArbitrageAt (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (t : ℕ) : Prop :=
  ∀ θ : Ω → F, StronglyMeasurable[𝓕 t] θ →
    0 ≤ᵐ[P] (fun ω ↦ ⟪θ ω, S (t + 1) ω - S t ω⟫_ℝ) →
      (fun ω ↦ ⟪θ ω, S (t + 1) ω - S t ω⟫_ℝ) =ᵐ[P] 0

/-- **No arbitrage in each conditional one-period market** of the periods `t < T`. -/
def NoArbitrageLocal (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ) : Prop :=
  ∀ t < T, NoArbitrageAt 𝓕 P S t

/-- The strategy holding `θ` over the single period `(t, t+1]` and nothing else. -/
def singleStrategy (t : ℕ) (θ : Ω → F) : ℕ → Ω → F :=
  fun s ω ↦ if s = t + 1 then θ ω else 0

/-- The truncation `θ 1_{‖θ‖ ≤ n}` of a position. -/
noncomputable def truncation (n : ℕ) (θ : Ω → F) : Ω → F :=
  {ω | ‖θ ω‖ ≤ (n : ℝ)}.indicator θ

section Truncation

variable {θ : Ω → F} {n : ℕ} {ω : Ω}

omit [InnerProductSpace ℝ F] in
lemma truncation_of_le (h : ‖θ ω‖ ≤ (n : ℝ)) : truncation n θ ω = θ ω := by
  simp [truncation, h]

omit [InnerProductSpace ℝ F] in
lemma truncation_of_not_le (h : ¬ ‖θ ω‖ ≤ (n : ℝ)) : truncation n θ ω = 0 := by
  simp [truncation, h]

omit [InnerProductSpace ℝ F] in
lemma norm_truncation_le : ‖truncation n θ ω‖ ≤ (n : ℝ) := by
  by_cases h : ‖θ ω‖ ≤ (n : ℝ)
  · rw [truncation_of_le h]; exact h
  · rw [truncation_of_not_le h]; simp

omit [InnerProductSpace ℝ F] in
lemma stronglyMeasurable_truncation {m : MeasurableSpace Ω} (hθ : StronglyMeasurable[m] θ) :
    StronglyMeasurable[m] (truncation n θ) :=
  hθ.indicator (hθ.norm.measurable (measurableSet_Iic (a := (n : ℝ))))

end Truncation

section SingleStrategy

variable {t T : ℕ} {θ : Ω → F}

omit [InnerProductSpace ℝ F] in
lemma singleStrategy_self : singleStrategy t θ (t + 1) = θ := by
  funext ω; simp [singleStrategy]

omit [InnerProductSpace ℝ F] in
lemma singleStrategy_of_ne {u : ℕ} (h : u ≠ t) : singleStrategy t θ (u + 1) = 0 := by
  funext ω; simp [singleStrategy, h]

omit [InnerProductSpace ℝ F] in
lemma singleStrategy_predictable {𝓕 : Filtration ℕ m0} (hθ : StronglyMeasurable[𝓕 t] θ) :
    ∀ u < T, StronglyMeasurable[𝓕 u] (singleStrategy t θ (u + 1)) := by
  intro u _
  by_cases h : u = t
  · subst h
    rw [singleStrategy_self]
    exact hθ
  · rw [singleStrategy_of_ne h]
    exact stronglyMeasurable_zero

omit [InnerProductSpace ℝ F] in
lemma norm_singleStrategy_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, ‖θ ω‖ ≤ K) (s : ℕ) (ω : Ω) :
    ‖singleStrategy t θ s ω‖ ≤ K := by
  by_cases h : s = t + 1
  · simpa [singleStrategy, h] using hK ω
  · simpa [singleStrategy, h] using hK0

lemma martingaleTransform_singleStrategy (S : ℕ → Ω → F) (ht : t < T) :
    martingaleTransform (singleStrategy t θ) S T =
      fun ω ↦ ⟪θ ω, S (t + 1) ω - S t ω⟫_ℝ := by
  funext ω
  rw [martingaleTransform, Finset.sum_eq_single t]
  · simp [singleStrategy]
  · intro k _ hk
    simp [singleStrategy, hk]
  · intro h
    exact absurd (Finset.mem_range.2 ht) h

end SingleStrategy

variable {𝓕 : Filtration ℕ m0} {P : Measure Ω} {S : ℕ → Ω → F}

/-- **Multi-period no arbitrage gives conditional one-period no arbitrage.** A position `θ` with
a nonnegative gain is truncated to the bounded `θ 1_{‖θ‖ ≤ n}` and held over `(t, t+1]` only; the
resulting bounded predictable strategy has a nonnegative gain, so its gain vanishes; the gain of
`θ` vanishes on each `{‖θ‖ ≤ n}`, hence a.s. -/
theorem noArbitrageLocal_of_noArbitrage {T : ℕ} (hNA : NoArbitrage 𝓕 P S T) :
    NoArbitrageLocal 𝓕 P S T := by
  intro t ht θ hθ hpos
  have key (n : ℕ) :
      (fun ω ↦ ⟪truncation n θ ω, S (t + 1) ω - S t ω⟫_ℝ) =ᵐ[P] 0 := by
    have hpos' : 0 ≤ᵐ[P] martingaleTransform (singleStrategy t (truncation n θ)) S T := by
      rw [martingaleTransform_singleStrategy S ht]
      filter_upwards [hpos] with ω hω
      have hω' : 0 ≤ ⟪θ ω, S (t + 1) ω - S t ω⟫_ℝ := hω
      change 0 ≤ ⟪truncation n θ ω, S (t + 1) ω - S t ω⟫_ℝ
      by_cases h : ‖θ ω‖ ≤ (n : ℝ)
      · rw [truncation_of_le h]; exact hω'
      · rw [truncation_of_not_le h]; simp
    have hbdd : ∃ K : ℝ, ∀ s ≤ T, ∀ ω, ‖singleStrategy t (truncation n θ) s ω‖ ≤ K :=
      ⟨n, fun s _ ω ↦
        norm_singleStrategy_le (Nat.cast_nonneg n) (fun ω ↦ norm_truncation_le) s ω⟩
    have h := hNA (singleStrategy t (truncation n θ))
      (singleStrategy_predictable (stronglyMeasurable_truncation hθ)) hbdd hpos'
    rwa [martingaleTransform_singleStrategy S ht] at h
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ⟪truncation n θ ω, S (t + 1) ω - S t ω⟫_ℝ = 0 :=
    ae_all_iff.2 fun n ↦ key n
  filter_upwards [hall] with ω hω
  have h1 := hω ⌈‖θ ω‖⌉₊
  rw [truncation_of_le (θ := θ) (ω := ω) (Nat.le_ceil ‖θ ω‖)] at h1
  exact h1

/-- The gain process of a predictable strategy is adapted: `martingaleTransform φ S n` is
`𝓕 n`-measurable for `n ≤ T`, for an adapted price. -/
lemma stronglyMeasurable_martingaleTransform {T : ℕ}
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) {φ : ℕ → Ω → F}
    (hφ : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1))) :
    ∀ n ≤ T, StronglyMeasurable[𝓕 n] (martingaleTransform φ S n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [martingaleTransform_zero]
    exact stronglyMeasurable_zero
  | succ n ih =>
    intro hn
    have hnT : n < T := Nat.lt_of_succ_le hn
    have e : martingaleTransform φ S (n + 1) = martingaleTransform φ S n +
        fun ω ↦ ⟪φ (n + 1) ω, S (n + 1) ω - S n ω⟫_ℝ := by
      funext ω
      simp only [martingaleTransform, Finset.sum_range_succ, Pi.add_apply]
    have h1 : StronglyMeasurable[𝓕 (n + 1)] (martingaleTransform φ S n) :=
      (ih hnT.le).mono (𝓕.mono n.le_succ)
    have h2 : StronglyMeasurable[𝓕 (n + 1)] (φ (n + 1)) :=
      (hφ n hnT).mono (𝓕.mono n.le_succ)
    have h3 : StronglyMeasurable[𝓕 (n + 1)] (S n) := (hS n hnT.le).mono (𝓕.mono n.le_succ)
    rw [e]
    exact h1.add (h2.inner ((hS (n + 1) hn).sub h3))

/-- **Conditional one-period no arbitrage gives multi-period no arbitrage**, for a price adapted
up to the horizon. -/
theorem noArbitrage_of_noArbitrageLocal {T : ℕ}
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) (hloc : NoArbitrageLocal 𝓕 P S T) :
    NoArbitrage 𝓕 P S T := by
  revert hS hloc
  induction T with
  | zero =>
    intro _ _ φ _ _ _
    rw [martingaleTransform_zero]
  | succ T ih =>
    intro hS hloc φ hφ hbdd hnn
    have hloc' : NoArbitrageLocal 𝓕 P S T := fun t ht ↦ hloc t (Nat.lt_succ_of_lt ht)
    have hφ' : ∀ t < T, StronglyMeasurable[𝓕 t] (φ (t + 1)) :=
      fun t ht ↦ hφ t (Nat.lt_succ_of_lt ht)
    have hbdd' : ∃ K : ℝ, ∀ n ≤ T, ∀ ω, ‖φ n ω‖ ≤ K :=
      hbdd.imp fun K hK n hn ↦ hK n (hn.trans T.le_succ)
    have hS' : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t) := fun t ht ↦ hS t (ht.trans T.le_succ)
    have hsplit (ω : Ω) : martingaleTransform φ S (T + 1) ω =
        martingaleTransform φ S T ω + ⟪φ (T + 1) ω, S (T + 1) ω - S T ω⟫_ℝ := by
      simp only [martingaleTransform, Finset.sum_range_succ]
    have hV : StronglyMeasurable[𝓕 T] (martingaleTransform φ S T) :=
      stronglyMeasurable_martingaleTransform hS' hφ' T le_rfl
    have hB : MeasurableSet[𝓕 T] {ω | martingaleTransform φ S T ω < 0} :=
      hV.measurable (measurableSet_Iio (a := (0 : ℝ)))
    obtain ⟨θ, hθ⟩ : ∃ θ : Ω → F,
        θ = {ω | martingaleTransform φ S T ω < 0}.indicator (φ (T + 1)) := ⟨_, rfl⟩
    have hθ_pos (ω : Ω) (h : martingaleTransform φ S T ω < 0) : θ ω = φ (T + 1) ω := by
      rw [hθ]; simp [h]
    have hθ_neg (ω : Ω) (h : ¬ martingaleTransform φ S T ω < 0) : θ ω = 0 := by
      rw [hθ]; simp [h]
    have hθm : StronglyMeasurable[𝓕 T] θ := by
      rw [hθ]
      exact (hφ T T.lt_succ_self).indicator hB
    have hnn1 : 0 ≤ᵐ[P] fun ω ↦ ⟪θ ω, S (T + 1) ω - S T ω⟫_ℝ := by
      filter_upwards [hnn] with ω hω
      have hω' : 0 ≤ martingaleTransform φ S (T + 1) ω := hω
      change 0 ≤ ⟪θ ω, S (T + 1) ω - S T ω⟫_ℝ
      by_cases h : martingaleTransform φ S T ω < 0
      · rw [hθ_pos ω h]
        have := hsplit ω
        linarith
      · rw [hθ_neg ω h]
        simp
    have h1 := hloc T T.lt_succ_self θ hθm hnn1
    have hV0 : 0 ≤ᵐ[P] martingaleTransform φ S T := by
      filter_upwards [hnn, h1] with ω hω h1ω
      have hω' : 0 ≤ martingaleTransform φ S (T + 1) ω := hω
      have h1ω' : ⟪θ ω, S (T + 1) ω - S T ω⟫_ℝ = 0 := h1ω
      change 0 ≤ martingaleTransform φ S T ω
      by_contra h
      have h' : martingaleTransform φ S T ω < 0 := not_le.1 h
      rw [hθ_pos ω h'] at h1ω'
      have := hsplit ω
      linarith
    have hV00 : martingaleTransform φ S T =ᵐ[P] 0 := ih hS' hloc' φ hφ' hbdd' hV0
    have hg : 0 ≤ᵐ[P] fun ω ↦ ⟪φ (T + 1) ω, S (T + 1) ω - S T ω⟫_ℝ := by
      filter_upwards [hnn, hV00] with ω hω hVω
      have hω' : 0 ≤ martingaleTransform φ S (T + 1) ω := hω
      have hVω' : martingaleTransform φ S T ω = 0 := hVω
      change 0 ≤ ⟪φ (T + 1) ω, S (T + 1) ω - S T ω⟫_ℝ
      have := hsplit ω
      linarith
    have h2 := hloc T T.lt_succ_self (φ (T + 1)) (hφ T T.lt_succ_self) hg
    filter_upwards [hV00, h2] with ω hVω h2ω
    have hVω' : martingaleTransform φ S T ω = 0 := hVω
    have h2ω' : ⟪φ (T + 1) ω, S (T + 1) ω - S T ω⟫_ℝ = 0 := h2ω
    change martingaleTransform φ S (T + 1) ω = 0
    rw [hsplit ω, hVω', h2ω', add_zero]

/-- **No arbitrage is local.** For a price adapted up to the horizon `T`, the multi-period market
is arbitrage free if and only if every one-period market conditional on `𝓕 t`, `t < T`, is. -/
theorem noArbitrage_iff_noArbitrageLocal {T : ℕ}
    (hS : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)) :
    NoArbitrage 𝓕 P S T ↔ NoArbitrageLocal 𝓕 P S T :=
  ⟨noArbitrageLocal_of_noArbitrage, noArbitrage_of_noArbitrageLocal hS⟩

end MathFin
