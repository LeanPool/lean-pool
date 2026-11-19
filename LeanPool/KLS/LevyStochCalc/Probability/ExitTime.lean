/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Monotone

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

@[expose] public section

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

/-- The nonnegative times at which the path `X ω` has norm at least `k`. -/
def exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : Set ℝ := {t : ℝ | 0 ≤ t ∧ k ≤ ‖X ω t‖}

open scoped Classical in
/-- The first nonnegative time at which the path `X ω` has norm at least `k`, and `⊤` when the
path never reaches that norm. -/
noncomputable def exitTime (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : WithTop ℝ :=
  if (exitSet X k ω).Nonempty then ((sInf (exitSet X k ω) : ℝ) : WithTop ℝ) else ⊤

/-- The `n`-th rational, clamped to `[0, t]`. -/
noncomputable def gridPt (t : ℝ) (n : ℕ) : ℝ :=
  max 0 (min t (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ))

theorem bddBelow_exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : BddBelow (exitSet X k ω) :=
  ⟨0, fun _ ht => ht.1⟩

theorem isClosed_exitSet {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) :
    IsClosed (exitSet X k ω) := by
  have h : exitSet X k ω = Set.Ici (0 : ℝ) ∩ (fun r => ‖X ω r‖) ⁻¹' Set.Ici k := by
    ext r
    simp only [exitSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Ici.preimage hX.norm)

theorem csInf_exitSet_mem {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k : ℝ}
    (h : (exitSet X k ω).Nonempty) : sInf (exitSet X k ω) ∈ exitSet X k ω :=
  (isClosed_exitSet hX k).csInf_mem h (bddBelow_exitSet X k ω)

theorem coe_zero_le_exitTime (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) :
    ((0 : ℝ) : WithTop ℝ) ≤ exitTime X k ω := by
  rw [exitTime]
  split_ifs with h
  · exact_mod_cast le_csInf h fun _ hr => hr.1
  · exact le_top

/-- For a continuous path, the exit time is at most `t` exactly when the path reaches norm `k`
somewhere on `[0, t]`. -/
theorem exitTime_le_iff {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k t : ℝ) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔ ∃ s ∈ Set.Icc (0 : ℝ) t, k ≤ ‖X ω s‖ := by
  constructor
  · intro hle
    rw [exitTime] at hle
    split_ifs at hle with h
    · have hmem := csInf_exitSet_mem hX h
      have hst : sInf (exitSet X k ω) ≤ t := by exact_mod_cast hle
      exact ⟨sInf (exitSet X k ω), ⟨hmem.1, hst⟩, hmem.2⟩
    · exact absurd hle (by simp)
  · rintro ⟨s, ⟨hs0, hst⟩, hks⟩
    have hne : (exitSet X k ω).Nonempty := ⟨s, hs0, hks⟩
    rw [exitTime, ite_eq_left hne]
    have hle : sInf (exitSet X k ω) ≤ t :=
      le_trans (csInf_le (bddBelow_exitSet X k ω) ⟨hs0, hks⟩) hst
    exact_mod_cast hle

theorem gridPt_mem_Icc {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : gridPt t n ∈ Set.Icc (0 : ℝ) t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩

/-- Clamping to `[0, t]` does not increase the distance to a point of `[0, t]`. -/
theorem abs_clamp_sub_le {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) (x : ℝ) :
    |max 0 (min t x) - s| ≤ |x - s| := by
  obtain ⟨hs0, hst⟩ := hs
  rcases lt_or_ge x 0 with hx | hx
  · rw [min_eq_right (hx.le.trans ht), max_eq_left hx.le,
      abs_of_nonpos (by linarith : (0 : ℝ) - s ≤ 0), abs_of_nonpos (by linarith : x - s ≤ 0)]
    linarith
  · rcases lt_or_ge t x with hxt | hxt
    · rw [min_eq_left hxt.le, max_eq_right ht,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - s)]
      linarith
    · rw [min_eq_right hxt, max_eq_right hx]

theorem exists_gridPt_near {t : ℝ} (ht : 0 ≤ t) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) {δ : ℝ}
    (hδ : 0 < δ) : ∃ n : ℕ, |gridPt t n - s| < δ := by
  obtain ⟨q, hq⟩ := exists_rat_near s hδ
  refine ⟨Denumerable.eqv ℚ q, ?_⟩
  have hqn : ((Denumerable.eqv ℚ).symm (Denumerable.eqv ℚ q) : ℚ) = q := Equiv.symm_apply_apply _ _
  rw [gridPt, hqn]
  refine lt_of_le_of_lt (abs_clamp_sub_le ht hs _) ?_
  rwa [abs_sub_comm]

/-- The comparison `exitTime X k ω ≤ t` is decided by the values of a continuous path on the
rationals of `[0, t]`. -/
theorem exitTime_le_iff_forall {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) (k : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    exitTime X k ω ≤ (t : WithTop ℝ) ↔
      ∀ n : ℕ, ∃ m : ℕ, k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖ := by
  rw [exitTime_le_iff hX]
  constructor
  · rintro ⟨s, hs, hks⟩ n
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hca : ContinuousAt (fun r => ‖X ω r‖) s := hX.norm.continuousAt
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hca _ hε
    obtain ⟨m, hm⟩ := exists_gridPt_near ht hs hδ
    refine ⟨m, ?_⟩
    have hdist : dist (gridPt t m) s < δ := by rwa [Real.dist_eq]
    have hclose := hδ' hdist
    rw [Real.dist_eq] at hclose
    have hle : ‖X ω s‖ - ‖X ω (gridPt t m)‖ ≤ |‖X ω (gridPt t m)‖ - ‖X ω s‖| := by
      rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · intro hall
    obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
      (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
    refine ⟨s₀, hs₀, ?_⟩
    rcases lt_or_ge ‖X ω s₀‖ k with hlt | hge
    · exfalso
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < k - ‖X ω s₀‖ by linarith)
      obtain ⟨m, hm⟩ := hall n
      have hle : ‖X ω (gridPt t m)‖ ≤ ‖X ω s₀‖ := hmax (gridPt_mem_Icc ht m)
      rw [one_div] at hn
      linarith
    · exact hge

theorem measurable_norm_of_adapted [MeasurableSpace E] [OpensMeasurableSpace E]
    {ℱ : Filtration ℝ mΩ} {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r) (r : ℝ) :
    Measurable[ℱ r] fun ω => ‖X ω r‖ := by
  let : MeasurableSpace Ω := ℱ r
  exact Measurable.norm (hadapt r)

theorem measurableSet_exitTime_le {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k t : ℝ) :
    MeasurableSet[ℱ t] {ω | exitTime X k ω ≤ (t : WithTop ℝ)} := by
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω | exitTime X k ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      obtain ⟨s, hs, -⟩ := (exitTime_le_iff (hcont ω) k t).1 hle
      exact absurd (hs.1.trans hs.2) (not_le.2 ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω | exitTime X k ω ≤ (t : WithTop ℝ)}
        = ⋂ n : ℕ, ⋃ m : ℕ, {ω | k - ((n : ℝ) + 1)⁻¹ < ‖X ω (gridPt t m)‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
      exact exitTime_le_iff_forall (hcont ω) k ht
    rw [hset]
    have hmeas : ∀ m : ℕ, Measurable[ℱ t] fun ω => ‖X ω (gridPt t m)‖ := fun m =>
      (measurable_norm_of_adapted hadapt (gridPt t m)).mono
        (ℱ.mono (gridPt_mem_Icc ht m).2) le_rfl
    let : MeasurableSpace Ω := ℱ t
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m =>
      measurableSet_lt measurable_const (hmeas m)

/-- The exit time of a continuous adapted process is a stopping time. -/
theorem isStoppingTime_exitTime {ℱ : Filtration ℝ mΩ} [MeasurableSpace E]
    [OpensMeasurableSpace E] {X : Ω → ℝ → E} (hadapt : Adapted ℱ fun r ω => X ω r)
    (hcont : ∀ ω, Continuous (X ω)) (k : ℝ) :
    IsStoppingTime ℱ (exitTime X k) := fun t => measurableSet_exitTime_le hadapt hcont k t

theorem exitTime_mono (X : Ω → ℝ → E) (ω : Ω) {k k' : ℝ} (h : k ≤ k') :
    exitTime X k ω ≤ exitTime X k' ω := by
  have hsub : exitSet X k' ω ⊆ exitSet X k ω := fun r hr => ⟨hr.1, h.trans hr.2⟩
  rw [exitTime, exitTime]
  split_ifs with h1 h2 h2
  · exact_mod_cast csInf_le_csInf (bddBelow_exitSet X k ω) h2 hsub
  · exact le_top
  · exact absurd (Set.Nonempty.mono hsub h2) h1
  · exact le_rfl

/-- Up to and including the exit time, a continuous path started at a positive time has norm at
most `k`. The restriction to positive times is necessary: at time `0` the exit time is `0`
whenever the path already starts outside the ball. -/
theorem norm_le_of_le_exitTime {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by
  classical
  have hnot : ∀ u : ℝ, 0 ≤ u → u < s → ‖X ω u‖ ≤ k := by
    intro u hu0 hus
    by_contra hcon
    have hmem : u ∈ exitSet X k ω := ⟨hu0, (not_le.mp hcon).le⟩
    have : exitTime X k ω ≤ ((u : ℝ) : WithTop ℝ) := by
      rw [exitTime, ite_eq_left ⟨u, hmem⟩]
      exact_mod_cast csInf_le (bddBelow_exitSet X k ω) hmem
    have hsu : ((s : ℝ) : WithTop ℝ) ≤ ((u : ℝ) : WithTop ℝ) := hle.trans this
    exact absurd (by exact_mod_cast hsu : s ≤ u) (not_le.mpr hus)
  have hlim : Filter.Tendsto (fun u => ‖X ω u‖) (nhdsWithin s (Set.Iio s)) (nhds ‖X ω s‖) :=
    (hX.norm.tendsto s).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in nhdsWithin s (Set.Iio s), ‖X ω u‖ ≤ k := by
    have h0 : ∀ᶠ u in nhdsWithin s (Set.Iio s), 0 < u :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hs)
    filter_upwards [h0, self_mem_nhdsWithin] with u hu0 huc
    exact hnot u hu0.le huc
  exact le_of_tendsto hlim hev

/-- **Localisation.** For a continuous path, every time lies strictly below the exit time at
level `k` for all large `k`. -/
theorem exists_lt_exitTime {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {t : ℝ} (ht : 0 ≤ t) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → (t : WithTop ℝ) < exitTime X (k : ℝ) ω := by
  obtain ⟨s₀, hs₀, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_isMaxOn
    (Set.nonempty_Icc.2 ht) hX.norm.continuousOn
  obtain ⟨K, hK⟩ := exists_nat_gt ‖X ω s₀‖
  refine ⟨K, fun k hk => ?_⟩
  rcases lt_or_ge (t : WithTop ℝ) (exitTime X (k : ℝ) ω) with hlt | hle
  · exact hlt
  · exfalso
    obtain ⟨s, hs, hks⟩ := (exitTime_le_iff hX (k : ℝ) t).1 hle
    have h1 : ‖X ω s‖ ≤ ‖X ω s₀‖ := hmax hs
    have h2 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith

end LevyStochCalc.Probability
