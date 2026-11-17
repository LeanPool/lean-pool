/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMoment

/-!
# Restriction of a simple predictable integrand to `(a, b]`

An adapted simple integrand `G` multiplied by the simple integrand `1_{(a, b]}` on their common
refinement is again an adapted simple integrand: its evaluation is `1_{(a, b]}·G`, its
coefficients vanish on every tile not contained in `(a, b]` and stay bounded by any bound on the
coefficients of `G`, and the variance budget of that per-tile bound is at most `C²(b − a)`.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)

/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => ite_eq_right fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact ite_eq_left hs

/-- A simple integrand with coefficients bounded by `C ≥ 0` has evaluations bounded by `C`. -/
theorem SimplePredictable.abs_eval_le {T : ℝ} (H : SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C := by
  classical
  by_cases h : ∃ j : Fin H.N, H.partition j.castSucc < s ∧ s ≤ H.partition j.succ
  · obtain ⟨j, hj⟩ := h
    rw [H.eval_of_mem_Ioc j hj ω]
    exact hC j ω
  · push Not at h
    have hz : H.eval s ω = 0 := by
      unfold SimplePredictable.eval
      exact Finset.sum_eq_zero fun j _ =>
        ite_eq_right fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz, abs_zero]
    exact hC0

/-- The variance budget of the per-tile bound `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`. -/
theorem SimplePredictable.varClock_le_Ioc {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
    (hab : a ≤ b) :
    H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
        H.N ≤ C ^ 2 * (b - a) := by
  classical
  set F : ℕ → ℝ := fun k =>
    min b (max a (H.partition ⟨min k H.N, Nat.lt_succ_of_le (min_le_right _ _)⟩)) with hFdef
  have hFmono : ∀ k, F k ≤ F (k + 1) := by
    intro k
    refine min_le_min le_rfl (max_le_max le_rfl (H.partition_strictMono.monotone ?_))
    rw [Fin.le_def]
    simp only
    omega
  have hFval : ∀ (j : ℕ) (hj : j < H.N),
      F j = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).castSucc))
        ∧ F (j + 1) = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).succ)) := by
    intro j hj
    have hidx0 : (⟨min j H.N, Nat.lt_succ_of_le (min_le_right j H.N)⟩ : Fin (H.N + 1))
        = (⟨j, hj⟩ : Fin H.N).castSucc := by
      apply Fin.ext
      change min j H.N = j
      omega
    have hidx1 : (⟨min (j + 1) H.N, Nat.lt_succ_of_le (min_le_right (j + 1) H.N)⟩
          : Fin (H.N + 1)) = (⟨j, hj⟩ : Fin H.N).succ := by
      apply Fin.ext
      change min (j + 1) H.N = j + 1
      omega
    refine ⟨?_, ?_⟩
    · simp only [hFdef]
      rw [hidx0]
    · simp only [hFdef]
      rw [hidx1]
  have hstep : ∀ j ∈ Finset.range H.N,
      (if h : j < H.N then
        (if a ≤ H.partition (⟨j, h⟩ : Fin H.N).castSucc
            ∧ H.partition (⟨j, h⟩ : Fin H.N).succ ≤ b then C else 0) ^ 2
          * (H.partition (⟨j, h⟩ : Fin H.N).succ - H.partition (⟨j, h⟩ : Fin H.N).castSucc)
        else 0) ≤ C ^ 2 * (F (j + 1) - F j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [dite_eq_left hj]
    obtain ⟨hFj, hFj1⟩ := hFval j hj
    have hmono := H.partition_strictMono (Fin.castSucc_lt_succ (i := (⟨j, hj⟩ : Fin H.N)))
    by_cases hin : a ≤ H.partition (⟨j, hj⟩ : Fin H.N).castSucc
        ∧ H.partition (⟨j, hj⟩ : Fin H.N).succ ≤ b
    · rw [ite_eq_left hin, hFj, hFj1,
        max_eq_right hin.1, max_eq_right (le_trans hin.1 hmono.le),
        min_eq_right (le_trans hmono.le hin.2), min_eq_right hin.2]
    · rw [ite_eq_right hin]
      have : F j ≤ F (j + 1) := hFmono j
      nlinarith [sq_nonneg C]
  calc H.varClock
        (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0) H.N
      ≤ ∑ j ∈ Finset.range H.N, C ^ 2 * (F (j + 1) - F j) := Finset.sum_le_sum hstep
    _ = C ^ 2 * (F H.N - F 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ C ^ 2 * (b - a) := by
        have hup : F H.N ≤ b := min_le_left _ _
        have hlow : a ≤ F 0 := le_min hab (le_max_left _ _)
        nlinarith [sq_nonneg C]


/-- The simple integrand `1_{(a, b]}` for `0 ≤ a < b`. -/
noncomputable def stepIocGen (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SimplePredictable Ω b :=
  if h : 0 < a then stepIoc Ω h hab else stepIoc₀ Ω (lt_of_le_of_lt ha hab)

@[simp] theorem stepIocGen_eval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIocGen Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dite_eq_left h, stepIoc_eval]
  · rw [dite_eq_right h]
    have ha0 : a = 0 := le_antisymm (not_lt.mp h) ha
    subst ha0
    exact stepIoc₀_eval _ s ω

theorem stepIocGen_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∀ i : Fin (stepIocGen Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocGen Ω ha hab).partition i.castSucc)) ((stepIocGen Ω ha hab).ξ i) := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dite_eq_left h]; exact stepIoc_adapt ℱ h hab
  · rw [dite_eq_right h]; exact stepIoc₀_adapt ℱ _

/-- A simple integrand whose coefficients vanish on every tile not contained in `(a, b]` has the
same elementary integral at every time past `b`. -/
theorem SimplePredictable.simpleIntegral_eq_of_support
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {a b : ℝ}
    (hz : ∀ (j : Fin H.N) (ω : Ω),
      ¬(a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b) → H.ξ j ω = 0)
    {t : ℝ} (hbt : b ≤ t) (ω : Ω) : simpleIntegral W H t ω = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum]
  unfold simpleIntegral
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b
  · have h1 : H.partition j.succ ≤ t := hj.2.trans hbt
    have h2 : H.partition j.castSucc ≤ t :=
      ((H.partition_strictMono Fin.castSucc_lt_succ).le).trans h1
    rw [min_eq_left h1, min_eq_left h2]
  · rw [hz j ω hj, zero_mul, zero_mul]


/-- **Restriction of a simple integrand to `(a, b]`.** Multiplying an adapted simple integrand
by `1_{(a, b]}` on their common refinement gives an adapted simple integrand whose evaluation is
the restricted evaluation and whose coefficients vanish on every tile not contained in `(a, b]`
and are bounded by `C` on the others. -/
theorem SimplePredictable.exists_restrict_Ioc
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
      ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
          ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0) := by
  classical
  obtain ⟨T₃, Q, hQadapt, hQeval, -⟩ :=
    SimplePredictable.exists_mul_simple W ℱ G (stepIocGen Ω ha hab) h_adapt
      (stepIocGen_adapt ℱ ha hab)
  have hQeval' : ∀ s ω, Q.eval s ω
      = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω := by
    intro s ω
    rw [hQeval s ω, stepIocGen_eval ha hab, mul_comm]
  refine ⟨T₃, Q, hQadapt, hQeval', fun j ω => ?_⟩
  have hlt : Q.partition j.castSucc < Q.partition j.succ :=
    Q.partition_strictMono Fin.castSucc_lt_succ
  by_cases hin : a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b
  · rw [ite_eq_left hin]
    have hs : Q.partition j.castSucc < Q.partition j.succ
        ∧ Q.partition j.succ ≤ Q.partition j.succ := ⟨hlt, le_rfl⟩
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' _ ω, abs_mul]
    have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)| ≤ 1 := by
      by_cases hm : Q.partition j.succ ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hm]; norm_num
      · rw [Set.indicator_of_notMem hm]; norm_num
    calc |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)|
          * |G.eval (Q.partition j.succ) ω|
        ≤ 1 * C := by
          exact mul_le_mul h1 (G.abs_eval_le hC0 hC _ ω) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [ite_eq_right hin]
    -- pick a time in the tile that lies outside `(a, b]`
    obtain ⟨s, hs, hsout⟩ : ∃ s : ℝ, (Q.partition j.castSucc < s ∧ s ≤ Q.partition j.succ)
        ∧ s ∉ Set.Ioc a b := by
      by_cases hb : Q.partition j.succ ≤ b
      · have hna : Q.partition j.castSucc < a := by
          by_contra hcon
          exact hin ⟨not_lt.mp hcon, hb⟩
        refine ⟨min a (Q.partition j.succ), ⟨lt_min hna hlt, min_le_right _ _⟩, ?_⟩
        exact fun hm => absurd (Set.mem_Ioc.mp hm).1 (not_lt.mpr (min_le_left _ _))
      · refine ⟨Q.partition j.succ, ⟨hlt, le_rfl⟩, ?_⟩
        exact fun hm => hb (Set.mem_Ioc.mp hm).2
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' s ω, Set.indicator_of_notMem hsout, zero_mul,
      abs_zero]

end LevyStochCalc.Brownian.Ito
