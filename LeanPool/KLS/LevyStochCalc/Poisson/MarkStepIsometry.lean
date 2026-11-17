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

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensity

/-!
# Mark-step integrands, their compensated integrals and the `L²` isometry

A *mark-step integrand* is a finite sum `∑ᵢ 𝟙_{(pᵢ, pᵢ₊₁]}(s) ∑ₖ ξᵢₖ(ω) 𝟙_{Bₖ}(e)` over a
time grid `0 = p₀ < ⋯ < p_{N₀}` (`TimeGrid`) and finitely many mark sets `Bₖ` of finite
`ν`-measure, with bounded coefficients `ξᵢₖ`. Its compensated integral up to time `t` is
`∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ ∧ t, pᵢ₊₁ ∧ t] × Bₖ)`. Clamping a grid at a time `t` (`TimeGrid.clamp`)
expresses that integral as the integral over the whole clamped horizon, which carries the
`L²` isometry from the horizon to every time, in both real and `ℝ≥0∞` form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A finite time grid `0 = p 0 < p 1 < ⋯ < p N₀`; values of `p` beyond `N₀` are
irrelevant. -/
structure TimeGrid where
  /-- Number of pieces. -/
  N₀ : ℕ
  /-- The grid points. -/
  p : ℕ → ℝ
  p_zero : p 0 = 0
  p_lt : ∀ i, i < N₀ → p i < p (i + 1)

namespace TimeGrid

variable (g : TimeGrid)

lemma p_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ g.N₀) : g.p i ≤ g.p j := by
  induction hij with
  | refl => exact le_rfl
  | step h ih =>
    exact (ih (Nat.le_of_succ_le hj)).trans (g.p_lt _ (Nat.lt_of_succ_le hj)).le

lemma p_strictMono {i j : ℕ} (hij : i < j) (hj : j ≤ g.N₀) : g.p i < g.p j :=
  (g.p_lt i (lt_of_lt_of_le hij hj)).trans_le (g.p_mono (Nat.succ_le_of_lt hij) hj)

lemma p_nonneg {i : ℕ} (hi : i ≤ g.N₀) : 0 ≤ g.p i := by
  have := g.p_mono (Nat.zero_le i) hi
  rwa [g.p_zero] at this

/-- The grid as a strictly monotone map on `Fin (N₀ + 1)`. -/
lemma strictMono_fin : StrictMono (fun i : Fin (g.N₀ + 1) => g.p i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact g.p_lt i i.isLt

/-- The horizon of the grid. -/
def horizon : ℝ := g.p g.N₀

lemma horizon_nonneg : 0 ≤ g.horizon := g.p_nonneg le_rfl

end TimeGrid

/-- A mark-step integrand on the time grid `g`: mark sets `B k` of finite `ν`-measure and
bounded measurable coefficients `ξ i k` for each piece `i` and mark `k`. Coefficients
with `N₀ ≤ i` are irrelevant. -/
structure MarkStep (Ω : Type u) [MeasurableSpace Ω] (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] (g : TimeGrid) where
  /-- Number of mark sets. -/
  K : ℕ
  /-- The mark sets. -/
  B : Fin K → Set E
  B_measurable : ∀ k, MeasurableSet (B k)
  B_finite : ∀ k, ν (B k) ≠ ⊤
  /-- The coefficients. -/
  ξ : ℕ → Fin K → Ω → ℝ
  ξ_bounded : ∀ i k, ∃ M : ℝ, ∀ ω, |ξ i k ω| ≤ M
  ξ_measurable : ∀ i k, Measurable (ξ i k)

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The compensated integral of a mark-step integrand up to time `t`. -/
noncomputable def integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω

/-- The compensated integral of a mark-step integrand over its whole horizon. -/
noncomputable def full (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω

/-- The integrand as a function of time, mark and sample point. -/
noncomputable def eval (G : MarkStep Ω E ν g) (s : ℝ) (e : E) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
    * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e

/-- Adaptedness of the coefficients to the natural filtration at the left endpoints of
their pieces. -/
def Adapted (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (G : MarkStep Ω E ν g) : Prop :=
  ∀ i, i < g.N₀ → ∀ k,
    @StronglyMeasurable Ω ℝ _ (ℱ (g.p i)) (G.ξ i k)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g)

lemma full_eq_fin (ω : Ω) :
    G.full N ω = ∑ i : Fin g.N₀, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω :=
  (Fin.sum_univ_eq_sum_range (fun i => ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω) g.N₀).symm

lemma eval_eq_fin (s : ℝ) (e : E) (ω : Ω) :
    G.eval s e ω = ∑ i : Fin g.N₀,
      (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
        * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e :=
  (Fin.sum_univ_eq_sum_range (fun i =>
    (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e) g.N₀).symm

/-- The compensated integral of an empty time interval vanishes. -/
lemma compensated_Ioc_self (a : ℝ) (B : Set E) (ω : Ω) :
    N.compensated (Set.Ioc a a ×ˢ B) ω = 0 := by
  rw [Set.Ioc_self, Set.empty_prod]
  change (N.N ω ∅).toReal - (referenceIntensity ν ∅).toReal = 0
  simp

/-- Past the horizon, the integral up to `t` is the integral over the whole horizon. -/
lemma integral_eq_full_of_horizon_le {t : ℝ} (ht : g.horizon ≤ t) (ω : Ω) :
    G.integral N t ω = G.full N ω := by
  unfold integral full
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [min_eq_left ((g.p_mono hi.le le_rfl).trans ht),
    min_eq_left ((g.p_mono hi le_rfl).trans ht)]

/-- The integral up to a nonpositive time vanishes. -/
lemma integral_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : G.integral N t ω = 0 := by
  unfold integral
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.mem_range] at hi
  rw [min_eq_right (ht.trans (g.p_nonneg hi.le)), min_eq_right (ht.trans (g.p_nonneg hi)),
    compensated_Ioc_self, mul_zero]

/-- The `k`-th mark of a mark-step integrand as a simple predictable integrand. -/
noncomputable def toSimple (k : Fin G.K) : SimplePredictable Ω E ν g.horizon where
  N := g.N₀
  partition := fun i => g.p i
  partition_zero := by simp [g.p_zero]
  partition_le_T := by simp [TimeGrid.horizon]
  partition_strictMono := g.strictMono_fin
  A := fun _ => G.B k
  A_measurable := fun _ => G.B_measurable k
  A_finite := fun _ => G.B_finite k
  ξ := fun i => G.ξ i k
  ξ_bounded := fun i => G.ξ_bounded i k
  ξ_measurable := fun i => G.ξ_measurable i k

lemma integral_eq_stepIntegral (t : ℝ) (ω : Ω) :
    G.integral N t ω = stepIntegral N G.toSimple t ω := by
  unfold integral stepIntegral simpleIntegral
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => G.ξ i k ω
    * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω) g.N₀]
  rfl

include hℱ in
/-- The compensated integral of an adapted mark-step integrand is a martingale on the
natural filtration. -/
lemma martingale_integral (hG : G.Adapted ℱ) :
    Martingale (fun t => G.integral N t) ℱ P := by
  have hfun : (fun t => G.integral N t) = fun t => stepIntegral N G.toSimple t :=
    funext fun t => funext fun ω => G.integral_eq_stepIntegral N t ω
  rw [hfun]
  exact martingale_stepIntegral_compensated N ℱ hℱ G.toSimple (fun k i => hG i i.isLt k)

/-- The compensated integral of a mark-step integrand up to any time is square
integrable. -/
lemma memLp_integral (t : ℝ) : MemLp (fun ω => G.integral N t ω) 2 P := by
  have : (fun ω => G.integral N t ω) = fun ω => ∑ k, simpleIntegral N (G.toSimple k) t ω := by
    funext ω
    exact G.integral_eq_stepIntegral N t ω
  rw [this]
  exact memLp_finsetSum _ fun k _ => simpleIntegral_memLp_at N (G.toSimple k) t

lemma memLp_full : MemLp (fun ω => G.full N ω) 2 P := by
  have : (fun ω => G.full N ω) = fun ω => G.integral N g.horizon ω := by
    funext ω
    exact (G.integral_eq_full_of_horizon_le N le_rfl ω).symm
  rw [this]
  exact G.memLp_integral N _

include hℱ in
/-- The `L²` isometry of the compensated integral over the whole horizon. -/
theorem integral_full_sq (hG : G.Adapted ℱ) {T : ℝ} (hT : g.horizon ≤ T) :
    ∫ ω, (G.full N ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T, (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := markSumProcess_isometry_L2 (fun i : Fin (g.N₀ + 1) => g.p i)
    (by simp [g.p_zero]) g.strictMono_fin (T := T) (by simpa [TimeGrid.horizon] using hT) N ℱ hℱ G.B
    G.B_measurable G.B_finite (fun i k => G.ξ i k) (fun i k => G.ξ_bounded i k)
    (fun i k => G.ξ_measurable i k) (fun i k => hG i i.isLt k)
  simp only [Fin.val_castSucc, Fin.val_succ] at key
  simp_rw [full_eq_fin, eval_eq_fin]
  exact key

end MarkStep

namespace TimeGrid

variable (g : TimeGrid)

open Classical in
/-- The index of the first grid point at or after `t`, capped at `N₀`. -/
noncomputable def clampIndex (t : ℝ) : ℕ :=
  Nat.find (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i)

open Classical in
lemma clampIndex_le (t : ℝ) : g.clampIndex t ≤ g.N₀ := Nat.find_le (Or.inl le_rfl)

open Classical in
lemma lt_of_lt_clampIndex {t : ℝ} {i : ℕ} (hi : i < g.clampIndex t) :
    i < g.N₀ ∧ g.p i < t := by
  have := Nat.find_min (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i) hi
  exact ⟨not_le.1 fun h => this (Or.inl h), not_le.1 fun h => this (Or.inr h)⟩

open Classical in
lemma le_p_of_clampIndex_le {t : ℝ} {i : ℕ} (hi : g.clampIndex t ≤ i) (hiN : i < g.N₀) :
    t ≤ g.p i := by
  have hspec := Nat.find_spec (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i)
  rcases hspec with h | h
  · exact absurd (lt_of_le_of_lt hi hiN) (not_lt.2 h)
  · exact h.trans (g.p_mono hi hiN.le)

/-- The grid clamped at a time `t ≥ 0`: the pieces starting before `t`, the last grid
point being cut at `t`. -/
noncomputable def clamp (t : ℝ) (ht : 0 ≤ t) : TimeGrid where
  N₀ := g.clampIndex t
  p := fun i => min (g.p i) t
  p_zero := by simp [g.p_zero, ht]
  p_lt := fun i hi => by
    obtain ⟨hiN, hpi⟩ := g.lt_of_lt_clampIndex hi
    show min (g.p i) t < min (g.p (i + 1)) t
    rw [min_eq_left hpi.le]
    exact lt_min (g.p_lt i hiN) hpi

lemma clamp_p_of_lt {t : ℝ} (ht : 0 ≤ t) {i : ℕ} (hi : i < (g.clamp t ht).N₀) :
    (g.clamp t ht).p i = g.p i :=
  min_eq_left (g.lt_of_lt_clampIndex hi).2.le

lemma clamp_horizon_le (t : ℝ) (ht : 0 ≤ t) : (g.clamp t ht).horizon ≤ t :=
  min_le_right _ _

open Classical in
/-- The index of the piece containing `s`: the first `i` with `s < p (i + 1)`, capped at
`N₀`. -/
noncomputable def startIndex (s : ℝ) : ℕ :=
  Nat.find (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ s < g.p (i + 1))

open Classical in
lemma startIndex_le (s : ℝ) : g.startIndex s ≤ g.N₀ := Nat.find_le (Or.inl le_rfl)

open Classical in
lemma p_succ_le_of_lt_startIndex {s : ℝ} {i : ℕ} (hi : i < g.startIndex s) :
    i < g.N₀ ∧ g.p (i + 1) ≤ s := by
  have := Nat.find_min (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ s < g.p (i + 1)) hi
  exact ⟨not_le.1 fun h => this (Or.inl h), not_lt.1 fun h => this (Or.inr h)⟩

open Classical in
lemma lt_p_succ_startIndex {s : ℝ} (h : g.startIndex s < g.N₀) :
    s < g.p (g.startIndex s + 1) := by
  have hspec := Nat.find_spec (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ s < g.p (i + 1))
  rcases hspec with h' | h'
  · exact absurd h (not_lt.2 h')
  · exact h'

lemma p_startIndex_le {s : ℝ} (hs : 0 ≤ s) : g.p (g.startIndex s) ≤ s := by
  rcases Nat.eq_zero_or_pos (g.startIndex s) with h | h
  · rw [h, g.p_zero]
    exact hs
  · have := g.p_succ_le_of_lt_startIndex (Nat.sub_lt h one_pos)
    have h1 : g.startIndex s - 1 + 1 = g.startIndex s := by omega
    rw [h1] at this
    exact this.2

lemma startIndex_lt_clampIndex {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (h : g.startIndex s < g.N₀) : g.startIndex s < g.clampIndex t := by
  refine not_le.1 fun hle => ?_
  have := g.le_p_of_clampIndex_le hle h
  exact absurd (this.trans (g.p_startIndex_le hs)) (not_le.2 hst)

lemma startIndex_le_clampIndex {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    g.startIndex s ≤ g.clampIndex t := by
  rcases Nat.lt_or_ge (g.startIndex s) g.N₀ with h | h
  · exact (g.startIndex_lt_clampIndex hs hst h).le
  · refine not_lt.1 fun hlt => ?_
    have hbN : g.clampIndex t < g.N₀ := lt_of_lt_of_le hlt (g.startIndex_le s)
    have h1 := g.le_p_of_clampIndex_le le_rfl hbN
    have h2 := (g.p_succ_le_of_lt_startIndex hlt).2
    exact absurd ((h1.trans (g.p_mono (Nat.le_succ _) hbN)).trans h2) (not_le.2 hst)

/-- The grid of the increment over `(s, t]`: a first piece `(0, s]`, then the pieces of `g`
meeting `(s, t]`, cut at `s` and `t`. -/
noncomputable def incr (s t : ℝ) (hs : 0 < s) (hst : s < t) : TimeGrid where
  N₀ := g.clampIndex t - g.startIndex s + 1
  p := fun i => if i = 0 then 0 else min (max (g.p (g.startIndex s + (i - 1))) s) t
  p_zero := by simp
  p_lt := by
    intro i hi
    have hpa : g.p (g.startIndex s) ≤ s := g.p_startIndex_le hs.le
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      change (0 : ℝ) < min (max (g.p (g.startIndex s + (0 + 1 - 1))) s) t
      rw [show 0 + 1 - 1 = 0 by rfl, add_zero, max_eq_right hpa, min_eq_left hst.le]
      exact hs
    · have hi' : g.startIndex s + (i - 1) < g.clampIndex t := by omega
      have hlt := g.lt_of_lt_clampIndex hi'
      have haN : g.startIndex s < g.N₀ := lt_of_le_of_lt (Nat.le_add_right _ _) hlt.1
      have hsa1 : s < g.p (g.startIndex s + 1) := g.lt_p_succ_startIndex haN
      rw [ite_eq_right hpos.ne', ite_eq_right (Nat.succ_ne_zero i)]
      rw [show i + 1 - 1 = i - 1 + 1 by omega, ← add_assoc]
      have hmono : g.p (g.startIndex s + (i - 1)) < g.p (g.startIndex s + (i - 1) + 1) :=
        g.p_lt _ hlt.1
      rcases Nat.eq_zero_or_pos (i - 1) with hz | hz
      · rw [hz, add_zero, max_eq_right hpa, min_eq_left hst.le]
        rw [hz, add_zero] at hmono
        exact lt_min (lt_of_lt_of_le hsa1 (le_max_left _ _)) hst
      · have hgt : s < g.p (g.startIndex s + (i - 1)) :=
        hsa1.trans_le (g.p_mono (by omega) hlt.1.le)
        rw [max_eq_left hgt.le, min_eq_left hlt.2.le]
        exact lt_min (lt_of_lt_of_le hmono (le_max_left _ _)) hlt.2

lemma incr_p_succ (s t : ℝ) (hs : 0 < s) (hst : s < t) (j : ℕ) :
    (g.incr s t hs hst).p (j + 1) = min (max (g.p (g.startIndex s + j)) s) t := by
  change (if j + 1 = 0 then (0 : ℝ) else min (max (g.p (g.startIndex s + (j + 1 - 1))) s) t) = _
  rw [ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel]

lemma incr_horizon_le (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    (g.incr s t hs hst).horizon ≤ t := by
  change (g.incr s t hs hst).p (g.clampIndex t - g.startIndex s + 1) ≤ t
  rw [incr_p_succ]
  exact min_le_right _ _

lemma clampIndex_p {b : ℕ} (hb : b ≤ g.N₀) : g.clampIndex (g.p b) = b := by
  refine le_antisymm (not_lt.1 fun h => ?_) (not_lt.1 fun h => ?_)
  · exact lt_irrefl _ (g.lt_of_lt_clampIndex h).2
  · rcases Nat.lt_or_ge (g.clampIndex (g.p b)) g.N₀ with h' | h'
    · exact absurd (g.le_p_of_clampIndex_le le_rfl h') (not_le.2 (g.p_strictMono h hb))
    · exact absurd (lt_of_lt_of_le h hb) (not_lt.2 h')

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g}

/-- A mark-step integrand transported to the clamped grid. -/
def clamp (G : MarkStep Ω E ν g) (t : ℝ) (ht : 0 ≤ t) : MarkStep Ω E ν (g.clamp t ht) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable

lemma integral_eq_full_clamp (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ht : 0 ≤ t) (ω : Ω) : G.integral N t ω = (G.clamp t ht).full N ω := by
  unfold integral full
  symm
  refine Finset.sum_subset
    (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t)))
    ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
  refine Finset.sum_eq_zero fun k _ => ?_
  change G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω = 0
  rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
    compensated_Ioc_self, mul_zero]

lemma eval_clamp (G : MarkStep Ω E ν g) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) (e : E) (ω : Ω) :
    (G.clamp t ht).eval s e ω = if s ≤ t then G.eval s e ω else 0 := by
  unfold eval
  split_ifs with hst
  · symm
    calc ∑ i ∈ Finset.range g.N₀,
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          symm
          refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
            Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t))) ?_
          intro i hi hni
          rw [Finset.mem_range] at hi hni
          have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
          rw [Set.indicator_of_notMem, zero_mul]
          intro hs
          exact absurd (hst.trans hti) (not_le.2 hs.1)
      _ = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hpi := (g.lt_of_lt_clampIndex hi).2
          congr 1
          rw [min_eq_left hpi.le]
          by_cases hs : s ∈ Set.Ioc (g.p i) (g.p (i + 1))
          · rw [Set.indicator_of_mem hs, Set.indicator_of_mem
              (show s ∈ Set.Ioc (g.p i) (min (g.p (i + 1)) t) from ⟨hs.1, le_min hs.2 hst⟩)]
          · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem]
            intro hs'
            exact hs ⟨hs'.1, hs'.2.trans (min_le_left _ _)⟩
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Set.indicator_of_notMem, zero_mul]
    intro hs
    exact hst (hs.2.trans (min_le_right _ _))

lemma Adapted.clamp (hG : G.Adapted ℱ) (t : ℝ) (ht : 0 ≤ t) :
    (G.clamp t ht).Adapted ℱ := by
  intro i hi k
  have h := hG i (g.lt_of_lt_clampIndex hi).1 k
  change @StronglyMeasurable Ω ℝ _ (ℱ (min (g.p i) t)) (G.ξ i k)
  rwa [min_eq_left (g.lt_of_lt_clampIndex hi).2.le]

/-- The `L²` isometry of the compensated integral up to any time `t ≥ 0`. -/
theorem integral_sq_at (N : PoissonRandomMeasure P ν)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)
    (G : MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t, (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  simp_rw [G.integral_eq_full_clamp N t ht]
  rw [(G.clamp t ht).integral_full_sq N hℱ (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [G.eval_clamp t ht, ite_eq_left hs.2]

section Eval

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (G : MarkStep Ω E ν g)

lemma abs_indicator_one_le {α : Type*} (s : Set α) (x : α) :
    |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- The integrand is jointly measurable in sample point, time and mark. -/
lemma eval_measurable : Measurable (fun q : Ω × ℝ × E => G.eval q.2.1 q.2.2 q.1) := by
  unfold eval
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (Finset.measurable_sum _ fun k _ =>
    Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.comp measurable_snd)
  · exact (G.ξ_measurable i k).comp measurable_fst
  · exact (measurable_const.indicator (G.B_measurable k)).comp (measurable_snd.comp measurable_snd)

/-- The integrand is bounded. -/
lemma eval_bounded : ∃ C : ℝ, ∀ ω s e, |G.eval s e ω| ≤ C := by
  choose M hM using G.ξ_bounded
  refine ⟨∑ i ∈ Finset.range g.N₀, ∑ k, |M i k|, fun ω s e => ?_⟩
  unfold eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_one_le _ _)).trans ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (abs_indicator_one_le _ _)).trans
    ((hM i k ω).trans (le_abs_self _))

/-- The integrand vanishes off the union of the mark sets. -/
lemma eval_support (ω : Ω) (s : ℝ) (e : E) (he : e ∉ ⋃ k, G.B k) : G.eval s e ω = 0 := by
  unfold eval
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_eq_zero fun k _ => ?_, mul_zero]
  rw [Set.indicator_of_notMem (fun hk => he (Set.mem_iUnion.2 ⟨k, hk⟩)), mul_zero]

lemma measurableSet_iUnion_B : MeasurableSet (⋃ k, G.B k) :=
  MeasurableSet.iUnion fun k => G.B_measurable k

lemma measure_iUnion_B_ne_top : ν (⋃ k, G.B k) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun k _ => G.B_finite k)
    (measure_iUnion_fintype_le ν G.B)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ)

include hℱ in
/-- The `L²` isometry over the whole horizon, in `ℝ≥0∞` form. -/
theorem lintegral_full_sq (hG : G.Adapted ℱ) {T : ℝ} (hT : g.horizon ≤ T) :
    ∫⁻ ω, (‖G.full N ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  rw [lintegral_sq_eq_ofReal_integral (G.memLp_full N), G.integral_full_sq N hℱ hG hT]
  exact triple_ofReal_integral_eq_lintegral (fun ω s e => G.eval s e ω) G.eval_measurable hC
    G.measurableSet_iUnion_B G.measure_iUnion_B_ne_top (fun ω s e he => G.eval_support ω s e he)

include hℱ in
/-- The `L²` isometry up to any time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sq_at (hG : G.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  simp_rw [G.integral_eq_full_clamp N t ht]
  rw [(G.clamp t ht).lintegral_full_sq N hℱ (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine lintegral_congr fun ω => lintegral_congr fun e => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [G.eval_clamp t ht, ite_eq_left hs.2]

end Eval

end MarkStep

end LevyStochCalc.Poisson.Compensated
