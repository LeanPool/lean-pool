/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Distribution.Stationary
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationMonotone

/-!
# Uniqueness of the stationary agent distribution

A Doeblin argument, made available by the borrowing constraint.

The asset transition is deterministic given the shock, so the laws started from two
different asset levels have disjoint supports and no minorization against a spread-out
measure can hold. An ATOM escapes that obstruction: if a long enough run of bad income
shocks drives every household to exactly the borrowing constraint, then every `N`-step law
charges the single point `s₀ = (0, z₀)` with probability at least `ε`, and that is a genuine
Doeblin condition.

The contraction is run on the function side, where `markovOp` already lives, rather than on
signed measures. The oscillation `supF h - infF h` contracts by `1 - ε` every `N` steps, so
for two stationary distributions `∫ h dμ - ∫ h dν` is squeezed to zero for every bounded
continuous `h`, and extensionality finishes.
-/

@[expose] public section

open scoped NNReal ENNReal
open Set Filter Topology BoundedContinuousFunction MeasureTheory

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The range of a bounded continuous function -/

theorem bddAbove_range (h : P.State →ᵇ ℝ) : BddAbove (Set.range h) := by
  refine ⟨‖h‖, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact (abs_le.mp (h.norm_coe_le_norm s)).2

theorem bddBelow_range (h : P.State →ᵇ ℝ) : BddBelow (Set.range h) := by
  refine ⟨-‖h‖, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact (abs_le.mp (h.norm_coe_le_norm s)).1

/-- The supremum of a bounded continuous function on the state space. -/
noncomputable def supF (h : P.State →ᵇ ℝ) : ℝ := ⨆ s, h s

/-- The infimum of a bounded continuous function on the state space. -/
noncomputable def infF (h : P.State →ᵇ ℝ) : ℝ := ⨅ s, h s

theorem le_supF (h : P.State →ᵇ ℝ) (s : P.State) : h s ≤ P.supF h :=
  le_ciSup (f := fun t => h t) (P.bddAbove_range h) s

theorem infF_le (h : P.State →ᵇ ℝ) (s : P.State) : P.infF h ≤ h s :=
  ciInf_le (f := fun t => h t) (P.bddBelow_range h) s

theorem infF_le_supF (h : P.State →ᵇ ℝ) : P.infF h ≤ P.supF h :=
  le_trans (P.infF_le h Classical.ofNonempty) (P.le_supF h Classical.ofNonempty)

/-- If every gap is at most `C`, the oscillation is at most `C`. -/
theorem sup_sub_inf_le {h : P.State →ᵇ ℝ} {C : ℝ} (hC : ∀ s t, h s - h t ≤ C) :
    P.supF h - P.infF h ≤ C := by
  have hkey : ∀ s, h s ≤ C + P.infF h := by
    intro s
    have : h s - C ≤ P.infF h :=
      le_ciInf (f := fun t => h t) fun t => by linarith [hC s t]
    linarith
  have : P.supF h ≤ C + P.infF h := ciSup_le hkey
  linarith

/-! ### The Markov operator preserves bounds -/

theorem infF_le_markovOp (h : P.State →ᵇ ℝ) (s : P.State) : P.infF h ≤ P.markovOp h s := by
  rw [P.markovOp_apply]
  calc P.infF h = ∑ z', P.prob s z' * P.infF h := by
        rw [← Finset.sum_mul, P.prob_sum, one_mul]
    _ ≤ ∑ z', P.prob s z' * h (P.nextState s z') :=
        Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_left (P.infF_le h _) (P.prob_nonneg s z')

theorem markovOp_le_supF (h : P.State →ᵇ ℝ) (s : P.State) : P.markovOp h s ≤ P.supF h := by
  rw [P.markovOp_apply]
  calc ∑ z', P.prob s z' * h (P.nextState s z')
      ≤ ∑ z', P.prob s z' * P.supF h :=
        Finset.sum_le_sum fun z' _ =>
          mul_le_mul_of_nonneg_left (P.le_supF h _) (P.prob_nonneg s z')
    _ = P.supF h := by rw [← Finset.sum_mul, P.prob_sum, one_mul]

theorem infF_le_iterate (h : P.State →ᵇ ℝ) (n : ℕ) (s : P.State) :
    P.infF h ≤ (P.markovOp^[n] h) s := by
  induction n generalizing s with
  | zero => exact P.infF_le h s
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (le_ciInf fun t => ih t) (P.infF_le_markovOp _ s)

theorem iterate_le_supF (h : P.State →ᵇ ℝ) (n : ℕ) (s : P.State) :
    (P.markovOp^[n] h) s ≤ P.supF h := by
  induction n generalizing s with
  | zero => exact P.le_supF h s
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (P.markovOp_le_supF _ s) (ciSup_le fun t => ih t)

/-! ### The Doeblin minorization -/

/-- One period under the worst income shock `z₀`. -/
noncomputable def badStep (z₀ : Z) (s : P.State) : P.State := P.nextState s z₀

/-- **Minorization, lower half.** After `n` periods, a share `p₀ⁿ` of the mass sits at the
state reached by `n` consecutive bad shocks, and the rest is worth at least `infF h`. -/
theorem iterate_lower {z₀ : Z} {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀)
    (h : P.State →ᵇ ℝ) (n : ℕ) (s : P.State) :
    p₀ ^ n * h ((P.badStep z₀)^[n] s) + (1 - p₀ ^ n) * P.infF h ≤ (P.markovOp^[n] h) s := by
  classical
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply' P.markovOp n h, P.markovOp_apply,
        Function.iterate_succ_apply (P.badStep z₀) n s, pow_succ]
      have hq0 : 0 ≤ P.prob s z₀ := P.prob_nonneg s z₀
      have hsplit : ∑ z', P.prob s z' * (P.markovOp^[n] h) (P.nextState s z')
          = P.prob s z₀ * (P.markovOp^[n] h) (P.badStep z₀ s)
            + ∑ z' ∈ Finset.univ.erase z₀,
                P.prob s z' * (P.markovOp^[n] h) (P.nextState s z') :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ z₀)).symm
      have hprobrest : ∑ z' ∈ Finset.univ.erase z₀, P.prob s z' = 1 - P.prob s z₀ := by
        have hs := P.prob_sum s
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z₀)] at hs
        linarith
      have hrest : (1 - P.prob s z₀) * P.infF h
          ≤ ∑ z' ∈ Finset.univ.erase z₀,
              P.prob s z' * (P.markovOp^[n] h) (P.nextState s z') := by
        calc (1 - P.prob s z₀) * P.infF h
            = ∑ z' ∈ Finset.univ.erase z₀, P.prob s z' * P.infF h := by
              rw [← Finset.sum_mul, hprobrest]
          _ ≤ _ := Finset.sum_le_sum fun z' _ =>
              mul_le_mul_of_nonneg_left (P.infF_le_iterate h n _) (P.prob_nonneg s z')
      have hIH := mul_le_mul_of_nonneg_left (ih (P.badStep z₀ s)) hq0
      have hHI : P.infF h ≤ h ((P.badStep z₀)^[n] (P.badStep z₀ s)) := P.infF_le h _
      have hgap : 0 ≤ (P.prob s z₀ - p₀) * p₀ ^ n :=
        mul_nonneg (sub_nonneg.mpr (hp s)) (pow_nonneg hp0 n)
      rw [hsplit]
      nlinarith [hIH, hrest, hHI, hgap, pow_nonneg hp0 n, hp s]

/-- **Minorization, upper half.** -/
theorem iterate_upper {z₀ : Z} {p₀ : ℝ} (hp0 : 0 ≤ p₀) (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀)
    (h : P.State →ᵇ ℝ) (n : ℕ) (s : P.State) :
    (P.markovOp^[n] h) s ≤ p₀ ^ n * h ((P.badStep z₀)^[n] s) + (1 - p₀ ^ n) * P.supF h := by
  classical
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply' P.markovOp n h, P.markovOp_apply,
        Function.iterate_succ_apply (P.badStep z₀) n s, pow_succ]
      have hq0 : 0 ≤ P.prob s z₀ := P.prob_nonneg s z₀
      have hsplit : ∑ z', P.prob s z' * (P.markovOp^[n] h) (P.nextState s z')
          = P.prob s z₀ * (P.markovOp^[n] h) (P.badStep z₀ s)
            + ∑ z' ∈ Finset.univ.erase z₀,
                P.prob s z' * (P.markovOp^[n] h) (P.nextState s z') :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ z₀)).symm
      have hprobrest : ∑ z' ∈ Finset.univ.erase z₀, P.prob s z' = 1 - P.prob s z₀ := by
        have hs := P.prob_sum s
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z₀)] at hs
        linarith
      have hrest : ∑ z' ∈ Finset.univ.erase z₀,
            P.prob s z' * (P.markovOp^[n] h) (P.nextState s z')
          ≤ (1 - P.prob s z₀) * P.supF h := by
        calc ∑ z' ∈ Finset.univ.erase z₀,
              P.prob s z' * (P.markovOp^[n] h) (P.nextState s z')
            ≤ ∑ z' ∈ Finset.univ.erase z₀, P.prob s z' * P.supF h :=
              Finset.sum_le_sum fun z' _ =>
                mul_le_mul_of_nonneg_left (P.iterate_le_supF h n _) (P.prob_nonneg s z')
          _ = (1 - P.prob s z₀) * P.supF h := by rw [← Finset.sum_mul, hprobrest]
      have hIH := mul_le_mul_of_nonneg_left (ih (P.badStep z₀ s)) hq0
      have hHI : h ((P.badStep z₀)^[n] (P.badStep z₀ s)) ≤ P.supF h := P.le_supF h _
      have hgap : 0 ≤ (P.prob s z₀ - p₀) * p₀ ^ n :=
        mul_nonneg (sub_nonneg.mpr (hp s)) (pow_nonneg hp0 n)
      rw [hsplit]
      nlinarith [hIH, hrest, hHI, hgap, pow_nonneg hp0 n, hp s]

/-! ### The oscillation contracts -/

/-- **One Doeblin cycle contracts the oscillation** by the factor `1 - p₀ᴺ`. Both households
are compared against the *same* value `h s₀`, which is what `hbad` buys. -/
theorem osc_markovOp_le {z₀ : Z} {s₀ : P.State} {p₀ : ℝ} {N : ℕ} (hp0 : 0 ≤ p₀)
    (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀) (hbad : ∀ s, (P.badStep z₀)^[N] s = s₀)
    (h : P.State →ᵇ ℝ) :
    P.supF (P.markovOp^[N] h) - P.infF (P.markovOp^[N] h)
      ≤ (1 - p₀ ^ N) * (P.supF h - P.infF h) := by
  refine P.sup_sub_inf_le fun s t => ?_
  have hs := P.iterate_upper hp0 hp h N s
  have ht := P.iterate_lower hp0 hp h N t
  rw [hbad s] at hs
  rw [hbad t] at ht
  linarith

theorem osc_cycle_le {z₀ : Z} {s₀ : P.State} {p₀ : ℝ} {N : ℕ} (hp0 : 0 ≤ p₀)
    (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀) (hbad : ∀ s, (P.badStep z₀)^[N] s = s₀)
    (k : ℕ) (h : P.State →ᵇ ℝ) :
    P.supF ((P.markovOp^[N])^[k] h) - P.infF ((P.markovOp^[N])^[k] h)
      ≤ (1 - p₀ ^ N) ^ k * (P.supF h - P.infF h) := by
  have hp1 : p₀ ≤ 1 := le_trans (hp Classical.ofNonempty) (P.prob_le_one _ _)
  have hfac : (0 : ℝ) ≤ 1 - p₀ ^ N := by
    have : p₀ ^ N ≤ 1 := pow_le_one₀ hp0 hp1
    linarith
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      calc P.supF ((P.markovOp^[N])^[k] (P.markovOp^[N] h))
            - P.infF ((P.markovOp^[N])^[k] (P.markovOp^[N] h))
          ≤ (1 - p₀ ^ N) ^ k
              * (P.supF (P.markovOp^[N] h) - P.infF (P.markovOp^[N] h)) := ih _
        _ ≤ (1 - p₀ ^ N) ^ k * ((1 - p₀ ^ N) * (P.supF h - P.infF h)) :=
            mul_le_mul_of_nonneg_left (P.osc_markovOp_le hp0 hp hbad h) (by positivity)
        _ = (1 - p₀ ^ N) ^ (k + 1) * (P.supF h - P.infF h) := by ring

variable [MeasurableSpace Z] [BorelSpace Z]

/-! ### Stationarity is preserved along the iteration -/

theorem integral_iterate_eq {μ : Measure P.State} [IsProbabilityMeasure μ]
    (hμ : P.push μ = μ) (n : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, (P.markovOp^[n] h) s ∂μ = ∫ s, h s ∂μ := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih (P.markovOp h)]
      have hint := P.integral_push μ h
      rw [hμ] at hint
      exact hint.symm

theorem integral_cycle_eq {μ : Measure P.State} [IsProbabilityMeasure μ]
    (hμ : P.push μ = μ) (N k : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, ((P.markovOp^[N])^[k] h) s ∂μ = ∫ s, h s ∂μ := by
  induction k generalizing h with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, P.integral_iterate_eq hμ]

theorem integral_le_supF (μ : Measure P.State) [IsProbabilityMeasure μ] (h : P.State →ᵇ ℝ) :
    ∫ s, h s ∂μ ≤ P.supF h := by
  calc ∫ s, h s ∂μ ≤ ∫ _s, P.supF h ∂μ :=
        integral_mono (h.integrable μ) (integrable_const _) fun s => P.le_supF h s
    _ = P.supF h := by simp

theorem infF_le_integral (μ : Measure P.State) [IsProbabilityMeasure μ] (h : P.State →ᵇ ℝ) :
    P.infF h ≤ ∫ s, h s ∂μ := by
  calc P.infF h = ∫ _s, P.infF h ∂μ := by simp
    _ ≤ ∫ s, h s ∂μ :=
        integral_mono (integrable_const _) (h.integrable μ) fun s => P.infF_le h s

/-! ### Uniqueness -/

/-- **The stationary agent distribution is unique**, given a Doeblin condition: some income
state `z₀` is always reachable with probability at least `p₀ > 0`, and `N` consecutive `z₀`
shocks drive *every* state to the single state `s₀`.

In the income fluctuation problem `s₀` is the borrowing constraint. The atom is what makes a
Doeblin argument possible at all: the asset transition is deterministic, so laws started from
different assets have disjoint supports and no minorization against a spread-out measure can
hold — but they all charge the constraint. -/
theorem stationary_unique {z₀ : Z} {s₀ : P.State} {p₀ : ℝ} {N : ℕ} (hp0 : 0 < p₀)
    (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀) (hbad : ∀ s, (P.badStep z₀)^[N] s = s₀)
    {μ ν : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (hν : P.IsStationary ν) :
    μ = ν := by
  have hp1 : p₀ ≤ 1 := le_trans (hp Classical.ofNonempty) (P.prob_le_one _ _)
  have hεpos : 0 < p₀ ^ N := pow_pos hp0 N
  have hεle : p₀ ^ N ≤ 1 := pow_le_one₀ hp0.le hp1
  have hμ' : P.push (μ : Measure P.State) = (μ : Measure P.State) :=
    congrArg (fun x : ProbabilityMeasure P.State => (x : Measure P.State)) hμ
  have hν' : P.push (ν : Measure P.State) = (ν : Measure P.State) :=
    congrArg (fun x : ProbabilityMeasure P.State => (x : Measure P.State)) hν
  have key : ∀ h : P.State →ᵇ ℝ,
      ∫ s, h s ∂(μ : Measure P.State) = ∫ s, h s ∂(ν : Measure P.State) := by
    intro h
    set D := ∫ s, h s ∂(μ : Measure P.State) - ∫ s, h s ∂(ν : Measure P.State) with hD
    have hbound : ∀ k : ℕ, |D| ≤ (1 - p₀ ^ N) ^ k * (P.supF h - P.infF h) := by
      intro k
      set g := (P.markovOp^[N])^[k] h with hg
      have hμg : ∫ s, g s ∂(μ : Measure P.State) = ∫ s, h s ∂(μ : Measure P.State) :=
        P.integral_cycle_eq hμ' N k h
      have hνg : ∫ s, g s ∂(ν : Measure P.State) = ∫ s, h s ∂(ν : Measure P.State) :=
        P.integral_cycle_eq hν' N k h
      have hgap := P.osc_cycle_le hp0.le hp hbad k h
      have h1 := P.integral_le_supF (μ : Measure P.State) g
      have h2 := P.infF_le_integral (ν : Measure P.State) g
      have h3 := P.integral_le_supF (ν : Measure P.State) g
      have h4 := P.infF_le_integral (μ : Measure P.State) g
      rw [abs_le]
      constructor <;> [linarith; linarith]
    have hlim : Filter.Tendsto
        (fun k : ℕ => (1 - p₀ ^ N) ^ k * (P.supF h - P.infF h)) atTop (𝓝 0) := by
      have : Filter.Tendsto (fun k : ℕ => (1 - p₀ ^ N) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
      simpa using this.mul_const (P.supF h - P.infF h)
    have : |D| ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
    have : D = 0 := by
      have := abs_nonneg D
      have hz : |D| = 0 := le_antisymm ‹|D| ≤ 0› (abs_nonneg D)
      exact abs_eq_zero.mp hz
    linarith [hD ▸ this]
  have hfin : (μ : ProbabilityMeasure P.State).toFiniteMeasure
      = (ν : ProbabilityMeasure P.State).toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq key
  exact ProbabilityMeasure.toMeasure_injective
    (congrArg (fun x : FiniteMeasure P.State => (x : Measure P.State)) hfin)

/-! ### Discharging the Doeblin condition in the model

The abstract condition asks that `N` bad shocks drive *every* state to the borrowing
constraint. Monotonicity of the policy reduces that to the single worst case: if the richest
household is exhausted in `N` periods, everyone is, because the asset map is increasing and
bounded below by zero. -/

/-- The asset map under the worst income shock. -/
noncomputable def gBad (z₀ : Z) (x : ↥(Icc assetFloor assetCap)) : ↥(Icc assetFloor assetCap) :=
  P.nextAssets (x, z₀)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem gBad_mono (z₀ : Z) : Monotone (P.gBad z₀) := fun x y hxy =>
  P.policy_mono x.2 y.2 hxy

/-- The richest state. -/
def topState : ↥(Icc assetFloor assetCap) := ⟨assetCap, ⟨P.assetFloor_le_assetCap, le_rfl⟩⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem le_topState (x : ↥(Icc assetFloor assetCap)) : x ≤ P.topState := x.2.2

/-- The bottom state: the borrowing constraint. -/
def botState : ↥(Icc assetFloor assetCap) := ⟨assetFloor, ⟨le_rfl, P.assetFloor_le_assetCap⟩⟩

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem botState_le (x : ↥(Icc assetFloor assetCap)) : P.botState ≤ x := x.2.1

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **Monotonicity reduces exhaustion to the worst case.** -/
theorem gBad_iterate_eq_bot {z₀ : Z} {N : ℕ} (hexh : (P.gBad z₀)^[N] P.topState = P.botState)
    (x : ↥(Icc assetFloor assetCap)) : (P.gBad z₀)^[N] x = P.botState :=
  le_antisymm (hexh ▸ (P.gBad_mono z₀).iterate N (P.le_topState x)) (P.botState_le _)

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem badStep_iterate_succ (z₀ : Z) (n : ℕ) (s : P.State) :
    (P.badStep z₀)^[n + 1] s = ((P.gBad z₀)^[n] (P.nextAssets s), z₀) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih (P.badStep z₀ s)]
      rfl

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The Doeblin condition holds** once the richest household is exhausted by `N` bad
shocks: after one more period every state has collapsed to the borrowing constraint. -/
theorem badStep_iterate_eq {z₀ : Z} {N : ℕ} (hexh : (P.gBad z₀)^[N] P.topState = P.botState)
    (s : P.State) : (P.badStep z₀)^[N + 1] s = (P.botState, z₀) := by
  rw [P.badStep_iterate_succ z₀ N s, P.gBad_iterate_eq_bot hexh]

/-- **Uniqueness of the stationary agent distribution for the income fluctuation problem.**

The two economic assumptions are that the worst income state `z₀` is reachable from every
income state (`hreach`), and that a household starting with the maximum assets is driven to
the borrowing constraint by `N` consecutive draws of `z₀` (`hexh`). Monotonicity of the
policy then carries the second from the richest household to every household. -/
theorem stationary_unique_of_exhausts {z₀ : Z} {N : ℕ}
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    (hexh : (P.gBad z₀)^[N] P.topState = P.botState)
    {μ ν : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) (hν : P.IsStationary ν) :
    μ = ν := by
  obtain ⟨z₁, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun z => P.transitionMatrix z z₀) ⟨Classical.ofNonempty, Finset.mem_univ _⟩
  exact P.stationary_unique (p₀ := P.transitionMatrix z₁ z₀) (hreach z₁)
    (fun s => hmin _ (Finset.mem_univ _)) (P.badStep_iterate_eq hexh) hμ hν

/-- **Existence and uniqueness together.** -/
theorem existsUnique_isStationary {z₀ : Z} {N : ℕ}
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    (hexh : (P.gBad z₀)^[N] P.topState = P.botState) :
    ∃! μ : ProbabilityMeasure P.State, P.IsStationary μ := by
  obtain ⟨μ, hμ⟩ := P.exists_isStationary
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩
  exact ⟨μ, hμ, fun ν hν => P.stationary_unique_of_exhausts hreach hexh hν hμ⟩

/-! ### Convergence

Uniqueness says there is one stationary distribution; convergence says the economy finds it.
The same oscillation contraction gives both. Iterating the operator flattens any test
function geometrically, and a flat test function cannot tell two distributions apart, so the
iterates of ANY initial distribution become indistinguishable from the stationary one.

This is what makes the stationary distribution computable rather than merely unique: it is
the limit of iterating from wherever you start. -/

theorem integral_pushProb_iterate (μ : ProbabilityMeasure P.State) (m : ℕ) (h : P.State →ᵇ ℝ) :
    ∫ s, h s ∂((P.pushProb^[m] μ : ProbabilityMeasure P.State) : Measure P.State)
      = ∫ s, (P.markovOp^[m] h) s ∂(μ : Measure P.State) := by
  induction m generalizing h with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', P.coe_pushProb, P.integral_push, ih,
        Function.iterate_succ_apply]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- Oscillation cannot grow under the operator. -/
theorem osc_iterate_le (h : P.State →ᵇ ℝ) (j : ℕ) :
    P.supF (P.markovOp^[j] h) - P.infF (P.markovOp^[j] h) ≤ P.supF h - P.infF h := by
  have h1 : P.supF (P.markovOp^[j] h) ≤ P.supF h :=
    ciSup_le fun s => P.iterate_le_supF h j s
  have h2 : P.infF h ≤ P.infF (P.markovOp^[j] h) :=
    le_ciInf fun s => P.infF_le_iterate h j s
  linarith

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- **The oscillation of an iterated test function vanishes.** -/
theorem tendsto_osc_iterate {z₀ : Z} {s₀ : P.State} {p₀ : ℝ} {N : ℕ} (hp0 : 0 < p₀)
    (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀) (hbad : ∀ s, (P.badStep z₀)^[N] s = s₀)
    (h : P.State →ᵇ ℝ) :
    Tendsto (fun m => P.supF (P.markovOp^[m] h) - P.infF (P.markovOp^[m] h)) atTop (𝓝 0) := by
  have hp1 : p₀ ≤ 1 := le_trans (hp Classical.ofNonempty) (P.prob_le_one _ _)
  have hεpos : 0 < p₀ ^ N := pow_pos hp0 N
  have hεle : p₀ ^ N ≤ 1 := pow_le_one₀ hp0.le hp1
  rw [Metric.tendsto_atTop]
  intro γ hγ
  have hlim : Tendsto (fun k : ℕ => (1 - p₀ ^ N) ^ k * (P.supF h - P.infF h)) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith : 1 - p₀ ^ N < 1)
    simpa using this.mul_const (P.supF h - P.infF h)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hγ)).exists
  refine ⟨N * k, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hsplit : P.markovOp^[N * k + j] h = P.markovOp^[j] ((P.markovOp^[N])^[k] h) := by
    rw [add_comm, Function.iterate_add_apply, Function.iterate_mul]
  rw [Real.dist_eq, hsplit, sub_zero,
    abs_of_nonneg (by linarith [P.infF_le_supF (P.markovOp^[j] ((P.markovOp^[N])^[k] h))])]
  exact lt_of_le_of_lt (le_trans (P.osc_iterate_le _ j)
    (P.osc_cycle_le hp0.le hp hbad k h)) hk

/-- **Convergence to the stationary distribution.** From any starting point, the iterates of
the distribution operator converge weakly to the stationary distribution. -/
theorem tendsto_pushProb_iterate {z₀ : Z} {s₀ : P.State} {p₀ : ℝ} {N : ℕ} (hp0 : 0 < p₀)
    (hp : ∀ s : P.State, p₀ ≤ P.prob s z₀) (hbad : ∀ s, (P.badStep z₀)^[N] s = s₀)
    (μ₀ : ProbabilityMeasure P.State) {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    Tendsto (fun m => P.pushProb^[m] μ₀) atTop (𝓝 μ) := by
  have hμ' : P.push (μ : Measure P.State) = (μ : Measure P.State) :=
    congrArg (fun x : ProbabilityMeasure P.State => (x : Measure P.State)) hμ
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun m => ?_)
    (P.tendsto_osc_iterate hp0 hp hbad h)
  -- the gap is at most the oscillation of the iterated test function
  have hleft : ∫ s, h s ∂((P.pushProb^[m] μ₀ : ProbabilityMeasure P.State) : Measure P.State)
      = ∫ s, (P.markovOp^[m] h) s ∂(μ₀ : Measure P.State) := P.integral_pushProb_iterate μ₀ m h
  have hright : ∫ s, h s ∂(μ : Measure P.State)
      = ∫ s, (P.markovOp^[m] h) s ∂(μ : Measure P.State) :=
    (P.integral_iterate_eq hμ' m h).symm
  rw [Real.dist_eq, hleft, hright]
  have h1 := P.integral_le_supF (μ₀ : Measure P.State) (P.markovOp^[m] h)
  have h2 := P.infF_le_integral (μ₀ : Measure P.State) (P.markovOp^[m] h)
  have h3 := P.integral_le_supF (μ : Measure P.State) (P.markovOp^[m] h)
  have h4 := P.infF_le_integral (μ : Measure P.State) (P.markovOp^[m] h)
  rw [abs_le]
  constructor <;> linarith

/-! ### Exhaustion from strict dissaving

`badStep_iterate_eq` takes exhaustion as a hypothesis in the awkward form `gBad^[N] top = bot`
-- an exact hit on the borrowing constraint after a specified number of periods. That is hard
to check directly, and in the earlier calibrations it was obtained only by making the policy
identically zero.

In Açıkgöz's April 2016 author draft, Proposition 5 (printed page 9; proof in Appendix E,
printed page 32) uses two natural facts:
the constraint binds near zero, and assets strictly decline above that at the worst income
state. A continuous strictly declining map on a compact interval has a UNIFORM minimum
decline, so finitely many periods carry the richest household below the threshold, and one
more step pins it to the constraint.

In that edition, Proposition 3 (printed page 8) supplies worst-state decline, while
Proposition 4 (the same page) supplies a finite asset bound. The source is
https://mpra.ub.uni-muenchen.de/71066/1/MPRA_paper_71066.pdf.
The lemma below uses only continuity, binding near the constraint and strict decline on an
already compact interval; the Euler arguments establishing these inputs appear separately.
 -/

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem exists_exhaust_of_decline {z₀ : Z} {a₀ : ℝ} (ha₀ : assetFloor < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc assetFloor a₀, P.policy (a, z₀) = assetFloor)
    (hdecl : ∀ a ∈ Icc a₀ assetCap, P.policy (a, z₀) < a) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState := by
  classical
  -- the minimal decline over the compact interval above the threshold
  have hne : (Icc a₀ assetCap).Nonempty := ⟨a₀, ⟨le_rfl, hle⟩⟩
  have hcont : ContinuousOn (fun a : ℝ => a - P.policy (a, z₀)) (Icc a₀ assetCap) := by
    refine continuousOn_id.sub (P.continuousOn_policy.comp
      (continuous_id.prodMk continuous_const).continuousOn fun a ha => ?_)
    exact ⟨le_trans ha₀.le ha.1, ha.2⟩
  obtain ⟨am, hamem, hamin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  set Δ : ℝ := am - P.policy (am, z₀) with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; linarith [hdecl am hamem]
  have hstep : ∀ a ∈ Icc a₀ assetCap, P.policy (a, z₀) ≤ a - Δ := fun a ha => by
    have h := hamin ha
    rw [Set.mem_ofPred_eq] at h
    rw [hΔdef]
    linarith
  -- after `k` steps either the threshold is reached or assets have fallen by `k·Δ`
  have key : ∀ k : ℕ, (((P.gBad z₀)^[k] P.topState : ↥(Icc assetFloor assetCap)) : ℝ) ≤ a₀ ∨
      (((P.gBad z₀)^[k] P.topState : ↥(Icc assetFloor assetCap)) : ℝ) ≤ assetCap - k * Δ := by
    intro k
    induction k with
    | zero => right; simp [topState]
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        have hval : (((P.gBad z₀) ((P.gBad z₀)^[k] P.topState) :
            ↥(Icc assetFloor assetCap)) : ℝ)
            = P.policy ((((P.gBad z₀)^[k] P.topState : ↥(Icc assetFloor assetCap)) : ℝ), z₀) := rfl
        rcases ih with h | h
        · -- already at or below the threshold: the next step is exactly zero
          left
          rw [hval, hzero _ ⟨((P.gBad z₀)^[k] P.topState).2.1, h⟩]
          exact ha₀.le
        · rcases le_total (((P.gBad z₀)^[k] P.topState : ↥(Icc assetFloor assetCap)) : ℝ) a₀
            with hlow | hhigh
          · left
            rw [hval, hzero _ ⟨((P.gBad z₀)^[k] P.topState).2.1, hlow⟩]
            exact ha₀.le
          · right
            rw [hval]
            have hmem : (((P.gBad z₀)^[k] P.topState : ↥(Icc assetFloor assetCap)) : ℝ)
                ∈ Icc a₀ assetCap := ⟨hhigh, ((P.gBad z₀)^[k] P.topState).2.2⟩
            have hdec := hstep _ hmem
            push_cast
            rw [show assetCap - ((k : ℝ) + 1) * Δ = (assetCap - (k : ℝ) * Δ) - Δ by ring]
            linarith
  -- finitely many steps carry assets below the threshold
  obtain ⟨N, hN⟩ := exists_nat_gt ((assetCap - a₀) / Δ)
  refine ⟨N + 1, ?_⟩
  have hNle : (((P.gBad z₀)^[N] P.topState : ↥(Icc assetFloor assetCap)) : ℝ) ≤ a₀ := by
    rcases key N with h | h
    · exact h
    · rw [div_lt_iff₀ hΔpos] at hN
      linarith
  refine Subtype.ext ?_
  rw [Function.iterate_succ_apply']
  change P.policy ((((P.gBad z₀)^[N] P.topState : ↥(Icc assetFloor assetCap)) : ℝ), z₀)
    = assetFloor
  exact hzero _ ⟨((P.gBad z₀)^[N] P.topState).2.1, hNle⟩

end IncomeFluctuation

end LeanEconomics
