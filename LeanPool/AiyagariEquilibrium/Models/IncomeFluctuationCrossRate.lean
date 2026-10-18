/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationBounds


/-!
# Comparing two interest rates

Estimates relating two household problems that share an income process and an asset cap but
differ in the interest rate. These are the cross-rate ingredients of the sup-norm estimate on
the Bellman operator; they are stated for two programs rather than for a family, which is
more flexible and needs no indexing.

They are only expressible at all because `assetCap` is a structure PARAMETER: `P` and `Q`
below have the same type, so their state spaces and feasible sets are directly comparable.

## The trap

The obvious estimate is false as stated. Resources differ by

  resources_P s - resources_Q s = (P.interest - Q.interest) * max 0 s.1

which is UNBOUNDED in the state: a household with enormous assets sees an enormous change in
income from a small change in the rate. A sup-norm estimate over all states cannot come from
this quantity directly.

What rescues it is that the difference is only visible through a clamp. Maximum feasible
saving is `min assetCap resources`, so once resources exceed the cap at BOTH rates the
difference is exactly zero. The difference can be nonzero only where some rate leaves
resources below the cap, and that confines the state: `(1 + r) * max 0 s.1 < assetCap`. So
wherever the estimate is not trivially zero, the offending factor is bounded — by
`assetCap / (1 + rlo)`, with `rlo` any lower bound on the rates considered.

That is the shape every cross-rate estimate here takes: a case split on whether the clamp
binds, trivial on one side, and bounded on the other precisely because the clamp failing to
bind confines the state.
-/

@[expose] public section

open Set BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}

/-- `min c ·` is 1-Lipschitz. A direct corollary of Mathlib's `lipschitzWith_min`. -/
theorem abs_min_sub_min_le (c x y : ℝ) : |min c x - min c y| ≤ |x - y| := by
  have h : LipschitzWith 1 fun t : ℝ => min c t := LipschitzWith.const_min LipschitzWith.id c
  simpa [Real.dist_eq] using h.dist_le_mul x y

/-- Resources differ by the rate gap times assets — a quantity unbounded in the state. -/
theorem resources_sub {P Q : IncomeFluctuation Z assetFloor assetCap} (hinc : P.income = Q.income)
    (s : ℝ × Z) :
    P.resources s - Q.resources s = (P.interest - Q.interest) * max assetFloor s.1 := by
  simp only [resources, hinc]
  ring

/-- The uniform bound on the state coordinate that the confinement lemmas deliver. With a
borrowing limit the coordinate can be negative, so what is bounded is its ABSOLUTE value, and
the limit contributes its own modulus to the constant. -/
noncomputable def stateBoundCross (P : IncomeFluctuation Z assetFloor assetCap) (rlo : ℝ) : ℝ :=
  |assetFloor| + |assetCap| + (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo)

theorem maxIncome_pos (P : IncomeFluctuation Z assetFloor assetCap) : 0 < P.maxIncome :=
  lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome

theorem stateBoundCross_nonneg (P : IncomeFluctuation Z assetFloor assetCap) {rlo : ℝ}
    (hr : 0 < 1 + rlo) : 0 ≤ P.stateBoundCross rlo := by
  have h1 : 0 ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) := by
    have := P.maxIncome_pos
    positivity
  have := abs_nonneg assetFloor
  have := abs_nonneg assetCap
  simp only [stateBoundCross]; linarith

theorem abs_assetCap_le_stateBoundCross (P : IncomeFluctuation Z assetFloor assetCap) {rlo : ℝ}
    (hr : 0 < 1 + rlo) : |assetCap| ≤ P.stateBoundCross rlo := by
  have h1 : 0 ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) := by
    have := P.maxIncome_pos
    positivity
  have := abs_nonneg assetFloor
  simp only [stateBoundCross]; linarith

/-- The elementary division step the two confinement lemmas share. -/
private theorem div_le_div_of_le_denom {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hbc : b ≤ c) : a / c ≤ a / b := by
  rw [div_le_div_iff₀ hc hb]
  nlinarith

/-- **Where the cap fails to bind, the state is confined.** This is what tames the unbounded
factor above. -/
theorem abs_max_le_of_resources_lt {P : IncomeFluctuation Z assetFloor assetCap} {rlo : ℝ}
    (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) {s : ℝ × Z} (hlt : P.resources s < assetCap) :
    |max assetFloor s.1| ≤ P.stateBoundCross rlo := by
  have hp1 : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hy : 0 < P.income s.2 := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le s.2)
  have hres : P.resources s = P.income s.2 + (1 + P.interest) * max assetFloor s.1 := rfl
  have hcapabs := le_abs_self assetCap
  have hfl := abs_nonneg assetFloor
  have hca := abs_nonneg assetCap
  have hmi := P.maxIncome_pos
  have hup : max assetFloor s.1 ≤ |assetCap| / (1 + P.interest) :=
    (le_div_iff₀ hp1).mpr (by linarith)
  have hmono : |assetCap| / (1 + P.interest) ≤ |assetCap| / (1 + rlo) :=
    div_le_div_of_le_denom hca hr hp1 (by linarith)
  have hnum : |assetCap| / (1 + rlo)
      ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) := by
    rw [div_le_div_iff₀ hr hr]
    nlinarith
  have hlow : -|assetFloor| ≤ max assetFloor s.1 :=
    le_trans (neg_abs_le _) (le_max_left _ _)
  have hdiv : 0 ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) := by positivity
  rw [abs_le]
  simp only [stateBoundCross]
  constructor <;> linarith

/-- **The maximum feasible saving moves little when the interest rate does.**

The bound is uniform over the whole state space, which the raw resources gap is not. -/
theorem abs_maxSaving_sub_le {P Q : IncomeFluctuation Z assetFloor assetCap}
    (hinc : P.income = Q.income) (hmi : P.maxIncome = Q.maxIncome)
    {rlo : ℝ} (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) (hQ : rlo ≤ Q.interest) (s : ℝ × Z) :
    |P.maxSaving s - Q.maxSaving s|
      ≤ |P.interest - Q.interest| * P.stateBoundCross rlo := by
  rw [P.maxSaving_eq, Q.maxSaving_eq]
  rcases lt_or_ge (P.resources s) assetCap with hPlt | hPge
  · -- the cap fails to bind at `P`, so the state is confined
    refine le_trans (abs_min_sub_min_le _ _ _) ?_
    rw [resources_sub hinc, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_max_le_of_resources_lt hr hP hPlt) (abs_nonneg _)
  · rcases lt_or_ge (Q.resources s) assetCap with hQlt | hQge
    · -- symmetrically at `Q`
      refine le_trans (abs_min_sub_min_le _ _ _) ?_
      rw [resources_sub hinc, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_max_le_of_resources_lt hr hQ hQlt
      simpa only [stateBoundCross, hmi] using this
    · -- the cap binds at both rates: the difference is exactly zero
      rw [min_eq_left hPge, min_eq_left hQge, sub_self, abs_zero]
      exact mul_nonneg (abs_nonneg _) (P.stateBoundCross_nonneg hr)

/-! ### The clamped consumption gap

Harder than the saving bound in two ways. The clamp LEVEL `maxConsumption` now moves with the
rate too, since it is `maxIncome + (1 + r) * assetCap - assetFloor`; and the chosen saving has
to be carried along, which is where the `θ` reparametrisation earns its place — with the choice
written as the borrowing limit plus a fraction of the saving room, the same `θ` can be fed to
both programs. -/

/-- `min` is 1-Lipschitz in both arguments at once: `lipschitzWith_min` read through the
product's supremum metric. -/
theorem abs_min_sub_min_le_max (A B x y : ℝ) :
    |min A x - min B y| ≤ max |A - B| |x - y| := by
  simpa [Prod.dist_eq, Real.dist_eq] using lipschitzWith_min.dist_le_mul (A, x) (B, y)

/-- The clamp level itself moves with the rate, but only by a bounded amount. -/
theorem abs_maxConsumption_sub {P Q : IncomeFluctuation Z assetFloor assetCap}
    (hmax : P.maxIncome = Q.maxIncome) :
    |P.maxConsumption - Q.maxConsumption| = |P.interest - Q.interest| * |assetCap| := by
  have hexp : P.maxConsumption - Q.maxConsumption
      = (P.interest - Q.interest) * assetCap := by
    simp only [maxConsumption, hmax]; ring
  rw [hexp, abs_mul]

/-- **Where the consumption clamp fails to bind, the state is confined.** The same move as
`abs_max_le_of_resources_lt`, one clamp further along. -/
theorem abs_max_le_of_consumption_lt {P : IncomeFluctuation Z assetFloor assetCap} {rlo : ℝ}
    (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {s : ℝ × Z}
    (hlt : P.consumption s (assetFloor + θ * P.savingRoom s) < P.maxConsumption) :
    |max assetFloor s.1| ≤ P.stateBoundCross rlo := by
  have hp1 : 0 < 1 + P.interest := P.interest_gt_neg_one
  have hmi := P.maxIncome_pos
  have hy : 0 < P.income s.2 := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le s.2)
  have hres : P.resources s = P.income s.2 + (1 + P.interest) * max assetFloor s.1 := rfl
  have hmc : P.maxConsumption = P.maxIncome + (1 + P.interest) * assetCap - assetFloor := rfl
  have hcons : P.consumption s (assetFloor + θ * P.savingRoom s)
      = P.resources s - (assetFloor + θ * P.savingRoom s) := rfl
  have hroom := P.savingRoom_nonneg s
  have hroomle : P.savingRoom s ≤ assetCap - assetFloor := by
    simp only [savingRoom]; linarith [P.maxSaving_le_assetCap s]
  -- saving at most the cap, so consumption is at least resources minus the cap
  have hsav : assetFloor + θ * P.savingRoom s ≤ assetCap := by nlinarith [hθ.1, hθ.2]
  have hcapabs := le_abs_self assetCap
  have hflabs : -assetFloor ≤ |assetFloor| := neg_le_abs _
  have hfl := abs_nonneg assetFloor
  have hca := abs_nonneg assetCap
  have hcapmul : (1 + P.interest) * assetCap ≤ (1 + P.interest) * |assetCap| :=
    mul_le_mul_of_nonneg_left hcapabs hp1.le
  have hstep : (max assetFloor s.1 - |assetCap|) * (1 + P.interest)
      < P.maxIncome + |assetFloor| + |assetCap| := by
    rw [hcons, hres, hmc] at hlt
    nlinarith
  have hlt' : max assetFloor s.1 - |assetCap|
      < (P.maxIncome + |assetFloor| + |assetCap|) / (1 + P.interest) :=
    (lt_div_iff₀ hp1).mpr hstep
  have hdiv : (P.maxIncome + |assetFloor| + |assetCap|) / (1 + P.interest)
      ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) :=
    div_le_div_of_le_denom (by linarith) hr hp1 (by linarith)
  have hlow : -|assetFloor| ≤ max assetFloor s.1 :=
    le_trans (neg_abs_le _) (le_max_left _ _)
  have hdivnn : 0 ≤ (P.maxIncome + |assetFloor| + |assetCap|) / (1 + rlo) := by positivity
  rw [abs_le]
  simp only [stateBoundCross]
  constructor <;> linarith

/-- **The clamped consumption gap.** Uniform over the state space and over the choice `θ`. -/
theorem abs_clamped_consumption_sub_le {P Q : IncomeFluctuation Z assetFloor assetCap}
    (hinc : P.income = Q.income) (hmax : P.maxIncome = Q.maxIncome)
    {rlo : ℝ} (hr : 0 < 1 + rlo) (hP : rlo ≤ P.interest) (hQ : rlo ≤ Q.interest)
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (s : ℝ × Z) :
    |min P.maxConsumption (P.consumption s (assetFloor + θ * P.savingRoom s))
        - min Q.maxConsumption (Q.consumption s (assetFloor + θ * Q.savingRoom s))|
      ≤ |P.interest - Q.interest| * (2 * P.stateBoundCross rlo) := by
  have hgap : (0 : ℝ) ≤ |P.interest - Q.interest| := abs_nonneg _
  have hB : 0 ≤ P.stateBoundCross rlo := P.stateBoundCross_nonneg hr
  have hBQ : Q.stateBoundCross rlo = P.stateBoundCross rlo := by
    simp only [stateBoundCross, hmax]
  -- the gap in unclamped consumption, given a bound on the state
  have hcons : |max assetFloor s.1| ≤ P.stateBoundCross rlo →
      |P.consumption s (assetFloor + θ * P.savingRoom s)
          - Q.consumption s (assetFloor + θ * Q.savingRoom s)|
        ≤ |P.interest - Q.interest| * (2 * P.stateBoundCross rlo) := by
    intro hBd
    have hms := abs_maxSaving_sub_le hinc hmax hr hP hQ s
    have hres := resources_sub hinc s
    have hexp : P.consumption s (assetFloor + θ * P.savingRoom s)
        - Q.consumption s (assetFloor + θ * Q.savingRoom s)
        = (P.resources s - Q.resources s) - θ * (P.maxSaving s - Q.maxSaving s) := by
      simp only [consumption, savingRoom]; ring
    rw [hexp, hres]
    have h1 : |(P.interest - Q.interest) * max assetFloor s.1|
        ≤ |P.interest - Q.interest| * P.stateBoundCross rlo := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hBd hgap
    have h2 : |θ * (P.maxSaving s - Q.maxSaving s)|
        ≤ |P.interest - Q.interest| * P.stateBoundCross rlo := by
      rw [abs_mul, abs_of_nonneg hθ.1]
      calc θ * |P.maxSaving s - Q.maxSaving s|
          ≤ 1 * |P.maxSaving s - Q.maxSaving s| :=
            mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)
        _ = |P.maxSaving s - Q.maxSaving s| := one_mul _
        _ ≤ _ := hms
    have h3 := abs_sub (((P.interest - Q.interest) * max assetFloor s.1))
      (θ * (P.maxSaving s - Q.maxSaving s))
    nlinarith [h1, h2, h3]
  -- the clamp-level gap is always available as a bound
  have hlevel : |P.maxConsumption - Q.maxConsumption|
      ≤ |P.interest - Q.interest| * (2 * P.stateBoundCross rlo) := by
    rw [abs_maxConsumption_sub hmax]
    refine mul_le_mul_of_nonneg_left ?_ hgap
    linarith [P.abs_assetCap_le_stateBoundCross hr]
  rcases le_or_gt P.maxConsumption (P.consumption s (assetFloor + θ * P.savingRoom s))
    with hPge | hPlt
  · rcases le_or_gt Q.maxConsumption (Q.consumption s (assetFloor + θ * Q.savingRoom s))
      with hQge | hQlt
    · -- BOTH clamps bind, so the two operators see the same clamped value and the
      -- unclamped gap -- which may be enormous -- is invisible
      rw [min_eq_left hPge, min_eq_left hQge]
      exact hlevel
    · -- `Q`'s clamp fails to bind, which confines the state
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le hlevel ?_)
      refine hcons ?_
      have := abs_max_le_of_consumption_lt hr hQ hθ hQlt
      rwa [hBQ] at this
  · -- `P`'s clamp fails to bind, which confines the state
    refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le hlevel ?_)
    exact hcons (abs_max_le_of_consumption_lt hr hP hθ hPlt)

/-! ### Assembling: from pointwise bounds to a bound on the supremum

The sup-norm estimate compares two suprema, and the reparametrisation has already made them
suprema over the SAME set `[0,1]`. What remains is to get from a bound on the objectives to a
bound on their suprema.

A naive pointwise bound would not do, and the reason is worth stating. Where consumption is
tiny but positive, `u` of the two consumptions can differ by an arbitrary amount however close
the rates are, because `u` falls to `-∞`; so

  ∀ θ, objective_P θ ≤ objective_Q θ + ε

is FALSE. Those actions are dominated -- consuming almost nothing is far worse than the
always-available choice `θ = 0` -- so they cannot affect either supremum, but a pointwise
statement cannot see that.

The cutoff `L` is what encodes it. The hypothesis is only required at actions worth at least
`L`, and `L` is separately known to sit below the other program's supremum. Actions below `L`
are then bounded by `L` itself and need no comparison at all. In use, `L` will be the value of
`θ = 0`, which both programs have available. -/

theorem maxE_le_of_pointwise {P Q : IncomeFluctuation Z assetFloor assetCap} (v : (ℝ × Z) →ᵇ ℝ)
    (s : ℝ × Z) (L : EReal) (ε : EReal)
    (hL : L ≤ Q.toExtended.maxE v s + ε)
    (h : ∀ θ ∈ Icc (0 : ℝ) 1,
      L ≤ P.toExtended.objectiveE v s (assetFloor + θ * P.savingRoom s) →
      P.toExtended.objectiveE v s (assetFloor + θ * P.savingRoom s)
        ≤ Q.toExtended.objectiveE v s (assetFloor + θ * Q.savingRoom s) + ε) :
    P.toExtended.maxE v s ≤ Q.toExtended.maxE v s + ε := by
  rw [P.maxE_eq_sSup_unit]
  refine sSup_le ?_
  rintro x ⟨θ, hθ, rfl⟩
  rcases le_or_gt L (P.toExtended.objectiveE v s (assetFloor + θ * P.savingRoom s))
    with hge | hlt
  · -- worth at least the cutoff: the pointwise hypothesis applies
    refine le_trans (h θ hθ hge) ?_
    have hmem : assetFloor + θ * Q.savingRoom s ∈ Q.toExtended.feasible s := by
      rw [Q.feasible_eq_image]; exact ⟨θ, hθ, rfl⟩
    gcongr
    exact le_maxValueE hmem
  · -- below the cutoff: dominated, and bounded by the cutoff itself
    exact le_trans hlt.le hL

end IncomeFluctuation

end LeanEconomics
