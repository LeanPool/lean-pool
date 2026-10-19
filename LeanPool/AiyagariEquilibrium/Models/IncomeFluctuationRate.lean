/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRegion
public import LeanPool.AiyagariEquilibrium.Distribution.Feller

/-!
# Varying the interest rate

The cross-rate estimates so far take two programmes plus a hypothesis for each field they
must share -- income, maximum income, minimum income, the transition matrix, the discount
factor, the utility function. Six hypotheses is a signal that the wrong object is being
quantified over: in the comparative statics only the INTEREST RATE varies.

`withRate` makes that structural. Every field except `interest` is inherited, so every
sharing hypothesis becomes `rfl` and disappears from the statements, and
`fun r => P.withRate r _` is the family the equilibrium theorem wants.

The other content here is the step that turns the two argument gaps -- in consumption and in
the continuation value -- into a comparison of objectives. It is stated with the gaps as
hypotheses, so the analytic work (uniform continuity) and the arithmetic (extended reals)
stay separate.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- The same household problem at a different interest rate. -/
def withRate (r : ℝ) (hr : P.RateOK r) : IncomeFluctuation Z assetFloor assetCap :=
  { P with interest := r, interest_gt_neg_one := hr.1, minConsumption_le_floor := hr.2 }

@[simp] theorem withRate_interest (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).interest = r := rfl
@[simp] theorem withRate_income (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).income = P.income := rfl
@[simp] theorem withRate_maxIncome (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).maxIncome = P.maxIncome := rfl
@[simp] theorem withRate_minIncome (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).minIncome = P.minIncome := rfl
@[simp] theorem withRate_minConsumption (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).minConsumption = P.minConsumption := rfl
@[simp] theorem withRate_u (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).u = P.u := rfl
@[simp] theorem withRate_discount (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).discount = P.discount := rfl
@[simp] theorem withRate_transitionMatrix (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).transitionMatrix = P.transitionMatrix := rfl
@[simp] theorem withRate_region (r : ℝ) (hr : P.RateOK r) :
    (P.withRate r hr).region = P.region := rfl
@[simp] theorem withRate_loBound (r : ℝ) (hr : P.RateOK r) (v : (ℝ × Z) →ᵇ ℝ) :
    (P.withRate r hr).toExtended.loBound v = P.toExtended.loBound v := rfl

/-- **From argument gaps to an objective comparison.**

The reward is real at both actions because consumption is positive at both -- which is what
the cutoff delivers -- so the extended-real objective collapses to a real one and the
comparison is ordinary arithmetic. Keeping the two gaps as hypotheses separates the analytic
work from the arithmetic. -/
theorem objectiveE_le_of_gaps (v : (ℝ × Z) →ᵇ ℝ) {r r' : ℝ} (hr : P.RateOK r) (hr' : P.RateOK r')
    {s : ℝ × Z} (hs : s ∈ P.region) {a a' : ℝ}
    (ha : a ∈ (P.withRate r hr).toExtended.feasible s)
    (ha' : a' ∈ (P.withRate r' hr').toExtended.feasible s)
    (hcA : 0 < (P.withRate r hr).consumption s a)
    (hcB : 0 < (P.withRate r' hr').consumption s a')
    {e₁ e₂ : ℝ}
    (hu : P.u ((P.withRate r hr).consumption s a)
        - P.u ((P.withRate r' hr').consumption s a') ≤ e₁)
    (hv : (P.withRate r hr).toExtended.expect v (s, a)
        - (P.withRate r' hr').toExtended.expect v (s, a') ≤ e₂) :
    (P.withRate r hr).toExtended.objectiveE v s a
      ≤ (P.withRate r' hr').toExtended.objectiveE v s a'
        + ((e₁ + P.discount * e₂ : ℝ) : EReal) := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hrwA := (P.withRate r hr).reward_eq_coe hs ha hcA
  have hrwB := (P.withRate r' hr').reward_eq_coe hs ha' hcB
  have hdA : ((P.withRate r hr).toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  have hdB : ((P.withRate r' hr').toExtended.discount : ℝ) = (P.discount : ℝ) := rfl
  simp only [ExtendedStochasticProgram.objectiveE, hrwA, hrwB, hdA, hdB]
  rw [← EReal.coe_add, add_assoc, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hu' : (P.withRate r hr).u = P.u := rfl
  have hu'' : (P.withRate r' hr').u = P.u := rfl
  rw [hu', hu''] at *
  nlinarith [hu, hv, hβ]

/-! ### The sup-norm estimate

Everything assembled. Choosing the rate gap small enough makes the Bellman operator move by
less than any prescribed amount, uniformly over the region.

Three separate smallness requirements are imposed on the rate gap, and the `+ 1` in each
constant is only to keep the divisions safe when the asset cap is zero:

* the saving gap must fall under the continuation value's modulus,
* the consumption gap must fall under utility's modulus,
* the consumption gap must be at most `δ/2`, so that consumption at the SECOND rate stays
  positive given that the cutoff bounds it at the first. Without this the reward at the
  second rate could be `⊥` and the comparison would be vacuous.

Actions below the cutoff need no comparison at all: they are already worth less than
`loBound v`, which is itself below the other operator's value. -/

theorem exists_rate_modulus (hd : P.Unbounded) (v : (ℝ × Z) →ᵇ ℝ) {rlo rhi : ℝ}
    (hrlo : 0 < 1 + rlo)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (r r' : ℝ) (hr : P.RateOK r) (hr' : P.RateOK r'),
      rlo ≤ r → r ≤ rhi → rlo ≤ r' → r' ≤ rhi → |r - r'| < η →
      ∀ s ∈ P.region,
        (P.withRate r hr).toExtended.bellmanFn v s
          ≤ (P.withRate r' hr').toExtended.bellmanFn v s + ε := by
  classical
  have hcap := P.assetFloor_le_assetCap
  have hmaxI : 0 ≤ P.maxIncome := le_trans P.minIncome_pos.le P.minIncome_le_maxIncome
  obtain ⟨δ, hδ, hδspec⟩ := P.exists_cutoff hd v
  have hB : 0 ≤ P.stateBoundCross rlo := P.stateBoundCross_nonneg hrlo
  set K₁ : ℝ := P.stateBoundCross rlo + 1 with hK₁def
  set K₂ : ℝ := 2 * P.stateBoundCross rlo + 1 with hK₂def
  have hK₁ : 1 ≤ K₁ := by rw [hK₁def]; linarith
  have hK₂ : 1 ≤ K₂ := by rw [hK₂def]; linarith
  obtain ⟨η₁, hη₁, hmu⟩ :=
    P.exists_modulus_u (lo := δ / 2) (hi := P.maxIncome + (1 + rhi) * assetCap - assetFloor)
      (by linarith) (half_pos hε)
  obtain ⟨η₂, hη₂, hmv⟩ := exists_modulus_v (assetCap := assetCap) v (half_pos hε)
  refine ⟨min (min (η₂ / K₁) (η₁ / K₂)) (δ / (2 * K₂)), by positivity, ?_⟩
  intro r r' hr hr' hlo hhi hlo' hhi' hclose s hs
  set A := P.withRate r hr with hA
  set B := P.withRate r' hr' with hB
  refine A.toExtended.bellmanFn_le v fun a ha => ?_
  -- actions below the cutoff need no comparison
  rcases le_or_gt ((P.toExtended.loBound v : ℝ) : EReal)
      (A.toExtended.objectiveE v s a) with hcut | hbelow
  · -- the matched action at the other rate
    have hafe := ha
    rw [A.feasible_eq_image] at hafe
    obtain ⟨θ, hθ, rfl⟩ := hafe
    set a' : ℝ := (assetFloor + θ * B.savingRoom s) with ha'def
    have ha' : a' ∈ B.toExtended.feasible s := by rw [B.feasible_eq_image]; exact ⟨θ, hθ, rfl⟩
    -- consumption at the first rate is bounded below by the cutoff
    have hcA : δ ≤ A.consumption s ((assetFloor + θ * A.savingRoom s)) :=
      A.le_consumption_of_cutoff v hδspec hs ha hcut
    -- the two consumptions are close, so the second is positive too
    have hgapc : |A.consumption s ((assetFloor + θ * A.savingRoom s)) - B.consumption s a'|
        ≤ |r - r'| * K₂ := by
      have hclamp := abs_clamped_consumption_sub_le (P := A) (Q := B) rfl rfl hrlo hlo hlo' hθ s
      have hA' : min A.maxConsumption (A.consumption s ((assetFloor + θ * A.savingRoom s)))
          = A.consumption s ((assetFloor + θ * A.savingRoom s)) :=
        min_eq_right (A.consumption_le_maxConsumption hs
          (le_add_of_nonneg_right (mul_nonneg hθ.1 (A.savingRoom_nonneg s))))
      have hB' : min B.maxConsumption (B.consumption s a') = B.consumption s a' :=
        min_eq_right (B.consumption_le_maxConsumption hs
          (le_add_of_nonneg_right (mul_nonneg hθ.1 (B.savingRoom_nonneg s))))
      rw [hA', hB'] at hclamp
      rw [show A.stateBoundCross rlo = P.stateBoundCross rlo from rfl] at hclamp
      refine le_trans hclamp ?_
      have hint : |A.interest - B.interest| = |r - r'| := rfl
      rw [hint]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [hK₂def]
      linarith
    have hsmall2 : |r - r'| * K₂ ≤ δ / 2 := by
      have h := lt_of_lt_of_le hclose (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h
      nlinarith [h]
    have hcB : δ / 2 ≤ B.consumption s a' := by
      rw [abs_le] at hgapc; linarith [hgapc.1, hgapc.2]
    -- utility moves little
    have hupper : ∀ {X : IncomeFluctuation Z assetFloor assetCap} {b : ℝ},
        X.consumption s b ≤ X.maxConsumption → X.maxIncome = P.maxIncome →
        X.interest ≤ rhi →
        X.consumption s b ≤ P.maxIncome + (1 + rhi) * assetCap - assetFloor := by
      intro X b hb hmi hint
      have : X.maxConsumption = X.maxIncome + (1 + X.interest) * assetCap - assetFloor := rfl
      rw [this, hmi] at hb
      nlinarith [P.assetCap_nonneg]
    have hgu : |P.u (A.consumption s ((assetFloor + θ * A.savingRoom s)))
        - P.u (B.consumption s a')| < ε / 2 := by
      have hbA := A.consumption_le_maxConsumption hs
        (le_add_of_nonneg_right (mul_nonneg hθ.1 (A.savingRoom_nonneg s)))
      have hbB := B.consumption_le_maxConsumption hs
        (le_add_of_nonneg_right (mul_nonneg hθ.1 (B.savingRoom_nonneg s)))
      refine hmu _ ⟨by linarith, hupper hbA rfl hhi⟩ _ ⟨by linarith, hupper hbB rfl hhi'⟩ ?_
      have h := lt_of_lt_of_le (lt_of_lt_of_le hclose (min_le_left _ _)) (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h
      rw [abs_le] at hgapc
      rw [abs_lt]; constructor <;> linarith [hgapc.1, hgapc.2]
    -- the continuation value moves little
    have hgapa : |(assetFloor + θ * A.savingRoom s) - a'| < η₂ := by
      have hms := abs_maxSaving_sub_le (P := A) (Q := B) rfl rfl hrlo hlo hlo' s
      have hint : |A.interest - B.interest| = |r - r'| := rfl
      rw [hint] at hms
      have h := lt_of_lt_of_le (lt_of_lt_of_le hclose (min_le_left _ _)) (min_le_left _ _)
      rw [lt_div_iff₀ (by linarith)] at h
      rw [ha'def, show assetFloor + θ * A.savingRoom s - (assetFloor + θ * B.savingRoom s)
        = θ * (A.maxSaving s - B.maxSaving s) by simp only [savingRoom]; ring,
        abs_mul, abs_of_nonneg hθ.1]
      calc θ * |A.maxSaving s - B.maxSaving s| ≤ 1 * (|r - r'| * P.stateBoundCross rlo) := by
            refine mul_le_mul hθ.2 hms (abs_nonneg _) (by norm_num)
        _ ≤ |r - r'| * K₁ := by rw [one_mul, hK₁def]; nlinarith [abs_nonneg (r - r')]
        _ < η₂ := h
    have hgv : |A.toExtended.expect v (s, (assetFloor + θ * A.savingRoom s))
        - B.toExtended.expect v (s, a')| ≤ ε / 2 := by
      have hmem : ∀ x : ℝ, x ∈ A.toExtended.feasible s → x ∈ Icc assetFloor assetCap := fun x hx =>
        A.feasible_subset_region hx
      have h1 : (assetFloor + θ * A.savingRoom s) ∈ Icc assetFloor assetCap := hmem _ ha
      have h2 : a' ∈ Icc assetFloor assetCap := B.feasible_subset_region ha'
      have hpA : ∀ z' : Z, A.toExtended.prob z' (s, (assetFloor + θ * A.savingRoom s))
          = P.transitionMatrix s.2 z' := fun _ => rfl
      have hpB : ∀ z' : Z, B.toExtended.prob z' (s, a') = P.transitionMatrix s.2 z' := fun _ => rfl
      have htA : ∀ z' : Z, A.toExtended.transition z' (s, (assetFloor + θ * A.savingRoom s))
          = ((assetFloor + θ * A.savingRoom s), z') := fun _ => rfl
      have htB : ∀ z' : Z, B.toExtended.transition z' (s, a') = (a', z') := fun _ => rfl
      simp only [ExtendedStochasticProgram.expect, hpA, hpB, htA, htB, ← Finset.sum_sub_distrib,
        ← mul_sub]
      calc |∑ z' : Z, P.transitionMatrix s.2 z'
            * (v ((assetFloor + θ * A.savingRoom s), z') - v (a', z'))|
          ≤ ∑ z' : Z, |P.transitionMatrix s.2 z'
            * (v ((assetFloor + θ * A.savingRoom s), z') - v (a', z'))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z' : Z, P.transitionMatrix s.2 z' * (ε / 2) := by
            refine Finset.sum_le_sum fun z' _ => ?_
            rw [abs_mul, abs_of_nonneg (P.transitionMatrix_nonneg s.2 z')]
            exact mul_le_mul_of_nonneg_left (hmv z' _ h1 _ h2 hgapa).le
              (P.transitionMatrix_nonneg s.2 z')
        _ = ε / 2 := by rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
    -- combine
    have hobj := P.objectiveE_le_of_gaps v hr hr' hs ha ha'
      (by linarith) (by linarith)
      (e₁ := ε / 2) (e₂ := ε / 2)
      (by rw [abs_lt] at hgu; linarith [hgu.2])
      (by rw [abs_le] at hgv; linarith [hgv.2])
    refine le_trans hobj ?_
    have hbB := B.toExtended.le_bellmanFn v ha'
    have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
    have hβ0 : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
    calc B.toExtended.objectiveE v s a' + ((ε / 2 + P.discount * (ε / 2) : ℝ) : EReal)
        ≤ ((B.toExtended.bellmanFn v s : ℝ) : EReal)
            + ((ε / 2 + P.discount * (ε / 2) : ℝ) : EReal) := by gcongr
      _ ≤ ((B.toExtended.bellmanFn v s + ε : ℝ) : EReal) := by
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]; nlinarith
  · -- below the cutoff: already worth less than the other operator's value
    refine le_trans hbelow.le ?_
    rw [EReal.coe_le_coe_iff]
    have := (B.toExtended.bellmanFn_bounds v s).1
    have hlb : B.toExtended.loBound v = P.toExtended.loBound v := rfl
    rw [hlb] at this
    linarith

/-- **The value function moves continuously with the interest rate, on the region.**

Stated AT a reference rate rather than between two arbitrary rates, and that is not a
weakening -- it is what makes the argument work. The modulus produced by
`exists_rate_modulus` depends on the continuation value fed to the operator, so comparing two
moving rates would need the family of value functions to be equicontinuous. Fixing the
reference rate makes the continuation value a single fixed function, and continuity at every
point is continuity. -/
theorem exists_valueFunction_modulus (hd : P.Unbounded) {rlo rhi : ℝ} (hrlo : 0 < 1 + rlo)
    {r₀ : ℝ}
    (hr₀ : P.RateOK r₀) (hlo₀ : rlo ≤ r₀) (hhi₀ : r₀ ≤ rhi) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ (r : ℝ) (hr : P.RateOK r), rlo ≤ r → r ≤ rhi → |r - r₀| < η →
      ∀ s ∈ P.region,
        |(P.withRate r hr).toExtended.valueFunction s
          - (P.withRate r₀ hr₀).toExtended.valueFunction s| ≤ ε := by
  have hβ1 : (P.discount : ℝ) < 1 := by exact_mod_cast P.discount_lt_one
  set V₀ := (P.withRate r₀ hr₀).toExtended.valueFunction with hV₀
  obtain ⟨η, hη, hmod⟩ :=
    P.exists_rate_modulus hd V₀ (rlo := rlo) (rhi := rhi) hrlo (ε := ε * (1 - P.discount))
      (by positivity)
  refine ⟨η, hη, fun r hr hlo hhi hclose s hs => ?_⟩
  -- the operator gap at the fixed continuation value, both directions
  have hfix : ∀ t : ℝ × Z, (P.withRate r₀ hr₀).toExtended.bellmanFn V₀ t = V₀ t := fun t => by
    rw [hV₀, ← (P.withRate r₀ hr₀).toExtended.bellman_apply,
      (P.withRate r₀ hr₀).toExtended.bellman_valueFunction]
  have hD : ∀ t : ℝ × Z, t ∈ (P.withRate r hr).region →
      |(P.withRate r hr).toExtended.bellmanFn V₀ t - V₀ t| ≤ ε * (1 - P.discount) := by
    intro t ht
    have h1 := hmod r r₀ hr hr₀ hlo hhi hlo₀ hhi₀ hclose t ht
    have h2 := hmod r₀ r hr₀ hr hlo₀ hhi₀ hlo hhi (by rwa [abs_sub_comm]) t ht
    rw [hfix t] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  -- and the bridge turns it into a bound on the value functions
  have hbr := abs_valueFunction_sub_le_region (P := P.withRate r hr) (Q := P.withRate r₀ hr₀)
    hD hs
  have hdisc : ((P.withRate r hr).discount : ℝ) = (P.discount : ℝ) := rfl
  rw [hdisc] at hbr
  refine le_trans hbr ?_
  rw [div_le_iff₀ (by linarith)]

/-! ### What policy continuity is for

The distribution side consumes the policy only through the Markov operator, and only through
its SUP norm: the closed-graph argument for `r ↦ μ r` needs

  ‖markovOp_r h - markovOp_r₀ h‖ → 0

because `∫ markovOp_r h dμ_r` splits into `∫ (markovOp_r h - markovOp_r₀ h) dμ_r`, bounded by
that norm, plus a term weak convergence handles. Pointwise convergence of the policy would
not do.

The lemma below is the interface: it reduces the operator gap to the gap in the SUCCESSOR
STATES, which is where the policy enters. Combined with uniform continuity of `h` on the
compact state space, uniform convergence of the policy is exactly what is needed, and
nothing more. -/

theorem abs_markovFn_sub_le {A B : IncomeFluctuation Z assetFloor assetCap}
    (hAB : A.transitionMatrix = B.transitionMatrix) (h : A.State →ᵇ ℝ) {ε : ℝ}
    (hclose : ∀ s : A.State, ∀ z' : Z, |h (A.nextState s z') - h (B.nextState s z')| ≤ ε)
    (s : A.State) : |A.markovFn h s - B.markovFn h s| ≤ ε := by
  have hprob : ∀ z' : Z, B.prob s z' = A.prob s z' := fun z' => by
    simp only [IncomeFluctuation.prob, hAB]
  simp only [IncomeFluctuation.markovFn, hprob, ← Finset.sum_sub_distrib, ← mul_sub]
  calc |∑ z' : Z, A.prob s z' * (h (A.nextState s z') - h (B.nextState s z'))|
      ≤ ∑ z' : Z, |A.prob s z' * (h (A.nextState s z') - h (B.nextState s z'))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z' : Z, A.prob s z' * ε := by
        refine Finset.sum_le_sum fun z' _ => ?_
        rw [abs_mul, abs_of_nonneg (A.prob_nonneg s z')]
        exact mul_le_mul_of_nonneg_left (hclose s z') (A.prob_nonneg s z')
    _ = ε := by rw [← Finset.sum_mul, A.prob_sum, one_mul]

end IncomeFluctuation

end LeanEconomics
