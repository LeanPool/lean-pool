/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Equilibrium.Firm
public import LeanPool.AiyagariEquilibrium.Equilibrium.PositiveCapital
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationConsumption
public import LeanPool.AiyagariEquilibrium.Models.MinimalMPC


/-!
# The sign change, both ends

`Equilibrium.Firm` proved the LOW end of the sign change — capital demand diverges as the rate
approaches `-δ`, while capital supply can never exceed the asset cap — and recorded that the HIGH
end was open, needing `capitalDemand δ rhi ≤ S rhi` and hence `S rhi > 0`, which it called
"obvious economically and unproved here".

That is now proved. `PositiveCapital` gives strictly positive capital supply, and what remains is
to make the bound QUANTITATIVE: the sign change needs a number, not merely positivity, because
`rhi` has to be chosen from it. `le_aggregateCapital` supplies the number from a uniform lower
bound on saving, and `exists_capitalDemand_le` is the mirror of `exists_capitalDemand_ge` —
Cobb–Douglas demand vanishes at high rates, so any positive supply floor is eventually met.

`exists_sign_change` then brackets the equilibrium from two-sided bounds on capital supply, and
`exists_equilibrium_of_bounds` hands the bracket to `exists_aiyagari_equilibrium`.

## What is still assumed, and it is no longer the demand side

The bounds `m ≤ S r ≤ M` are required at every rate. The upper one is free, from
`aggregateCapital_le`.
The lower one is the live hypothesis: `PositiveCapital` proves it at a rate, and making it uniform
over an interval wide enough for the curves to cross is what the crude constants make hard — the
decline condition alone needs `ε > r/(1+r)`, and with `ε ≈ 0.27` that caps the interval near
`r = 0.37`. So the remaining obstruction is a QUANTITATIVE one about the household side, not a
structural gap in the equilibrium argument.
-/

@[expose] public section

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-- **Capital demand vanishes at high rates.** The mirror of `exists_capitalDemand_ge`, and what
makes the high end of the sign change a theorem. -/
theorem exists_capitalDemand_le (A δ : ℝ) {m : ℝ} (hm : 0 < m) (r₀ : ℝ) :
    ∃ rhi : ℝ, r₀ ≤ rhi ∧ 0 < rhi + δ ∧ capitalDemand A δ rhi ≤ m := by
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  set t : ℝ := (|A| + 1) / (2 * Real.sqrt m) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  refine ⟨max r₀ (t - δ), le_max_left _ _, ?_, ?_⟩
  · have := le_max_right r₀ (t - δ)
    linarith
  · have hge : t ≤ max r₀ (t - δ) + δ := by
      have := le_max_right r₀ (t - δ); linarith
    have hpos : 0 < max r₀ (t - δ) + δ := lt_of_lt_of_le ht0 hge
    have hts : t ^ 2 * (4 * m) = (|A| + 1) ^ 2 := by
      rw [ht]
      field_simp
      rw [Real.sq_sqrt hm.le]
      ring
    have hsqle : t ^ 2 ≤ (max r₀ (t - δ) + δ) ^ 2 := by nlinarith [hge, ht0.le]
    have hA : A ^ 2 ≤ (|A| + 1) ^ 2 := by nlinarith [abs_nonneg A, sq_abs A]
    simp only [capitalDemand]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsqle, hm, hts, hA]

/-- **The sign change, from two-sided bounds on capital supply.** -/
theorem exists_sign_change (δ : ℝ) {S : ℝ → ℝ} {m M : ℝ} (hm : 0 < m)
    (hlb : ∀ r, m ≤ S r) (hub : ∀ r, S r ≤ M) :
    ∃ rlo rhi : ℝ, 0 < rlo + δ ∧ rlo ≤ rhi ∧ S rlo ≤ capitalDemand 1 δ rlo
      ∧ capitalDemand 1 δ rhi ≤ S rhi := by
  have hM : 0 ≤ M := le_trans hm.le (le_trans (hlb 0) (hub 0))
  obtain ⟨rlo, hrlo, hD⟩ := exists_capitalDemand_ge δ hM
  obtain ⟨rhi, hge, _, hD'⟩ := exists_capitalDemand_le 1 δ hm rlo
  exact ⟨rlo, rhi, hrlo, hge, le_trans (hub rlo) hD, le_trans hD' (hlb rhi)⟩

/-- **The firm can be calibrated to the households**, rather than the other way round. Given any
rate interval and any two-sided bound on capital supply, some productivity and depreciation put
capital demand above supply at the low end and below it at the high end.

This is what the productivity parameter buys. With `A` fixed at one the demand schedule carries a
scale of its own, and the household economy has to be stretched — in practice to absurd
depreciation rates — for the curves to meet. Here `A` sets the scale and `δ` the curvature, and
the construction is explicit: `η = d √m / (√M + √m)` with `d = rhi - rlo`, then `δ = η - rlo` and
`A = 2 η √M`, at which the low end holds with EQUALITY. -/
theorem exists_firm_of_bounds {rlo rhi m M : ℝ} (hlt : rlo < rhi) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < rlo + δ ∧ M ≤ capitalDemand A δ rlo ∧ capitalDemand A δ rhi ≤ m := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  set sm : ℝ := Real.sqrt m with hsmdef
  set sM : ℝ := Real.sqrt M with hsMdef
  have hsm0 : 0 < sm := Real.sqrt_pos.mpr hm
  have hsM0 : 0 < sM := Real.sqrt_pos.mpr hM
  have hsm2 : sm ^ 2 = m := Real.sq_sqrt hm.le
  have hsM2 : sM ^ 2 = M := Real.sq_sqrt hM.le
  set d : ℝ := rhi - rlo with hddef
  have hd0 : 0 < d := by rw [hddef]; linarith
  set η : ℝ := d * sm / (sM + sm) with hηdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηkey : η * (sM + sm) = d * sm := by rw [hηdef]; field_simp
  refine ⟨2 * η * sM, η - rlo, by positivity, by linarith, ?_, ?_⟩
  · have hr : rlo + (η - rlo) = η := by ring
    simp only [capitalDemand, hr]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsM2, hη0]
  · have hr : rhi + (η - rlo) = d + η := by rw [hddef]; ring
    have hkey : η * sM ≤ sm * (d + η) := by nlinarith [hηkey, hη0, hsm0]
    have hsq : (η * sM) ^ 2 ≤ (sm * (d + η)) ^ 2 := by
      nlinarith [hkey, mul_pos hη0 hsM0, mul_pos hsm0 (by linarith : (0 : ℝ) < d + η)]
    simp only [capitalDemand, hr]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsq, hsM2, hsm2]


namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
-- Stated at a zero borrowing limit: the quantitative saving bounds and Light's rescaling
-- that these results rest on are proved there.
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **A quantitative lower bound on capital supply.** Households in income state `z₁` save at
least `ε`, the stationary distribution puts at least `p₀` of its mass there, and capital is mean
saving — so capital is at least `ε p₀`. Positivity alone would not do: the sign change needs a
number from which to choose `rhi`. -/
theorem le_aggregateCapital {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ)
    {z₁ : Z} {p₀ ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hpol : ∀ a ∈ Icc (0 : ℝ) assetCap, ε ≤ P.policy (a, z₁)) :
    ε * p₀ ≤ P.aggregateCapital μ := by
  rw [P.aggregateCapital_eq_integral_policy hμ]
  have hbound : ∀ s : P.State, ε * P.incomeIndicator z₁ s ≤ P.policyCoord s := by
    intro s
    by_cases hz : s.2 = z₁
    · have hge := hpol _ (s.1.2 : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap)
      have hind : P.incomeIndicator z₁ s = 1 := by simp [hz]
      have hpc : P.policyCoord s = P.policy ((s.1 : ℝ), s.2) := rfl
      rw [hind, mul_one, hpc, hz]
      exact hge
    · have hind : P.incomeIndicator z₁ s = 0 := by simp [hz]
      rw [hind, mul_zero]
      exact (P.policy_mem_region (P.incl s)).1
  calc ε * p₀ ≤ ε * ∫ s, P.incomeIndicator z₁ s ∂(μ : Measure P.State) :=
        mul_le_mul_of_nonneg_left (P.le_integral_incomeIndicator hμ hp) hε
    _ = ∫ s, ε * P.incomeIndicator z₁ s ∂(μ : Measure P.State) := (integral_const_mul _ _).symm
    _ ≤ ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
        integral_mono (((P.incomeIndicator z₁).integrable _).const_mul ε)
          (P.policyCoord.integrable _) hbound

/-- **The supply floor, in primitives.** Combining the quantitative saving bound with the
primitive bound on the continuation's gain: every stationary distribution carries at least
`h/2 · p₀` of capital. -/
theorem le_aggregateCapital_of_gain (hpc : P.PositiveConsumption) (hu : P.u = Real.log)
    {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ h : ℝ} (hh0 : 0 < h)
    (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hgain : Real.log (P.income z₁ / (P.income z₁ - h))
      < P.discount * (P.transitionMatrix z₁ z₀ * Real.log (1 + (1 + P.interest) * (h / 2)
          / (P.income z₀ + (1 + P.interest) * (h / 2))))) :
    h / 2 * p₀ ≤ P.aggregateCapital μ := by
  refine P.le_aggregateCapital hμ (by linarith) hp fun a ha => ?_
  refine P.policy_ge_of_gain rfl hpc hu z₁ hh0 hhcap hhinc ?_ ha
  refine lt_of_lt_of_le hgain (mul_le_mul_of_nonneg_left ?_ P.discount.coe_nonneg)
  have hhalf : h / 2 ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, by linarith⟩
  have hfull : h ∈ Icc (0 : ℝ) assetCap := ⟨hh0.le, hhcap⟩
  have hgen := P.log_cont_sub_ge_gen rfl hpc hu z₁ z₀ hhalf hfull (by linarith)
  rw [show h - h / 2 = h / 2 from by ring] at hgen
  exact hgen

/-! ### The equilibrium, from uniqueness and a floor

Everything the equilibrium theorem wants is now available on the household side: uniqueness of the
stationary distribution at each rate (from the uniform corner and decline conditions) and a
positive floor under capital supply (from the gain condition, checked at the low end). This
assembles them.

The selection `ν` is built by choosing the unique stationary distribution at the CLAMPED rate, so
it is defined at every real number while agreeing with the intended one on the interval — the same
device `rateFamily` uses, and for the same reason. Uniqueness then gives both halves of what
`exists_equilibrium_of_selection` asks: that `ν r` is stationary, and that nothing else is.

`exists_equilibrium_of_technology` is the primitive statement: the technology `(A, δ)` is GIVEN,
and two inequalities on it — enough demand at `rlo` to clear the asset cap, little enough at `rhi`
to fall under the supply floor — deliver the equilibrium.
`exists_equilibrium_of_uniqueness_and_floor` is then the corollary in which the firm is chosen
last, by `exists_firm_of_bounds`, from the supply floor `m` and the asset cap.
-/

omit [MeasurableSpace Z] [BorelSpace Z] in
theorem withRate_congr {a b : ℝ} (hab : a = b) (h₁ : P.RateOK a) (h₂ : P.RateOK b) :
    P.withRate a h₁ = P.withRate b h₂ := by
  subst hab; rfl

/-- **The same for any continuous demand schedule.** The ceiling at `rlo` and the floor at
`rhi` are compared with `D` there; the selection of stationary distributions supplies the
continuity of supply in between. -/
theorem exists_equilibrium_of_ceiling_and_floor_of_demand {rlo rhi : ℝ} (hrlo : 0 < 1 + rlo)
    (hlt : rlo < rhi)
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    {m M : ℝ}
    (hceil : ∀ hrlo' : P.RateOK rlo, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rlo hrlo').IsStationary μ → P.aggregateCapital μ ≤ M)
    (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ)
    (D : ℝ → ℝ) (hD : ContinuousOn D (Icc rlo rhi)) (hDlo : M ≤ D rlo) (hDhi : D rhi ≤ m) :
    ∃ r ∈ Icc rlo rhi, IsAiyagariEquilibrium (P.rateFamily hrlo hlt.le) D r := by
  classical
  have hle : rlo ≤ rhi := hlt.le
  have hclamp : ∀ r : ℝ, clampRate rlo rhi r ∈ Icc rlo rhi := clampRate_mem hle
  have hpos : ∀ r : ℝ, P.RateOK (clampRate rlo rhi r) :=
    fun r => rateOK_of_floor_zero (one_add_clampRate_pos hrlo hle r)
  have hE : ∀ r : ℝ, ∃! μ : ProbabilityMeasure P.State,
      (P.withRate (clampRate rlo rhi r) (hpos r)).IsStationary μ :=
    fun r => huniq _ (hclamp r) (hpos r)
  set ν : ℝ → ProbabilityMeasure P.State := fun r => (hE r).choose with hνdef
  have hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r) := by
    intro r hr hrr
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    rw [← P.withRate_congr hc (hpos r) hrr]
    exact (hE r).choose_spec.1
  have hunique : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r := by
    intro r hr hrr μ hμ
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    refine (hE r).choose_spec.2 μ ?_
    rw [P.withRate_congr hc (hpos r) hrr]
    exact hμ
  have hlo' : rlo ∈ Icc rlo rhi := ⟨le_rfl, hle⟩
  have hhi' : rhi ∈ Icc rlo rhi := ⟨hle, le_rfl⟩
  have hrlo' : P.RateOK rlo := rateOK_of_floor_zero hrlo
  have hrhi : P.RateOK rhi := rateOK_of_floor_zero (by linarith)
  have hub : P.aggregateCapital (ν rlo) ≤ M := hceil hrlo' _ (hν rlo hlo' hrlo')
  have hlbhi : m ≤ P.aggregateCapital (ν rhi) := hfloor hrhi _ (hν rhi hhi' hrhi)
  exact P.exists_equilibrium_of_selection hrlo hle ν hν hunique D hD
    (le_trans hub hDlo) (le_trans hDhi hlbhi)

/-- **An Aiyagari equilibrium with the technology GIVEN.** The firm is no longer chosen to fit
the household: any `(A, δ)` whose demand clears the asset cap at the bottom of the interval and
falls below the supply floor at the top produces an equilibrium inside it.

The two hypotheses are inequalities on the technology and nothing else — `le_capitalDemand_of_sq`
and `capitalDemand_le_of_sq` turn them into `4(rlo+δ)²·assetCap ≤ A²` and
`A² ≤ 4(rhi+δ)²·m`, which is the band `2(rlo+δ)√assetCap ≤ A ≤ 2(rhi+δ)√m`. Such an `A` exists
exactly when `(rlo+δ)√assetCap ≤ (rhi+δ)√m`, so the band is non-empty for small `δ` whenever the
household has a positive supply floor: that is the content of
`exists_equilibrium_of_uniqueness_and_floor`, which is now a corollary.

Note which bound is used where. The ceiling is the free one, `aggregateCapital_le`; only the floor
`m` is household work. -/
theorem exists_equilibrium_of_ceiling_and_floor {rlo rhi : ℝ} (hrlo : 0 < 1 + rlo)
    (hlt : rlo < rhi)
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    {m M : ℝ}
    (hceil : ∀ hrlo' : P.RateOK rlo, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rlo hrlo').IsStationary μ → P.aggregateCapital μ ≤ M)
    (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ)
    (A δ : ℝ) (hδ : 0 < rlo + δ)
    (hDlo : M ≤ capitalDemand A δ rlo) (hDhi : capitalDemand A δ rhi ≤ m) :
    ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium (P.rateFamily hrlo hlt.le) (capitalDemand A δ) r :=
  P.exists_equilibrium_of_ceiling_and_floor_of_demand hrlo hlt huniq hceil hfloor
    (capitalDemand A δ) (continuousOn_capitalDemand hδ) hDlo hDhi

/-- **The same with the free ceiling.** Capital supply can never exceed the asset cap, so a
technology that clears the cap at `rlo` needs no household-side ceiling at all. This is the form
every witness used before `crra_aggregateCapital_le_of_minMPC` gave a sharper one. -/
theorem exists_equilibrium_of_technology {rlo rhi : ℝ} (hrlo : 0 < 1 + rlo) (hlt : rlo < rhi)
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    {m : ℝ}
    (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ)
    (A δ : ℝ) (hδ : 0 < rlo + δ)
    (hDlo : assetCap ≤ capitalDemand A δ rlo) (hDhi : capitalDemand A δ rhi ≤ m) :
    ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium (P.rateFamily hrlo hlt.le) (capitalDemand A δ) r :=
  P.exists_equilibrium_of_ceiling_and_floor hrlo hlt huniq
    (fun _ μ _ => P.aggregateCapital_le μ) hfloor A δ hδ hDlo hDhi


/-- **An Aiyagari equilibrium from household-side hypotheses alone.** Uniqueness of the stationary
distribution at each rate, and a positive floor under capital supply AT THE TOP OF THE INTERVAL,
suffice: the firm is then calibrated to meet them.

The floor is needed only at `rhi`, which matters: `gain_term_mono` says the gain condition is
easier at higher rates, so the floor may be taken at the best rate rather than the worst. -/
theorem exists_equilibrium_of_uniqueness_and_floor {rlo rhi : ℝ} (hrlo : 0 < 1 + rlo)
    (hlt : rlo < rhi)
    (huniq : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r,
      ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ)
    {m : ℝ} (hm : 0 < m)
    (hfloor : ∀ hrhi : P.RateOK rhi, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate rhi hrhi).IsStationary μ → m ≤ P.aggregateCapital μ) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < rlo + δ ∧ ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium (P.rateFamily hrlo hlt.le) (capitalDemand A δ) r := by
  classical
  have hle : rlo ≤ rhi := hlt.le
  have hrhi : P.RateOK rhi := rateOK_of_floor_zero (by linarith)
  -- the household side supplies the two numbers the firm has to be squeezed between
  obtain ⟨μ₀, hμ₀⟩ := (huniq rhi ⟨hle, le_rfl⟩ hrhi).exists
  have hmM : m ≤ assetCap :=
    le_trans (hfloor hrhi μ₀ hμ₀) (P.aggregateCapital_le _)
  obtain ⟨A, δ, hA, hrδ, hDlo, hDhi⟩ := exists_firm_of_bounds hlt hm hmM
  exact ⟨A, δ, hA, hrδ,
    P.exists_equilibrium_of_technology hrlo hlt huniq hfloor A δ hrδ hDlo hDhi⟩


/-- **Capital supply is bounded above by the impatience of the household.** Every household saves
at most `1 - ε` of its resources, capital is mean saving, and resources are income plus the return
on capital — so the bound closes on itself.

This is the quantitative form of "assets are small when the household is impatient", and it blows
up exactly as `(1-ε)(1+r) → 1`, which is where the household stops running its assets down. -/
theorem aggregateCapital_le_of_consumption_bound {μ : ProbabilityMeasure P.State}
    (hμ : P.IsStationary μ) {ε : ℝ} (hε1 : ε ≤ 1)
    (hlt : (1 - ε) * (1 + P.interest) < 1)
    (hlb : ∀ (z : Z), ∀ a ∈ Icc (0 : ℝ) assetCap, ε * P.resources (a, z) ≤ P.consumptionFn z a) :
    P.aggregateCapital μ ≤ (1 - ε) * P.maxIncome / (1 - (1 - ε) * (1 + P.interest)) := by
  have hε0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have hr : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  set K : ℝ := P.aggregateCapital μ with hKdef
  have hK : K = ∫ s, P.policyCoord s ∂(μ : Measure P.State) :=
    P.aggregateCapital_eq_integral_policy hμ
  have hA : ∫ s, P.assetCoord s ∂(μ : Measure P.State) = K := rfl
  have hbound : ∀ s : P.State, P.policyCoord s
      ≤ (1 - ε) * P.maxIncome + (1 - ε) * (1 + P.interest) * P.assetCoord s := by
    intro s
    have hmem : ((s.1 : ℝ)) ∈ Icc (0 : ℝ) assetCap := s.1.2
    have hlbs := hlb s.2 _ hmem
    have hres : P.resources ((s.1 : ℝ), s.2) = P.income s.2 + (1 + P.interest) * (s.1 : ℝ) := by
      simp only [resources, max_eq_right hmem.1]
    have hpol : P.policyCoord s
        = P.resources ((s.1 : ℝ), s.2) - P.consumptionFn s.2 (s.1 : ℝ) := by
      simp only [policyCoord_apply, incl, consumptionFn, consumption]; ring
    have hinc : P.income s.2 ≤ P.maxIncome := P.le_maxIncome _
    have hacoord : P.assetCoord s = (s.1 : ℝ) := rfl
    rw [hpol, hres, hacoord]
    rw [hres] at hlbs
    nlinarith [hlbs, hinc, hε0, hr, hmem.1]
  have hsplit : ∫ s, ((1 - ε) * P.maxIncome + (1 - ε) * (1 + P.interest) * P.assetCoord s)
        ∂(μ : Measure P.State)
      = (1 - ε) * P.maxIncome + (1 - ε) * (1 + P.interest) * K := by
    have hprob : IsProbabilityMeasure (μ : Measure P.State) := μ.2
    rw [integral_add (integrable_const _) ((P.assetCoord.integrable _).const_mul _)]
    have h1 : ∫ _s : P.State, (1 - ε) * P.maxIncome ∂(μ : Measure P.State)
        = (1 - ε) * P.maxIncome := by simp
    have h2 : ∫ s, (1 - ε) * (1 + P.interest) * P.assetCoord s ∂(μ : Measure P.State)
        = (1 - ε) * (1 + P.interest) * K := by rw [integral_const_mul, hA]
    rw [h1, h2]
  have hint : ∫ s, P.policyCoord s ∂(μ : Measure P.State)
      ≤ (1 - ε) * P.maxIncome + (1 - ε) * (1 + P.interest) * K := by
    rw [← hsplit]
    exact integral_mono (P.policyCoord.integrable _)
      ((integrable_const _).add ((P.assetCoord.integrable _).const_mul _)) hbound
  rw [← hK] at hint
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hint]

/-- **A quantitative ceiling on capital supply, from primitives.** The minimal-MPC bound says the
household consumes at least the share `κ` of cash on hand; feeding that to
`aggregateCapital_le_of_consumption_bound` replaces the asset cap, which is bookkeeping, by a
number the calibration determines. The denominator is `1 - Þ`, so the ceiling blows up exactly as
the household stops being impatient. -/
theorem crra_aggregateCapital_le_of_minMPC {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcapit : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    P.aggregateCapital μ
      ≤ (1 - P.minMPC γ) * P.maxIncome / (1 - (1 - P.minMPC γ) * (1 + P.interest)) := by
  refine P.aggregateCapital_le_of_consumption_bound hμ
    (IncomeFluctuation.minMPC_le_one hγ0 hβ) ?_ ?_
  · rw [IncomeFluctuation.one_sub_minMPC_mul]
    exact IncomeFluctuation.patience_lt_one hγ0 hβR
  · exact fun z a ha => P.crra_minMPC_mul_le_consumptionFn hγ0 hu rfl hκ hβ hβR hpos hcapit z ha

/-- **The ceiling for shifted CRRA.** The subsistence level enters through `minMPCShare`, which
charges the constant in `κ(η+m) ≤ η+c` against the smallest cash on hand there can be. At `η = 0`
it is the CRRA statement. -/
theorem hara_aggregateCapital_le_of_minMPC {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hκ : 0 < P.minMPC γ) (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hshare : (1 - P.minMPCShare γ η) * (1 + P.interest) < 1)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hcapit : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) :
    P.aggregateCapital μ
      ≤ (1 - P.minMPCShare γ η) * P.maxIncome
        / (1 - (1 - P.minMPCShare γ η) * (1 + P.interest)) := by
  refine P.aggregateCapital_le_of_consumption_bound hμ ?_ hshare ?_
  · have hκ : P.minMPC γ ≤ 1 := IncomeFluctuation.minMPC_le_one hγ0 hβ
    have hy : 0 < P.minIncome := P.minIncome_pos
    have : (0 : ℝ) ≤ (1 - P.minMPC γ) * η / P.minIncome := by
      apply div_nonneg (mul_nonneg (by linarith) hη) hy.le
    simp only [IncomeFluctuation.minMPCShare]
    linarith
  · exact fun z a ha =>
      P.hara_minMPCShare_mul_le_consumptionFn hγ0 hη hu rfl hκ hβ hβR hpos hcapit z ha

end IncomeFluctuation

/-! ### Uniformity in the interest rate

The supply floor has to hold at every rate in the interval, and the gain condition is MONOTONE in
the rate: raising `r` raises `(1+r) t / (y₀ + (1+r) t)` towards one, so the right-hand side grows
while the left does not move. Checking the condition at the LOW end of the interval therefore
covers all of it. -/


theorem gain_term_mono {y₀ t : ℝ} (hy₀ : 0 < y₀) (ht : 0 < t) {s₀ s₁ : ℝ}
    (hs₀ : 0 < s₀) (hs : s₀ ≤ s₁) :
    Real.log (1 + s₀ * t / (y₀ + s₀ * t)) ≤ Real.log (1 + s₁ * t / (y₀ + s₁ * t)) := by
  have h0 : 0 < y₀ + s₀ * t := by positivity
  have h1 : 0 < y₀ + s₁ * t := by nlinarith
  refine Real.log_le_log (by positivity) ?_
  have hfrac : s₀ * t / (y₀ + s₀ * t) ≤ s₁ * t / (y₀ + s₁ * t) := by
    rw [div_le_div_iff₀ h0 h1]
    nlinarith [mul_le_mul_of_nonneg_right hs (mul_nonneg ht.le hy₀.le)]
  linarith


/-- **An Aiyagari equilibrium with the Cobb–Douglas firm**, from two-sided bounds on capital
supply. Both ends of the sign change are now theorems; what is assumed is a positive floor under
capital supply, uniform in the rate. -/
theorem exists_equilibrium_of_bounds {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z]
    [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z] {assetFloor assetCap : ℝ}
    {Pf : ℝ → IncomeFluctuation Z assetFloor assetCap} {S : ℝ → ℝ} (δ : ℝ) {m M : ℝ} (hm : 0 < m)
    (hlb : ∀ r, m ≤ S r) (hub : ∀ r, S r ≤ M)
    (hS : ∀ r, ∃ μ : ProbabilityMeasure (Pf r).State,
      (Pf r).IsStationary μ ∧ (Pf r).aggregateCapital μ = S r)
    (hScont : ∀ rlo rhi : ℝ, ContinuousOn S (Icc rlo rhi)) :
    ∃ rlo rhi : ℝ, rlo ≤ rhi ∧ ∃ r ∈ Icc rlo rhi,
      IsAiyagariEquilibrium Pf (capitalDemand 1 δ) r := by
  obtain ⟨rlo, rhi, hrlo, hle, hloS, hhiS⟩ := exists_sign_change δ hm hlb hub
  refine ⟨rlo, rhi, hle, exists_aiyagari_equilibrium hle hS (hScont rlo rhi)
    (continuousOn_capitalDemand hrlo) hloS hhiS⟩

end LeanEconomics
