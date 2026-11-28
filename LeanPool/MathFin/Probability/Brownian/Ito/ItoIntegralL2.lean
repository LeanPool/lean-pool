/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.KLS.BrownianMotion.StochasticIntegral.SimpleProcess
public import LeanPool.MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
public import LeanPool.KLS.BrownianMotion.StochasticIntegral.Predictable
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The L²-adapted Itô isometry, anchored on Degenne's `SimpleProcess`

This file establishes the **Itô isometry for adapted simple processes** — the substantive
analytic content of the L² Itô integral — built on Degenne's
`BrownianMotion.StochasticIntegral` objects (the maximally-coherent choice). The Itô integral
*operator* itself (the CLM `itoIntegralCLM`) is assembled from this isometry in
`ItoIntegralCLM.lean`; the *discrete* isometry core is `ItoIsometryAdapted.lean`. The cornerstone
is that the cross-terms vanish by the **weak Markov property** (`rect_increment_pairing`,
from `ItoIsometryAdapted.lean`), *not* by deterministic covariance — the precise distinction
between the Itô integral (random adapted integrands) and the Wiener integral (deterministic
integrands, `WienerIntegralL2.lean`). Degenne's `SimpleProcess` allows *overlapping*
intervals, which is exactly why `rect_increment_pairing` is the right tool.

## Main definitions

* `natFiltration`: the natural Brownian filtration `𝓕ᴮ_t = σ(B_u : u ≤ t)`.
* `itoSimple`: the elementary Itô integral of a simple process `V` at the terminal time,
  `∑ₚ V(p) · (B_{p.2} − B_{p.1})`.
* `itoSimpleLp`: that integral as an element of `Lp ℝ 2 μ`.
* `itoAssembly`: the elementary Itô integral as a linear map `SimpleProcess →ₗ[ℝ] Lp ℝ 2 μ`.
* `timeMeasure`: Lebesgue measure on the time axis `ℝ≥0`.
* `elemIntegrand`: the elementary integrand `Z · 1_{(a,b]}`, a bounded weight on `Ω` switched on
  over a time band.
* `rectTerm`: the contribution `𝟙_{(p.1,p.2]}(t) · V(p)(ω)` of one interval `p` to the uncurried
  simple process.
* `simpleProcessL2`: the embedding of a simple process into the predictable `L²` space, as the
  class of its uncurried version.
* `simpleAssembly`: that embedding as a linear map.

## Main results

* `SimpleProcess.coe_finset_sum` — Degenne's `coe_add`, summed over a `Finset`: the coercion
  of a finite sum of simple processes is the sum of the coercions (an upstream candidate).
* `elemIntegrand` — the elementary integrand `Z·1_{(a,b]}`, and `rectTerm` its instance at a
  simple process's band; `uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero` decomposes a simple
  process into its bands for **any** measure charging the time origin nothing, which is what
  lets the bracket-weighted spaces of the integral-against-a-martingale reuse it.
* `itoSimple` / `itoSimple_apply` — the elementary Itô integral
  `(V ● B)_⊤ = ∑ₚ V(p)·(B_{p.2}−B_{p.1})` (Degenne's `SimpleProcess.integral` against
  multiplication, at the terminal time `⊤`).
* `memLp_itoSimple` / `itoSimpleLp` — it lies in `L²(μ)`.
* `itoSimple_sq_integral` / `itoSimpleLp_norm_sq` — **the Itô isometry**:
  `‖itoSimpleLp V‖² = ∫ (itoSimple V)² dμ = Σ_{p,q} E[V(p)·V(q)] · vol((p]∩(q])`.

## Toward the continuous integral

The continuous extension to a CLM `L2Predictable ν μ →L[ℝ] Lp ℝ 2 μ` is built on top of the
isometry by L²-completion: the time measure `ν` (Lebesgue on `ℝ≥0`, below), the embedding of
simple processes into the predictable `L²`, density of those embeddings (via
`generateFrom_eq_predictable`), and `LinearMap.extendOfNorm`. This is the foundation of a
continuous-time Itô-*calculus* layer (Itô's lemma, SDEs). The full resume-plan is in
`docs/archive/ito-integral-clm-deferred.md`.

## Tags

Itô isometry, simple processes, elementary Itô integral, natural filtration, stochastic integral,
weak Markov property, MSC 60H05, MSC 60G44, MSC 60J65
-/

@[expose] public section

namespace ProbabilityTheory.SimpleProcess

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [NormedSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] {𝓕 : MeasureTheory.Filtration ι mΩ}

/-- The coercion of a finite sum of simple processes is the sum of the coercions: `coe_zero` and
`coe_add` make the coercion an additive map, and `map_sum` sums it. -/
theorem coe_finset_sum {κ : Type*} (s : Finset κ) (W : κ → SimpleProcess E 𝓕) :
    ⇑(∑ k ∈ s, W k) = ∑ k ∈ s, ⇑(W k) :=
  map_sum (⟨⟨fun V ↦ ⇑V, coe_zero⟩, coe_add⟩ : SimpleProcess E 𝓕 →+ ι → Ω → E) W s

end ProbabilityTheory.SimpleProcess

namespace MathFin
namespace ItoIntegralL2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The **natural Brownian filtration** `𝓕ᴮ_t = σ(B_u : u ≤ t)`. -/
noncomputable def natFiltration (hBmeas : ∀ t, Measurable (B t)) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t ↦ (hBmeas t).stronglyMeasurable)

/-- `B` is adapted to its own natural filtration
(Mathlib's `Filtration.stronglyAdapted_natural`). -/
theorem stronglyAdapted_natFiltration (hBmeas : ∀ t, Measurable (B t)) :
    StronglyAdapted (natFiltration hBmeas) B :=
  Filtration.stronglyAdapted_natural _

/-- The **elementary Itô integral** of a simple process `V` against Brownian motion
`B`, evaluated at the terminal time: `(V ● B)_⊤ = ∑ₚ V(p)·(B_{p.2} − B_{p.1})`,
the increment sum with nothing truncated.

Until the 2026-07-27 pin this *was* Degenne's `SimpleProcess.integral … ⊤`: his
elementary integral was indexed by `WithTop ι`, so `⊤` named the untruncated
value and `SimpleProcess.integral_top` unfolded it to this sum. At the new pin
`integral : ι → Ω → G` — the index dropped `WithTop`, `integral_top` is
commented out upstream, and with `ι = ℝ≥0` there is no `⊤` to evaluate at. The
untruncated value is therefore no longer *expressible* as an evaluation of
`integral`, and is taken as the definition here.

Nothing downstream is weakened: every consumer goes through `itoSimple_apply`
(now definitional), and the process-level integral `itoSimpleProcess` still
consumes `SimpleProcess.integral` directly, at a genuine time `t : ℝ≥0`.
Restoring the consumption relation — `itoSimple = integral … t` for any `t`
dominating `V`'s finite support — is a follow-up recorded in
`docs/archive/upstream-consumption-review-2026-07-27.md`. -/
noncomputable def itoSimple (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Ω → ℝ :=
  fun ω ↦ V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω)

/-- The terminal Itô integral as the explicit increment sum
`(V ● B)_⊤ ω = ∑ₚ V(p) ω · (B_{p.2} ω − B_{p.1} ω)`. -/
lemma itoSimple_apply (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (ω : Ω) :
    itoSimple hBmeas V ω
      = V.value.sum fun p v ↦ v ω * (B p.2 ω - B p.1 ω) :=
  rfl

variable [IsProbabilityMeasure μ]

/-- **Step 1 — `L²` membership.** The terminal Itô integral of a simple process is in
`L²(μ)`: it is the finite sum `∑ₚ V(p)·(B_{p.2}−B_{p.1})`, and each summand is in `L²`
by `memLp_adapted_mul_increment` — the coefficient `V(p)` is `𝓕_{p.1}`-measurable (the
filtration the core is stated against) and bounded (hence `L²` on the probability space). -/
theorem memLp_itoSimple (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (itoSimple hBmeas V) 2 μ := by
  rw [show itoSimple hBmeas V
        = fun ω ↦ ∑ p ∈ V.value.support, V.value p ω * (B p.2 ω - B p.1 ω)
      from funext fun ω ↦ by rw [itoSimple_apply]; rfl]
  refine memLp_finsetSum V.value.support (fun p hp ↦ ?_)
  refine ItoIsometryAdapted.memLp_adapted_mul_increment (hB.isFilteredPreBrownian hBmeas)
    (V.le_of_mem_support_value p hp) (V.measurable_value p) ?_
  exact MemLp.of_bound
    ((V.measurable_value p).mono ((natFiltration hBmeas).le p.1) le_rfl).aestronglyMeasurable
    V.valueBound (ae_of_all _ (V.value_le_valueBound p))

/-- The terminal Itô integral of a simple process as an element of `Lp ℝ 2 μ`. -/
noncomputable def itoSimpleLp (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) : Lp ℝ 2 μ :=
  (memLp_itoSimple hB hBmeas V).toLp _

/-- **Step 2 — the Itô isometry on simple processes** (the predictable-rectangle double
sum). For a simple process `V`,

  `∫ (itoSimple V)² dμ = Σ_{p,q} E[V(p)·V(q)] · vol((p.1,p.2] ∩ (q.1,q.2])`,

where `vol((p.1,p.2] ∩ (q.1,q.2]) = max 0 (min p.2 q.2 − max p.1 q.1)`. The square of the
increment sum expands into a double sum whose every term collapses by
`rect_increment_pairing` — the genuinely-stochastic content (cross terms vanish by the
weak Markov property, diagonal terms give the deterministic overlap). The right-hand side
is exactly `‖V‖²` in the predictable `L²` space, so this is the Itô isometry. -/
theorem itoSimple_sq_integral (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  set a : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω ↦ V.value p ω * (B p.2 ω - B p.1 ω)
  have ha_L2 : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := fun p hp ↦
    ItoIsometryAdapted.memLp_adapted_mul_increment (hB.isFilteredPreBrownian hBmeas)
      (V.le_of_mem_support_value p hp) (V.measurable_value p)
      (MemLp.of_bound
        ((V.measurable_value p).mono ((natFiltration hBmeas).le p.1) le_rfl).aestronglyMeasurable
        V.valueBound (ae_of_all _ (V.value_le_valueBound p)))
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun ω ↦ a p ω * a q ω) μ :=
    fun p hp q hq ↦ (ha_L2 p hp).integrable_mul (ha_L2 q hq)
  calc ∫ ω, (itoSimple hBmeas V ω) ^ 2 ∂μ
      = ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        change itoSimple hBmeas V ω ^ 2
          = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, a p ω * a q ω
        rw [show itoSimple hBmeas V ω = ∑ p ∈ V.value.support, a p ω from by
              rw [itoSimple_apply]; rfl, sq, Finset.sum_mul_sum]
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support, ∫ ω, a p ω * a q ω ∂μ := by
        rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
        exact Finset.sum_congr rfl fun p hp ↦
          integral_finsetSum _ (fun q hq ↦ hint p hp q hq)
    _ = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
        refine Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun q hq ↦ ?_
        exact ItoIsometryAdapted.rect_increment_pairing (hB.isFilteredPreBrownian hBmeas)
          (V.measurable_value p) (V.measurable_value q)
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound p ω)
          (fun ω ↦ by rw [← Real.norm_eq_abs]; exact V.value_le_valueBound q ω)
          (V.le_of_mem_support_value p hp) (V.le_of_mem_support_value q hq)

/-- **The Itô isometry in `Lp`-norm form.** `‖itoSimpleLp V‖²` equals the predictable-
rectangle double sum — i.e. `‖V‖²` in the predictable `L²` space. This is the norm
identity that `extendOfNorm` consumes to build the continuous Itô integral. -/
theorem itoSimpleLp_norm_sq (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ‖(itoSimpleLp hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  rw [lp_two_norm_sq, ← itoSimple_sq_integral hB hBmeas V]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_itoSimple hB hBmeas V).coeFn_toLp] with ω hω
  rw [show (itoSimpleLp hB hBmeas V : Ω → ℝ) ω = itoSimple hBmeas V ω from hω]

/-! ### The time measure `ν` — Lebesgue on `ℝ≥0`

The CLM domain is `L2Predictable ν μ = Lp ℝ 2 ((ν.prod μ).trim 𝓕.predictable_le_prod)`
(Degenne's `L2M`). The interval overlap appearing in the isometry **is** Lebesgue length
(it comes from `E[(Bₜ−Bₛ)²] = t−s`), so `ν` must be Lebesgue measure on the time axis `ℝ≥0`.
Since `ℝ≥0` carries no canonical `volume`, we take the comap of `volume` along the (closed,
hence measurable) embedding `ℝ≥0 ↪ ℝ`. -/

/-- The coercion `ℝ≥0 → ℝ` as a measurable embedding (it is a closed embedding). -/
lemma measurableEmbedding_nnrealCoe : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
  NNReal.isClosedEmbedding_coe.measurableEmbedding

/-- Lebesgue measure on the time axis `ℝ≥0` — the comap of `volume` along `ℝ≥0 ↪ ℝ`. -/
noncomputable def timeMeasure : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- `timeMeasure` of a time interval `(a, b]` is its length `b - a`. -/
lemma timeMeasure_Ioc (a b : ℝ≥0) :
    timeMeasure (Set.Ioc a b) = ENNReal.ofReal ((b : ℝ) - a) := by
  have himg : ((↑) : ℝ≥0 → ℝ) '' Set.Ioc a b = Set.Ioc (a : ℝ) b := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioc]
    constructor
    · rintro ⟨y, ⟨hay, hyb⟩, rfl⟩
      exact ⟨by exact_mod_cast hay, by exact_mod_cast hyb⟩
    · rintro ⟨hax, hxb⟩
      have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt a.coe_nonneg hax)
      exact ⟨⟨x, hx0⟩, ⟨by exact_mod_cast hax, by exact_mod_cast hxb⟩, rfl⟩
  rw [timeMeasure, measurableEmbedding_nnrealCoe.comap_apply, himg, Real.volume_Ioc]

/-- The `vol((p.1,p.2] ∩ (q.1,q.2])` factor of the Itô-isometry double sum, as a
`timeMeasure` of the intersection of two time intervals. -/
lemma timeMeasure_Ioc_inter (a b c d : ℝ≥0) :
    timeMeasure (Set.Ioc a b ∩ Set.Ioc c d)
      = ENNReal.ofReal (min (b : ℝ) d - max (a : ℝ) c) := by
  rw [Set.Ioc_inter_Ioc, timeMeasure_Ioc, NNReal.coe_min, NNReal.coe_max]

/-- `timeMeasure` is finite on compacts (comap of `volume`, which is, along the
continuous measurable embedding `ℝ≥0 ↪ ℝ`). -/
instance : IsFiniteMeasureOnCompacts timeMeasure :=
  IsFiniteMeasureOnCompacts.comap' volume NNReal.continuous_coe measurableEmbedding_nnrealCoe

/-- `timeMeasure` is σ-finite (Lebesgue on the locally compact, σ-compact `ℝ≥0`). -/
instance : SigmaFinite timeMeasure := inferInstance

/-- `timeMeasure` of a single time point is `0` (Lebesgue is non-atomic). -/
lemma timeMeasure_singleton (a : ℝ≥0) : timeMeasure {a} = 0 := by
  rw [timeMeasure, measurableEmbedding_nnrealCoe.comap_apply, Set.image_singleton,
    Real.volume_singleton]

/-! ### Embedding simple processes into the predictable `L²`

The uncurried simple process `uncurry V : ℝ≥0 × Ω → ℝ` is, up to a `timeMeasure.prod μ`-null
set (the time-fibre `{⊥}`), the finite sum over `V.value.support` of **rectangle terms**
`𝟙_{(p.1,p.2]}(t) · V(p)(ω)`. Each rectangle term is `L²` in the product (its time-support is
a finite-measure interval and `V` is bounded), so `uncurry V ∈ L²(timeMeasure.prod μ)`; being
predictable-strongly-measurable, it descends to `L2Predictable timeMeasure μ`. -/

/-- **The elementary integrand** `Z·1_{(a,b]}`: a bounded weight on `Ω` switched on over a
time band. It is the atom of every simple process (`rectTerm` below is this at the band `p`
with weight `V.value p`) and, in the tower above, the integrand on which a stochastic integral
is pinned to its Riemann–Stieltjes value. It depends on neither the driver nor the
filtration. -/
noncomputable def elemIntegrand (a b : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun z ↦ (Set.Ioc a b).indicator (fun _ ↦ (1 : ℝ)) z.1 * Z z.2

/-- The contribution of one interval `p` to the uncurried simple process, in product
form `𝟙_{(p.1,p.2]}(t) · V(p)(ω)` — the elementary integrand at the band `p`. -/
noncomputable def rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p : ℝ≥0 × ℝ≥0) :
    ℝ≥0 × Ω → ℝ :=
  elemIntegrand p.1 p.2 (V.value p)

/-- The rectangle term as an indicator of the product rectangle `(p.1,p.2] ×ˢ univ`. -/
lemma rectTerm_eq_indicator (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p : ℝ≥0 × ℝ≥0) :
    rectTerm hBmeas V p
      = (Set.Ioc p.1 p.2 ×ˢ (Set.univ : Set Ω)).indicator (fun z ↦ V.value p z.2) := by
  funext z
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  simp only [Set.mem_prod, Set.mem_univ, and_true]
  split_ifs <;> simp

/-- **Each rectangle term is `L²`** in the product measure: its time-support is the
finite-measure interval `(p.1,p.2]` and `V(p)` is bounded. -/
lemma memLp_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p : ℝ≥0 × ℝ≥0) :
    MemLp (rectTerm hBmeas V p) 2 (timeMeasure.prod μ) := by
  have : IsFiniteMeasure (timeMeasure.restrict (Set.Ioc p.1 p.2)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, timeMeasure_Ioc];
        exact ENNReal.ofReal_lt_top⟩
  rw [rectTerm_eq_indicator,
      memLp_indicator_iff_restrict (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet,
      ← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : Measurable (fun z : ℝ≥0 × Ω ↦ V.value p z.2) :=
    ((V.measurable_value p).mono ((natFiltration hBmeas).le p.1) le_rfl).comp measurable_snd
  exact MemLp.of_bound hmeas.aestronglyMeasurable V.valueBound
    (ae_of_all _ fun z ↦ by rw [Real.norm_eq_abs]; exact V.value_le_valueBound p z.2)

/-- **The uncurried simple process is a.e. the finite sum of its rectangle terms** — for
*any* measure that charges the time origin nothing.

The origin is the whole content: `SimpleProcess.apply_eq` writes `V` as its value at `⊥` plus
the band sum, and the first term is what has to go. Nothing else about the measure is used, and
in particular nothing about the σ-algebra it lives on, so the same statement serves the flat
product measure here and the bracket-weighted predictable measure the integral against an Itô
integral is built on. -/
lemma uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero {m : MeasurableSpace (ℝ≥0 × Ω)}
    {ν : @Measure (ℝ≥0 × Ω) m} (hν : ∀ᵐ z ∂ν, z.1 ≠ 0) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑V =ᵐ[ν] fun z ↦ ∑ p ∈ V.value.support, rectTerm hBmeas V p z := by
  filter_upwards [hν] with z hz
  change ⇑V z.1 z.2 = _
  rw [SimpleProcess.apply_eq, Set.indicator_of_notMem (by simpa using hz), zero_add, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [rectTerm, elemIntegrand, Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

/-- The time origin is `timeMeasure.prod μ`-null, the time fibre `{⊥}` being Lebesgue-null. -/
lemma ae_fst_ne_zero_prod (μ : Measure Ω) [SFinite μ] :
    ∀ᵐ z : ℝ≥0 × Ω ∂(timeMeasure.prod μ), z.1 ≠ 0 := by
  rw [Filter.eventually_iff, mem_ae_iff,
      show {z : ℝ≥0 × Ω | z.1 ≠ 0}ᶜ = {(0 : ℝ≥0)} ×ˢ (Set.univ : Set Ω) from by ext z; simp,
      Measure.prod_prod, timeMeasure_singleton, zero_mul]

/-- **The uncurried simple process is a.e. the finite sum of its rectangle terms.**
They agree off the time-fibre `{⊥}`, which is `timeMeasure.prod μ`-null. -/
lemma uncurry_ae_eq_sum_rectTerm (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑V
      =ᵐ[timeMeasure.prod μ] fun z ↦ ∑ p ∈ V.value.support, rectTerm hBmeas V p z :=
  uncurry_ae_eq_sum_rectTerm_of_ae_fst_ne_zero (ae_fst_ne_zero_prod μ) hBmeas V

/-- **The uncurried simple process is `L²`** in the product measure (finite sum of
`L²` rectangle terms). -/
lemma memLp_uncurry_prod (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2 (timeMeasure.prod μ) :=
  (memLp_congr_ae (uncurry_ae_eq_sum_rectTerm hBmeas V)).mpr
    (memLp_finsetSum _ fun p _ ↦ memLp_rectTerm hBmeas V p)

/-- The uncurried simple process is `L²` in the **trimmed** (predictable) product
measure: it is predictable-strongly-measurable (`SimpleProcess.isStronglyPredictable`)
with the same finite `L²` norm as in the untrimmed product (`eLpNorm_trim`). -/
lemma memLp_uncurry_trim (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    MemLp (Function.uncurry ⇑V) 2
      ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) :=
  by rw [memLp_iff, eLpNorm_trim _ V.isStronglyPredictable]; exact memLp_uncurry_prod hBmeas V

/-- **The embedding** of a simple process into the predictable `L²` space, as the class of
its uncurried version. The codomain `Lp ℝ 2 ((timeMeasure.prod μ).trim …)` is *definitionally*
Degenne's `L2Predictable timeMeasure μ`; we keep it unfolded here so the `Lp` norm instance is
available (the opaque `L2Predictable` def has none), and re-wrap as `L2Predictable` only at the
final continuous integral. The Itô isometry identifies its norm with that of `itoSimpleLp`. -/
noncomputable def simpleProcessL2 (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) :=
  (memLp_uncurry_trim hBmeas V).toLp (Function.uncurry ⇑V)

/-- **Cross-integral of two rectangle terms.** Fubini (`integral_prod_mul`) factorises it
into the time-overlap `vol((p]∩(q]) = max 0 (min p.2 q.2 − max p.1 q.1)` and the sample
correlation `E[V(p)·V(q)]`. -/
lemma integral_rectTerm_mul (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) (p q : ℝ≥0 × ℝ≥0) :
    ∫ z, rectTerm hBmeas V p z * rectTerm hBmeas V q z ∂(timeMeasure.prod μ)
      = (∫ ω, V.value p ω * V.value q ω ∂μ)
          * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  have hfun : (fun z : ℝ≥0 × Ω ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z)
      = fun z ↦ ((Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) z.1
                    * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) z.1)
                  * (V.value p z.2 * V.value q z.2) := by
    funext z; simp only [rectTerm, elemIntegrand]; ring
  rw [hfun, integral_prod_mul
        (fun i ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
          * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i)
        (fun ω ↦ V.value p ω * V.value q ω), mul_comm]
  congr 1
  have hpt : ∀ i : ℝ≥0, (Set.Ioc p.1 p.2).indicator (fun _ ↦ (1 : ℝ)) i
        * (Set.Ioc q.1 q.2).indicator (fun _ ↦ (1 : ℝ)) i
        = (Set.Ioc p.1 p.2 ∩ Set.Ioc q.1 q.2).indicator (1 : ℝ≥0 → ℝ) i := by
    intro i; rw [Set.inter_indicator_one]; rfl
  simp_rw [hpt]
  rw [integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
      Measure.real_def, timeMeasure_Ioc_inter, ENNReal.toReal_ofReal', max_comm]

/-- **The embedding is an `L²` isometry onto the Itô-isometry double sum.** Its squared norm
in `L2Predictable` equals the same predictable-rectangle double sum as the elementary Itô
integral `itoSimpleLp` (the squared increment-sum expands and Fubini-factorises termwise).
This norm identity is what makes the continuous extension an isometry. -/
theorem simpleProcessL2_norm_sq (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          (∫ ω, V.value p ω * V.value q ω ∂μ)
            * max 0 ((min (p.2 : ℝ) q.2) - (max (p.1 : ℝ) q.1)) := by
  -- Step A: ‖simpleProcessL2 V‖² = ∫ (uncurry V)² in the product measure (via `eLpNorm_trim`).
  have hStepA : ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
      = ∫ z, (Function.uncurry ⇑V z) ^ 2 ∂(timeMeasure.prod μ) := by
    rw [lp_two_norm_sq (simpleProcessL2 (μ := μ) hBmeas V)]
    have hco : (fun z ↦ (simpleProcessL2 (μ := μ) hBmeas V z) ^ 2)
        =ᵐ[(timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod]
          fun z ↦ (Function.uncurry ⇑V z) ^ 2 := by
      filter_upwards [(memLp_uncurry_trim hBmeas V).coeFn_toLp] with z hz
      rw [show (simpleProcessL2 (μ := μ) hBmeas V) z = Function.uncurry ⇑V z from hz]
    rw [integral_congr_ae hco]
    simp only [pow_two]
    have hsm2 : StronglyMeasurable[(natFiltration hBmeas).predictable]
        (fun z ↦ Function.uncurry ⇑V z * Function.uncurry ⇑V z) :=
      V.isStronglyPredictable.mul V.isStronglyPredictable
    exact (integral_trim (natFiltration hBmeas).predictable_le_prod hsm2).symm
  rw [hStepA]
  -- Step B: expand the square into the rectangle double sum and integrate termwise.
  have hint : ∀ p ∈ V.value.support, ∀ q ∈ V.value.support,
      Integrable (fun z ↦ rectTerm hBmeas V p z * rectTerm hBmeas V q z) (timeMeasure.prod μ) :=
    fun p _ q _ ↦ (memLp_rectTerm hBmeas V p).integrable_mul (memLp_rectTerm hBmeas V q)
  have hsq : ∀ᵐ z ∂(timeMeasure.prod μ), (Function.uncurry ⇑V z) ^ 2
      = ∑ p ∈ V.value.support, ∑ q ∈ V.value.support,
          rectTerm hBmeas V p z * rectTerm hBmeas V q z := by
    filter_upwards [uncurry_ae_eq_sum_rectTerm hBmeas V] with z hz
    rw [hz, sq, Finset.sum_mul_sum]
  rw [integral_congr_ae hsq,
      integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hint p hp q hq)]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [integral_finsetSum _ fun q hq ↦ hint p hp q hq]
  exact Finset.sum_congr rfl fun q _ ↦ integral_rectTerm_mul hBmeas V p q

/-! ### Linear assembly maps and the isometry on simple processes -/

/-- The elementary Itô integral is additive in the simple process. -/
lemma itoSimple_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimple hBmeas (V + W) = itoSimple hBmeas V + itoSimple hBmeas W := by
  funext ω
  simp only [itoSimple, Pi.add_apply, show (V + W).value = V.value + W.value from rfl]
  exact Finsupp.sum_add_index' (fun p ↦ by simp) (fun p v w ↦ by simp [add_mul])

/-- The elementary Itô integral is homogeneous in the simple process. -/
lemma itoSimple_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    itoSimple hBmeas (c • V) = c • itoSimple hBmeas V := by
  funext ω
  simp only [itoSimple, Pi.smul_apply, smul_eq_mul,
    show (c • V).value = c • V.value from rfl]
  rw [Finsupp.sum_smul_index' (fun p ↦ by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun p _ ↦ by simp [mul_assoc]

/-- **The elementary Itô integral as a linear map** `SimpleProcess →ₗ[ℝ] Lp ℝ 2 μ`. -/
noncomputable def itoAssembly (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun V := itoSimpleLp hB hBmeas V
  map_add' V W := by
    rw [itoSimpleLp, itoSimpleLp, itoSimpleLp,
        ← MemLp.toLp_add (memLp_itoSimple hB hBmeas V) (memLp_itoSimple hB hBmeas W)]
    congr 1
    exact itoSimple_add hBmeas V W
  map_smul' c V := by
    rw [itoSimpleLp, itoSimpleLp, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_itoSimple hB hBmeas V)]
    congr 1
    exact itoSimple_smul hBmeas c V

/-- The uncurried simple process is additive. -/
lemma uncurry_coe_add (hBmeas : ∀ t, Measurable (B t))
    (V W : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑(V + W) = Function.uncurry ⇑V + Function.uncurry ⇑W := by
  rw [SimpleProcess.coe_add]; rfl

/-- The uncurried simple process is homogeneous. -/
lemma uncurry_coe_smul (hBmeas : ∀ t, Measurable (B t)) (c : ℝ)
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    Function.uncurry ⇑(c • V) = c • Function.uncurry ⇑V := by
  rw [SimpleProcess.coe_smul]; rfl

/-- **The embedding into the predictable `L²` as a linear map**
`SimpleProcess →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim …)`. -/
noncomputable def simpleAssembly (hBmeas : ∀ t, Measurable (B t)) :
    SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)
      →ₗ[ℝ] Lp ℝ 2 ((timeMeasure.prod μ).trim (natFiltration hBmeas).predictable_le_prod) where
  toFun V := simpleProcessL2 (μ := μ) hBmeas V
  map_add' V W := by
    rw [simpleProcessL2, simpleProcessL2, simpleProcessL2,
        ← MemLp.toLp_add (memLp_uncurry_trim hBmeas V) (memLp_uncurry_trim hBmeas W)]
    congr 1
    exact uncurry_coe_add hBmeas V W
  map_smul' c V := by
    rw [simpleProcessL2, simpleProcessL2, RingHom.id_apply,
        ← MemLp.toLp_const_smul c (memLp_uncurry_trim hBmeas V)]
    congr 1
    exact uncurry_coe_smul hBmeas c V

/-- **The Itô isometry on simple processes.** `‖itoAssembly V‖ = ‖simpleAssembly V‖`: both
squared norms equal the predictable-rectangle double sum (`itoSimpleLp_norm_sq`,
`simpleProcessL2_norm_sq`). This is the bound `extendOfNorm` consumes. -/
theorem assembly_isometry (hB : IsPreBrownianReal B μ) (hBmeas : ∀ t, Measurable (B t))
    (V : SimpleProcess ℝ (natFiltration (mΩ := mΩ) hBmeas)) :
    ‖itoAssembly (μ := μ) hB hBmeas V‖ = ‖simpleAssembly (μ := μ) hBmeas V‖ := by
  have hsq : ‖itoAssembly (μ := μ) hB hBmeas V‖ ^ 2 = ‖simpleAssembly (μ := μ) hBmeas V‖ ^ 2 := by
    change ‖(itoSimpleLp hB hBmeas V : Lp ℝ 2 μ)‖ ^ 2 = ‖simpleProcessL2 (μ := μ) hBmeas V‖ ^ 2
    rw [itoSimpleLp_norm_sq hB hBmeas V, simpleProcessL2_norm_sq hBmeas V]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end ItoIntegralL2
end MathFin
