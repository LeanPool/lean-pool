/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Martingales.ChangeOfMeasure
public import LeanPool.MathFin.Probability.Brownian.BrownianMartingale
public import LeanPool.MathFin.Probability.Martingales.EquivMeasure
public import LeanPool.MathFin.Probability.Brownian.ExpMartingaleQBrownian

/-!
# Constant-θ distributional Girsanov — the drift-corrected exponential is a Q-martingale

Route-α base case (`docs/specs/2026-07-05-adapted-ito-formula-design.md`, "Route
decision update"). For a **constant** market price of risk `θ`, the Girsanov measure
is `Q = P.withDensity Z_T` with the Wald density `Z_t = exp(−θ X_t − ½θ² t)`
(a `P`-martingale, `waldExponential_isMartingale (−θ)`), and the drift-corrected
process is `B^θ_t = X_t + θ t`.

The key exponential-characterization brick: for **every** `a : ℝ`,
`exp(a·B^θ_t − ½a² t)` is a `Q`-martingale on `[0,T]`. The mechanism is the reusable
Bayes change-of-measure engine (`changeOfMeasure_setIntegral_eq`) fed two Wald
exponentials —

  `Z_t   = exp(−θ X_t − ½θ² t)`            (Wald at `−θ`),
  `Z_t·D_t = exp((a−θ) X_t − ½(a−θ)² t)`   (Wald at `a−θ`, by the pointwise algebra
                                            `−θx − ½θ²u + a(x+θu) − ½a²u
                                             = (a−θ)x − ½(a−θ)²u`),

both `P`-martingales; the engine turns `D_t = exp(a·B^θ_t − ½a² t)` into a
`Q`-martingale. The one genuinely new estimate is the mixed-time integrability of
`D_u · Z_T`, by AM–GM (`exp(a X_u)·exp(−θ X_T) ≤ exp(2a X_u) + exp(−2θ X_T)`, each a
Gaussian-MGF term via `integrable_exp_mul_gaussianReal`). The Black–Scholes discounted-price
martingale `bs_discounted_isQMartingale` is this theorem at `a = σ`.

The identity `E_Q[exp(a(B^θ_t − B^θ_s)) | 𝓕_s] = exp(½a²(t−s))` for all `a`, together with
`B^θ_0 = 0`, determines every finite-dimensional law of `B^θ` on `[0,T]` as that of a `Q`-Brownian
motion. The theorems below
derive from it (through `ExpMartingaleQBrownian`) the marginal law, the `N(0,t−s)` increment law,
and independent increments (`HasIndepIncrements`) on `[0,T]`; path continuity is not stated. This
is the constant-θ case of the distributional Girsanov theorem, reached with the existing tower — no
adapted-integrand Itô formula.

## Main results

* `MathFin.expBtheta_isQMartingale` — the exponential `Q`-martingale above.
* `MathFin.Btheta_isQBrownianMotion` — zero start, `N(0,t−s)` increments and independent
  increments of `B^θ` under `Q` on `[0,T]`.

## Tags

Girsanov theorem, constant market price of risk, Wald exponential, drift-corrected Brownian motion,
Bayes rule, risk-neutral measure, MSC 60J65, MSC 60G44, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

/-- **Constant-θ Girsanov: the drift-corrected exponential is a `Q`-martingale.**
For constant `θ` and any `a : ℝ`, under `Q = P.withDensity (exp(−θ X_T − ½θ² T))`,
the exponential `exp(a·(X_t + θ t) − ½a² t)` of the drift-corrected process
`B^θ_t = X_t + θ t` is a martingale on `[0,T]`: for `s ≤ t ≤ T` and `A ∈ 𝓕_s`, the
`Q`-integrals over `A` at `t` and `s` agree. Proof: `Z = exp(−θX − ½θ²·)` and
`Z·D = exp((a−θ)X − ½(a−θ)²·)` are the Wald `P`-martingales at `−θ` and `a−θ`; the
Bayes engine `changeOfMeasure_setIntegral_eq` does the rest. -/
theorem expBtheta_isQMartingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, Real.exp (a * (X t ω + θ * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2)
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      = ∫ ω in A, Real.exp (a * (X s ω + θ * (s : ℝ)) - a ^ 2 * (s : ℝ) / 2)
        ∂(P.withDensity fun ω ↦ ENNReal.ofReal
          (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  set Z : ℝ≥0 → Ω → ℝ := fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2) with hZdef
  set D : ℝ≥0 → Ω → ℝ :=
    fun u ω ↦ Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2) with hDdef
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  -- Density `Z_T` is measurable and nonnegative.
  have hZmeasT : Measurable (Z T) := by
    rw [hZdef]; exact Real.measurable_exp.comp (((hmeasX T).const_mul (-θ)).sub_const _)
  have hZpos : ∀ ω, 0 ≤ Z T ω := fun ω ↦ (Real.exp_pos _).le
  -- `D` is adapted (continuous function of the adapted `X_u`).
  have hDsm : ∀ u, StronglyMeasurable[𝓕 u] (D u) := by
    intro u
    have hcont : Continuous fun x : ℝ ↦ a * (x + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2 := by
      fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable
      (hcont.comp_stronglyMeasurable (hX.stronglyAdapted u))
  -- `Z` is a `P`-martingale: the Wald exponential at `α = −θ`.
  have hZ : Martingale Z 𝓕 P := by
    have key : Z = fun u ω ↦ Real.exp (-θ * X u ω - (-θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω; rw [hZdef, neg_sq]
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (-θ)
  -- `Z · D = Wald(a − θ)` is a `P`-martingale.
  have hZD : Martingale (fun u ω ↦ Z u ω * D u ω) 𝓕 P := by
    have key : (fun u ω ↦ Z u ω * D u ω)
        = fun u ω ↦ Real.exp ((a - θ) * X u ω - (a - θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω
      simp only [hZdef, hDdef]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (a - θ)
  -- Mixed-time integrability of `D_u · Z_T` via AM–GM.
  have hmix : ∀ u, u ≤ T → Integrable (fun ω ↦ D u ω * Z T ω) P := by
    intro u _
    simp only [hZdef, hDdef]
    have hcore : Integrable (fun ω ↦ Real.exp (a * X u ω) * Real.exp (-θ * X T ω)) P := by
      have hbnd : Integrable
          (fun ω ↦ Real.exp (2 * a * X u ω) + Real.exp (-2 * θ * X T ω)) P :=
        ((hX.hasLaw_eval u).integrable_fun_comp (integrable_exp_mul_gaussianReal (2 * a))).add
          ((hX.hasLaw_eval T).integrable_fun_comp (integrable_exp_mul_gaussianReal (-2 * θ)))
      refine Integrable.mono' hbnd ?_ ?_
      · exact ((Real.measurable_exp.comp ((hmeasX u).const_mul a)).mul
          (Real.measurable_exp.comp ((hmeasX T).const_mul (-θ)))).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (by positivity)]
        have ea : Real.exp (2 * a * X u ω) = Real.exp (a * X u ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        have eb : Real.exp (-2 * θ * X T ω) = Real.exp (-θ * X T ω) ^ 2 := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        rw [ea, eb]
        nlinarith [sq_nonneg (Real.exp (a * X u ω) - Real.exp (-θ * X T ω)),
          (Real.exp_pos (a * X u ω)).le, (Real.exp_pos (-θ * X T ω)).le,
          mul_pos (Real.exp_pos (a * X u ω)) (Real.exp_pos (-θ * X T ω))]
    have hrw : (fun ω ↦
        Real.exp (a * (X u ω + θ * (u : ℝ)) - a ^ 2 * (u : ℝ) / 2) *
        Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))
        = fun ω ↦ (Real.exp (a * θ * (u : ℝ) - a ^ 2 * (u : ℝ) / 2
            - θ ^ 2 * (T : ℝ) / 2)) *
            (Real.exp (a * X u ω) * Real.exp (-θ * X T ω)) := by
      funext ω
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hrw]; exact hcore.const_mul _
  exact changeOfMeasure_setIntegral_eq T hZmeasT hZpos hDsm hZ hZD hmix hst htT hA

/-- **The constant-θ Girsanov measure is a probability measure.** `Q = P.withDensity Z_T`
with the Wald density `Z_T = exp(−θ X_T − ½θ² T)`: the density is strictly
positive, `P`-integrable (Gaussian MGF), and has unit `P`-mean — the Wald exponential is a
`P`-martingale started at `Z_0 = exp(−θ X_0) = 1` (since `X_0 = 0` a.s.), so `∫ Z_T dP =
∫ Z_0 dP = 1`. -/
theorem girsanovMeasure_isProbabilityMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦
    ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  set g : Ω → ℝ := fun ω ↦ Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)
  have hgpos : ∀ ω, 0 < g ω := fun ω ↦ Real.exp_pos _
  have hgfactor : g = fun ω ↦ Real.exp (-(θ ^ 2 * (T : ℝ) / 2)) * Real.exp (-θ * X T ω) := by
    funext ω
    change Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)
        = Real.exp (-(θ ^ 2 * (T : ℝ) / 2)) * Real.exp (-θ * X T ω)
    rw [show -θ * X T ω - θ ^ 2 * (T : ℝ) / 2
          = -(θ ^ 2 * (T : ℝ) / 2) + -θ * X T ω from by ring, Real.exp_add]
  have hgint : Integrable g P := by
    rw [hgfactor]
    exact ((hX.hasLaw_eval T).integrable_fun_comp
      (integrable_exp_mul_gaussianReal (-θ))).const_mul _
  -- The Wald exponential `Z_u = exp(−θ X_u − ½θ² u)` is a `P`-martingale.
  have hZmart : Martingale (fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2)) 𝓕 P := by
    have key : (fun u ω ↦ Real.exp (-θ * X u ω - θ ^ 2 * (u : ℝ) / 2))
        = fun u ω ↦ Real.exp (-θ * X u ω - (-θ) ^ 2 * (u : ℝ) / 2) := by
      funext u ω; rw [neg_sq]
    rw [key]; exact IsFilteredPreBrownian.waldExponential_isMartingale (-θ)
  -- `X_0 = 0` a.s. (its law is `gaussianReal 0 0 = dirac 0`).
  have hX0 : P {ω | X 0 ω ≠ 0} = 0 := by
    have hmap := Measure.map_apply (μ := P) (hmeasX 0) (measurableSet_singleton (0 : ℝ)).compl
    rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
        Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
    have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by
      ext ω; simp [Set.mem_preimage]
    rw [hpre] at hmap
    simpa using hmap.symm
  -- `∫ Z_0 dP = 1`, hence `∫ g dP = ∫ Z_T dP = ∫ Z_0 dP = 1`.
  have hgsum : ∫ ω, g ω ∂P = 1 := by
    have hmean := hZmart.setIntegral_eq (i := 0) (j := T) zero_le (s := Set.univ)
      MeasurableSet.univ
    simp only [Measure.restrict_univ] at hmean
    have hZ0 : ∫ ω, Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂P = 1 := by
      have hae : (fun ω ↦ Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
          =ᵐ[P] fun _ ↦ (1 : ℝ) := by
        filter_upwards [ae_iff.mpr hX0] with ω hω
        simp [hω]
      rw [integral_congr_ae hae]; simp
    calc ∫ ω, g ω ∂P
        = ∫ ω, Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2) ∂P := rfl
      _ = ∫ ω, Real.exp (-θ * X 0 ω - θ ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂P := hmean.symm
      _ = 1 := hZ0
  exact (isEquivProbMeasure_withDensity P hgpos hgint hgsum).isProb

/-- **The constant-θ drift-corrected process, packaged as exponential-martingale data.**
For constant `θ`, the process `B^θ_u = X_u + θ u` is `𝓕`-adapted, starts at `0` a.e. under the
Girsanov measure `Q = P.withDensity(exp(−θ X_T − ½θ² T))` (`X_0 = 0` a.e. `P`, `Q ≪ P`), and for
every `a` the exponential `exp(a·B^θ − ½a²·)` is a `Q`-martingale on `[0,T]`
(`expBtheta_isQMartingale`). This is exactly `IsExpQMartingale`, the hypothesis bundle consumed by
the process-agnostic `isQBrownianMotion_of_expMartingale`. -/
private theorem isExpQMartingale_Btheta
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P] (θ : ℝ) (T : ℝ≥0) :
    IsExpQMartingale
      (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2)))
      𝓕 (fun u ω ↦ X u ω + θ * (u : ℝ)) T := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦ ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  refine ⟨fun u ↦ (hX.stronglyAdapted u).add_const _, ?_, ?_⟩
  · -- Zero start: `X_0 = 0` a.e. `P` (law `N(0,0) = δ₀`), transported to `Q ≪ P`.
    have hX0P : P {ω | X 0 ω ≠ 0} = 0 := by
      have hmap := Measure.map_apply (μ := P) (hmeasX 0) (measurableSet_singleton (0 : ℝ)).compl
      rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
          Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
      have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by ext ω; simp [Set.mem_preimage]
      rw [hpre] at hmap
      simpa using hmap.symm
    have hQP : (P.withDensity fun ω ↦ ENNReal.ofReal
        (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) ≪ P :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [hQP.ae_le (ae_iff.mpr hX0P)] with ω hω
    simp [hω]
  · intro a s t hst htT A hA
    exact expBtheta_isQMartingale (P := P) (𝓕 := 𝓕) (X := X) θ a T hst htT hA

/-- **Constant-θ distributional Girsanov (marginal law).** Under `Q = P.withDensity(exp(−θ X_T −
½θ² T))`, the drift-corrected marginal `B^θ_t = X_t + θ t` has law `N(0, t)`. One application of the
exponential characterization `map_eq_gaussianReal_of_expMartingale` to the constant-θ exponential
martingale (`isExpQMartingale_Btheta`) — the same Bayes-engine + Wald-exponential mechanism, now
routed through the reusable characterization instead of a bespoke chain. -/
theorem Btheta_map_eq_gaussianReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {t : ℝ≥0} (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ X t ω + θ * (t : ℝ))
      = gaussianReal 0 t := by
  have : IsProbabilityMeasure (P.withDensity fun ω ↦ ENNReal.ofReal
      (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  exact map_eq_gaussianReal_of_expMartingale (isExpQMartingale_Btheta (X := X) (𝓕 := 𝓕) θ T) htT

/-- **Constant-θ distributional Girsanov (increment law).** Under `Q`, the increment
`B^θ_t − B^θ_s = (X_t + θ t) − (X_s + θ s)` has law `N(0, t−s)`. One application of
`increment_map_eq_gaussianReal_of_expMartingale`. -/
theorem Btheta_increment_map_eq_gaussianReal
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) (htT : t ≤ T) :
    (P.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))).map
        (fun ω ↦ (X t ω + θ * (t : ℝ)) - (X s ω + θ * (s : ℝ)))
      = gaussianReal 0 (t - s) := by
  have : IsProbabilityMeasure (P.withDensity fun ω ↦ ENNReal.ofReal
      (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  exact increment_map_eq_gaussianReal_of_expMartingale
      (isExpQMartingale_Btheta (X := X) (𝓕 := 𝓕) θ T) hst htT

/-- **Constant-θ distributional Girsanov: `B^θ` has the increments of a `Q`-Brownian motion.** Under
`Q = P.withDensity(exp(−θ X_T − ½θ² T))` the drift-corrected process `B^θ_t = X_t + θ t` has, on
`[0,T]`: zero start `B^θ_0 = 0` a.e. `Q`, Gaussian increments `B^θ_t − B^θ_s ~ N(0, t−s)`, and
independent increments (`HasIndepIncrements`). Together these fix every finite-dimensional law of
`B^θ` under `Q` on `[0,T]` to that of a standard Brownian motion; path continuity is not stated. One
application of `isQBrownianMotion_of_expMartingale` to the constant-θ exponential martingale
(`isExpQMartingale_Btheta`), reached on the existing tower (Bayes engine + Wald exponentials) with
no adapted-integrand Itô formula. The bounded-*adapted*-θ statements are delivered separately, by
`GirsanovSimpleTheta` (piecewise-constant), `GirsanovAdaptedTheta` (bounded continuous adapted) and
`GirsanovPredictableTheta` (bounded predictable). -/
theorem Btheta_isQBrownianMotion
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    {X : ℝ≥0 → Ω → ℝ} [hX : IsFilteredPreBrownian X 𝓕 P]
    (θ : ℝ) (T : ℝ≥0) :
    IsBrownianOn (P.withDensity fun ω ↦
      ENNReal.ofReal (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) T
      fun t ω ↦ X t ω + θ * (t : ℝ) := by
  have : IsProbabilityMeasure (P.withDensity fun ω ↦ ENNReal.ofReal
      (Real.exp (-θ * X T ω - θ ^ 2 * (T : ℝ) / 2))) :=
    girsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) θ T
  exact isQBrownianMotion_of_expMartingale (isExpQMartingale_Btheta (X := X) (𝓕 := 𝓕) θ T)

end MathFin
