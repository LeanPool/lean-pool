/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Esscher
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Mathlib.Probability.Process.Adapted

/-!
# Brownian increment laws from an exponential martingale

A process-agnostic packaging of the argument that turns an **exponential-martingale
hypothesis** into the increment laws of a Brownian motion under a probability measure `Q`. Fix a
probability space `(Ω, Q)`, a filtration `𝓕`, a horizon `T`, and a real process
`Y : ℝ≥0 → Ω → ℝ` that is `𝓕`-adapted, starts at `0` (a.e. `Q`), and satisfies

  `for every a : ℝ, the process t ↦ exp(a·Y_t − ½a² t) is a Q-martingale on [0,T]`.

These three data are bundled as `IsExpQMartingale Q 𝓕 Y T`. The single theorem
`isQBrownianMotion_of_expMartingale` restates the zero start and derives two more properties of `Y`
under `Q` on `[0,T]`: `N(0,t−s)` increments, and independent increments in Mathlib's sense
(`HasIndepIncrements`). Together they fix every finite-dimensional law of `Y` on `[0,T]` to that
of a Brownian motion; that implication is not restated here (on the whole time axis `ℝ≥0` it is
Mathlib's `HasIndepIncrements.isPreBrownianReal_of_hasLaw`). Neither path continuity nor
independence of the increments from the past (`Y_t − Y_s` from `𝓕_s`) is part of the conclusion.
Nothing in the argument refers to how `Y` or `Q` was constructed.

The mechanism: the exponential martingale at `s = 0` fixes the marginal moment-generating
function `𝔼_Q[exp(a·Y_t)] = exp(½a²t)`, hence the marginal law, and the conditional form
`𝔼_Q[exp(a·(Y_t − Y_s))|𝓕_s] = exp(½a²(t−s))` is deterministic, giving Gaussian increments. For
successive increments over `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ`, the earlier ones are `𝓕_{tₙ₋₁}`-measurable and
factor out of the conditional expectation given `𝓕_{tₙ₋₁}`, so by induction the joint
moment-generating function is the product of the Gaussian ones. Every linear combination of the
increments is then Gaussian with the diagonal variance, and `iIndepFun_iff_charFun_pi` turns that
into joint independence.

The value of the abstraction is coherence: the constant-, simple-, continuous- and
predictable-`θ` Girsanov drift-corrected processes each need only supply their own
exponential martingale (via the Bayes change-of-measure engine) and then instantiate this
one theorem.

## Main definitions

* `IsExpQMartingale`: the characterization data on a process `Y` under `Q`: adapted, starting at
  `0` almost surely, and for every `a : ℝ` the set-integral martingale identity for
  `exp(a·Y_t − ½a²t)` on `[0, T]` (integrability is not a field).
* `IsBrownianOn`: under `Q`, `Y` starts at `0` almost surely, has `N(0, t − s)` increments and
  independent increments (`HasIndepIncrements`) on `[0, T]`; these fix the finite-dimensional
  laws of a Brownian motion, but path continuity is not part of it.

## Main results

* `MathFin.map_eq_gaussianReal_of_expMartingale` — the marginal law `Q.map Y_t = N(0,t)`.
* `MathFin.increment_map_eq_gaussianReal_of_expMartingale` — the increment law `N(0,t−s)`.
* `MathFin.increments_iIndepFun_of_expMartingale` — successive increments are jointly
  `Q`-independent.
* `MathFin.hasIndepIncrements_of_expMartingale` — `Y` has independent increments on `[0,T]`.
* `MathFin.isQBrownianMotion_of_expMartingale` — `IsExpQMartingale Q 𝓕 Y T → IsBrownianOn Q T Y`.
* `MathFin.IsBrownianOn.congr_modification` — invariance under a modification.

## Tags

Girsanov theorem, Lévy characterization, exponential martingale, Brownian increments,
moment generating function, Q-Brownian motion, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The exponential-martingale characterization data.** A real process `Y` on the filtered
probability space `(Ω, 𝓕, Q)` that is `𝓕`-adapted, starts at `0` a.e. `Q`, and for which every
`t ↦ exp(a·Y_t − ½a² t)` is a `Q`-martingale on `[0,T]` (stated as the set-integral identity over
`𝓕_s`-sets). These are exactly the data output by the Bayes change-of-measure engine for a
drift-corrected process, and exactly the data consumed by `isQBrownianMotion_of_expMartingale`. -/
structure IsExpQMartingale (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Prop where
  /-- `Y` is adapted to the filtration. -/
  adapted : StronglyAdapted 𝓕 Y
  /-- `Y` starts at `0` (a.e. `Q`). -/
  zero_start : Y 0 =ᵐ[Q] 0
  /-- For every `a`, `exp(a·Y_· − ½a²·)` is a `Q`-martingale on `[0,T]`. -/
  martingale : ∀ (a : ℝ) {s t : ℝ≥0}, s ≤ t → t ≤ T → ∀ {A : Set Ω},
    MeasurableSet[(𝓕 s : MeasurableSpace Ω)] A →
      ∫ ω in A, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
        = ∫ ω in A, Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) ∂Q

/-- Each `Y_u` of the characterization data is measurable, being `𝓕_u`-measurable. -/
protected theorem IsExpQMartingale.measurable {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} (h : IsExpQMartingale Q 𝓕 Y T) (u : ℝ≥0) : Measurable (Y u) :=
  h.adapted.stronglyMeasurable.measurable

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **A Gaussian MGF identifies the Gaussian law.** If a real random variable has the
moment-generating function `a ↦ exp(v·a²/2)` of `N(0,v)` under `Q`, its law is `N(0,v)`:
`N(0,v)` has every exponential moment, so its moment-generating function determines it
(`measure_eq_of_mgf_id_eq`). -/
theorem map_eq_gaussianReal_of_mgf {X : Ω → ℝ} (hX : AEMeasurable X Q) {v : ℝ≥0}
    (hmgf : ∀ a, mgf X Q a = Real.exp (v * a ^ 2 / 2)) : Q.map X = gaussianReal 0 v := by
  refine Eq.symm (measure_eq_of_mgf_id_eq integrable_exp_mul_gaussianReal ?_)
  rw [mgf_id_gaussianReal, mgf_id_map hX]
  funext a
  rw [hmgf, zero_mul, zero_add]

/-- **Marginal `Q`-MGF.** `𝔼_Q[exp(a·Y_t)] = exp(½ t a²)`: read off from the exponential
martingale at `s = 0` (the `Q`-integral of `exp(a·Y_t − ½a²t)` equals its value at `0`, which is
`exp(a·Y_0) = 1` a.e. since `Y_0 = 0`). -/
private theorem mgf_expY_eq (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0} (htT : t ≤ T) (a : ℝ) :
    ∫ ω, Real.exp (a * Y t ω) ∂Q = Real.exp ((t : ℝ) * a ^ 2 / 2) := by
  have hbrick := h.martingale a (zero_le : (0 : ℝ≥0) ≤ t) htT (A := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at hbrick
  have hRHS : ∫ ω, Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2) ∂Q = 1 := by
    have hae : (fun ω ↦ Real.exp (a * Y 0 ω - a ^ 2 * ((0 : ℝ≥0) : ℝ) / 2))
        =ᵐ[Q] fun _ ↦ (1 : ℝ) := by
      filter_upwards [h.zero_start] with ω hω; simp [hω]
    rw [integral_congr_ae hae]; simp
  rw [hRHS] at hbrick
  have hLHS : ∫ ω, Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) ∂Q
      = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * ∫ ω, Real.exp (a * Y t ω) ∂Q := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    change Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
        = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
    rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
      Real.exp_add]
  rw [hLHS, mul_comm] at hbrick
  have hfac : Real.exp (-(a ^ 2 * (t : ℝ) / 2)) ≠ 0 := (Real.exp_pos _).ne'
  rw [(mul_eq_one_iff_eq_inv₀ hfac).mp hbrick, ← Real.exp_neg]
  congr 1; ring

/-- **Marginal law.** `Q.map Y_t = N(0, t)`: the `Q`-MGF is the Gaussian MGF (`mgf_expY_eq`),
which identifies the law (`map_eq_gaussianReal_of_mgf`). -/
theorem map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℝ≥0}
    (htT : t ≤ T) : Q.map (Y t) = gaussianReal 0 t :=
  map_eq_gaussianReal_of_mgf (h.measurable t).aemeasurable (mgf_expY_eq h htT)

/-- **Marginal `Q`-integrability.** `exp(a·Y_u)` is `Q`-integrable for `u ≤ T` — its law is
`N(0,u)` and the Gaussian MGF is finite. -/
private theorem integrable_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) :
    Integrable (fun ω ↦ Real.exp (a * Y u ω)) Q := by
  rw [show (fun ω ↦ Real.exp (a * Y u ω)) = (fun x ↦ Real.exp (a * x)) ∘ (Y u) from rfl,
      ← integrable_map_measure (by fun_prop) (h.measurable u).aemeasurable,
      map_eq_gaussianReal_of_expMartingale h huT]
  exact integrable_exp_mul_gaussianReal a

omit [IsProbabilityMeasure Q] in
/-- **Cauchy–Schwarz for exponentials.** If `exp(2f)` and `exp(2g)` are `Q`-integrable, so is
`exp(f)·exp(g)`: `exp f` and `exp g` are then in `L²(Q)`. -/
theorem integrable_exp_mul_exp {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun ω ↦ Real.exp (2 * f ω)) Q)
    (hg2 : Integrable (fun ω ↦ Real.exp (2 * g ω)) Q) :
    Integrable (fun ω ↦ Real.exp (f ω) * Real.exp (g ω)) Q := by
  have hL2 {u : Ω → ℝ} (hu : Measurable u) (hu2 : Integrable (fun ω ↦ Real.exp (2 * u ω)) Q) :
      MemLp (fun ω ↦ Real.exp (u ω)) 2 Q := by
    refine (memLp_two_iff_integrable_sq hu.exp.aestronglyMeasurable).2 (hu2.congr ?_)
    filter_upwards with ω
    rw [two_mul, Real.exp_add, pow_two]
  exact (hL2 hf hf2).integrable_mul (hL2 hg hg2)

/-- **Conditional exponential martingale.** `𝔼_Q[exp(a·Y_t − ½a² t)|𝓕_s] = exp(a·Y_s − ½a² s)`
a.e., the conditional form of the `martingale` field (its set-integral identity converted via
`ae_eq_condExp_of_forall_setIntegral_eq`). -/
private theorem condExp_expY (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) | 𝓕 s]
      =ᵐ[Q] fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) := by
  have hfint : ∀ u : ℝ≥0, u ≤ T →
      Integrable (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2)) Q := by
    intro u huT
    have hfac : (fun ω ↦ Real.exp (a * Y u ω - a ^ 2 * (u : ℝ) / 2))
        = fun ω ↦ Real.exp (-(a ^ 2 * (u : ℝ) / 2)) * Real.exp (a * Y u ω) := by
      funext ω
      rw [show a * Y u ω - a ^ 2 * (u : ℝ) / 2 = -(a ^ 2 * (u : ℝ) / 2) + a * Y u ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a huT).const_mul _
  have hsm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (s : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hfint t htT)
    (fun A _ _ ↦ (hfint s (hst.trans htT)).integrableOn) (fun A hA _ ↦ ?_)
    hsm.aestronglyMeasurable).symm
  exact (h.martingale a hst htT hA).symm

/-- **Conditional moment-generating function of an increment.**
`𝔼_Q[exp(a·(Y_t − Y_s)) | 𝓕_s] = exp(½a²(t−s))` a.e., deterministic: pull the `𝓕_s`-measurable
factor `exp(½a²t − a·Y_s)` out of `condExp_expY`. -/
theorem IsExpQMartingale.condExp_exp_increment (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q[fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) | 𝓕 s]
      =ᵐ[Q] fun _ ↦ Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  set ft : Ω → ℝ := fun ω ↦ Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2) with hftdef
  set gs : Ω → ℝ := fun ω ↦ Real.exp (a ^ 2 * (t : ℝ) / 2 - a * Y s ω) with hgsdef
  have hgs_sm : StronglyMeasurable[(𝓕 s : MeasurableSpace Ω)] gs := by
    have hcont : Continuous fun x : ℝ ↦ a ^ 2 * (t : ℝ) / 2 - a * x := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable (h.adapted s))
  have hft_int : Integrable ft Q := by
    have hfac : ft = fun ω ↦ Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω) := by
      funext ω
      change Real.exp (a * Y t ω - a ^ 2 * (t : ℝ) / 2)
          = Real.exp (-(a ^ 2 * (t : ℝ) / 2)) * Real.exp (a * Y t ω)
      rw [show a * Y t ω - a ^ 2 * (t : ℝ) / 2 = -(a ^ 2 * (t : ℝ) / 2) + a * Y t ω from by ring,
        Real.exp_add]
    rw [hfac]; exact (integrable_expY h a htT).const_mul _
  have hprod : (fun ω ↦ gs ω * ft ω) = fun ω ↦ Real.exp (a * (Y t ω - Y s ω)) := by
    funext ω; rw [hgsdef, hftdef, ← Real.exp_add]; congr 1; ring
  have hprod_int : Integrable (fun ω ↦ gs ω * ft ω) Q := by
    rw [hprod]
    refine (integrable_exp_mul_exp ((h.measurable t).const_mul a) ((h.measurable s).const_mul (-a))
      (by simpa only [mul_assoc] using integrable_expY h (2 * a) htT)
      (by simpa only [mul_assoc] using integrable_expY h (2 * -a) (hst.trans htT))).congr ?_
    filter_upwards with ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := (𝓕 s : MeasurableSpace Ω))
    hgs_sm hprod_int hft_int
  have hcond := condExp_expY h a hst htT
  have hint_eq : (fun ω ↦ Real.exp (a * (Y t ω - Y s ω))) = gs * ft := hprod.symm
  rw [hint_eq]
  filter_upwards [hpull, hcond] with ω hp hc
  rw [hp, Pi.mul_apply,
    show (Q[ft | 𝓕 s]) ω = Real.exp (a * Y s ω - a ^ 2 * (s : ℝ) / 2) from hc,
    hgsdef, ← Real.exp_add]
  congr 1; ring

/-- **Unconditional `Q`-MGF of the increment.** `𝔼_Q[exp(a·(Y_t − Y_s))] = exp(½a²(t−s))` — the
tower property on the deterministic conditional MGF `IsExpQMartingale.condExp_exp_increment`. -/
private theorem Y_increment_mgf (h : IsExpQMartingale Q 𝓕 Y T) (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (htT : t ≤ T) :
    ∫ ω, Real.exp (a * (Y t ω - Y s ω)) ∂Q = Real.exp (a ^ 2 * ((t : ℝ) - (s : ℝ)) / 2) := by
  rw [← integral_condExp (𝓕.le s), integral_congr_ae (h.condExp_exp_increment a hst htT),
    integral_const, show Q.real Set.univ = 1 from by simp, one_smul]

/-- **Increment law.** `Q.map (Y_t − Y_s) = N(0, t−s)`: the unconditional increment MGF
(`Y_increment_mgf`) is the Gaussian one. -/
theorem increment_map_eq_gaussianReal_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s) := by
  refine map_eq_gaussianReal_of_mgf ((h.measurable t).sub (h.measurable s)).aemeasurable
    fun a ↦ (Y_increment_mgf h a hst htT).trans ?_
  rw [NNReal.coe_sub hst]
  congr 1
  ring

/-- **`Q`-integrability of the increment exponential.** `exp(c·(Y_t − Y_s))` is `Q`-integrable —
its law is `N(0,t−s)`. -/
private theorem integrable_exp_Y_increment (h : IsExpQMartingale Q 𝓕 Y T) (c : ℝ) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Integrable (fun ω ↦ Real.exp (c * (Y t ω - Y s ω))) Q := by
  have hincmeas : Measurable fun ω ↦ Y t ω - Y s ω := (h.measurable t).sub (h.measurable s)
  rw [show (fun ω ↦ Real.exp (c * (Y t ω - Y s ω)))
        = (fun x ↦ Real.exp (c * x)) ∘ (fun ω ↦ Y t ω - Y s ω) from rfl,
      ← integrable_map_measure (by fun_prop) hincmeas.aemeasurable,
      increment_map_eq_gaussianReal_of_expMartingale h hst htT]
  exact integrable_exp_mul_gaussianReal c

/-! ### Independence of any number of increments -/

/-- **Joint `Q`-MGF of successive increments.** For a monotone sequence of times `t` in `[0,T]` and
reals `a`, `exp(∑_{k<n} a_k·(Y_{t_{k+1}} − Y_{t_k}))` is `Q`-integrable, with integral
`∏_{k<n} exp(½a_k²(t_{k+1} − t_k))`. Induction on `n`: the first `n` increments are
`𝓕_{t_n}`-measurable, so they factor out of the conditional expectation given `𝓕_{t_n}`, and the
conditional MGF of the last one is the deterministic `exp(½a_n²(t_{n+1} − t_n))`
(`IsExpQMartingale.condExp_exp_increment`). Integrability comes along the induction, by
Cauchy–Schwarz (`integrable_exp_mul_exp`). -/
private theorem Y_increments_mgf_range (h : IsExpQMartingale Q 𝓕 Y T) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) (a : ℕ → ℝ) :
    Integrable (fun ω ↦ Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω))) Q ∧
      ∫ ω, Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
        = ∏ k ∈ Finset.range n, Real.exp (a k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) := by
  induction n generalizing a with
  | zero => constructor <;> simp
  | succ n ih =>
    have htn : t n ≤ t (n + 1) := ht (Nat.le_add_right n 1)
    -- the first `n` increments are `𝓕_{t_n}`-measurable
    have hS : StronglyMeasurable[(𝓕 (t n) : MeasurableSpace Ω)]
        (fun ω ↦ ∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω)) :=
      Finset.stronglyMeasurable_fun_sum _ fun k hk ↦ by
        have hk : k + 1 ≤ n := Finset.mem_range.mp hk
        exact ((h.adapted.stronglyMeasurable_le (ht hk)).sub
          (h.adapted.stronglyMeasurable_le (ht (Nat.le_of_succ_le hk)))).const_mul (a k)
    set e1 : Ω → ℝ := fun ω ↦ Real.exp (∑ k ∈ Finset.range n, a k * (Y (t (k + 1)) ω - Y (t k) ω))
    set e2 : Ω → ℝ := fun ω ↦ Real.exp (a n * (Y (t (n + 1)) ω - Y (t n) ω))
    have he1 : StronglyMeasurable[(𝓕 (t n) : MeasurableSpace Ω)] e1 :=
      Real.continuous_exp.comp_stronglyMeasurable hS
    have he2 : Integrable e2 Q := integrable_exp_Y_increment h (a n) htn (htT _)
    have h12 : Integrable (e1 * e2) Q :=
      integrable_exp_mul_exp (hS.mono (𝓕.le (t n))).measurable
        (((h.measurable (t (n + 1))).sub (h.measurable (t n))).const_mul (a n))
        (by simpa only [Finset.mul_sum, mul_assoc] using (ih fun k ↦ 2 * a k).1)
        (by simpa only [mul_assoc] using integrable_exp_Y_increment h (2 * a n) htn (htT _))
    rw [show (fun ω ↦ Real.exp (∑ k ∈ Finset.range (n + 1), a k * (Y (t (k + 1)) ω - Y (t k) ω)))
        = e1 * e2 from funext fun ω ↦ by
          simp only [e1, e2, Pi.mul_apply]
          rw [Finset.sum_range_succ, Real.exp_add]]
    refine ⟨h12, ?_⟩
    calc ∫ ω, (e1 * e2) ω ∂Q
        = ∫ ω, (Q[e1 * e2 | 𝓕 (t n)]) ω ∂Q := (integral_condExp (𝓕.le (t n))).symm
      _ = ∫ ω, e1 ω * Real.exp (a n ^ 2 * ((t (n + 1) : ℝ) - (t n : ℝ)) / 2) ∂Q := by
          refine integral_congr_ae ?_
          filter_upwards [condExp_mul_of_stronglyMeasurable_left
              (m := (𝓕 (t n) : MeasurableSpace Ω)) he1 h12 he2,
            h.condExp_exp_increment (a n) htn (htT (n + 1))] with ω hp hc
          rw [hp, Pi.mul_apply]
          exact congrArg (e1 ω * ·) hc
      _ = (∫ ω, e1 ω ∂Q) * Real.exp (a n ^ 2 * ((t (n + 1) : ℝ) - (t n : ℝ)) / 2) :=
          integral_mul_const _ _
      _ = ∏ k ∈ Finset.range (n + 1), Real.exp (a k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) := by
          rw [Finset.prod_range_succ]
          exact congrArg (· * _) (ih a).2

/-- **Linear combinations of successive increments are Gaussian under `Q`.** For a monotone
sequence of times in `[0,T]` and reals `c`, `∑_{k<n} c_k·(Y_{t_{k+1}} − Y_{t_k})` has law `N(0,v)`
under `Q`, for `v = ∑_{k<n} c_k²(t_{k+1} − t_k)`: its `Q`-MGF is the Gaussian one
(`Y_increments_mgf_range`). -/
private theorem Y_linComb_range_map_eq_gaussianReal (h : IsExpQMartingale Q 𝓕 Y T)
    {t : ℕ → ℝ≥0} (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) (c : ℕ → ℝ) {v : ℝ≥0}
    (hv : (v : ℝ) = ∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) :
    Q.map (fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω))
      = gaussianReal 0 v := by
  have hlin : Measurable fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) :=
    Finset.measurable_sum _ fun k _ ↦ ((h.measurable _).sub (h.measurable _)).const_mul (c k)
  refine map_eq_gaussianReal_of_mgf hlin.aemeasurable fun r ↦ ?_
  have hr : (fun ω ↦ Real.exp (r * ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)))
      = fun ω ↦ Real.exp (∑ k ∈ Finset.range n, (r * c k) * (Y (t (k + 1)) ω - Y (t k) ω)) := by
    funext ω; simp only [Finset.mul_sum, mul_assoc]
  have hmgfn :
      ∫ ω, Real.exp (∑ k ∈ Finset.range n, (r * c k) * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
        = ∏ k ∈ Finset.range n, Real.exp ((r * c k) ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) / 2) :=
    (Y_increments_mgf_range h ht htT n fun k ↦ r * c k).2
  change ∫ ω, Real.exp (r * ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)) ∂Q
      = Real.exp (v * r ^ 2 / 2)
  rw [hr, hmgfn, ← Real.exp_sum, hv, Finset.sum_mul, Finset.sum_div]
  exact congrArg Real.exp (Finset.sum_congr rfl fun k _ ↦ by ring)

/-- **Successive increments are jointly `Q`-independent.** For a monotone sequence of times `t` in
`[0,T]`, the increments `Y_{t_{k+1}} − Y_{t_k}`, `k < n`, are independent under `Q`. By
`iIndepFun_iff_charFun_pi` independence is the factorisation of the joint characteristic function.
At `w` it is the characteristic function at `1` of the Gaussian linear combination
`∑_k w_k·(Y_{t_{k+1}} − Y_{t_k})` (`Y_linComb_range_map_eq_gaussianReal`), which is the product of
the marginal Gaussian characteristic functions. -/
theorem increments_iIndepFun_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {t : ℕ → ℝ≥0}
    (ht : Monotone t) (htT : ∀ k, t k ≤ T) (n : ℕ) :
    iIndepFun (fun (i : Fin n) ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) Q := by
  have hX (i : Fin n) : AEMeasurable (fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) Q :=
    ((h.measurable _).sub (h.measurable _)).aemeasurable
  refine (iIndepFun_iff_charFun_pi hX).mpr fun w ↦ ?_
  set c : ℕ → ℝ := fun k ↦ if hk : k < n then w ⟨k, hk⟩ else 0
  have hc (i : Fin n) : c i = w i := dite_eq_left i.isLt
  have hσ2 : 0 ≤ ∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ)) :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_add_right k 1))))
  have hmarg (i : Fin n) : charFun (Q.map fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) (w i)
      = Complex.exp ((-(w i ^ 2 * ((t ((i : ℕ) + 1) : ℝ) - (t i : ℝ)) / 2) : ℝ) : ℂ) := by
    rw [increment_map_eq_gaussianReal_of_expMartingale h (ht (Nat.le_add_right _ 1)) (htT _),
      charFun_gaussianReal, NNReal.coe_sub (ht (Nat.le_add_right _ 1))]
    congr 1
    push_cast
    ring
  have hsum : ∑ i : Fin n, -(w i ^ 2 * ((t ((i : ℕ) + 1) : ℝ) - (t i : ℝ)) / 2)
      = -(∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) / 2 := by
    rw [← Fin.sum_univ_eq_sum_range, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hc i]
  calc charFun (Q.map fun ω ↦ WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) w
      -- the joint characteristic function at `w` is that of `∑ₖ wₖ·(Y_{tₖ₊₁} − Y_{tₖ})` at `1`,
      = charFun (Q.map fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω)) 1 := by
        have hvec : Measurable fun ω ↦
            WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω :=
          (WithLp.measurable_toLp 2 _).comp
            (Measurable.of_eval fun i ↦ (h.measurable _).sub (h.measurable _) :
              Measurable fun ω (i : Fin n) ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω)
        have hlin : Measurable fun ω ↦ ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) :=
          Finset.measurable_sum _ fun k _ ↦ ((h.measurable _).sub (h.measurable _)).const_mul (c k)
        rw [charFun_apply, charFun_apply_real, integral_map hvec.aemeasurable (by fun_prop),
          integral_map hlin.aemeasurable (by fun_prop)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        have hinner : ⟪WithLp.toLp 2 fun i : Fin n ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω, w⟫
            = ∑ k ∈ Finset.range n, c k * (Y (t (k + 1)) ω - Y (t k) ω) := by
          rw [PiLp.inner_apply, ← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hc i]
          simp only [RCLike.inner_apply, conj_trivial]
        simp only [hinner, Complex.ofReal_one, one_mul]
      -- a centred Gaussian with the diagonal variance,
      _ = Complex.exp ((-(∑ k ∈ Finset.range n, c k ^ 2 * ((t (k + 1) : ℝ) - (t k : ℝ))) / 2 : ℝ)
            : ℂ) := by
        rw [Y_linComb_range_map_eq_gaussianReal h ht htT n c (Real.coe_toNNReal _ hσ2),
          charFun_gaussianReal, Real.coe_toNNReal _ hσ2]
        congr 1
        push_cast
        ring
      -- so the product of the marginal Gaussian characteristic functions
      _ = ∏ i : Fin n, charFun (Q.map fun ω ↦ Y (t ((i : ℕ) + 1)) ω - Y (t i) ω) (w i) := by
        rw [Finset.prod_congr rfl fun i _ ↦ hmarg i, ← Complex.exp_sum, ← Complex.ofReal_sum, hsum]

/-- **Independent increments under `Q`.** On `[0,T]`, `Y` has independent increments under `Q` in
Mathlib's sense: for times `t₀ ≤ ⋯ ≤ tₙ` in `[0,T]`, the increments `Y_{t₁} − Y_{t₀}, …,
Y_{tₙ} − Y_{tₙ₋₁}` are jointly independent. Every finite family of increments along a monotone
sequence sits inside the first `N` of them (`increments_iIndepFun_of_expMartingale`). -/
theorem hasIndepIncrements_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) :
    HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q := by
  refine HasIndepIncrements.of_nat fun τ hτ _ ↦ iIndepFun_iff_finset.2 fun S ↦ ?_
  obtain ⟨N, hN⟩ := S.exists_nat_subset_range
  exact (increments_iIndepFun_of_expMartingale h (t := fun k ↦ (τ k : ℝ≥0))
      (fun i j hij ↦ Subtype.coe_le_coe.mpr (hτ hij)) (fun k ↦ Set.mem_Iic.mp (τ k).2) N).precomp
    (g := fun k : S ↦ (⟨k, Finset.mem_range.mp (hN k.2)⟩ : Fin N))
    fun a b hab ↦ Subtype.ext (congrArg Fin.val hab)

/-- **`Y` has the finite-dimensional laws of a Brownian motion on `[0,T]` under `Q`**: zero start,
`N(0,t−s)` increments, and independent increments (`HasIndepIncrements`). Path continuity and
independence of the increments from the past are not part of it.

This is `IsPreBrownianReal` restricted to a horizon, and it has to be a separate predicate:
`IsPreBrownianReal Y Q` quantifies over all of `ℝ≥0`, while a Girsanov measure
`Q = μ.withDensity(Z_T)` is only defined up to the horizon `T`. Nor can it be phrased as
`IsPreBrownianReal` of the process stopped at `T`, whose increments past `T` vanish and whose
variance is `t ∧ T`, not `t`. -/
def IsBrownianOn (Q : Measure Ω) (T : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂Q, Y 0 ω = 0)
    ∧ (∀ ⦃s t : ℝ≥0⦄, s ≤ t → t ≤ T → Q.map (fun ω ↦ Y t ω - Y s ω) = gaussianReal 0 (t - s))
    ∧ HasIndepIncrements (fun t : Set.Iic T ↦ Y t) Q

/-- **Being Brownian on `[0,T]` is invariant under a modification.** If `X` and `Y` agree
`Q`-a.e. at every time `u ≤ T`, each of the three properties depends on the process only through
finitely many of its coordinates, up to `Q`-null sets. -/
theorem IsBrownianOn.congr_modification {Q : Measure Ω} {T : ℝ≥0} {X Y : ℝ≥0 → Ω → ℝ}
    (h : ∀ u ≤ T, X u =ᵐ[Q] Y u) (hX : IsBrownianOn Q T X) : IsBrownianOn Q T Y := by
  obtain ⟨h0, hlaw, hind⟩ := hX
  refine ⟨?_, fun s t hst htT ↦ ?_, fun n t ht ↦ ?_⟩
  · filter_upwards [h0, h 0 zero_le] with ω h1 h2
    rw [← h2]
    exact h1
  · rw [← hlaw hst htT]
    exact Measure.map_congr ((h t htT).sub (h s (hst.trans htT))).symm
  · exact iIndepFun.congr
      (fun i ↦ (h (t i.succ) (t i.succ).2).sub (h (t i.castSucc) (t i.castSucc).2))
      (hind n t ht)

/-- **Brownian increment laws from an exponential martingale.** From the exponential-martingale
data `IsExpQMartingale Q 𝓕 Y T`, the process `Y` is Brownian on `[0,T]` under `Q`
(`IsBrownianOn`):

* **zero start**: `Y_0 = 0` a.e. `Q` (the hypothesis `zero_start`, restated);
* **Gaussian increments**: `Y_t − Y_s ~ N(0, t−s)`
  (`increment_map_eq_gaussianReal_of_expMartingale`);
* **independent increments**: `HasIndepIncrements` for `Y` restricted to `[0,T]`
  (`hasIndepIncrements_of_expMartingale`).

Together these fix every finite-dimensional law of `Y` on `[0,T]` to that of a Brownian motion.
Neither path continuity nor independence of the increments from `𝓕_s` is part of the conclusion.
Process- and measure-agnostic: any drift-corrected Girsanov process supplying its own exponential
martingale (via the Bayes engine) gets these three properties by one application of this
theorem. -/
theorem isQBrownianMotion_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) : IsBrownianOn Q T Y :=
  ⟨h.zero_start, fun _ _ hst htT ↦ increment_map_eq_gaussianReal_of_expMartingale h hst htT,
    hasIndepIncrements_of_expMartingale h⟩

end MathFin
