/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.EuropeanReplication
public import LeanPool.MathFin.Probability.Discrete.SnellEnvelope
public import LeanPool.MathFin.Probability.Discrete.MarkovPathMeasure
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The binomial price as an expectation over coin-flip paths

`binomialPrice u d r g N S₀` (`Models/Binomial/Model.lean`) is the backward-induction price of the
`N`-step CRR tree, and `Models/Binomial/SnellEnvelope.lean` works on coin-flip paths `ω : ℕ → Bool`
with the spot `spotPath S₀ u d N ω = S₀ · ∏_{i<N} (u if ωᵢ else d)`, without a measure on paths.
Here the paths get one: `coinFlipMeasure q`, the infinite product of Mathlib's
`bernoulliMeasure` on `Bool` (the law of i.i.d. `Bernoulli(q)` flips). With `q = crrUpProb u d r`
the backward recursion is an expectation over whole paths under i.i.d. `Bernoulli(crrUpProb)`
flips (risk-neutral under `BinomialNoArb`, `crrUpProb_mul_up_add`, which is not assumed here):

  `binomialPrice u d r g N S₀ = e^{−rN} · ∫ g(spotPath S₀ u d N ω) d(coinFlipMeasure q)(ω)`.

The cylinder probabilities `q^{#up}(1 − q)^{#down}` are not assumed: they come from
`Measure.infinitePi_pi`, the product-measure formula. The
library's other probabilistic form of the price, `binomialPrice_eq_integral_convPow`
(`Models/Binomial/CRRCharFun.lean`), integrates over the law of the terminal log-return instead.

## Main definitions

* `coinMeasure`: the law of one `Bernoulli(q)` flip on `Bool`.
* `coinFlipMeasure`: the law of i.i.d. `Bernoulli(q)` flips on `ℕ → Bool`, the infinite product of
  `coinMeasure`.
* `flips`: the first `N` flips of a path.
* `flipFiltration`: the natural filtration of the coin flips, `ℱₙ = σ(ω₀, …, ω_{n−1})`.

## Main results

* `coinFlipMeasure_cylinder` — the first `n + 1` flips of a path have probability
  `∏_{k ≤ n} Bernoulli(q)(path k)`.
* `integral_comp_flips` — the integral of a function of the first `N` flips is the finite sum
  over the `2^N` flip sequences weighted by their probabilities.
* `binomialPrice_eq_sum` — the backward recursion unrolled into that finite sum.
* `binomialPrice_eq_integral_coinFlipMeasure` — the price as an expectation over paths.
* `measurable_spotPath`, `abs_spotPath_le` — the spot after `k` flips is a measurable, bounded
  function of the path.
* `stronglyMeasurable_flipFiltration_iff` — a real function is `ℱₙ`-strongly measurable for
  `flipFiltration` exactly when it is the library's `PathAdaptedAt n` (it depends only on the
  first `n` flips).
* `martingale_of_oneStep` — a path process adapted to the flips whose node averages
  `q M_{n+1}(…,↑) + (1 − q) M_{n+1}(…,↓) = M_n` close up is a Mathlib `Martingale` under
  `coinFlipMeasure q`; the independence of the flips comes from `iIndepFun_infinitePi`.
* `martingale_discountedSpot`, `martingale_discountedTreeValue` — the discounted CRR spot and
  the discounted tree price are Mathlib martingales under `coinFlipMeasure (crrUpProb …)`.
* `snell_ae_eq_snellEnvelope` — the tree's pathwise Snell envelope `snell` is, almost surely and
  at times `k ≤ N`, the library's Snell envelope `snellEnvelope`
  (`Probability/Discrete/SnellEnvelope.lean`) of the same payoff for the flip filtration under
  `coinFlipMeasure`: `snell` is its explicit form, computed by the node-average conditional
  expectation (`condExp_flipFiltration_succ`).
* `supermartingale_snell` — the pathwise `snell`, frozen at the horizon, is a Mathlib
  `Supermartingale` for `flipFiltration` under `coinFlipMeasure`.
* `snellEnvelope_discounted_bermudanPrice` — the Snell envelope of the discounted payoff
  `e^{−rn} g(Sₙ)` is, at every time `k ≤ N` and almost surely, the discounted `bermudanPrice`.

## References

* [J. C. Cox, S. A. Ross and M. Rubinstein, *Option pricing: a simplified
  approach*][CoxRossRubinstein1979]
* [D. Lamberton and B. Lapeyre, *Introduction to Stochastic Calculus Applied to
  Finance*][LambertonLapeyre2008], §2.2
* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Ch. 4; §2.4

## Tags

coin-flip measure, risk-neutral expectation, Bernoulli product measure, Snell envelope, path space,
binomial filtration, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

/-- The law of one `Bernoulli(q)` flip on `Bool`: `true` with probability `q`, `false` with
probability `1 − q` (Mathlib's `bernoulliMeasure`). -/
noncomputable def coinMeasure (q : ℝ≥0) (hq : q ≤ 1) : Measure Bool :=
  bernoulliMeasure true false ⟨q, q.2, by exact_mod_cast hq⟩

instance (q : ℝ≥0) (hq : q ≤ 1) : IsProbabilityMeasure (coinMeasure q hq) := by
  unfold coinMeasure bernoulliMeasure
  refine ⟨?_⟩
  simp only [measure_univ]

lemma coinMeasure_singleton (q : ℝ≥0) (hq : q ≤ 1) (b : Bool) :
    coinMeasure q hq {b} = if b then (q : ℝ≥0∞) else 1 - q := by
  cases b
  · rw [coinMeasure, bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub]
    congr 1
    ext
    simp [NNReal.coe_sub hq]
  · rw [coinMeasure, bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    rfl

/-- The law of i.i.d. `Bernoulli(q)` coin flips on `ℕ → Bool`: the infinite product of
`Bernoulli(q)` measures. -/
noncomputable def coinFlipMeasure (q : ℝ≥0) (hq : q ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ ↦ coinMeasure q hq

instance (q : ℝ≥0) (hq : q ≤ 1) : IsProbabilityMeasure (coinFlipMeasure q hq) := by
  unfold coinFlipMeasure
  infer_instance

/-- **Cylinder probabilities of the coin-flip measure.** The event that a path agrees with
`path` up to time `n` has probability `∏_{k ≤ n} Bernoulli(q)(path k)`: the product-measure
formula `infinitePi_pi` on the box `∏_{k ≤ n} {path k}`. -/
theorem coinFlipMeasure_cylinder (q : ℝ≥0) (hq : q ≤ 1) (path : ℕ → Bool) (n : ℕ) :
    coinFlipMeasure q hq (pathCylinder path n)
      = ∏ k ∈ range (n + 1), if path k then (q : ℝ≥0∞) else 1 - q := by
  have : pathCylinder path n = Set.pi (range (n + 1) : Finset ℕ) fun k ↦ {path k} := by
    ext ω
    simp [pathCylinder]
  rw [this, coinFlipMeasure, Measure.infinitePi_pi _ fun _ _ ↦ measurableSet_singleton _]
  exact prod_congr rfl fun k _ ↦ coinMeasure_singleton q hq _

/-- The first `N` flips of a path. -/
def flips (N : ℕ) (ω : ℕ → Bool) : Fin N → Bool := fun i ↦ ω i

lemma measurable_flips (N : ℕ) : Measurable (flips N) :=
  .of_eval fun i ↦ measurable_pi_apply (i : ℕ)

/-- A function of the first `n` flips factors through `flips n`. -/
lemma PathAdaptedAt.eq_comp_flips {n : ℕ} {f : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt n f) :
    f = (fun x : Fin n → Bool ↦ f fun k ↦ if h : k < n then x ⟨k, h⟩ else false) ∘ flips n :=
  funext fun ω ↦ hf _ _ fun i hi ↦ by simp [flips, hi]

/-- The **natural filtration of the coin flips**: `ℱₙ = σ(ω₀, …, ω_{n−1})` is generated by the
first `n` flips, the information revealed by time `n`. (Mathlib's `Filtration.natural` of the
coordinate process is indexed one step ahead, `ℱₙ ∋ ωₙ`; the trees here reveal flip `n` at time
`n + 1`.) -/
def flipFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Bool)) where
  seq n := MeasurableSpace.comap (flips n) inferInstance
  mono' m n hmn := by
    have : flips m = (fun x : Fin n → Bool ↦ fun i : Fin m ↦ x (Fin.castLE hmn i)) ∘ flips n :=
      rfl
    dsimp only
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))
  le' n := (measurable_flips n).comap_le

/-- **The measurable functions of the natural flip filtration are the `n`-adapted ones.** A real
function is `ℱₙ`-strongly measurable exactly when it depends only on the first `n` flips. -/
theorem stronglyMeasurable_flipFiltration_iff {n : ℕ} {f : (ℕ → Bool) → ℝ} :
    StronglyMeasurable[flipFiltration n] f ↔ PathAdaptedAt n f := by
  constructor
  · intro hf ω ω' h
    obtain ⟨t, -, ht⟩ := hf.measurable (measurableSet_singleton (f ω))
    have hω : flips n ω ∈ t := by
      have : ω ∈ f ⁻¹' {f ω} := rfl
      rwa [← ht] at this
    have hflips : flips n ω' = flips n ω := funext fun i ↦ (h i i.2).symm
    have hω' : ω' ∈ f ⁻¹' {f ω} := by
      rw [← ht]
      exact (show flips n ω' ∈ t by rw [hflips]; exact hω)
    exact hω'.symm
  · intro hf
    rw [hf.eq_comp_flips]
    exact ((measurable_of_countable _).comp (comap_measurable (flips n))).stronglyMeasurable

section Martingale

variable {q : ℝ≥0} (hq : q ≤ 1)

/-- A function of the first `n` flips is integrable: it takes finitely many values. -/
lemma PathAdaptedAt.integrable {n : ℕ} {f : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt n f) :
    Integrable f (coinFlipMeasure q hq) := by
  rw [hf.eq_comp_flips]
  exact Integrable.of_finite.comp_measurable (measurable_flips n)

/-- The `n`-th flip is independent of the first `n`. -/
lemma indep_flip_flipFiltration (n : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → Bool ↦ ω n) inferInstance) (flipFiltration n)
      (coinFlipMeasure q hq) := by
  have hind : iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) ↦ ω i) (coinFlipMeasure q hq) :=
    iIndepFun_infinitePi (P := fun _ ↦ coinMeasure q hq) (X := fun _ x ↦ x)
      fun _ ↦ measurable_id
  have := (hind.indepFun_finset {n} (range n) (by simp) fun i ↦ measurable_pi_apply i).comp
    (φ := fun x : ↥({n} : Finset ℕ) → Bool ↦ x (Subtype.mk n (mem_singleton_self n)))
    (ψ := fun x : ↥(range n) → Bool ↦ fun i : Fin n ↦ x (Subtype.mk (i : ℕ) (mem_range.2 i.2)))
    (measurable_pi_apply (X := fun _ : ↥({n} : Finset ℕ) ↦ Bool) ⟨n, mem_singleton_self n⟩)
    (by fun_prop)
  exact this

/-- The expected value of the `n`-th flip indicator is `q`. -/
lemma integral_flip_indicator (n : ℕ) :
    ∫ ω, (if ω n then (1 : ℝ) else 0) ∂coinFlipMeasure q hq = q := by
  have hmap : (coinFlipMeasure q hq).map (fun ω ↦ ω n) = coinMeasure q hq :=
    Measure.infinitePi_map_eval _ n
  have h := integral_map (μ := coinFlipMeasure q hq) (φ := fun ω : ℕ → Bool ↦ ω n)
    (f := fun b : Bool ↦ if b then (1 : ℝ) else 0) (measurable_pi_apply n).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable
  rw [hmap] at h
  refine h.symm.trans ?_
  rw [integral_fintype Integrable.of_finite]
  simp [measureReal_def, coinMeasure_singleton]

end Martingale

lemma flips_preimage_singleton (n : ℕ) (x : Fin (n + 1) → Bool) :
    flips (n + 1) ⁻¹' {x} = pathCylinder (fun k ↦ if h : k < n + 1 then x ⟨k, h⟩ else false) n := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, flips, pathCylinder,
    Set.mem_ofPred_eq]
  constructor
  · intro h k hk
    rw [dite_eq_left (Nat.lt_succ_of_le hk)]
    exact h ⟨k, Nat.lt_succ_of_le hk⟩
  · intro h i
    have hi := h i (Nat.le_of_lt_succ i.isLt)
    rwa [dite_eq_left i.isLt] at hi

/-- The probability that the first `N` flips are `x` is `∏ᵢ Bernoulli(q)(xᵢ)`. -/
theorem coinFlipMeasure_flips_preimage (q : ℝ≥0) (hq : q ≤ 1) (N : ℕ) (x : Fin N → Bool) :
    coinFlipMeasure q hq (flips N ⁻¹' {x}) = ∏ i, if x i then (q : ℝ≥0∞) else 1 - q := by
  cases N with
  | zero =>
    have huniv : flips 0 ⁻¹' {x} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ Subsingleton.elim (flips 0 ω) x
    rw [huniv, measure_univ, Finset.univ_eq_empty, prod_empty]
  | succ n =>
    rw [flips_preimage_singleton, coinFlipMeasure_cylinder, ← Fin.prod_univ_eq_prod_range]
    exact prod_congr rfl fun i _ ↦ by simp [i.isLt]

/-- **Full support on cylinders.** For `0 < q < 1`, every finite flip sequence has positive
probability. -/
theorem coinFlipMeasure_flips_preimage_pos {q : ℝ≥0} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ)
    (x : Fin N → Bool) : 0 < coinFlipMeasure q hq1.le (flips N ⁻¹' {x}) := by
  rw [coinFlipMeasure_flips_preimage, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact_mod_cast hq0.ne'
  · exact (tsub_pos_iff_lt.2 (by exact_mod_cast hq1)).ne'

/-- **Almost-sure equality of functions of finitely many flips is pointwise equality**, for
`0 < q < 1`: the cylinder through every path has positive probability. -/
theorem PathAdaptedAt.eq_of_ae_eq {q : ℝ≥0} (hq0 : 0 < q) (hq1 : q < 1) {n : ℕ}
    {f g : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt n f) (hg : PathAdaptedAt n g)
    (h : f =ᵐ[coinFlipMeasure q hq1.le] g) (ω : ℕ → Bool) : f ω = g ω := by
  by_contra hne
  refine (coinFlipMeasure_flips_preimage_pos hq0 hq1 n (flips n ω)).ne' ?_
  refine measure_mono_null (fun ω' (hω' : flips n ω' = flips n ω) ↦ ?_) (ae_iff.1 h)
  have hagree : ∀ i, i < n → ω' i = ω i := fun i hi ↦ congrFun hω' ⟨i, hi⟩
  change ¬ f ω' = g ω'
  rw [hf ω' ω hagree, hg ω' ω hagree]
  exact hne

/-- **Integrals of functions of finitely many flips are finite sums.** For any
`F : (Fin N → Bool) → ℝ`, the expectation of `F` of the first `N` flips is the sum over the
`2^N` flip sequences `x` of `F x` weighted by `∏ᵢ Bernoulli(q)(xᵢ)`. -/
theorem integral_comp_flips (q : ℝ≥0) (hq : q ≤ 1) (N : ℕ) (F : (Fin N → Bool) → ℝ) :
    ∫ ω, F (flips N ω) ∂coinFlipMeasure q hq
      = ∑ x, (∏ i, if x i then (q : ℝ) else 1 - q) * F x := by
  rw [← integral_map (measurable_flips N).aemeasurable
      (measurable_of_countable F).aestronglyMeasurable, integral_fintype Integrable.of_finite]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, measureReal_def, Measure.map_apply (measurable_flips N)
    (measurableSet_singleton x), coinFlipMeasure_flips_preimage, ENNReal.toReal_prod]
  congr 1
  refine prod_congr rfl fun i _ ↦ ?_
  cases x i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ENNReal.toReal_sub_of_le (ENNReal.coe_le_one_iff.mpr hq) ENNReal.one_ne_top]
    simp
  | true => simp

/-- **The backward recursion unrolled.** For `q = crrUpProb u d r`, the `N`-step binomial
price is `e^{−rN}` times the sum over the `2^N` up/down sequences `x` of
`(∏ᵢ (q if xᵢ else 1 − q)) · g(S · ∏ᵢ (u if xᵢ else d))`. -/
theorem binomialPrice_eq_sum (u d r q : ℝ) (hq : crrUpProb u d r = q) (g : ℝ → ℝ) (N : ℕ)
    (S : ℝ) :
    binomialPrice u d r g N S = Real.exp (-(r * N)) *
      ∑ x : Fin N → Bool, (∏ i, if x i then q else 1 - q) * g (S * ∏ i, if x i then u else d) := by
  induction N generalizing S with
  | zero => simp
  | succ n ih =>
    have hsplit : ∑ x : Fin (n + 1) → Bool,
          (∏ i, if x i then q else 1 - q) * g (S * ∏ i, if x i then u else d)
        = q * ∑ y : Fin n → Bool,
            (∏ i, if y i then q else 1 - q) * g (S * u * ∏ i, if y i then u else d)
          + (1 - q) * ∑ y : Fin n → Bool,
            (∏ i, if y i then q else 1 - q) * g (S * d * ∏ i, if y i then u else d) := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ Bool).sum_comp, Fintype.sum_prod_type,
          Fintype.sum_bool,
        mul_sum, mul_sum]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, Bool.false_eq_true, ↓reduceIte, mul_assoc]
    rw [binomialPrice_succ, hq, ih, ih, hsplit,
      show -(r * ((n + 1 : ℕ) : ℝ)) = -r + -(r * n) by push_cast; ring, Real.exp_add]
    ring

/-- **The binomial price is an expectation over coin-flip paths.** If the CRR
risk-neutral up-probability `crrUpProb u d r` is `q ∈ [0, 1]`, then for every payoff `g`,
horizon `N` and spot `S₀`,

  `binomialPrice u d r g N S₀ = e^{−rN} · ∫ g(spotPath S₀ u d N ω) d(coinFlipMeasure q)(ω)`,

where `coinFlipMeasure q` is the infinite product measure of i.i.d. `Bernoulli(q)` flips
on `ℕ → Bool`. -/
theorem binomialPrice_eq_integral_coinFlipMeasure (u d r : ℝ) (g : ℝ → ℝ) {q : ℝ≥0}
    (hq : q ≤ 1) (hqcrr : crrUpProb u d r = q) (N : ℕ) (S₀ : ℝ) :
    binomialPrice u d r g N S₀
      = Real.exp (-(r * N)) * ∫ ω, g (spotPath S₀ u d N ω) ∂coinFlipMeasure q hq := by
  have hspot (ω : ℕ → Bool) :
      g (spotPath S₀ u d N ω) = g (S₀ * ∏ i, if flips N ω i then u else d) := by
    rw [spotPath, ← Fin.prod_univ_eq_prod_range]
    rfl
  rw [binomialPrice_eq_sum u d r (q : ℝ) hqcrr g N S₀]
  congr 1
  rw [integral_congr_ae (ae_of_all _ hspot), integral_comp_flips q hq N
    fun x ↦ g (S₀ * ∏ i, if x i then u else d)]

/-- The spot after `k` flips is a measurable function of the path. -/
theorem measurable_spotPath (S₀ u d : ℝ) (k : ℕ) : Measurable (spotPath S₀ u d k) :=
  measurable_const.mul (Finset.measurable_prod _ fun i _ ↦
    (measurable_of_countable fun b : Bool ↦ if b then u else d).comp (measurable_pi_apply i))

/-- The spot after `k` flips is at most `|S₀| · max(|u|, |d|)ᵏ` in absolute value, along every
path. -/
theorem abs_spotPath_le (S₀ u d : ℝ) (k : ℕ) (ω : ℕ → Bool) :
    |spotPath S₀ u d k ω| ≤ |S₀| * max |u| |d| ^ k := by
  rw [spotPath, abs_mul, abs_prod]
  gcongr
  calc ∏ i ∈ range k, |if ω i then u else d| ≤ ∏ _i ∈ range k, max |u| |d| :=
        prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ by split_ifs <;> simp
    _ = max |u| |d| ^ k := by simp

section Martingale

variable {q : ℝ≥0} (hq : q ≤ 1)

/-- **The conditional expectation of a function of `n + 1` flips is its node average.** For `f`
depending only on the first `n + 1` flips, `E[f | ℱₙ](ω) = q f(ω, flip n up) + (1 − q) f(ω, flip n
down)` almost surely, because the next flip is independent of the past
(`indep_flip_flipFiltration`, from `iIndepFun_infinitePi`). -/
theorem condExp_flipFiltration_succ {n : ℕ} {f : (ℕ → Bool) → ℝ} (hf : PathAdaptedAt (n + 1) f) :
    (coinFlipMeasure q hq)[f | flipFiltration n] =ᵐ[coinFlipMeasure q hq]
      fun ω ↦ (q : ℝ) * f (Function.update ω n true) + (1 - q) * f (Function.update ω n false) := by
  set μ := coinFlipMeasure q hq
  set A : (ℕ → Bool) → ℝ := fun ω ↦ f (Function.update ω n true)
  set B : (ℕ → Bool) → ℝ := fun ω ↦ f (Function.update ω n false)
  set ind : (ℕ → Bool) → ℝ := fun ω ↦ if ω n then 1 else 0
  have hA := hf.fixFlip (n := n) true
  have hB := hf.fixFlip (n := n) false
  have hdecomp : f = B + (A - B) * ind := by
    funext ω
    have e := Function.update_eq_self n ω
    cases hω : ω n
    · rw [hω] at e
      simp [A, B, ind, hω, e]
    · rw [hω] at e
      simp [A, B, ind, hω, e]
  have hind_sm : StronglyMeasurable[MeasurableSpace.comap (fun ω : ℕ → Bool ↦ ω n) inferInstance]
      ind :=
    ((measurable_of_countable fun b : Bool ↦ if b then (1 : ℝ) else 0).comp
      (comap_measurable fun ω : ℕ → Bool ↦ ω n)).stronglyMeasurable
  have hind_int : Integrable ind μ :=
    Integrable.of_finite.comp_measurable (g := fun b : Bool ↦ if b then (1 : ℝ) else 0)
      (measurable_pi_apply n)
  have hAB_sm : StronglyMeasurable[flipFiltration n] (A - B) :=
    (stronglyMeasurable_flipFiltration_iff.2 hA).sub (stronglyMeasurable_flipFiltration_iff.2 hB)
  have hBint : Integrable B μ := hB.integrable hq
  have hmul_int : Integrable ((A - B) * ind) μ := by
    have : (A - B) * ind = f - B := by rw [hdecomp]; ring
    rw [this]
    exact (hf.integrable hq).sub hBint
  have hind_cond : μ[ind | flipFiltration n] =ᵐ[μ] fun _ ↦ (q : ℝ) :=
    (condExp_indep_eq (measurable_pi_apply n).comap_le (flipFiltration.le n) hind_sm
      (indep_flip_flipFiltration hq n)).trans (by rw [integral_flip_indicator hq])
  have h1 := condExp_add hBint hmul_int (flipFiltration n) (μ := μ)
  have hc : μ[f | flipFiltration n] = μ[B + (A - B) * ind | flipFiltration n] := by
    rw [← hdecomp]
  rw [hc]
  filter_upwards [h1, condExp_mul_of_stronglyMeasurable_left hAB_sm hmul_int hind_int
      (m := flipFiltration n), hind_cond] with ω h1 h2 h3
  rw [Pi.add_apply] at h1
  rw [h1, h2, condExp_of_stronglyMeasurable (flipFiltration.le n)
    (stronglyMeasurable_flipFiltration_iff.2 hB) hBint, Pi.mul_apply, h3]
  simp only [Pi.sub_apply, A, B]
  ring

/-- **One-step node averages make a martingale.** A path process `M` adapted to the flips
(`Mₙ` depends only on the first `n` flips) whose node averages close up,
`q Mₙ₊₁(ω, flip n up) + (1 − q) Mₙ₊₁(ω, flip n down) = Mₙ(ω)`, is a Mathlib `Martingale` for
the natural flip filtration under i.i.d. `Bernoulli(q)` flips
(`condExp_flipFiltration_succ`). -/
theorem martingale_of_oneStep {M : ℕ → (ℕ → Bool) → ℝ} (hM : ∀ n, PathAdaptedAt n (M n))
    (hstep : ∀ n ω, (q : ℝ) * M (n + 1) (Function.update ω n true)
      + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω) :
    Martingale M flipFiltration (coinFlipMeasure q hq) :=
  martingale_nat (fun n ↦ stronglyMeasurable_flipFiltration_iff.2 (hM n))
    (fun n ↦ (hM n).integrable hq) fun n ↦
      ((condExp_flipFiltration_succ hq (hM (n + 1))).trans (ae_of_all _ (hstep n))).symm

/-- **A process adapted to the flips is a martingale exactly when its node averages close up**,
for `0 < q < 1` (every node has positive probability, so the almost-sure identity holds at
every path). The converse of `martingale_of_oneStep`. -/
theorem oneStep_of_martingale (hq0 : 0 < q) (hq1 : q < 1) {M : ℕ → (ℕ → Bool) → ℝ}
    (hM : Martingale M flipFiltration (coinFlipMeasure q hq1.le)) (n : ℕ) (ω : ℕ → Bool) :
    (q : ℝ) * M (n + 1) (Function.update ω n true)
      + (1 - q) * M (n + 1) (Function.update ω n false) = M n ω := by
  have hn1 : PathAdaptedAt (n + 1) (M (n + 1)) :=
    stronglyMeasurable_flipFiltration_iff.1 (hM.stronglyAdapted (n + 1))
  have hn : PathAdaptedAt n (M n) := stronglyMeasurable_flipFiltration_iff.1 (hM.stronglyAdapted n)
  have hae := (condExp_flipFiltration_succ hq1.le hn1).symm.trans
    (hM.2 n (n + 1) n.le_succ)
  refine PathAdaptedAt.eq_of_ae_eq hq0 hq1 (fun ω ω' h ↦ ?_) hn hae ω
  have h1 := hn1.fixFlip true ω ω' h
  have h2 := hn1.fixFlip false ω ω' h
  simp only at h1 h2
  rw [h1, h2]

end Martingale

/-- **The discounted CRR spot is a martingale** under i.i.d. `Bernoulli(crrUpProb)` flips,
for the natural flip filtration: the Mathlib `Martingale` form of `discountedSpot_step`. -/
theorem martingale_discountedSpot {u d r : ℝ} (h : BinomialNoArb u d r) (S₀ : ℝ) {q : ℝ≥0}
    (hq : q ≤ 1) (hqcrr : crrUpProb u d r = q) :
    Martingale (discountedSpot S₀ u d r) flipFiltration (coinFlipMeasure q hq) :=
  martingale_of_oneStep hq (pathAdaptedAt_discountedSpot S₀ u d r) fun n ω ↦ by
    simpa [hqcrr] using discountedSpot_step h S₀ n ω

/-- **The discounted tree price of a European claim is a martingale** under i.i.d.
`Bernoulli(crrUpProb)` flips: the Mathlib `Martingale` form of `discountedTreeValue_step`. -/
theorem martingale_discountedTreeValue (u d r : ℝ) (g : ℝ → ℝ) (N : ℕ) (S₀ : ℝ) {q : ℝ≥0}
    (hq : q ≤ 1) (hqcrr : crrUpProb u d r = q) :
    Martingale (discountedTreeValue u d r g N S₀) flipFiltration (coinFlipMeasure q hq) :=
  martingale_of_oneStep hq (pathAdaptedAt_discountedTreeValue u d r g N S₀) fun n ω ↦ by
    simpa [hqcrr] using discountedTreeValue_step u d r g N S₀ n ω

section Snell

variable {q : ℝ≥0} (hq : q ≤ 1) {E : Set ℕ} {Z : ℕ → (ℕ → Bool) → ℝ}

/-- **The pathwise Snell envelope is the Snell envelope, with `j` steps left from time `k`.** For a
payoff process adapted to the flips, `snellAux E q Z j k` agrees almost surely under
`coinFlipMeasure q` with `snellEnvelopeAux` for the flip filtration, whose exercise times are those
`i` with `N - i ∈ E` (`N = k + j` the horizon): the conditional expectation of the recursion is the
node average (`condExp_flipFiltration_succ`). -/
theorem snellAux_ae_eq_snellEnvelopeAux (hZ : ∀ n, PathAdaptedAt n (Z n)) (N : ℕ) :
    ∀ j k, k + j = N → snellAux E (q : ℝ) Z j k =ᵐ[coinFlipMeasure q hq]
      snellEnvelopeAux (coinFlipMeasure q hq) flipFiltration {i | N - i ∈ E} Z j k := by
  intro j
  induction j with
  | zero => exact fun k _ ↦ Filter.EventuallyEq.rfl
  | succ j ih =>
    intro k hk
    have hnode := condExp_flipFiltration_succ hq
      (pathAdaptedAt_snellAux (E := E) (q := (q : ℝ)) hZ j (k + 1))
    have hcongr := condExp_congr_ae (m := flipFiltration k) (ih (k + 1) (by omega)).symm
    have hkX : k ∈ {i | N - i ∈ E} ↔ j + 1 ∈ E := by
      change N - k ∈ E ↔ _
      rw [show N - k = j + 1 by omega]
    by_cases hj : j + 1 ∈ E
    · filter_upwards [hnode, hcongr] with ω h1 h2
      rw [snellAux_succ_of_mem hj, snellEnvelopeAux_succ_of_mem (hkX.2 hj)]
      beta_reduce
      rw [h2, h1]
    · filter_upwards [hnode, hcongr] with ω h1 h2
      rw [snellAux_succ_of_notMem hj, snellEnvelopeAux_succ_of_notMem (mt hkX.1 hj), h2, h1]

/-- **The tree's Snell envelope is an instance of the library's.** For a payoff process adapted to
the flips, `snell E q Z N k` is, almost surely under `coinFlipMeasure q` and for `k ≤ N`, the Snell
envelope `snellEnvelope` of `Z` for the flip filtration with horizon `N`, exercisable at the times
`i` with `N - i ∈ E` (`E` counts the steps still to go). `snell` is its explicit form: the
conditional expectations are node averages, which is what makes the pathwise minimality
`snellAux_le_of_supermartingale_of_ge` hold at every path. -/
theorem snell_ae_eq_snellEnvelope (hZ : ∀ n, PathAdaptedAt n (Z n)) {N k : ℕ} (hk : k ≤ N) :
    snell E (q : ℝ) Z N k =ᵐ[coinFlipMeasure q hq]
      snellEnvelope (coinFlipMeasure q hq) flipFiltration {i | N - i ∈ E} Z N k := by
  rw [snellEnvelope, min_eq_left hk]
  exact snellAux_ae_eq_snellEnvelopeAux hq hZ N (N - k) k (by omega)

/-- **The tree's Snell envelope is a Mathlib supermartingale.** For a payoff process adapted to the
flips, `k ↦ snell E q Z N (min k N)`, the pathwise envelope frozen at the horizon `N`, is a
`Supermartingale` for `flipFiltration` under `coinFlipMeasure q`: it is almost surely the library's
`snellEnvelope` at every time (`snell_ae_eq_snellEnvelope`), which is one
(`snellEnvelope_supermartingale`), and it is adapted and integrable because it depends only on the
first `k` flips. Past `N` the pathwise `snell` is the payoff again, so the freezing is needed. -/
theorem supermartingale_snell (hZ : ∀ n, PathAdaptedAt n (Z n)) (N : ℕ) :
    Supermartingale (fun k ↦ snell E (q : ℝ) Z N (min k N)) flipFiltration
      (coinFlipMeasure q hq) := by
  have hZ' : ∀ i, Integrable (Z i) (coinFlipMeasure q hq) := fun i ↦ (hZ i).integrable hq
  have key (k : ℕ) : snell E (q : ℝ) Z N (min k N) =ᵐ[coinFlipMeasure q hq]
      snellEnvelope (coinFlipMeasure q hq) flipFiltration {i | N - i ∈ E} Z N k := by
    rcases le_total k N with hk | hk
    · rw [min_eq_left hk]
      exact snell_ae_eq_snellEnvelope hq hZ hk
    · rw [min_eq_right hk, snellEnvelope_after_horizon hk]
      simpa only [snellEnvelope_after_horizon le_rfl] using
        snell_ae_eq_snellEnvelope hq (E := E) hZ le_rfl
  have hsuper := snellEnvelope_supermartingale (P := coinFlipMeasure q hq)
    (𝓕 := flipFiltration) (X := {i | N - i ∈ E})
    (fun n ↦ (stronglyMeasurable_flipFiltration_iff.2 (hZ n)).measurable) hZ' N
  refine ⟨fun k ↦ stronglyMeasurable_flipFiltration_iff.2 ?_, fun i j hij ↦ ?_, fun k ↦ ?_⟩
  · exact (pathAdaptedAt_snellAux (E := E) (q := (q : ℝ)) hZ (N - min k N) (min k N)).mono
      (min_le_left k N)
  · exact (condExp_congr_ae (key j)).trans_le ((hsuper.2.1 i j hij).trans_eq (key i).symm)
  · exact (hsuper.integrable k).congr (key k).symm

/-- **The Bermudan price is the Snell envelope of the discounted payoff.** Under i.i.d.
`Bernoulli(crrUpProb u d r)` flips, the Snell envelope (`snellEnvelope`) of the discounted
payoff `e^{−rn} g(Sₙ)` for the flip filtration, exercisable at the times `i` with `N - i ∈ E`, is
at time `k ≤ N` the discounted `bermudanPrice E` with `N - k` steps to go at the spot `S_k`. -/
theorem snellEnvelope_discounted_bermudanPrice (u d r : ℝ) (g : ℝ → ℝ) (S₀ : ℝ)
    (hqcrr : crrUpProb u d r = q) {N k : ℕ} (hk : k ≤ N) :
    snellEnvelope (coinFlipMeasure q hq) flipFiltration {i | N - i ∈ E}
        (fun n ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω)) N k
      =ᵐ[coinFlipMeasure q hq] fun ω ↦
        Real.exp (-r * k) * bermudanPrice E u d r g (N - k) (spotPath S₀ u d k ω) := by
  have hZ (n : ℕ) : PathAdaptedAt n fun ω ↦ Real.exp (-r * n) * g (spotPath S₀ u d n ω) :=
    fun ω ω' h ↦ by simp only [pathAdaptedAt_spotPath S₀ u d n ω ω' h]
  refine (snell_ae_eq_snellEnvelope hq (E := E) hZ hk).symm.trans (ae_of_all _ fun ω ↦ ?_)
  rw [snell, ← hqcrr, snellAux_eq_discounted_bermudanPrice]

end Snell

end MathFin
