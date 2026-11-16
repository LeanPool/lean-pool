/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases

/-!
# The maximal ergodic theorem

Stage 1 of the route to Birkhoff (`dyn.tex`): `maxBirkhoff`, Garsia's proof of the maximal
ergodic theorem, and its weak-type consequence `μ(Mf > ε) ≤ ‖f‖₁/ε`.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter Finset

open scoped ENNReal


variable {Ω : Type*}

/-- `maxBirkhoff σ f n x = max(0, S₁f(x), …, Sₙf(x))`, where `Sⱼ` is the `j`-th Birkhoff sum.

Defined by the recursion `Fₙ₊₁ = max(0, f + Fₙ ∘ σ)` rather than as an explicit `Finset.sup'`:
that recursion is exactly what Garsia's argument runs on, and it is what makes the induction
in `maxBirkhoff_integrable` and the case split in `maximal_ergodic` go through cleanly.
`maxBirkhoff_eq_sup'` below identifies it with the supremum form, which is what makes the
statement of `maximal_ergodic` recognisable. -/
noncomputable def maxBirkhoff (σ : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (f x + maxBirkhoff σ f n (σ x))

@[simp] theorem maxBirkhoff_zero (σ : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    maxBirkhoff σ f 0 x = 0 := rfl

theorem maxBirkhoff_succ (σ : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    maxBirkhoff σ f (n + 1) x = max 0 (f x + maxBirkhoff σ f n (σ x)) := rfl

theorem maxBirkhoff_nonneg (σ : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 ≤ maxBirkhoff σ f n x := by
  cases n with
  | zero => simp
  | succ n => exact le_max_left _ _

/-- `Fₙ` is the running maximum of the Birkhoff sums up to time `n`, so it increases in `n`. -/
theorem maxBirkhoff_mono (σ : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    Monotone (fun n => maxBirkhoff σ f n x) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  induction n generalizing x with
  | zero => exact maxBirkhoff_nonneg _ _ _ _
  | succ n ih =>
    rw [maxBirkhoff_succ σ f (n + 1) x, maxBirkhoff_succ σ f n x]
    exact max_le_max le_rfl (by linarith [ih (σ x)])

/-- Every Birkhoff sum up to time `n` is bounded by `Fₙ`. -/
theorem birkhoffSum_le_maxBirkhoff (σ : Ω → Ω) (f : Ω → ℝ) :
    ∀ (n j : ℕ), j ≤ n → ∀ x : Ω, birkhoffSum σ f j x ≤ maxBirkhoff σ f n x := by
  intro n
  induction n with
  | zero =>
    intro j hj x
    interval_cases j
    simp
  | succ n ih =>
    intro j hj x
    match j with
    | 0 => simpa using maxBirkhoff_nonneg σ f (n + 1) x
    | (i + 1) =>
      have hi : i ≤ n := Nat.succ_le_succ_iff.mp hj
      rw [congrFun (birkhoffSum_succ' σ f i) x, maxBirkhoff_succ]
      simp only [Pi.add_apply, Function.comp_apply]
      exact le_max_of_le_right (by linarith [ih i hi (σ x)])

/-- `Fₙ(x)` is *attained*: it equals `Sⱼf(x)` for some `j ≤ n` (with `j = 0` giving the `0`).
Together with `birkhoffSum_le_maxBirkhoff` this says `Fₙ = max_{j ≤ n} Sⱼf`, which is what makes
the statement of `maximal_ergodic` recognisable — without ever forming a `Finset.sup'`. -/
theorem maxBirkhoff_attained (σ : Ω → Ω) (f : Ω → ℝ) :
    ∀ (n : ℕ) (x : Ω), ∃ j ≤ n, maxBirkhoff σ f n x = birkhoffSum σ f j x := by
  intro n
  induction n with
  | zero => intro x; exact ⟨0, le_rfl, by simp⟩
  | succ n ih =>
    intro x
    rw [maxBirkhoff_succ]
    rcases le_or_gt (f x + maxBirkhoff σ f n (σ x)) 0 with h | h
    · exact ⟨0, Nat.zero_le _, by rw [max_eq_left h]; simp⟩
    · obtain ⟨i, hi, hieq⟩ := ih (σ x)
      refine ⟨i + 1, Nat.succ_le_succ hi, ?_⟩
      rw [max_eq_right h.le, hieq, congrFun (birkhoffSum_succ' σ f i) x]
      rfl

/-- `Fₙ(x) > 0` exactly when some Birkhoff sum `Sⱼf(x)`, `1 ≤ j ≤ n`, is positive. This is
Rudolph's `Eₙ = {x : Aⱼ(f,x) > 0 for some j ≤ n}`. -/
theorem maxBirkhoff_pos_iff (σ : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    0 < maxBirkhoff σ f n x ↔ ∃ j, 1 ≤ j ∧ j ≤ n ∧ 0 < birkhoffSum σ f j x := by
  constructor
  · intro hpos
    obtain ⟨j, hj, hjeq⟩ := maxBirkhoff_attained σ f n x
    refine ⟨j, ?_, hj, hjeq ▸ hpos⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hjeq] at hpos; simp at hpos
    · exact hj1
  · rintro ⟨j, _, hjn, hjpos⟩
    exact lt_of_lt_of_le hjpos (birkhoffSum_le_maxBirkhoff σ f n j hjn x)

/-- Mathlib's `birkhoffAverage` specialised to real scalars: it is the Birkhoff sum over `n`.
Statements in this file are phrased with `birkhoffAverage` to match Mathlib (its own ergodic
results, e.g. `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, are stated that
way); proofs reduce to the division form by rewriting with this. -/
@[simp] theorem birkhoffAverage_real (σ : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) :
    birkhoffAverage ℝ σ f n x = birkhoffSum σ f n x / n := by
  simp [birkhoffAverage, div_eq_inv_mul]

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω} {σ : Ω → Ω} {f : Ω → ℝ}

theorem maxBirkhoff_measurable (hσ : Measurable σ) (hf : Measurable f) (n : ℕ) :
    Measurable (maxBirkhoff σ f n) := by
  induction n with
  | zero => simp only [maxBirkhoff]; exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hσ))

/-- `Fₙ ∈ L¹` whenever `f` is, by closure under maxima and composition with the
measure-preserving transformation. -/
theorem maxBirkhoff_integrable (hmp : MeasurePreserving σ μ μ) (hf : Integrable f μ)
    (n : ℕ) : Integrable (maxBirkhoff σ f n) μ := by
  induction n with
  | zero => simpa only [maxBirkhoff] using integrable_fun_zero Ω ℝ μ
  | succ n ih =>
    exact (integrable_fun_zero Ω ℝ μ).sup (hf.add (hmp.integrable_comp_of_integrable ih))

/-- **Maximal ergodic theorem** (Garsia's form; Rudolph 1990 Lemma 3.2).
On `Eₙ = {x | 0 < Fₙ(x)}` — equivalently, by `maxBirkhoff_pos_iff`, the set where some Birkhoff
sum `Sⱼf`, `1 ≤ j ≤ n`, is positive — the integral of `f` is non-negative.

Garsia's argument: on `Eₙ₊₁` the max in `Fₙ₊₁ = max(0, f + Fₙ ∘ σ)` is attained by the right
branch, so `f = Fₙ₊₁ - Fₙ ∘ σ` there; off `Eₙ₊₁` we have `Fₙ₊₁ = 0` and `Fₙ ∘ σ ≥ 0`, so that
difference is `≤ 0`. Hence restricting the integral to `Eₙ₊₁` only *increases* it relative to
integrating over all of `Ω`, and `∫ (Fₙ₊₁ - Fₙ ∘ σ) = ∫ Fₙ₊₁ - ∫ Fₙ ≥ 0` by measure
preservation and monotonicity of `Fₙ` in `n`. -/
theorem maximal_ergodic (hmp : MeasurePreserving σ μ μ) (hf : Integrable f μ)
    (hfm : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxBirkhoff σ f n x}, f x ∂μ := by
  match n with
  | 0 => simp [maxBirkhoff]        -- degenerate: `F₀ ≡ 0`, so the domain is empty
  | (n + 1) =>
  have hFm : ∀ k, Measurable (maxBirkhoff σ f k) := maxBirkhoff_measurable hmp.measurable hfm
  have hFi : ∀ k, Integrable (maxBirkhoff σ f k) μ := maxBirkhoff_integrable hmp hf
  have hEmeas : MeasurableSet {x | 0 < maxBirkhoff σ f (n + 1) x} :=
    measurableSet_lt measurable_const (hFm (n + 1))
  have hcompi : Integrable (fun x => maxBirkhoff σ f n (σ x)) μ :=
    hmp.integrable_comp_of_integrable (hFi n)
  have hgi : Integrable (fun x => maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) μ :=
    (hFi (n + 1)).sub hcompi
  -- (a) On `E` the right branch of the max is attained, so `g = f` there.
  have hgE : ∀ x ∈ {x | 0 < maxBirkhoff σ f (n + 1) x},
      maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x) = f x := by
    intro x hx
    have hpos : 0 < max 0 (f x + maxBirkhoff σ f n (σ x)) := by
      rw [← maxBirkhoff_succ]; exact hx
    have ha : 0 < f x + maxBirkhoff σ f n (σ x) := by
      by_contra hc
      rw [max_eq_left (not_lt.mp hc)] at hpos
      exact lt_irrefl _ hpos
    rw [maxBirkhoff_succ, max_eq_right ha.le]
    ring
  -- (b) Off `E`: `F_{n+1} = 0` and `Fₙ ∘ σ ≥ 0`, so `g ≤ 0`.
  have hgEc : ∀ x ∈ {x | 0 < maxBirkhoff σ f (n + 1) x}ᶜ,
      maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x) ≤ 0 := by
    intro x hx
    have h0 : maxBirkhoff σ f (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hx) (maxBirkhoff_nonneg σ f (n + 1) x)
    have hn := maxBirkhoff_nonneg σ f n (σ x)
    rw [h0]
    linarith
  -- `∫_E f = ∫_E g`.
  have h1 : ∫ x in {x | 0 < maxBirkhoff σ f (n + 1) x}, f x ∂μ
      = ∫ x in {x | 0 < maxBirkhoff σ f (n + 1) x},
          (maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) ∂μ :=
    setIntegral_congr_fun hEmeas (fun x hx => (hgE x hx).symm)
  -- Restricting to `E` only increases `∫ g`, by (b).
  have h2 : ∫ x, (maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) ∂μ
      ≤ ∫ x in {x | 0 < maxBirkhoff σ f (n + 1) x},
          (maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) ∂μ := by
    have hsplit := (integral_add_compl hEmeas hgi).symm
    have hneg : ∫ x in {x | 0 < maxBirkhoff σ f (n + 1) x}ᶜ,
        (maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) ∂μ ≤ 0 :=
      setIntegral_nonpos hEmeas.compl hgEc
    linarith
  -- `∫ g = ∫ F_{n+1} - ∫ Fₙ ≥ 0`, by measure preservation and monotonicity of `Fₖ` in `k`.
  have h3 : 0 ≤ ∫ x, (maxBirkhoff σ f (n + 1) x - maxBirkhoff σ f n (σ x)) ∂μ := by
    have hcomp : ∫ x, maxBirkhoff σ f n (σ x) ∂μ = ∫ x, maxBirkhoff σ f n x ∂μ := by
      calc ∫ x, maxBirkhoff σ f n (σ x) ∂μ
          = ∫ x, maxBirkhoff σ f n x ∂(Measure.map σ μ) :=
            (integral_map hmp.measurable.aemeasurable (hFm n).aestronglyMeasurable).symm
        _ = ∫ x, maxBirkhoff σ f n x ∂μ := by rw [hmp.map_eq]
    rw [integral_sub (hFi (n + 1)) hcompi, hcomp, sub_nonneg]
    exact integral_mono (hFi n) (hFi (n + 1))
      (fun x => maxBirkhoff_mono σ f x (Nat.le_succ n))
  rw [h1]
  linarith

omit [MeasurableSpace Ω] in
/-- Subtracting a constant from the observable shifts each Birkhoff sum by `j * c`. This is the
bridge from Garsia's form of the maximal theorem to the weak-type bound: the maximal *average*
exceeding `ε` is the same as some Birkhoff sum of `f - ε` being positive. -/
theorem birkhoffSum_sub_const (σ : Ω → Ω) (f : Ω → ℝ) (c : ℝ) (j : ℕ) (x : Ω) :
    birkhoffSum σ (fun y => f y - c) j x = birkhoffSum σ f j x - j * c := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

/-- **Maximal ergodic inequality, weak type (1,1)**: for `ε > 0`,
`ε · μ{Mf > ε} ≤ ‖f‖₁`, where `{Mf > ε}` is the set on which some Birkhoff average
`Aⱼf = Sⱼf / j`, `1 ≤ j ≤ n`, exceeds `ε` (written here without dividing, as `ε · j < Sⱼf`).

This is the form used at stage 4 of `dyn.tex` to pass from a dense subspace to all of `L¹`.
It follows from `maximal_ergodic` applied to `f - ε`: that set is exactly
`{x | 0 < maxBirkhoff σ (f - ε) n x}`, on which `∫ (f - ε) ≥ 0`. -/
theorem maximal_inequality [IsFiniteMeasure μ] (hmp : MeasurePreserving σ μ μ)
    (hf : Integrable f μ) (hfm : Measurable f) {ε : ℝ} (n : ℕ) :
    ε * μ.real {x | ∃ j, 1 ≤ j ∧ j ≤ n ∧ ε * j < birkhoffSum σ f j x} ≤ ∫ x, |f x| ∂μ := by
  set g : Ω → ℝ := fun y => f y - ε with hgdef
  have hgm : Measurable g := hfm.sub measurable_const
  have hgi : Integrable g μ := hf.sub (integrable_const ε)
  -- The two descriptions of the set agree, via `maxBirkhoff_pos_iff` and `birkhoffSum_sub_const`.
  have hset : {x | 0 < maxBirkhoff σ g n x}
      = {x | ∃ j, 1 ≤ j ∧ j ≤ n ∧ ε * j < birkhoffSum σ f j x} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, maxBirkhoff_pos_iff]
    constructor
    · rintro ⟨j, hj1, hjn, hjpos⟩
      refine ⟨j, hj1, hjn, ?_⟩
      rw [hgdef, birkhoffSum_sub_const] at hjpos
      linarith [hjpos]
    · rintro ⟨j, hj1, hjn, hjpos⟩
      refine ⟨j, hj1, hjn, ?_⟩
      rw [hgdef, birkhoffSum_sub_const]
      linarith [hjpos]
  have hEmeas : MeasurableSet {x | 0 < maxBirkhoff σ g n x} :=
    measurableSet_lt measurable_const (maxBirkhoff_measurable hmp.measurable hgm n)
  -- Garsia on `g = f - ε`.
  have hgar : 0 ≤ ∫ x in {x | 0 < maxBirkhoff σ g n x}, g x ∂μ :=
    maximal_ergodic hmp hgi hgm n
  -- Split `∫_E (f - ε) = ∫_E f - ε · μ(E)`.
  have hsplit : ∫ x in {x | 0 < maxBirkhoff σ g n x}, g x ∂μ
      = (∫ x in {x | 0 < maxBirkhoff σ g n x}, f x ∂μ)
        - ε * μ.real {x | 0 < maxBirkhoff σ g n x} := by
    rw [hgdef, integral_sub hf.restrict (integrable_const ε), integral_const, smul_eq_mul,
      mul_comm, measureReal_restrict_apply_univ]
  -- `∫_E f ≤ ∫ |f|`.
  have hbound : ∫ x in {x | 0 < maxBirkhoff σ g n x}, f x ∂μ ≤ ∫ x, |f x| ∂μ := by
    calc ∫ x in {x | 0 < maxBirkhoff σ g n x}, f x ∂μ
        ≤ ∫ x in {x | 0 < maxBirkhoff σ g n x}, |f x| ∂μ :=
          integral_mono hf.restrict hf.abs.restrict (fun x => le_abs_self _)
      _ ≤ ∫ x, |f x| ∂μ := by
          refine setIntegral_le_integral hf.abs ?_
          filter_upwards with x using abs_nonneg _
  rw [← hset]
  linarith

end Measure

end MultiplicativeErgodic
