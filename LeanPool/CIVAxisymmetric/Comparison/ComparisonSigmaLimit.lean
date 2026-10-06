/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Barrier
public import LeanPool.CIVAxisymmetric.Statements.IsDistributionalDriftDiffusion
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.Topology.Order.OrderClosed

/-!
# The `σ ↓ 0` limit and the `−q` argument of `lem:aniso:comparison`

The Grönwall step of the comparison argument produces, for every rate parameter `σ > 0`, an
almost-everywhere pointwise bound of the slices of `q` by the barrier `Ψ_σ` of
`eq:aniso:comparison:barrier` (`CIV.barrier`): for a.e. `τ` in the working interval,
`q(·, τ) ≤ Ψ_σ(·, τ)` a.e. This file takes that family of bounds, one hypothesis per `σ`, and
carries out the last two steps of the upper bound of `lem:aniso:comparison`:

* **`σ ↓ 0`** (`ae_ae_le_of_forall_pos_ae_ae_le_barrier`): the barrier
  `barrier m M σ K τ₀ (x, τ) = M + σ (⟨x⟩ + K(τ - τ₀))` is affine in `τ` with rate `σK` and, at
  any fixed `(x, τ)`, converges to the constant `M` as `σ ↓ 0`, since the bracketed factor
  `⟨x⟩ + K(τ - τ₀)` no longer depends on `σ`. Passing to the limit along the countable sequence
  `σ_n = 1/(n+1)` turns the family of a.e. bounds into a single a.e. bound `q ≤ M`.

* **The `−q` argument.** The two hypotheses of the comparison lemma on `q` —
  `IsLocallyBoundedOn` and `IsDistributionalDriftDiffusion` — are both closed under negation:
  `IsLocallyBoundedOn.neg` and `IsDistributionalDriftDiffusion.neg` prove this directly from the
  definitions rather than asserting it. The second is the substantive check:
  `IsDistributionalDriftDiffusion`'s pairing is *linear*, not merely affine, in `q` — the integrand
  is `q z * (test-function combination)`, with no additive term independent of `q` — so negating `q`
  negates the integrand pointwise, and both the integrability and the vanishing integral survive
  unchanged. Consequently, a σ-family bound available for every function satisfying the two
  hypotheses applies equally to `q` and to `-q`, and combining the two one-sided bounds gives
  `|q| ≤ M` a.e. (`ae_ae_abs_le_of_isLocallyBoundedOn_isDistributionalDriftDiffusion`).

The passage from the a.e. pointwise bound to the essential supremum in the conclusion of the
statement `CIV.comparison` is `comparison_eLpNorm_top_of_ae_dominance`. The comparison proof uses
`ae_ae_le_of_forall_pos_ae_ae_le_barrier`, `IsLocallyBoundedOn.neg` and
`IsDistributionalDriftDiffusion.neg` (`CIV.ae_ae_le_of_window`,
`CIV.ae_ae_abs_le_of_isDistributionalDriftDiffusion`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section

namespace CIV

variable {m d : ℕ} {I : Set ℝ} {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ}

/-! ### The hypothesis class is closed under negation -/

/-- `IsLocallyBoundedOn` is closed under negation: the a.e. strong measurability and the local
`L^∞` bound of `q` transfer unchanged to `-q`, since `|(-q) z| = |q z|`. -/
theorem IsLocallyBoundedOn.neg {q : Vec m × ℝ → ℝ} (hq : IsLocallyBoundedOn m I q) :
    IsLocallyBoundedOn m I (fun z => -q z) := by
  obtain ⟨hmeas, hbound⟩ := hq
  refine ⟨hmeas.neg, fun J hJcompact hJI => ?_⟩
  obtain ⟨M, hM⟩ := hbound J hJcompact hJI
  refine ⟨M, ?_⟩
  filter_upwards [hM] with z hz
  simpa using hz

/-- `IsDistributionalDriftDiffusion` is closed under negation. The pairing against a test
function `φ` is *linear* in `q` — `q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z *
φ z - partialLaplacian m d φ z)`, with no summand independent of `q` — so negating `q` negates the
integrand pointwise; the integrability of the negated integrand and the vanishing of its integral
both follow directly from the corresponding facts for `q`. -/
theorem IsDistributionalDriftDiffusion.neg {q : Vec m × ℝ → ℝ}
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    IsDistributionalDriftDiffusion m d I B divB (fun z => -q z) := by
  intro φ hφ
  obtain ⟨hint, hzero⟩ := heq φ hφ
  have hfun : (fun z => (fun w => -q w) z * (-(timeDeriv m φ z) - gradPair m φ z (B z) -
      divB z * φ z - partialLaplacian m d φ z))
      = fun z => -(q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z -
          partialLaplacian m d φ z)) := by
    funext z
    simp only [neg_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hint.neg
  · rw [hfun]
    rw [integral_neg, hzero, neg_zero]

/-! ### The `σ ↓ 0` limit -/

/-- **The `σ ↓ 0` limit.** Given, for every `σ > 0`, an a.e.-in-`τ`, a.e.-in-`x` bound of `q` by
the barrier `barrier m M σ K τ₀` **at times at or after the reference time `τ₀`** — the shape
the Grönwall step of the comparison argument supplies — the same bound holds for `q` against the
constant
`M` alone: the barrier reduces to `M` as `σ ↓ 0` at every fixed `(x, τ)`.

The restriction `τ₀ ≤ τ` is load-bearing and not cosmetic. The barrier is
`M + σ (⟨x⟩ + K (τ − τ₀))` with `⟨x⟩ ≥ 1` and `K ≥ 0`, so for `τ` below `τ₀` it decreases without
bound as `τ` recedes; an unrestricted hypothesis of this shape, quantified over every `σ > 0`, is
satisfiable only by a function unbounded below, and in particular never by the bounded `q` of the
comparison lemma on an interval such as `Iio T`.

The proof restricts the uncountable family of hypotheses to the countable sequence
`σ_n = 1/(n+1)`, uses `ae_all_iff` twice (once in `τ`, once in `x`) to move the countable
universal quantifier inside both almost-everywhere quantifiers, and then passes to the limit
`n → ∞` at each surviving `(x, τ)`. -/
theorem ae_ae_le_of_forall_pos_ae_ae_le_barrier {M K τ₀ : ℝ} {q : Vec m × ℝ → ℝ}
    (h : ∀ σ : ℝ, 0 < σ → ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
        ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ barrier m M σ K τ₀ (x, τ)) :
    ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ M := by
  have hinner : ∀ᵐ τ ∂(volume.restrict I), ∀ n : ℕ, τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ barrier m M (1 / ((n : ℝ) + 1)) K τ₀ (x, τ) := by
    rw [ae_all_iff]
    intro n
    exact h (1 / ((n : ℝ) + 1)) (by positivity)
  filter_upwards [hinner] with τ hτ
  intro hτ₀le
  have hinner2 : ∀ᵐ x ∂(volume : Measure (Vec m)), ∀ n : ℕ,
      q (x, τ) ≤ barrier m M (1 / ((n : ℝ) + 1)) K τ₀ (x, τ) :=
    ae_all_iff.mpr fun n => hτ n hτ₀le
  filter_upwards [hinner2] with x hx
  have htendsto : Tendsto (fun n : ℕ => barrier m M (1 / ((n : ℝ) + 1)) K τ₀ (x, τ)) atTop
      (𝓝 M) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) *
        (japaneseBracket m x + K * (τ - τ₀))) atTop
        (𝓝 (0 * (japaneseBracket m x + K * (τ - τ₀)))) :=
      h0.mul tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => M + (1 / ((n : ℝ) + 1)) *
        (japaneseBracket m x + K * (τ - τ₀))) atTop
        (𝓝 (M + 0 * (japaneseBracket m x + K * (τ - τ₀)))) :=
      tendsto_const_nhds.add h1
    simpa [barrier] using h2
  exact ge_of_tendsto' htendsto hx

/-- **The restricted barrier hypothesis is satisfiable.** At times at or after the reference
time `τ₀`, `K (τ − τ₀) ≥ 0` and
`⟨x⟩ ≥ 1`, so the barrier sits strictly above `M`; hence any `q` bounded above by `M` satisfies
the hypothesis of `ae_ae_le_of_forall_pos_ae_ae_le_barrier`, for every `σ > 0`.

Without the `τ₀ ≤ τ` restriction no such witness exists: the barrier decreases without bound as
`τ` recedes below `τ₀`, so the unrestricted hypothesis is met only by a function unbounded below. -/
theorem ae_ae_le_barrier_of_forall_le {M K τ₀ : ℝ} (hK : 0 ≤ K) {q : Vec m × ℝ → ℝ}
    (hbd : ∀ z, q z ≤ M) (σ : ℝ) (hσ : 0 < σ) :
    ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ barrier m M σ K τ₀ (x, τ) := by
  refine Filter.Eventually.of_forall fun τ hτ => Filter.Eventually.of_forall fun x => ?_
  have hb : (1 : ℝ) ≤ japaneseBracket m x := one_le_japaneseBracket x
  have hKt : 0 ≤ K * (τ - τ₀) := mul_nonneg hK (by linarith only [hτ])
  have hpos : 0 ≤ σ * (japaneseBracket m x + K * (τ - τ₀)) :=
    mul_nonneg hσ.le (by linarith only [hb, hKt])
  have hq : q (x, τ) ≤ M := hbd (x, τ)
  simp only [barrier]
  linarith only [hq, hpos]

/-! ### The assembled two-sided bound -/

/-- **`σ ↓ 0` and `−q`, combined.** Given a general form of the Grönwall conclusion of the
comparison argument — the σ-family barrier bound of `ae_ae_le_of_forall_pos_ae_ae_le_barrier`,
restricted to times at or after the reference time `τ₀` (see that lemma's note on why the
restriction is required), available for
*every* function satisfying the two hypotheses `IsLocallyBoundedOn` and
`IsDistributionalDriftDiffusion` rather than only for the fixed `q` at hand — apply it once to `q`
and once to `-q` (licensed by `IsLocallyBoundedOn.neg` and `IsDistributionalDriftDiffusion.neg`),
and combine the two resulting one-sided a.e. bounds into `|q| ≤ M` a.e. -/
theorem ae_ae_abs_le_of_isLocallyBoundedOn_isDistributionalDriftDiffusion {M K τ₀ : ℝ}
    {q : Vec m × ℝ → ℝ} (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q)
    (hStep5b : ∀ q' : Vec m × ℝ → ℝ, IsLocallyBoundedOn m I q' →
        IsDistributionalDriftDiffusion m d I B divB q' →
        ∀ σ : ℝ, 0 < σ → ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
          ∀ᵐ x ∂(volume : Measure (Vec m)), q' (x, τ) ≤ barrier m M σ K τ₀ (x, τ)) :
    ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), |q (x, τ)| ≤ M := by
  have h1 : ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ M :=
    ae_ae_le_of_forall_pos_ae_ae_le_barrier (hStep5b q hq heq)
  have h2 : ∀ᵐ τ ∂(volume.restrict I), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), -q (x, τ) ≤ M :=
    ae_ae_le_of_forall_pos_ae_ae_le_barrier (q := fun z => -q z)
      (hStep5b (fun z => -q z) hq.neg heq.neg)
  filter_upwards [h1, h2] with τ hτ1 hτ2
  intro hτ₀le
  filter_upwards [hτ1 hτ₀le, hτ2 hτ₀le] with x hx1 hx2
  have hx2' : -q (x, τ) ≤ M := hx2
  rw [abs_le]
  exact ⟨by linarith only [hx2'], hx1⟩

end CIV
