/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardSpaceBieleckiEDist

/-!
# The Bielecki pseudo-emetric space and its separation quotient

The type synonym `SBoundedProcess.WithBielecki` carries the Bielecki β-weighted pseudo-edist,
keeping it apart from the discrete metric on `SBoundedProcess` itself. Its triangle inequality
comes from subadditivity of the Bielecki norm applied to the pointwise identity
`X - Z = (X - Y) + (Y - Z)`, whose measurability side conditions follow from slice
measurability of the inner integrand `ω ↦ (∑ i, ‖X t ω i‖₊²)^(1/2)`. The resulting
`PseudoEMetricSpace` has a separation quotient `SBoundedProcess.AEQuot`, an `EMetricSpace`
identifying processes that agree P-a.s. at each fixed `t`; the constant-zero process inhabits
both the synonym and the quotient. A closing note contrasts this weighted sup-of-`L²` norm
with the `S²` norm and records the role of the `IsRegular` hypothesis in well-posedness.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Type-synonym carrying the Bielecki pseudo-edist instance

To avoid clashing with the existing discrete `MetricSpace` instance in
`PicardSpace.lean`, we equip a **type synonym** with the Bielecki
pseudo-edist instance. Downstream callers wanting the literature metric
write `SBoundedProcess.WithBielecki β T` explicitly. -/

/-- **Type synonym for `SBoundedProcess` carrying the Bielecki β-weighted
pseudo-edist instance.** Two `SBoundedProcess`es that agree P-a.s. at
every `t` have Bielecki pseudo-distance zero; this synonym carries the
pseudo-metric, and `SBoundedProcess.AEQuot` (the `SeparationQuotient`)
carries the genuine metric.

The phantom `β` allows different Bielecki β-values to define distinct
typeclass instances on the same underlying type. The `β` parameter is
intentionally unused in the type definition (it only affects the
distinct `EDist` instance that downstream registers on it). -/
def SBoundedProcess.WithBielecki (n : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (T β : ℝ) : Type _ :=
  let _ := β  -- silence "unused variable β" — phantom parameter
  SBoundedProcess (n := n) P ℱ T

namespace SBoundedProcess.WithBielecki

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}

/-- **Constructor.** Wrap a `SBoundedProcess` as the Bielecki-flavored type. -/
def of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki (n := n) P ℱ T β := X

/-- **Underlying `SBoundedProcess` extractor.** -/
def get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess (n := n) P ℱ T := X

@[simp] lemma get_of (X : SBoundedProcess (n := n) P ℱ T) :
    SBoundedProcess.WithBielecki.get (SBoundedProcess.WithBielecki.of (n := n) (β := β) X) = X
    := rfl

@[simp] lemma of_get (X : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    SBoundedProcess.WithBielecki.of (n := n) (β := β)
      (SBoundedProcess.WithBielecki.get X) = X := rfl

end SBoundedProcess.WithBielecki

/-! ### EDist + PseudoEMetricSpace instances on `WithBielecki`

The instance is on `WithBielecki`, not on `SBoundedProcess` directly,
so the existing discrete-metric instance in `PicardSpace.lean` is
preserved. -/

noncomputable instance instEDistWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EDist (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist X Y := bieleckiEDist β T
    (SBoundedProcess.WithBielecki.get X)
    (SBoundedProcess.WithBielecki.get Y)

@[simp] lemma edist_WithBielecki_def
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ}
    (X Y : SBoundedProcess.WithBielecki (n := n) P ℱ T β) :
    edist X Y = bieleckiEDist β T
      (SBoundedProcess.WithBielecki.get X) (SBoundedProcess.WithBielecki.get Y) := rfl

/-! ### Notes on what's still required for the full `PseudoEMetricSpace` instance

To register `PseudoEMetricSpace (SBoundedProcess.WithBielecki P T β)`,
we need the three edist axioms (`self`, `comm`, `triangle`) plus a
choice of `UniformSpace`. The first two follow immediately from
`bieleckiEDist_self` and `bieleckiEDist_comm`. The triangle inequality
requires `bieleckiNorm_add_le` applied to `Y₁ = X - Y`, `Y₂ = Y - Z`
to get `bieleckiNorm β T ((X - Y) + (Y - Z)) ≤ bieleckiNorm β T (X - Y)
+ bieleckiNorm β T (Y - Z)`, then identify `(X - Y) + (Y - Z) = X - Z`
pointwise to conclude `bieleckiEDist β T X Z ≤ bieleckiEDist β T X Y +
bieleckiEDist β T Y Z`.

**Pending hypothesis on `SBoundedProcess`**: the triangle inequality
proof requires the per-`t` AEMeasurability of
`ω ↦ (∑ i, ‖X.X t ω i‖₊²)^(1/2)`. This follows from `X.measurable_path`
(joint measurability gives slice-measurability in `ω` at each fixed `t`,
which combined with the continuous function `r ↦ r²` and finite sums
gives AEMeasurability of the inner expression). Threading this through
the proof requires an auxiliary lemma `bieleckiNorm_inner_aemeasurable`
that I expose below. -/

/-- **Slice-AEMeasurability of the Bielecki inner integrand.** From joint
measurability of `(t, ω) ↦ X t ω`, the per-`t` slice `ω ↦ X t ω` is
measurable; composing with the continuous `r ↦ ‖r‖₊²` and finite sum
preserves measurability; the (1/2)-rpow is measurable; pushing through
gives AEMeasurable of the inner Bielecki expression. -/
lemma bieleckiNorm_inner_aemeasurable
    {n : ℕ} {P : Measure Ω}
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X)) (t : ℝ) :
    AEMeasurable
      (fun ω => (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P := by
  -- Slice-measurability of `ω ↦ X t ω` via `Measurable.of_uncurry_left`.
  have h_slice : Measurable (fun ω => X t ω) :=
    Measurable.of_uncurry_left hX_meas
  -- Each component `ω ↦ X t ω i` is measurable (composition with
  -- evaluation).
  have h_comp : ∀ i, Measurable (fun ω => X t ω i) := fun i =>
    h_slice.eval
  -- Each summand `ω ↦ ‖X t ω i‖₊²` is measurable.
  have h_summand : ∀ i, Measurable
      (fun ω => ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) := by
    intro i
    refine (Measurable.pow_const ?_ _)
    refine (ENNReal.continuous_coe.measurable.comp ?_)
    exact ((h_comp i).nnnorm)
  -- Finite sum is measurable.
  have h_sum : Measurable (fun ω => ∑ i, ((‖X t ω i‖₊ : ℝ≥0∞)) ^ 2) :=
    Finset.measurable_sum _ (fun i _ => h_summand i)
  -- Composing with the continuous `x ↦ x ^ (1/2)`.
  exact (h_sum.pow_const ((1 : ℝ) / 2)).aemeasurable

/-! ### Triangle inequality for `bieleckiEDist`

For `SBoundedProcess`es `X, Y, Z`, the pointwise identity `(X - Z) =
(X - Y) + (Y - Z)` on the underlying path maps combines with
`bieleckiNorm_add_le` to give

  `bieleckiEDist β T X Z ≤ bieleckiEDist β T X Y + bieleckiEDist β T Y Z`.

The AEMeasurability hypotheses for `bieleckiNorm_add_le` are discharged
via `bieleckiNorm_inner_aemeasurable` applied to `X.X - Y.X` and
`Y.X - Z.X`, using `X.measurable_path` etc. -/

/-- **AEMeasurability of the Bielecki inner integrand for the path
difference of two `SBoundedProcess`es.** Follows from
`bieleckiNorm_inner_aemeasurable` applied to `X.X - Y.X` after showing
the difference is jointly measurable. -/
lemma SBoundedProcess.pathDiff_aemeasurable
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (X Y : SBoundedProcess (n := n) P ℱ T) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖(X.X t ω - Y.X t ω) i‖₊ : ℝ≥0∞) ^ 2)
        ^ ((1 : ℝ) / 2)) P := by
  -- The pointwise difference `fun t ω => X.X t ω - Y.X t ω` is jointly
  -- measurable as the difference of two jointly measurable functions.
  have h_diff_meas : Measurable
      (Function.uncurry (fun t ω => X.X t ω - Y.X t ω)) := by
    have : Function.uncurry (fun t ω => X.X t ω - Y.X t ω)
        = fun p : ℝ × Ω => X.X p.1 p.2 - Y.X p.1 p.2 := by
      funext p
      rfl
    rw [this]
    exact X.measurable_path.sub Y.measurable_path
  exact bieleckiNorm_inner_aemeasurable
    (fun t ω => X.X t ω - Y.X t ω) h_diff_meas t

/-- **Triangle inequality for the Bielecki β-norm pseudo-edist.**
For `SBoundedProcess`es X, Y, Z, applying `bieleckiNorm_add_le` to
`Y₁ = X.X - Y.X`, `Y₂ = Y.X - Z.X` gives the triangle inequality. -/
lemma bieleckiEDist_triangle
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {β T : ℝ}
    (X Y Z : SBoundedProcess (n := n) P ℱ T) :
    bieleckiEDist β T X Z
      ≤ bieleckiEDist β T X Y + bieleckiEDist β T Y Z := by
  -- (X.X - Z.X) = (X.X - Y.X) + (Y.X - Z.X) pointwise.
  have h_id : (fun t ω => X.X t ω - Z.X t ω)
      = fun t ω => (X.X t ω - Y.X t ω) + (Y.X t ω - Z.X t ω) := by
    funext t ω
    funext i
    change X.X t ω i - Z.X t ω i = (X.X t ω i - Y.X t ω i) + (Y.X t ω i - Z.X t ω i)
    ring
  -- Apply `bieleckiNorm_add_le`.
  have h := bieleckiNorm_add_le (P := P) β T
    (fun t ω => X.X t ω - Y.X t ω) (fun t ω => Y.X t ω - Z.X t ω)
    (fun t => SBoundedProcess.pathDiff_aemeasurable X Y t)
    (fun t => SBoundedProcess.pathDiff_aemeasurable Y Z t)
  -- Conclude via the pointwise identity.
  change bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Z)
    ≤ bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff X Y)
      + bieleckiNorm (P := P) β T (SBoundedProcess.pathDiff Y Z)
  unfold SBoundedProcess.pathDiff
  rw [h_id]
  exact h

/-! ### PseudoEMetricSpace + EMetricSpace instances on `WithBielecki`

With `bieleckiEDist_self`, `bieleckiEDist_comm`, `bieleckiEDist_triangle`
proven, we can register the `PseudoEMetricSpace` instance on
`SBoundedProcess.WithBielecki`. Mathlib's `PseudoEMetricSpace.mk`
constructor takes the three edist axioms plus a default
`UniformSpace` (we use the canonical one generated from the edist). -/

noncomputable instance instPseudoEMetricSpaceWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    PseudoEMetricSpace (SBoundedProcess.WithBielecki (n := n) P ℱ T β) where
  edist_self X := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
      (SBoundedProcess.WithBielecki.get X) = 0
    exact bieleckiEDist_self _
  edist_comm X Y := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
      = bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
        (SBoundedProcess.WithBielecki.get X)
    exact bieleckiEDist_comm _ _
  edist_triangle X Y Z := by
    change bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Z)
      ≤ bieleckiEDist β T (SBoundedProcess.WithBielecki.get X)
        (SBoundedProcess.WithBielecki.get Y)
        + bieleckiEDist β T (SBoundedProcess.WithBielecki.get Y)
          (SBoundedProcess.WithBielecki.get Z)
    exact bieleckiEDist_triangle _ _ _

/-! ### AE-quotient: `SBoundedProcess.AEQuot β T`

The `SeparationQuotient` of the pseudo-emetric space `WithBielecki` is
automatically a `EMetricSpace` (separated) in Mathlib. This is the
**literature Banach space** `S²([0, T]; ℝⁿ)` modulo P-null sets, with
the Bielecki β-norm metric. -/

/-- **AE-quotient of `SBoundedProcess` by P-null-set equivalence.**

  `AEQuot β T := SeparationQuotient (SBoundedProcess.WithBielecki β T)`.

Mathlib's `SeparationQuotient` of a `PseudoEMetricSpace` is automatically
a genuine `EMetricSpace` (separated) — and hence a `MetricSpace` once we
project the edist down to a real-valued distance. This is the literature
Banach space `S²([0, T]; ℝⁿ)` modulo P-null-set equivalence. -/
def SBoundedProcess.AEQuot
    (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T β : ℝ) : Type _ :=
  SeparationQuotient (SBoundedProcess.WithBielecki (n := n) P ℱ T β)

/-- Mathlib auto-derives `EMetricSpace` on the `SeparationQuotient`.
Re-export under the project's namespace. -/
noncomputable instance instEMetricSpaceAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    EMetricSpace (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  instEMetricSpaceSeparationQuotient

/-! ### The `IsRegular` hypothesis and the `S²` norm

**The `IsRegular` hypothesis.** `JumpDiffusionCoeffs.IsLipschitz coeffs ν L`
alone does not yield a `JumpDiffusion W N coeffs x₀`, so the well-posedness
theorem `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`)
also takes `JumpDiffusionCoeffs.IsRegular coeffs ν`. `IsLipschitz` constrains
the coefficients only in the state variable `x`; it says nothing about their
dependence on `s`, or, for `γ`, on `e`. The `is_solution` field of
`JumpDiffusion` existentially bundles joint measurability, progressive
measurability and the `L²` bounds of `(s, ω) ↦ σ(s, X_s ω)` and
`(ω, s, e) ↦ γ(s, X_s ω, e)`, because the two stochastic integrals need
them to be well-typed. Two coefficient families satisfy `IsLipschitz`
with `L = 0` and admit no `JumpDiffusion` at all:

* `n = d = 1`, `μ = 0`, `γ = 0`, `σ s x = 1 / s`. Every Lipschitz clause
  reads `0 ≤ 0`, but `∫⁻ s in Icc 0 T', ‖1 / s‖₊ ^ 2 = ∞` for every
  `T' > 0`, so `h_σ_sq` fails for every path map `X`.
* `n = d = 1`, `μ = 0`, `γ = 0`, `σ s x = 1_A s` for a non-measurable
  `A ⊆ ℝ`. Again every Lipschitz clause reads `0 ≤ 0`, but
  `Function.uncurry (fun ω s => σ s (X s ω))` has `Set.univ ×ˢ A` as a
  preimage, and the `ω`-sections of that set are `A`, so `h_σ_meas`
  fails for every `X`.

`IsRegular` supplies (i) joint measurability of `(s, x) ↦ μ s x`,
`(s, x) ↦ σ s x` and `(s, x, e) ↦ γ s x e`, and (ii) square integrability
in `s` at a single state, `∫⁻ s in Icc 0 T', ‖σ s 0‖₊ ^ 2 < ∞` and
`∫⁻ s in Icc 0 T', ∫⁻ e, ‖γ s 0 e‖₊ ^ 2 ∂ν < ∞` (and the same for `μ`).
Together with the Lipschitz clauses these give the `L²` bounds along any
`L²`-bounded path, since Lipschitz continuity in the state gives
`‖f s x‖ ≤ ‖f s 0‖ + L ‖x‖` (`Ito/PicardIntegrand.lean`). Applebaum 6.2.9
assumes measurable coefficients of linear growth.

**Not the `S²` space.** `bieleckiNorm β T X` is
`⨆ t ∈ [0, T], exp (-β * t) * ‖X t‖_{L²}`, the weighted *sup-of-`L²`*
norm. It is not the `S²` norm `‖ ⨆ t ≤ T, ‖X t‖ ‖_{L²}`, which is what
`JumpDiffusion.sup_L2` asks for, and the separation quotient
`SBoundedProcess.AEQuot` therefore identifies processes that agree a.e.
*at each fixed `t`*, not processes with a.e. equal paths. The
well-posedness chain bridges the two in `Ito/PicardSupL2.lean`, by Doob's
`L²` inequality over the dyadic points for the stochastic components of
the Picard step.

**Where the chain lives.** The metric structure of this file —
`bieleckiEDist` with `bieleckiEDist_comm` and `bieleckiEDist_triangle`, the
`PseudoEMetricSpace` on `SBoundedProcess.WithBielecki`, the separation
quotient `SBoundedProcess.AEQuot` with its `EMetricSpace`, and
nonemptiness of both — is not what the well-posedness proof iterates on.
That proof works with the pseudo-edist on path maps directly: the Picard
step becomes a total self-map of the process space (`picardSelfMap`;
`Ito/PicardIntegrand.lean`, `Ito/PicardOutput.lean`), it is a Bielecki
contraction (`bieleckiNorm_picardSelfMap_diff_le`,
`Ito/PicardContraction.lean`), its iterates `picardIter` converge to
`picardLimit` (built on `bieleckiLimit`, `Ito/PicardLimit.lean`), the
process built on the limit is a fixed point
(`picardSelfMapRaw_isFixedPoint`), the fixed point solves the equation on
the window and is the only solution there (`exists_solvesOn`,
`ae_eq_of_solvesOn`, `Ito/PicardWindow.lean`), and the windows glue
(`exists_globalSolution`, `Ito/PicardGlobal.lean`). -/

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Nonemptiness of `WithBielecki β T` and `AEQuot β T`

The constant-zero `SBoundedProcess` (from `PicardSpace.lean`) witnesses
inhabitedness of the underlying type, hence of the type synonym and the
AE-quotient. -/

/-- **Nonemptiness of `WithBielecki β T`.** The constant-zero
`SBoundedProcess` (from `PicardSpace.lean`) witnesses inhabitedness
of the underlying type, which inhabits the type synonym. -/
noncomputable instance instNonemptyWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.WithBielecki (n := n) P ℱ T β) :=
  ⟨SBoundedProcess.WithBielecki.of (β := β) (constantZeroProcess (n := n) P ℱ T)⟩

/-- **Nonemptiness of `AEQuot β T`.** Lifts from the constant-zero process
via `SeparationQuotient.mk`. -/
noncomputable instance instNonemptyAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T β : ℝ} :
    Nonempty (SBoundedProcess.AEQuot (n := n) P ℱ T β) :=
  ⟨SeparationQuotient.mk (SBoundedProcess.WithBielecki.of (β := β)
    (constantZeroProcess (n := n) P ℱ T))⟩

/-! ### The well-posedness theorem

The existence and uniqueness statement for the jump-diffusion SDE is
`Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn` in `Ito/PicardWellPosed.lean`, at the end
of the Picard chain that starts here with the Bielecki metric on the process space. -/

end LevyStochCalc.Ito.Picard
