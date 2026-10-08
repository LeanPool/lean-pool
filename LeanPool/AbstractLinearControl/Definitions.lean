/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Background.Semigroup
public import LeanPool.AbstractLinearControl.Background.Lp


/-!
# Abstract linear control systems (Section 1 and § 2.1 of the paper)

* `ALCS 𝕜 X U p` : **Definition 1.1**, an abstract linear control system `(𝕋, Φ)`.
* `ALCS.IsZeroClass` : **Definition 1.4**, zero-class systems.
* `ALCS.Phi_zero` : `Φ_0 = 0` (§ 1.2).
* `ALCS.norm_Phi_mono` : equation `eq:Phi-monotone`, `κ(t) ≤ κ(t + τ)`,
  where `κ(t) = ‖Φ t‖`.
* `ALCS.causality`, `ALCS.delay`, `ALCS.free` : **Lemma 2.1** (`lem:Phi-properties`),
  equations `eq:causality`, `eq:delay`, `eq:free`.

## Formalization choices

* Scalars: any nontrivially normed field `𝕜` here; the main theorem uses `ℝ` or `ℂ`
  (`RCLike 𝕜`). Completeness of `X` and `U` is assumed only where it is used.
* `L^p(ℝ₊; U)` is `Lp U p muPlus` (see `ALCS/Background/Lp.lean`).
* Like the semigroup `T`, the input maps form a function `Φ : ℝ → (L^p →L X)`;
  only nonnegative times play a role in the axioms and in the results.
* Instead of constructing `u ⋄_τ v` as an element of `L^p`, the composition property
  is required for every `w ∈ L^p` whose representative is a.e. equal to
  `concat τ ⇑u ⇑v`. Since `u ⋄_τ v` does belong to `L^p` and a.e. classes are unique,
  this is exactly the identity of the paper.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- **Definition 1.1** (abstract linear control system).
An abstract linear control system with state space `X`, input space `U` and exponent
`p ∈ [1, ∞]` is a strongly continuous semigroup `T` on `X` (the parent structure
`C0Semigroup`) together with bounded linear input maps `Φ t : L^p(ℝ₊; U) → X`
satisfying the composition property `eq:composition`. -/
structure ALCS (𝕜 : Type*) (X : Type*) (U : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] extends C0Semigroup 𝕜 X where
  /-- the input maps `Φ t : L^p(ℝ₊; U) → X` -/
  Φ : ℝ → Lp U p muPlus →L[𝕜] X
  /-- composition property `eq:composition`: `Φ (τ + t) (u ⋄_τ v) = T t (Φ τ u) + Φ t v`,
  where `w` is any input representing `u ⋄_τ v` -/
  composition : ∀ τ t : ℝ, 0 ≤ τ → 0 ≤ t → ∀ u v w : Lp U p muPlus,
    (⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) → Φ (τ + t) w = T t (Φ τ u) + Φ t v

namespace ALCS

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : ALCS 𝕜 X U p)

/-- **Definition 1.4** (zero-class system): `κ(t) = ‖Φ t‖ → 0` as `t → 0⁺`
(equation `eq:kappa-0`). -/
def IsZeroClass : Prop :=
  Tendsto (fun t => ‖S.Φ t‖) (𝓝[≥] 0) (𝓝 0)

/-! ## Elementary consequences of the composition property (§ 1.2 and Lemma 2.1) -/

/-- `Φ 0 = 0` (§ 1.2): composition with `τ = t = 0` and `u = v`, since `u ⋄_0 u = u`. -/
theorem Phi_zero : S.Φ 0 = 0 := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  -- `u ⋄_0 u = u` everywhere
  have hw : ⇑u =ᵐ[muPlus] concat 0 ⇑u ⇑u :=
    Filter.Eventually.of_forall (fun s => by simp [concat])
  -- `Φ 0 u = T 0 (Φ 0 u) + Φ 0 u = Φ 0 u + Φ 0 u`
  have h := S.composition 0 0 le_rfl le_rfl u u u hw
  simpa [S.T_zero] using h

/-- **Lemma 2.1** (`lem:Phi-properties`), causality `eq:causality`:
`Φ τ (u ⋄_τ v) = Φ τ u`, i.e. `Φ τ u` only depends on the restriction of `u` to `[0, τ)`.
(Composition with `t = 0`.) -/
theorem causality (τ : ℝ) (hτ : 0 ≤ τ) (u v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑v) :
    S.Φ τ w = S.Φ τ u := by
  have h := S.composition τ 0 hτ le_rfl u v w hw
  simpa [S.T_zero, S.Phi_zero] using h

/-- **Lemma 2.1** (`lem:Phi-properties`), delay `eq:delay`:
`Φ (s + t) (0 ⋄_s v) = Φ t v`, i.e. an initial period of zero input has no effect.
(Composition with `u = 0`.) -/
theorem delay (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (v w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat s ⇑(0 : Lp U p muPlus) ⇑v) :
    S.Φ (s + t) w = S.Φ t v := by
  have h := S.composition s t hs ht 0 v w hw
  simpa using h

/-- **Lemma 2.1** (`lem:Phi-properties`), free evolution `eq:free`:
`Φ (τ + t) (u ⋄_τ 0) = T t (Φ τ u)`, i.e. once the input is switched off, the state evolves
freely. (Composition with `v = 0`.) -/
theorem free (τ t : ℝ) (hτ : 0 ≤ τ) (ht : 0 ≤ t) (u w : Lp U p muPlus)
    (hw : ⇑w =ᵐ[muPlus] concat τ ⇑u ⇑(0 : Lp U p muPlus)) :
    S.Φ (τ + t) w = S.T t (S.Φ τ u) := by
  have h := S.composition τ t hτ ht u 0 w hw
  simpa using h

/-- Monotonicity of `κ(t) = ‖Φ t‖`, equation `eq:Phi-monotone`:
`‖Φ s‖ ≤ ‖Φ t‖` for `0 ≤ s ≤ t`. Indeed `Φ s u = Φ t (0 ⋄_{t-s} u)` by `delay`. -/
theorem norm_Phi_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : ‖S.Φ s‖ ≤ ‖S.Φ t‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  obtain ⟨w, hw, hcat⟩ := exists_delay (t - s) u
  have heq := S.delay (t - s) s (sub_nonneg.2 hst) hs u w hcat
  rw [sub_add_cancel] at heq
  calc
    ‖S.Φ s u‖ = ‖S.Φ t w‖ := congrArg norm heq.symm
    _ ≤ ‖S.Φ t‖ * ‖w‖ := (S.Φ t).le_opNorm w
    _ ≤ ‖S.Φ t‖ * ‖u‖ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)

end ALCS

end

end AbstractLinearControl
