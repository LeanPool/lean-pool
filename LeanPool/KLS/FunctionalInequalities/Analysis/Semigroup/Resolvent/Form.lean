/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# The form domain of a closed operator, and the weak resolvent equation

The first steps of the construction of the heat semigroup
used by the Buser half of `thm:logconcave-cheeger-poincare-comparison`.

For a densely defined operator `T : H₀ →ₗ.[ℝ] H₁` the energy form is `E(u) = ‖T u‖²`, unbounded on
`H₀` but bounded on the form domain `D(T)` in the graph norm. This module supplies the three
statements that make the Lax–Milgram construction of the resolvent applicable:

* `completeSpace_graph` (the form construction): the graph of a closed operator is complete, which
  is the
  completeness the form domain needs;
* `min_one_mul_graphNormSq_le` (the shifted weak form): the shifted form `⟪u, v⟫ + s ⟪T u, T v⟫` is
  coercive in the
  graph norm, with explicit constant `min 1 s`;
* `norm_le_of_weak_resolvent` and `inner_nonneg_of_weak_resolvent` (the resolvent operator): any
  solution of the weak
  resolvent equation is a contraction of the datum and pairs nonnegatively with it.

This module supplies weak-form estimates. The resolvent construction is in
`Resolvent/Basic.lean`; Yosida limits and the generated semigroup have their separate owners.
The statements here are general real Hilbert space material, with no measure, log-concavity or
KLS quantity.
-/

@[expose] public section

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- the form construction: the graph of a closed operator is a complete space.

`LinearPMap.IsClosed` is by definition closedness of the graph as a set, so this is the closed
subspace of the complete product `H₀ × H₁`. It is the completeness that makes the form domain
`D(T)`, carrying the inner product `⟪u, v⟫ + ⟪T u, T v⟫`, a Hilbert space. -/
theorem completeSpace_graph (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) : CompleteSpace T.graph :=
  hT.completeSpace_coe

omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- the shifted weak form: coercivity of the shifted form in the graph norm.

The quadratic form `u ↦ ‖u‖² + s ‖T u‖²` dominates `min 1 s` times the squared graph norm. This is
the coercivity hypothesis that `IsCoercive` asks for, with an explicit constant.

Positivity of `s` is not needed and is therefore not assumed: for
`s ≤ 1` the claim reduces to `(s - 1) ‖u‖² ≤ 0` and for `s > 1` to `‖T u‖² ≤ s ‖T u‖²`. Neither
closedness nor density is used either. -/
theorem min_one_mul_graphNormSq_le (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (u : T.domain) :
    min 1 s * (‖(u : H₀)‖ ^ 2 + ‖T u‖ ^ 2) ≤ ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 := by
  have ha : (0 : ℝ) ≤ ‖(u : H₀)‖ ^ 2 := sq_nonneg _
  have hb : (0 : ℝ) ≤ ‖T u‖ ^ 2 := sq_nonneg _
  calc min 1 s * (‖(u : H₀)‖ ^ 2 + ‖T u‖ ^ 2)
      = min 1 s * ‖(u : H₀)‖ ^ 2 + min 1 s * ‖T u‖ ^ 2 := by ring
    _ ≤ 1 * ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) ha)
          (mul_le_mul_of_nonneg_right (min_le_right _ _) hb)
    _ = ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 := by ring

/-- The weak resolvent equation at `s > 0` with datum `f`: the equation solved by
`u = (1 + s T*T)⁻¹ f`, written without constructing the resolvent. -/
def WeakResolvent (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (f : H₀) (u : T.domain) : Prop :=
  ∀ v : T.domain, ⟪(u : H₀), (v : H₀)⟫ + s * ⟪T u, T v⟫ = ⟪f, (v : H₀)⟫

section WeakResolventEstimates

omit [CompleteSpace H₀] [CompleteSpace H₁]
/-- Testing the weak resolvent equation against the solution itself. -/
theorem graphNormSq_eq_inner_of_weakResolvent {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} {f : H₀} {u : T.domain}
    (hu : WeakResolvent T s f u) :
    ‖(u : H₀)‖ ^ 2 + s * ‖T u‖ ^ 2 = ⟪f, (u : H₀)⟫ := by
  have := hu u
  rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this

/--
the resolvent operator, first half: a solution of the weak resolvent equation is a contraction of
its datum,
so the resolvent is norm-nonexpansive. Test against `u` and apply Cauchy–Schwarz. -/
theorem norm_le_of_weakResolvent {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s) {f : H₀} {u : T.domain}
    (hu : WeakResolvent T s f u) : ‖(u : H₀)‖ ≤ ‖f‖ := by
  have key := graphNormSq_eq_inner_of_weakResolvent hu
  have hcs : ⟪f, (u : H₀)⟫ ≤ ‖f‖ * ‖(u : H₀)‖ := real_inner_le_norm _ _
  have hb : (0 : ℝ) ≤ s * ‖T u‖ ^ 2 := mul_nonneg hs.le (sq_nonneg _)
  rcases eq_or_lt_of_le (norm_nonneg (u : H₀)) with h0 | h0
  · rw [← h0]; exact norm_nonneg f
  · have hmul : ‖(u : H₀)‖ * ‖(u : H₀)‖ ≤ ‖f‖ * ‖(u : H₀)‖ := by nlinarith
    exact le_of_mul_le_mul_right hmul h0

/--
the resolvent operator, second half: a solution pairs nonnegatively with its datum, so the resolvent
is a
nonnegative operator. The pairing equals the squared graph norm. -/
theorem inner_nonneg_of_weakResolvent {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s) {f : H₀}
    {u : T.domain} (hu : WeakResolvent T s f u) : 0 ≤ ⟪(u : H₀), f⟫ := by
  have key := graphNormSq_eq_inner_of_weakResolvent hu
  have hb : (0 : ℝ) ≤ s * ‖T u‖ ^ 2 := mul_nonneg hs.le (sq_nonneg _)
  rw [real_inner_comm]
  nlinarith [sq_nonneg ‖(u : H₀)‖]

end WeakResolventEstimates

end FunctionalInequalities.Analysis.Semigroup
