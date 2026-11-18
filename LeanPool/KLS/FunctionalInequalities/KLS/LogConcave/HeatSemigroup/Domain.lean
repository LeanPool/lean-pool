/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Domain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.FormDomain
public import LeanPool.KLS.FunctionalInequalities.Analysis.Semigroup.Generated.Smoothing
public import LeanPool.KLS.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Basic

/-! # Heat semigroup domain interfaces
Every result allows arbitrary weights `B`. Time zero is allowed for the generator-domain and
form-domain interfaces; arbitrary-input smoothing requires strictly positive time. The
generator-domain interfaces
(`preserves_domain`, `generator_comm`, `mem_closedWeightedOperator_domain`, `right_derivative`)
require inputs in `D(Tbar†Tbar)`; the form-domain interfaces (`preserves_form_domain`,
`norm_closedWeightedOperator_le`) require only `f ∈ D(Tbar)`; the positive-time smoothing
interfaces (`mem_closedWeightedOperator_domain_of_pos`, `mem_adjointComp_domain_of_pos` and their
bounds) require nothing of the datum beyond membership in `L²(ν)`, but need `t > 0`.
The gradient supplied here is the closed weighted operator, not a classical representative:
no pointwise gradient, no smooth representative and no `Γ`-calculus is claimed, and the sharp
constants `1/√(2et)` and `1/(et)` are not claimed either.
-/

@[expose] public section
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Semigroup
namespace FunctionalInequalities.KLS.LogConcave.HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Generator-domain inputs remain in the generator domain, including at time zero. -/
theorem preserves_domain (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ}
    (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  Generated.preserves_domain _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- The nonnegative generator commutes with heat evolution on its domain. -/
theorem generator_comm
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    adjointComp (hν.closedWeightedOperator m B hi)
      ⟨HeatSemigroup.operator m B hν hi ht f, preserves_domain m B hν hi f ht⟩ =
      HeatSemigroup.operator m B hν hi ht (adjointComp (hν.closedWeightedOperator m B hi) f) :=
  Generated.generator_comm _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- Generator-domain inputs have a closed weighted gradient after heat evolution. -/
theorem mem_closedWeightedOperator_domain
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht f ∈ (hν.closedWeightedOperator m B hi).domain :=
  mem_domain_of_mem_adjointComp_domain _
    ⟨_, preserves_domain m B hν hi f ht⟩

/-- The right time derivative is `-A(P_t f)`, equal to `-P_t(Af)` by commutation. -/
theorem right_derivative
    (f : (adjointComp (hν.closedWeightedOperator m B hi)).domain) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, ∀ hh : 0 < h, h < δ →
      ‖h⁻¹ • (HeatSemigroup.operator m B hν hi (add_nonneg ht hh.le) f -
        HeatSemigroup.operator m B hν hi ht f) + adjointComp (hν.closedWeightedOperator m B hi)
          ⟨HeatSemigroup.operator m B hν hi ht f, preserves_domain m B hν hi f ht⟩‖ < ε :=
  Generated.right_derivative _
    (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hε

/-- Form-domain inputs remain in the form domain: for `f ∈ D(Tbar)` and `t ≥ 0`, `P_t f ∈ D(Tbar)`.
This is the concrete case of `Generated.preserves_form_domain`, with arbitrary weight `B`. -/
theorem preserves_form_domain
    (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ} (ht : 0 ≤ t) :
    HeatSemigroup.operator m B hν hi ht f ∈ (hν.closedWeightedOperator m B hi).domain :=
  Generated.preserves_form_domain _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- The heat semigroup contracts the closed weighted gradient on the whole form domain:
`‖Tbar (P_t f)‖ ≤ ‖Tbar f‖` for `f ∈ D(Tbar)` and `t ≥ 0`, with arbitrary weight `B`.
The gradient is `Tbar` in the closed-operator sense. -/
theorem norm_closedWeightedOperator_le
    (f : (hν.closedWeightedOperator m B hi).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : HeatSemigroup.operator m B hν hi ht f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    ‖hν.closedWeightedOperator m B hi ⟨HeatSemigroup.operator m B hν hi ht f, hft⟩‖
      ≤ ‖hν.closedWeightedOperator m B hi f‖ :=
  Generated.norm_map_apply_le _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hft

/-- **Positive-time smoothing into the form domain**: for *every* `f ∈ L²(ν)` and every `t > 0`,
`P_t f` has a closed weighted gradient.  Concrete case of
`Generated.mem_domain_apply_of_pos`, with arbitrary weight `B`. -/
theorem mem_closedWeightedOperator_domain_of_pos
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    HeatSemigroup.operator m B hν hi ht.le f ∈ (hν.closedWeightedOperator m B hi).domain :=
  Generated.mem_domain_apply_of_pos _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- The gradient bound accompanying `mem_closedWeightedOperator_domain_of_pos`:
`2 t ‖Tbar (P_t f)‖ ² ≤ ‖f‖ ²`, i.e. `‖Tbar (P_t f)‖ ≤ ‖f‖ / √(2t)`, for arbitrary `f ∈ L²(ν)`. -/
theorem two_mul_norm_closedWeightedOperator_sq_le
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hft : HeatSemigroup.operator m B hν hi ht.le f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    2 * t * ‖hν.closedWeightedOperator m B hi
        ⟨HeatSemigroup.operator m B hν hi ht.le f, hft⟩‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  Generated.two_mul_norm_map_apply_sq_le _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hft

/-- **Positive-time smoothing into the generator domain**: for *every* `f ∈ L²(ν)` and every
`t > 0`, `P_t f ∈ D(Tbar†Tbar)`.  Concrete case of
`Generated.mem_adjointComp_domain_apply_of_pos`, with arbitrary weight `B`. -/
theorem mem_adjointComp_domain_of_pos
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    HeatSemigroup.operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  Generated.mem_adjointComp_domain_apply_of_pos _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht

/-- The generator bound accompanying `mem_adjointComp_domain_of_pos`:
`t ‖Tbar†Tbar (P_t f)‖ ≤ ‖f‖` for arbitrary `f ∈ L²(ν)` and `t > 0`. -/
theorem mul_norm_adjointComp_le
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hft : HeatSemigroup.operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    t * ‖adjointComp (hν.closedWeightedOperator m B hi)
        ⟨HeatSemigroup.operator m B hν hi ht.le f, hft⟩‖ ≤ ‖f‖ :=
  Generated.mul_norm_adjointComp_apply_le _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hft

/-- **Second-order positive-time regularity**: for *every* `f ∈ L²(ν)` and every `t > 0`, the
generator image `Tbar†Tbar (P_t f)` again has a closed weighted gradient.  Concrete case of
`Generated.mem_domain_adjointComp_apply_of_pos`, with arbitrary weight `B`.  This is membership
in `D(Tbar)` of the generator image, not a classical representative and not a pointwise bound. -/
theorem mem_closedWeightedOperator_domain_adjointComp_of_pos
    (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hft : HeatSemigroup.operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    (adjointComp (hν.closedWeightedOperator m B hi)
        ⟨HeatSemigroup.operator m B hν hi ht.le f, hft⟩ : Lp ℝ 2 (ν : Measure V)) ∈
      (hν.closedWeightedOperator m B hi).domain :=
  Generated.mem_domain_adjointComp_apply_of_pos _ (hν.closedWeightedOperator_isClosed m B hi)
    (hν.dense_domain_closedWeightedOperator m B hi) f ht hft

end FunctionalInequalities.KLS.LogConcave.HeatSemigroup
