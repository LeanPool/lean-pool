/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Palomar.InductionSymbol
public import LeanPool.FastDynamo.Palomar.H2Dictionary
public import LeanPool.FastDynamo.Palomar.Solenoidal

/-!
# The induction semigroup of the Challenge statement

The Challenge statement asks for a strongly continuous semigroup `S` of bounded operators on its
`L²_σ(𝕋³)`, the submodule `L2σ` of `L2`, whose generator agrees with the induction operator
`L_{ε,u} = curl (u × ·) + εΔ` on `H² ∩ L²_σ`, the operator being read on Fourier coefficients
through `inductionRHS` (`FastDynamoChallenge.IsInductionSemigroup`).

The library constructs the induction semigroup on its literal solenoidal subspace,
`literalInductionSemigroup`, as the transport of the semigroup `solenoidalInductionSemigroup` on
the product solenoidal subspace.  Since the literal solenoidal subspace is `L2σ`
(`L2σ_eq_literalSolenoidalSubspace`), the identity of `L2` carries it to `L2σ`; the result is
`challengeInductionSemigroup`.

## The generator clause

Let `B ∈ L2σ` satisfy `MemH2`.  By the `H²` dictionary, `B` is the transport of a field `Bₕ` of
the product `H²` graph, and `Bₕ` is divergence free since `B ∈ L2σ`.  Such a field lies in the
domain of the generator of `solenoidalInductionSemigroup`, and the Challenge coefficients of the
value `G Bₕ` of the generator, transported to `T3`, are `inductionRHS` of `B`
(`exists_mem_generator_solenoidalInductionSemigroup_domain`).  On the domain of the generator the
right difference quotient `h⁻¹ (S(h) Bₕ − Bₕ)` converges to `G Bₕ` as `h → 0⁺`; transported to
`L2`, this is the right derivative of `t ↦ S(t⁺) B` at `0` in the form the Challenge asks for.

## Contents

* `challengeInductionSemigroup` — the semigroup on `L2σ`, with `challengeInductionSemigroup_apply`
  and `norm_challengeInductionSemigroup`.
* `exists_hasDerivWithinAt_challengeInductionSemigroup` — the generator clause.
* `isInductionSemigroup_challengeInductionSemigroup` — **G** for a divergence-free velocity of the
  library's class, read on `T3` through a pointwise representative.
* `exists_isInductionSemigroup_mainLiteralVelocity` — **G** at the main theorem's velocity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory FastDynamoChallenge UnitAddTorus Filter Topology
open scoped NNReal

section General

variable (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u) {ε : ℝ} (hε : 0 < ε)

/-- **The induction semigroup `e^{t L_{ε,u}}` on the Challenge's `L²_σ`**: the library's
`literalInductionSemigroup`, carried to `L2σ` by the identity of `L2`. -/
def challengeInductionSemigroup : StronglyContinuousSemigroup L2σ :=
  (literalInductionSemigroup u hu hε).congr literalSolenoidalEquivL2σ

/-- The semigroup on `L2σ` is the library's `solenoidalInductionSemigroup` on the product
solenoidal subspace, conjugated by `productSolenoidalEquivL2σ`. -/
theorem challengeInductionSemigroup_apply (t : ℝ≥0) (B : L2σ) :
    challengeInductionSemigroup u hu hε t B =
      productSolenoidalEquivL2σ
        (solenoidalInductionSemigroup u hu hε t (productSolenoidalEquivL2σ.symm B)) :=
  rfl

/-- The semigroup on `L2σ` has the operator norms of the library's `literalInductionSemigroup`. -/
theorem norm_challengeInductionSemigroup (t : ℝ≥0) :
    ‖challengeInductionSemigroup u hu hε t‖ = ‖literalInductionSemigroup u hu hε t‖ :=
  (literalInductionSemigroup u hu hε).norm_congr literalSolenoidalEquivL2σ t

/-- **The generator clause.**  For `B ∈ L2σ` with `MemH2`, the orbit `t ↦ S(t⁺) B`, read in `L2`,
has at `0` a right derivative `D ∈ L2σ` whose Challenge coefficients are
`inductionRHS (literalVelocity v) ε B`, for any pointwise representative `v` of the value field of
the velocity. -/
theorem exists_hasDerivWithinAt_challengeInductionSemigroup {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v)
    (B : L2σ) (hB : MemH2 ⇑(B : L2)) :
    ∃ D : L2σ, HasDerivWithinAt
        (fun t : ℝ ↦ (challengeInductionSemigroup u hu hε t.toNNReal B : L2)) (D : L2)
        (Set.Ici 0) 0 ∧
      ∀ m i, mFourierCoeff (fun x ↦ (D : L2) x i) m =
        inductionRHS (literalVelocity v) ε ⇑(B : L2) m i := by
  obtain ⟨Bh, hBh⟩ := (memH2_iff_exists_productH2 (B : L2)).1 hB
  have hdiv : productDivergenceFromH2 Bh = 0 := by
    rw [← productH2Embedding_mem_productSolenoidalSubspace_iff, ← toLiteralC3L2_mem_L2σ_iff,
      hBh]
    exact B.2
  obtain ⟨x, hx, hcoef⟩ :=
    exists_mem_generator_solenoidalInductionSemigroup_domain u hu hε hv Bh hdiv
  have hxB : productSolenoidalEquivL2σ (x : productSolenoidalSubspace) = B :=
    Subtype.ext (by rw [coe_productSolenoidalEquivL2σ, hx, hBh])
  refine ⟨productSolenoidalEquivL2σ ((solenoidalInductionSemigroup u hu hε).generator x), ?_,
    fun m i ↦ ?_⟩
  · let L : productSolenoidalSubspace →L[ℂ] L2 :=
      L2σ.subtypeL.comp (productSolenoidalEquivL2σ.toContinuousLinearEquiv :
        productSolenoidalSubspace →L[ℂ] L2σ)
    have hL : ∀ y, L y = (productSolenoidalEquivL2σ y : L2) := fun _ ↦ rfl
    have hlim := (L.continuous.tendsto _).comp
      ((solenoidalInductionSemigroup u hu hε).tendsto_diffQuotient_generator x)
    have hS : ∀ t : ℝ, (challengeInductionSemigroup u hu hε t.toNNReal B : L2) =
        L (solenoidalInductionSemigroup u hu hε t.toNNReal x) := by
      intro t
      rw [hL, challengeInductionSemigroup_apply, ← hxB, LinearIsometryEquiv.symm_apply_apply]
    rw [← hasDerivWithinAt_Ioi_iff_Ici,
      hasDerivWithinAt_iff_tendsto_slope' (by simp), ← hL]
    refine hlim.congr fun h ↦ ?_
    simp only [Function.comp_apply, slope_def_module, StronglyContinuousSemigroup.diffQuotient,
      map_smul, map_sub, hS, Real.toNNReal_zero, StronglyContinuousSemigroup.apply_zero,
      sub_zero, RCLike.real_smul_eq_coe_smul (K := ℂ), map_inv₀,
      Complex.coe_algebraMap]
  · rw [coe_productSolenoidalEquivL2σ, hcoef, hBh]

/-- **G for a velocity of the library's class.**  For a divergence-free velocity `u` of the
library's class and a pointwise representative `v` of its value field, the semigroup
`challengeInductionSemigroup u hu hε` is an induction semigroup of the Challenge statement for the
velocity `literalVelocity v` on `T3` and the diffusivity `ε > 0`. -/
theorem isInductionSemigroup_challengeInductionSemigroup {v : TransverseTorus → R3}
    (hv : (transverseW1InfValue u : TransverseTorus → R3) =ᵐ[transverseMeasure] v) :
    IsInductionSemigroup (literalVelocity v) ε (challengeInductionSemigroup u hu hε).operator where
  map_zero := (challengeInductionSemigroup u hu hε).operator_zero
  map_add := (challengeInductionSemigroup u hu hε).operator_add
  continuous B := (challengeInductionSemigroup u hu hε).strong_continuous' B
  generator B hB := exists_hasDerivWithinAt_challengeInductionSemigroup u hu hε hv B hB

end General

/-- **G at the main theorem's velocity.**  The library's induction semigroup at `mainVelocity`,
carried to `L2σ`, is an induction semigroup of the Challenge statement for `mainLiteralVelocity`
and every diffusivity `ε > 0`. -/
theorem isInductionSemigroup_mainLiteralVelocity {ε : ℝ} (hε : 0 < ε) :
    IsInductionSemigroup mainLiteralVelocity ε
      (challengeInductionSemigroup mainVelocity mainVelocity_isTransverseDivergenceFree
        hε).operator :=
  isInductionSemigroup_challengeInductionSemigroup mainVelocity
    mainVelocity_isTransverseDivergenceFree hε transverseW1InfValue_mainVelocity_ae

/-- **G.**  For every diffusivity `ε > 0` the induction semigroup of the main theorem's velocity
exists on the Challenge's `L²_σ`. -/
theorem exists_isInductionSemigroup_mainLiteralVelocity {ε : ℝ} (hε : 0 < ε) :
    ∃ S, IsInductionSemigroup mainLiteralVelocity ε S :=
  ⟨_, isInductionSemigroup_mainLiteralVelocity hε⟩

end

end FastDynamo
