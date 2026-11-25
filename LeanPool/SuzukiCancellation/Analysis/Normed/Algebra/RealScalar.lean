/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths and consolidated proofs. -/

module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.UniformRing

/-!
# Real scalars on a complete normed `ℚ`-algebra

A complete normed ring `𝔸` with a `NormedAlgebra ℚ 𝔸` structure carries a `NormedAlgebra ℝ 𝔸`
structure, and that structure is unique.

## Main results

* `normedAlgebraReal` — the `NormedAlgebra ℝ 𝔸` structure, obtained by extending the continuous
  ring homomorphism `algebraMap ℚ 𝔸` along the dense inclusion `ℚ → ℝ`.
* `realNormedAlgebraUnique` — that structure is unique.

Use `open scoped RealScalar` to synthesize the canonical real structure from the rational
structure and completeness. This opt-in instance has low priority, so an existing real
structure is preferred. Statements elaborated with the canonical structure use its scalar
action; when applying them with another real structure, use `Subsingleton.elim` to identify
the two structures first.

-/

@[expose] public noncomputable section

variable (𝔸 : Type*) [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

private lemma uniformContinuous_algebraMap : UniformContinuous (algebraMap ℚ 𝔸) := by
  have h : ⇑(algebraMap ℚ 𝔸) =
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℚ ℚ) (1 : 𝔸)) := by
    ext; simp [Algebra.algebraMap_eq_smul_one]
  exact h ▸ (ContinuousLinearMap.smulRight ..).uniformContinuous

/-- Extend normed algebras over `ℚ` to normed algebras over `ℝ` on Banach algebras. -/
@[no_expose]
abbrev normedAlgebraReal [CompleteSpace 𝔸] : NormedAlgebra ℝ 𝔸 where
  __ := (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (uniformContinuous_algebraMap 𝔸)).toAlgebra' fun r x ↦ by
      let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
      have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
        ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
        (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
          (uniformContinuous_algebraMap 𝔸)).continuous
      refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
      · exact isClosed_eq (by fun_prop) (by fun_prop)
      · change (ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a * x =
          x * (ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a
        rw [(ue.isDenseInducing Rat.denseRange_cast).extend_eq (by fun_prop), Algebra.commutes']
  norm_smul_le r x := by
    let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
    have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
      ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
      (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
        (uniformContinuous_algebraMap 𝔸)).continuous
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
    · simpa [Algebra.smul_def, algebraMap] using isClosed_le (by fun_prop) (by fun_prop)
    · change ‖(ue.isDenseInducing Rat.denseRange_cast).extend (algebraMap ℚ 𝔸) a * x‖ ≤ _
      rw [(ue.isDenseInducing Rat.denseRange_cast).extend_eq (by fun_prop), ← Algebra.smul_def]
      exact norm_smul_le a x

namespace RealScalar

attribute [scoped instance 100] normedAlgebraReal

end RealScalar

/-- A complete normed `ℚ`-algebra carries a unique `NormedAlgebra ℝ` structure. -/
@[instance_reducible]
noncomputable def realNormedAlgebraUnique [CompleteSpace 𝔸] :
    Unique (NormedAlgebra ℝ 𝔸) where
  default := normedAlgebraReal 𝔸
  uniq h := by
    have : Continuous (algebraMap ℝ 𝔸) := by fun_prop
    let ue := Rat.isUniformEmbedding_coe_real.isUniformInducing
    have : Continuous (IsDenseInducing.extendRingHom (i := Rat.castHom ℝ)
      ue Rat.denseRange_cast (uniformContinuous_algebraMap 𝔸)) :=
      (uniformContinuous_uniformly_extend ue Rat.denseRange_cast
        (uniformContinuous_algebraMap 𝔸)).continuous
    rcases h with @⟨P, hP⟩
    congr; ext r x
    rw [Algebra.smul_def, @Algebra.smul_def _ _ _ _ (normedAlgebraReal 𝔸).toAlgebra]
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r ?_ fun a ↦ ?_
    · exact isClosed_eq (by fun_prop) (by simp only [algebraMap]; fun_prop)
    · rw [← eq_ratCast (algebraMap ℚ ℝ), ← IsScalarTower.rat.algebraMap_apply,
        ← @(@IsScalarTower.rat _ _ _ _ (normedAlgebraReal 𝔸).toModule ..).algebraMap_apply]

namespace RealScalar

attribute [scoped instance] realNormedAlgebraUnique

end RealScalar
