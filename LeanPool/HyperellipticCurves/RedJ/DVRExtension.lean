/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.AdicComplete
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The integral closure of a complete DVR in a finite extension is a complete DVR

For a complete discrete valuation ring `O` with fraction field `K` and a finite separable
extension `L/K`, the integral closure `O_L` of `O` in `L` is again a complete discrete
valuation ring (`ChabautyColeman.integralClosure_isDiscreteValuationRing`,
`ChabautyColeman.integralClosure_isAdicComplete_maximalIdeal`). This provides the rings over
which the residue-disk machinery runs after base change to a finite extension (splitting fields
of norm polynomials, disk centers over extended residue fields).

The route is purely ideal-theoretic:
* `O_L` is Dedekind and module-finite over `O` (Mathlib's AKLB results);
* a finite module over an adically complete Noetherian ring is adically complete
  (`isAdicComplete_of_finite`, via `AdicCompletion.ofTensorProduct`);
* a domain that is `I`-adically complete with `A ⧸ I` Artinian is *local*
  (`IsLocalRing.of_isAdicComplete_of_isDomain`): a second maximal ideal yields a nontrivial
  idempotent of `A ⧸ nilradical A` (Artinian decomposition), which lifts along the nilradical
  and then, by Newton iteration through the completeness, to an exact nontrivial idempotent
  of the domain `A` — contradiction;
* a local Dedekind domain is a DVR, and `𝔪·O_L` is a power of the maximal ideal, so adic
  completeness transfers (`isAdicComplete_of_pow`).

None of this is specific to this project; the three general lemmas are candidates for
Mathlib.
-/

@[expose] public section

open IsLocalRing

namespace ChabautyColeman

/-! ### Assembly: the integral closure of a complete DVR in a finite separable extension -/

section Assembly

universe u

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (K L : Type u) [Field K] [Field L] [Algebra O K] [IsFractionRing O K]
  [Algebra K L] [Algebra O L] [IsScalarTower O K L]

include K in
/-- The extension `𝔪·O_L` of the maximal ideal to the integral closure is nonzero. -/
theorem integralClosure_map_maximalIdeal_ne_bot :
    (maximalIdeal O).map (algebraMap O (integralClosure O L)) ≠ ⊥ := by
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  rw [IsScalarTower.algebraMap_eq O (integralClosure O L) L, RingHom.coe_comp] at hinj
  exact fun hbot ↦ IsDiscreteValuationRing.not_a_field O
    ((Ideal.map_eq_bot_iff_of_injective hinj.of_comp).mp hbot)

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- The special fiber `O_L ⧸ 𝔪·O_L` is Artinian (a finite algebra over the residue field). -/
theorem integralClosure_quotient_isArtinianRing :
    IsArtinianRing ((integralClosure O L)
      ⧸ (maximalIdeal O).map (algebraMap O (integralClosure O L))) := by
  have := IsIntegralClosure.finite O K L (integralClosure O L)
  set A := integralClosure O L
  set J := (maximalIdeal O).map (algebraMap O A)
  have hfinO : Module.Finite O (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective O J)
  let : Algebra (ResidueField O) (A ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have htower : IsScalarTower O (ResidueField O) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun o ↦ rfl
  have hfinκ : Module.Finite (ResidueField O) (A ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O (ResidueField O) (A ⧸ J)
  exact isArtinian_of_tower (ResidueField O) inferInstance

variable [IsAdicComplete (maximalIdeal O) O]

include K in
/-- The integral closure is complete for the (extended) maximal-ideal-adic topology of the
base, being a finite module over the complete `O`. -/
theorem integralClosure_isAdicComplete_map :
    IsAdicComplete ((maximalIdeal O).map (algebraMap O (integralClosure O L)))
      (integralClosure O L) := by
  have := IsIntegralClosure.finite O K L (integralClosure O L)
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr
    (isAdicComplete_of_finite (maximalIdeal O) (integralClosure O L))

include K in
/-- **The integral closure of a complete DVR in a finite separable extension is local.** -/
theorem integralClosure_isLocalRing : IsLocalRing (integralClosure O L) := by
  have h1 := integralClosure_isAdicComplete_map O K L
  have h2 := integralClosure_quotient_isArtinianRing O K L
  exact IsLocalRing.of_isAdicComplete_of_isDomain
    (I := (maximalIdeal O).map (algebraMap O (integralClosure O L)))

include K in
theorem integralClosure_map_maximalIdeal_ne_top :
    (maximalIdeal O).map (algebraMap O (integralClosure O L)) ≠ ⊤ := by
  have := integralClosure_isAdicComplete_map O K L
  intro h
  have hle := IsAdicComplete.le_jacobson_bot
    ((maximalIdeal O).map (algebraMap O (integralClosure O L)))
  exact bot_ne_top (Ideal.jacobson_eq_top_iff.mp (top_le_iff.mp (h ▸ hle)))

include K in
/-- **The integral closure of a complete DVR in a finite separable extension is a DVR.** -/
theorem integralClosure_isDiscreteValuationRing :
    IsDiscreteValuationRing (integralClosure O L) := by
  have hded := integralClosure.isDedekindDomain O K L
  have hloc := integralClosure_isLocalRing O K L
  have hnf : ¬IsField (integralClosure O L) := by
    intro hf
    let := hf.toField
    exact (Ideal.eq_bot_or_top ((maximalIdeal O).map (algebraMap O (integralClosure O L)))).elim
      (integralClosure_map_maximalIdeal_ne_bot O K L)
      (integralClosure_map_maximalIdeal_ne_top O K L)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure O L) hnf).out 3 1).mp hded

/-- **The integral closure of a complete DVR in a finite separable extension is complete**
(for its own maximal-ideal-adic topology): `𝔪·O_L` is a power of the maximal ideal of the
DVR `O_L`, so completeness transfers from `integralClosure_isAdicComplete_map`. -/
theorem integralClosure_isAdicComplete_maximalIdeal :
    have := integralClosure_isLocalRing O K L
    IsAdicComplete (maximalIdeal (integralClosure O L)) (integralClosure O L) := by
  have hdvr := integralClosure_isDiscreteValuationRing O K L
  have hloc := integralClosure_isLocalRing O K L
  have hded := integralClosure.isDedekindDomain O K L
  have hcompl := integralClosure_isAdicComplete_map O K L
  have hnf := IsDiscreteValuationRing.not_isField (integralClosure O L)
  have hpow := ((IsDiscreteValuationRing.TFAE (integralClosure O L) hnf).out 1 7).mp hdvr
  obtain ⟨e, he⟩ := hpow _ (integralClosure_map_maximalIdeal_ne_bot O K L)
  have he0 : 0 < e := Nat.pos_of_ne_zero fun h ↦
    integralClosure_map_maximalIdeal_ne_top O K L (by simpa [h] using he)
  rw [he] at hcompl
  exact isAdicComplete_of_pow he0

end Assembly

end ChabautyColeman
