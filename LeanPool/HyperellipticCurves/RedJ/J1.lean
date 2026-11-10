/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.RedJ.Congr
public import LeanPool.HyperellipticCurves.RedJ.Hom

/-!
# The base change to the completed field and the kernel of reduction `J¹`

`ChabautyColeman.mapBase` is the base-change map `J(K₀) →* J(K)` from the Jacobian over the
arithmetic base field `K₀ ⊆ K` to the Jacobian over the fraction field `K` of the complete
DVR `O`, compatible with the Abel--Jacobi map (`ChabautyColeman.mapBase_aj`).

`ChabautyColeman.J1` is the kernel of the composed reduction `J(K₀) → J(K) → J(κ_bar)`
(`def:redJ`): the subgroup of classes whose base change reduces trivially. A class whose
base change is exhibited as a kernel element, or as a quotient of two kernel elements, lies
in `J¹` (`ChabautyColeman.mem_J1_of_mapBase_eq`, `ChabautyColeman.mem_J1_of_mapBase_eq_div`)
— this is how the same-disk difference classes of the counting chapter enter the pairing
`λ`, which is defined on `J¹` (blueprint `def:lambda`).

The finite-index theorem for `J¹` (`thm:J1-index`, via Frobenius equivariance) is formalized in
`upstream HyperellipticCurves.Archive.J1FiniteIndex`; the main theorems do not depend on it.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

/-! ### The base change from the Jacobian over the arithmetic base field -/

section Base

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K]
  {f : O[X]} (K₀ : Type*) [Field K₀] [Algebra K₀ K] (f₀ : K₀[X])

/-- The index equation of `ChabautyColeman.HypJac.congr` at the identity of `K`: transporting
`f₀` along the trivial automorphism returns the base-changed `f`. -/
theorem map_refl_eq (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) :
    (f₀.map (algebraMap K₀ K)).map ((RingEquiv.refl K : K ≃+* K) : K →+* K)
      = f.map (algebraMap O K) := by
  rw [RingEquiv.toRingHom_refl, Polynomial.map_id, hf₀]

variable [CharZero K] [CharZero K₀]
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd f₀.natDegree)] [Fact (Squarefree f₀)]

/-- The base-change map `J(K₀) →* J(K)`, with the target index expressed through `O`. -/
noncomputable def mapBase (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) :
    HypJac K₀ f₀ →* HypJac K (f.map (algebraMap O K)) :=
  ((HypJac.congr (f₀.map (algebraMap K₀ K)) (RingEquiv.refl K)
    (map_refl_eq K₀ f₀ hf₀)).toMonoidHom).comp (HypJac.map f₀)

/-- **The base change to `K` is compatible with the Abel--Jacobi map**: the class of a
`K₀`-rational point is the class of the same point read over `K`. This is what identifies
the base change of a difference of rational points with a same-disk difference. -/
theorem mapBase_aj (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) (x₀ y₀ : K₀) :
    mapBase K₀ f₀ hf₀ (aj f₀ x₀ y₀)
      = aj (f.map (algebraMap O K)) (algebraMap K₀ K x₀) (algebraMap K₀ K y₀) := by
  rw [mapBase, MonoidHom.comp_apply, HypJac.map_aj, MulEquiv.coe_toMonoidHom, HypJac.congr_aj]
  simp

end Base

/-! ### The kernel of reduction -/

section J1

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type u} [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
  [IsAlgClosed (ResidueField O)] [NeZero (2 : ResidueField O)]
  {f : O[X]}
  [Fact (Odd (f.map (algebraMap O K)).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O K)))]
  [Fact (Odd (f.map (residue O)).natDegree)] [Fact (Squarefree (f.map (residue O)))]
  (K₀ : Type*) [Field K₀] [Algebra K₀ K]
  (f₀ : K₀[X]) [Fact (Odd f₀.natDegree)]

/-- `J¹(K₀)`: the kernel of the reduction map on the Jacobian over the arithmetic base
field (blueprint `def:lambda`). -/
noncomputable def J1 (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) : Subgroup (HypJac K₀ f₀) :=
  ((redJHom hf hdeg).comp (mapBase K₀ f₀ hf₀)).ker

theorem mem_J1_iff (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)) {c : HypJac K₀ f₀} :
    c ∈ J1 K₀ f₀ hf hdeg hf₀ ↔ mapBase K₀ f₀ hf₀ c ∈ (redJHom (K := K) (f := f) hf hdeg).ker :=
  Iff.rfl

variable {K₀ f₀}

/-- A class whose base change is a kernel element lies in `J¹`. -/
theorem mem_J1_of_mapBase_eq {hf : f.Monic} {hdeg : 0 < f.natDegree}
    {hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)} {c : HypJac K₀ f₀}
    {k : (redJHom (K := K) (f := f) hf hdeg).ker} (hc : mapBase K₀ f₀ hf₀ c = k) :
    c ∈ J1 K₀ f₀ hf hdeg hf₀ := by
  rw [mem_J1_iff, hc]
  exact k.2

/-- A class whose base change is a quotient of two kernel elements lies in `J¹`. -/
theorem mem_J1_of_mapBase_eq_div {hf : f.Monic} {hdeg : 0 < f.natDegree}
    {hf₀ : f₀.map (algebraMap K₀ K) = f.map (algebraMap O K)} {c : HypJac K₀ f₀}
    {k k' : (redJHom (K := K) (f := f) hf hdeg).ker}
    (hc : mapBase K₀ f₀ hf₀ c = ↑k' * (↑k : HypJac K (f.map (algebraMap O K)))⁻¹) :
    c ∈ J1 K₀ f₀ hf hdeg hf₀ := by
  rw [mem_J1_iff, hc]
  exact mul_mem k'.2 (inv_mem k.2)

end J1

end ChabautyColeman

end
