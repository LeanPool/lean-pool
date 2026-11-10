/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.AdicTopology
public import LeanPool.HyperellipticCurves.ForMathlib.UniformGroup
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

import LeanPool.HyperellipticCurves.ForMathlib.AdicValuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# The fraction field of the DVR as a valued field

The `p`-adic kit topologizes the complete DVR `O` via its `𝔪`-adic topology
(`LeanPool.HyperellipticCurves.Series.PSeries`). To evaluate `K`-power series — the antiderivatives
of the
differentials `ω′`, which carry `p`-denominators and so cannot live over `O` — at disk
points, `K = FractionRing O` needs its own topology. This file gives `K` the `𝔪`-adic
*valuation* topology (`ChabautyColeman.FractionTopology.valuedFractionRing`, via the
height-one prime `IsDiscreteValuationRing.maximalIdeal O` and `HeightOneSpectrum.adicValued`),
which supplies the complete-nonarchimedean topological-ring structure without going through
the local-ring / adic-ideal machinery (`K` is a field, so it has no ideal-linear topology).

The two facts connecting to the `O`-side are:
* `ChabautyColeman.FractionTopology.isTopologicallyNilpotent_algebraMap` — a point of `𝔪`
  is topologically nilpotent in `K`, so it is a legitimate evaluation point;
* `ChabautyColeman.FractionTopology.continuous_algebraMap` — the inclusion `O ↪ K` is
  continuous, so `O`-level convergent sums (`ChabautyColeman.PSeries.hasSum_eval`) push
  forward to `K` unchanged. This is what realizes the `p`-adic Coleman integral value as
  the image of the integral `O`-level logarithm value.

When `O` is a *complete* DVR, `K` is moreover a complete valued field
(`ChabautyColeman.FractionTopology.instCompleteSpace`): the inclusion `O ↪ K` is a uniform
embedding (`isInducing_algebraMap`/`isUniformInducing_algebraMap`), so its image `𝒪[K]` is a
complete open additive subgroup (`isComplete_range_algebraMap`,
`range_algebraMap_eq_integer`), whence `AddSubgroup.completeSpace_of_isComplete` applies.
This completeness is what lets the bespoke `K`-power-series sums of the Coleman integral
converge in `K`.

The `Valued` instance is `scoped`, so it does not disturb the purely algebraic use of
`FractionRing O` elsewhere in the development.
-/

@[expose] public section

open IsLocalRing IsDedekindDomain.HeightOneSpectrum Filter Topology
open scoped WithZero

namespace ChabautyColeman.FractionTopology

section Valuation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The maximal ideal of the DVR `O` as a height-one prime. -/
noncomputable def Ospec (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    IsDedekindDomain.HeightOneSpectrum O :=
  IsDiscreteValuationRing.maximalIdeal O

/-- `K = FractionRing O` as a valued field for the `𝔪`-adic valuation. This supplies the
uniform / topological-ring structure needed to evaluate `K`-power series at disk points. -/
noncomputable scoped instance valuedFractionRing : Valued (FractionRing O) ℤᵐ⁰ :=
  (Ospec O).adicValued

/-- A point of the maximal ideal of `O` is topologically nilpotent in `K`, hence a legitimate
evaluation point for `K`-power series. -/
theorem isTopologicallyNilpotent_algebraMap {z₀ : O} (hz₀ : z₀ ∈ maximalIdeal O) :
    IsTopologicallyNilpotent (algebraMap O (FractionRing O) z₀) :=
  Valued.tendsto_zero_pow_of_v_lt_one
    (((Ospec O).valuation_lt_one_iff_mem (K := FractionRing O) z₀).mpr hz₀)

/-- The image of `O` in `K` is the valuation ring `𝒪[K]`. Mathlib's
`IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring` is the same fact stated as an
equality of subrings for the `maximalIdeal`-adic valuation; this is the `Set.range` /
`Valued.integer` form the scoped `Valued` instance below consumes. -/
theorem range_algebraMap_eq_integer :
    Set.range (algebraMap O (FractionRing O)) = (Valued.integer (FractionRing O) : Set _) := by
  ext x
  rw [Set.mem_range, SetLike.mem_coe, Valuation.mem_integer_iff]
  exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ (Ospec O).valuation_le_one r,
    fun h ↦ IsDiscreteValuationRing.exists_lift_of_le_one (A := O) h⟩

/-- `K = FractionRing O` is a nonarchimedean ring: the valuation balls form a neighbourhood
basis of open additive subgroups. -/
scoped instance instNonarchimedeanRing : NonarchimedeanRing (FractionRing O) :=
  (Valued.v : Valuation (FractionRing O) ℤᵐ⁰).subgroups_basis.nonarchimedean

end Valuation

section Continuity

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsTopologicalRing O]

/-- The inclusion of the DVR `O` into its valued fraction field `K` is continuous: the
`𝔪`-adic topology on `O` maps into the valuation topology on `K`. -/
theorem continuous_algebraMap : Continuous (algebraMap O (FractionRing O)) := by
  apply continuous_of_continuousAt_zero (algebraMap O (FractionRing O)).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [Filter.HasBasis.tendsto_iff (Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero
    (Valued.hasBasis_nhds_zero (FractionRing O) ℤᵐ⁰)]
  intro γ _
  let v : Valuation (FractionRing O) ℤᵐ⁰ := Valued.v
  have hlt : (WithZero.exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hlt
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (v : FractionRing O →*₀ ℤᵐ⁰))) γ)
  refine ⟨n, trivial, fun x hx ↦ ?_⟩
  rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [Units.coe_map] at hn
  change Valued.v (algebraMap O (FractionRing O) x) < _
  calc Valued.v (algebraMap O (FractionRing O) x)
      = (Ospec O).intValuation x := (Ospec O).valuation_of_algebraMap x
    _ ≤ WithZero.exp (-(n : ℤ)) := ((Ospec O).intValuation_le_pow_iff_mem x n).mpr hx
    _ = WithZero.exp (-1 : ℤ) ^ n := by rw [← WithZero.exp_nsmul]; congr 1; simp
    _ < _ := hn

end Continuity

section Complete

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsTopologicalRing O]

/-- The inclusion `O ↪ K` is a topological embedding: the `𝔪`-adic topology on `O` is exactly
the subspace topology from the valuation topology on `K`. -/
theorem isInducing_algebraMap : IsInducing (algebraMap O (FractionRing O)) := by
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
  refine le_antisymm ?_ ?_
  · have h := continuous_algebraMap (O := O).continuousAt (x := 0)
    rw [ContinuousAt, map_zero] at h
    exact h.le_comap
  · let v : Valuation (FractionRing O) ℤᵐ⁰ := Valued.v
    rw [(Fact.out : IsAdic (maximalIdeal O)).hasBasis_nhds_zero.ge_iff]
    intro n _
    rw [Filter.mem_comap]
    obtain ⟨π, hπ⟩ := (Ospec O).intValuation_exists_uniformizer
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [Valuation.map_zero] at hπ
      exact absurd hπ.symm WithZero.exp_ne_zero
    set fπn := algebraMap O (FractionRing O) (π ^ n)
    have hne : fπn ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O (FractionRing O))).mpr
        (pow_ne_zero n hπ0)
    have hvne : v fπn ≠ 0 := (Valuation.ne_zero_iff v).mpr hne
    set γ : v.ValueGroup₀ˣ :=
      Units.mk0 (restrict₀ (v : FractionRing O →*₀ ℤᵐ⁰) fπn)
        (by rw [ne_eq, restrict₀_eq_zero_iff]; exact hvne)
      with hγ
    have hval : v fπn = WithZero.exp (-(n : ℤ)) := by
      have h : v fπn = (Ospec O).intValuation (π ^ n) := (Ospec O).valuation_of_algebraMap (π ^ n)
      rw [h, map_pow, hπ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hemb : embedding γ.1 = WithZero.exp (-(n : ℤ)) := by
      rw [hγ, Units.val_mk0, embedding_restrict₀]; exact hval
    refine ⟨{x | v.restrict x < γ.1}, ?_, ?_⟩
    · rw [Valued.mem_nhds_zero]
      exact ⟨γ, subset_rfl⟩
    · intro r hr
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hr
      rw [Valuation.restrict_lt_iff_lt_embedding, hemb] at hr
      have hva : v (algebraMap O (FractionRing O) r) = (Ospec O).intValuation r :=
        (Ospec O).valuation_of_algebraMap r
      rw [hva] at hr
      exact ((Ospec O).intValuation_le_pow_iff_mem r n).mp hr.le

variable [IsUniformAddGroup O]

/-- The inclusion `O ↪ K` is a uniform embedding. -/
theorem isUniformInducing_algebraMap :
    IsUniformInducing (algebraMap O (FractionRing O)) :=
  AddMonoidHom.isUniformInducing_of_isInducing (f := algebraMap O (FractionRing O))
    isInducing_algebraMap

variable [CompleteSpace O]

/-- The valuation integers `𝒪[K] = range (O ↪ K)` are complete. -/
theorem isComplete_range_algebraMap :
    IsComplete (Set.range (algebraMap O (FractionRing O))) :=
  isUniformInducing_algebraMap.isComplete_range

/-- **The fraction field of a complete DVR is a complete valued field.** `𝒪[K]` (the image of
`O`) is a complete, open additive subgroup. -/
scoped instance instCompleteSpace : CompleteSpace (FractionRing O) := by
  set S : AddSubgroup (FractionRing O) :=
    (algebraMap O (FractionRing O) : O →+ FractionRing O).range
  have hScoe : (S : Set (FractionRing O)) = Set.range (algebraMap O (FractionRing O)) :=
    AddMonoidHom.coe_range _
  refine S.completeSpace_of_isComplete (hScoe ▸ isComplete_range_algebraMap) ?_
  rw [hScoe, range_algebraMap_eq_integer]
  exact (Valued.isOpen_integer _).mem_nhds (Valued.integer _).zero_mem

end Complete

section Equivariance

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The `𝔪`-adic valuation on the DVR `O` is invariant under any ring automorphism: `φ` carries
a uniformizer to a uniformizer (irreducibility is preserved by a ring equivalence) and units to
units. -/
theorem intValuation_ringEquiv (φ : O ≃+* O) (a : O) :
    (Ospec O).intValuation (φ a) = (Ospec O).intValuation a := by
  have hval {π : O} (hπ : Irreducible π) : (Ospec O).intValuation π = WithZero.exp (-1 : ℤ) :=
    (Ospec O).intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]
  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hirr
  rw [map_mul, map_pow, map_mul, map_mul, map_pow, map_pow, hval (hirr.map φ), hval hirr,
    (Ospec O).intValuation_eq_one_of_isUnit (u.isUnit.map φ),
    (Ospec O).intValuation_eq_one_of_isUnit u.isUnit]

/-- The valuation on `K = Frac O` is invariant under the field automorphism induced by a ring
automorphism of `O` (e.g. the Frobenius of `ℚ_q/ℚ_p` on `O = W(𝔽_q)`): such an automorphism
is an isometry. -/
theorem valuation_ringEquiv (φ : O ≃+* O) (φK : FractionRing O ≃+* FractionRing O)
    (hφK : ∀ a : O, φK (algebraMap O (FractionRing O) a) = algebraMap O (FractionRing O) (φ a))
    (x : FractionRing O) :
    Valued.v (φK x) = Valued.v x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hval : ∀ c : O, Valued.v (algebraMap O (FractionRing O) c) = (Ospec O).intValuation c :=
    fun c ↦ (Ospec O).valuation_of_algebraMap c
  rw [map_div₀, hφK, hφK, map_div₀, map_div₀, hval, hval, hval, hval,
    intValuation_ringEquiv φ, intValuation_ringEquiv φ]

/-- **A field automorphism of `K = Frac O` induced by a ring automorphism of `O` is
continuous** (being a valuation-preserving isometry). This makes limits of Galois-symmetric
series Galois-fixed — the analytic core of blueprint `lem:values-rational`. -/
theorem continuous_ringEquiv (φ : O ≃+* O) (φK : FractionRing O ≃+* FractionRing O)
    (hφK : ∀ a : O, φK (algebraMap O (FractionRing O) a) = algebraMap O (FractionRing O) (φ a)) :
    Continuous φK := by
  apply continuous_of_continuousAt_zero (φK : FractionRing O →+* FractionRing O).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [Filter.HasBasis.tendsto_iff (Valued.hasBasis_nhds_zero (FractionRing O) ℤᵐ⁰)
    (Valued.hasBasis_nhds_zero (FractionRing O) ℤᵐ⁰)]
  refine fun γ _ ↦ ⟨γ, trivial, fun x hx ↦ ?_⟩
  rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  change Valued.v (φK x) < _
  rwa [valuation_ringEquiv φ φK hφK]

end Equivariance

end ChabautyColeman.FractionTopology

end
