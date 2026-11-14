/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Specialization.CpZeros

import LeanPool.HyperellipticCurves.Disks.Charts
import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import LeanPool.HyperellipticCurves.ForMathlib.WeierstrassPreparation

/-!
# Zero-counting for split polynomials over a complete DVR

For a polynomial `G` over a complete DVR `O` with nonzero reduction, split over the fraction
field `K`, the total multiplicity of the roots of `G` in the open unit disk `𝔪` equals the
multiplicity of `0` as a root of the reduction `G_bar`
(`ChabautyColeman.finsum_rootMultiplicity_maximalIdeal`).

The key observation making this pure polynomial algebra is
`PowerSeries.IsWeierstrassFactorization.polynomial_cofactor`: when a *polynomial* is
Weierstrass-factored as a power series, `F = W·u`, the unit cofactor `u` is itself a
*polynomial* (namely `F /ₘ W`, by uniqueness of Weierstrass division), with unit constant
coefficient — so it has no zeros in the disk (`isUnit_eval_of_isUnit_coeff_zero`) and no
power-series evaluation is ever needed. Together with
`root_mem_maximalIdeal_of_distinguished` (roots of the distinguished factor lie in `𝔪`) the
count reduces to `deg W`, which is the vanishing order of `G_bar` at `0` since `W_bar = X^{deg W}`
(`Polynomial.IsDistinguishedAt.map_eq_X_pow`).

This is the splitting-field counterpart of the algebraically closed count
`ChabautyColeman.zeros_eq_ord` (in `upstream HyperellipticCurves.Archive.SpecializationGeneric`),
used for
the reduction-of-points assembly (`thm:redJ-hom`): over the splitting field of the norm polynomial,
all zeros of a function on a residue disk are rational, so the disk sums can be evaluated without
passing to `ℂ_p`.
-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace ChabautyColeman

/-! ### (P2) A polynomial with unit constant coefficient has no zeros in the open disk -/

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- A polynomial over a local ring whose constant coefficient is a unit takes unit values on the
maximal ideal. -/
theorem isUnit_eval_of_isUnit_coeff_zero {q : O[X]} (hq : IsUnit (q.coeff 0)) {z : O}
    (hz : z ∈ maximalIdeal O) : IsUnit (q.eval z) :=
  isUnit_eval_of_sub_mem (coeff_zero_eq_eval_zero q ▸ hq) (by simpa using hz)

/-! ### (P3) Root count in the open disk = order of the reduction -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- A polynomial over `O` with unit constant coefficient has no root of the form
`algebraMap O K z` with `z ∈ 𝔪`: its value there is a unit, hence nonzero. -/
private theorem rootMultiplicity_map_algebraMap_eq_zero {q : O[X]} (hq : IsUnit (q.coeff 0))
    (z : maximalIdeal O) :
    (q.map (algebraMap O K)).rootMultiplicity (algebraMap O K ↑z) = 0 := by
  refine rootMultiplicity_eq_zero fun hroot ↦ ?_
  rw [IsRoot, eval_map_apply] at hroot
  exact (isUnit_eval_of_isUnit_coeff_zero hq z.2).ne_zero
    ((map_eq_zero_iff _ (IsFractionRing.injective O K)).mp hroot)

/-- Counting tail: for a split polynomial `P` over `K` all of whose roots lie in the range of an
injection `e`, the total multiplicity of `P` at the points `e z` equals `deg P`. -/
private theorem finsum_rootMultiplicity_eq_natDegree {α : Type*} {P : K[X]} (hsplit : P.Splits)
    {e : α → K} (hinj : Function.Injective e) (hroots : ∀ x ∈ P.roots, x ∈ Set.range e) :
    ∑ᶠ z : α, P.rootMultiplicity (e z) = P.natDegree := by
  classical
  have hsupp : (Function.support fun z : α ↦ P.rootMultiplicity (e z))
      ⊆ ↑(P.roots.toFinset.preimage e hinj.injOn) := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [Finset.mem_coe, Finset.mem_preimage, Multiset.mem_toFinset]
    exact Multiset.count_pos.mp (by rw [count_roots]; exact Nat.pos_of_ne_zero hz)
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp,
    Finset.sum_preimage e P.roots.toFinset hinj.injOn (fun x ↦ P.rootMultiplicity x)
      (fun x hx hxr ↦ absurd (hroots x (Multiset.mem_toFinset.mp hx)) hxr)]
  calc ∑ x ∈ P.roots.toFinset, P.rootMultiplicity x
      = ∑ x ∈ P.roots.toFinset, P.roots.count x :=
        Finset.sum_congr rfl fun x _ ↦ (count_roots P).symm
    _ = P.roots.card := P.roots.toFinset_sum_count_eq
    _ = P.natDegree := splits_iff_card_roots.mp hsplit

/-- **Root count in the open disk.** For a polynomial `G` over a complete DVR with nonzero
reduction, split over the fraction field, the total multiplicity of its roots in the open unit
disk `𝔪` equals the multiplicity of `0` as a root of the reduction `G_bar`. -/
theorem finsum_rootMultiplicity_maximalIdeal {G : O[X]} (hG : G.map (residue O) ≠ 0)
    (hsplit : (G.map (algebraMap O K)).Splits) :
    ∑ᶠ z : maximalIdeal O, (G.map (algebraMap O K)).rootMultiplicity (algebraMap O K ↑z)
      = (G.map (residue O)).rootMultiplicity 0 := by
  classical
  have hG0 : G ≠ 0 := fun h ↦ hG (by rw [h, Polynomial.map_zero])
  have hGser : (G : O⟦X⟧).map (residue O) ≠ 0 := by
    rwa [← Polynomial.polynomial_map_coe, ne_eq, Polynomial.coe_eq_zero_iff]
  have hfac := PowerSeries.isWeierstrassFactorization_weierstrassDistinguished_weierstrassUnit
    (g := (G : O⟦X⟧)) hGser
  set W := PowerSeries.weierstrassDistinguished (G : O⟦X⟧) hGser
  obtain ⟨hFW, hQunit, -⟩ := hfac.polynomial_cofactor
  set Q := G /ₘ W
  -- the reduced factorization G_bar = X^d · Q_bar
  have hWX : W.map (residue O) = Polynomial.X ^ W.natDegree := hfac.isDistinguishedAt.map_eq_X_pow
  have hdred : G.map (residue O) = Polynomial.X ^ W.natDegree * Q.map (residue O) := by
    nth_rw 1 [hFW]
    rw [Polynomial.map_mul, hWX]
  have hQ0red : (Q.map (residue O)).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_map]
    exact (hQunit.map (residue O)).ne_zero
  have hRHS : (G.map (residue O)).rootMultiplicity 0 = W.natDegree := by
    rw [hdred, rootMultiplicity_zero_X_pow_mul _ hQ0red]
  -- the split factorization over K
  set ι : maximalIdeal O → K := fun z ↦ algebraMap O K ↑z
  have hinj : Function.Injective ι := fun a b hab ↦
    Subtype.ext (IsFractionRing.injective O K hab)
  have hGKfac : G.map (algebraMap O K) = W.map (algebraMap O K) * Q.map (algebraMap O K) := by
    nth_rw 1 [hFW]
    exact Polynomial.map_mul _
  have hGK0 : G.map (algebraMap O K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (IsFractionRing.injective O K)).mpr hG0
  -- pointwise on the disk, only the distinguished factor contributes
  have hterm (z : maximalIdeal O) :
      (G.map (algebraMap O K)).rootMultiplicity (ι z)
        = (W.map (algebraMap O K)).rootMultiplicity (ι z) := by
    rw [hGKfac, rootMultiplicity_mul (by rw [← hGKfac]; exact hGK0),
      rootMultiplicity_map_algebraMap_eq_zero hQunit z, add_zero]
  -- count the roots of the distinguished factor: all in ι(𝔪), total = deg W
  have hWsplit : (W.map (algebraMap O K)).Splits :=
    hsplit.of_dvd hGK0 ⟨Q.map (algebraMap O K), hGKfac⟩
  have hroots : ∀ x ∈ (W.map (algebraMap O K)).roots, x ∈ Set.range ι := by
    intro x hx
    obtain ⟨w, hw𝔪, hwx⟩ := root_mem_maximalIdeal_of_distinguished hfac.isDistinguishedAt
      (isRoot_of_mem_roots hx)
    exact ⟨⟨w, hw𝔪⟩, hwx⟩
  rw [finsum_congr hterm, hRHS,
    ← hfac.isDistinguishedAt.monic.natDegree_map (algebraMap O K)]
  exact finsum_rootMultiplicity_eq_natDegree hWsplit hinj hroots

end Count

end ChabautyColeman
