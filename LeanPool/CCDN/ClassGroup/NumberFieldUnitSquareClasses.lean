/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-! Uniform control of the unit contribution to quadratic descent.
Dirichlet's theorem and cyclicity of roots of unity give at most one
binary choice per free unit and one further binary choice for torsion.
The endpoint concerns the unit group modulo squares. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

private def integerParityIndex (e : ℤ) : Fin 2 :=
  ⟨(e % 2).toNat, by omega⟩

private theorem zpow_eq_parity_pow {G : Type*} [Group G] (x : G)
    (hx : x ^ 2 = 1) (e : ℤ) :
    x ^ e = x ^ (integerParityIndex e).val := by
  rw [zpow_eq_zpow_emod' e hx, ← zpow_natCast]
  congr 1
  exact (Int.toNat_of_nonneg (Int.emod_nonneg e (by norm_num))).symm

variable (K : Type*) [Field K] [NumberField K]

/-- Every exponent-two quotient of the unit group has cardinality
at most `2^(unit rank + 1)`. The finite parametrization is constructed
from a torsion generator and a fundamental system of units. -/
theorem numberFieldUnit_exponent_two_quotient
    {G : Type*} [CommGroup G] (φ : (𝓞 K)ˣ →* G)
    (hφ : Function.Surjective φ) (hG : ∀ x : G, x ^ 2 = 1) :
    Finite G ∧ Nat.card G ≤ 2 ^ (NumberField.Units.rank K + 1) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_zpow_surjective (NumberField.Units.torsion K)
  let code : Fin 2 × (Fin (NumberField.Units.rank K) → Fin 2) → G :=
    fun e ↦ φ (ζ : (𝓞 K)ˣ) ^ e.1.val *
      ∏ i, φ (NumberField.Units.fundSystem K i) ^ (e.2 i).val
  have hcode : Function.Surjective code := by
    intro y
    obtain ⟨u, rfl⟩ := hφ y
    obtain ⟨⟨η, e⟩, hu, _⟩ := NumberField.Units.exist_unique_eq_mul_prod K u
    obtain ⟨k, hk⟩ := hζ η
    refine ⟨(integerParityIndex k, fun i ↦ integerParityIndex (e i)), ?_⟩
    change φ (ζ : (𝓞 K)ˣ) ^ (integerParityIndex k).val *
      ∏ i, φ (NumberField.Units.fundSystem K i) ^ (integerParityIndex (e i)).val = φ u
    rw [hu, map_mul, map_prod]
    congr 1
    · rw [← hk, Subgroup.coe_zpow, map_zpow]
      exact (zpow_eq_parity_pow _ (hG _) k).symm
    · apply Finset.prod_congr rfl
      intro i _
      rw [map_zpow]
      exact (zpow_eq_parity_pow _ (hG _) (e i)).symm
  refine ⟨Finite.of_surjective code hcode, ?_⟩
  have hc := Nat.card_le_card_of_surjective code hcode
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, pow_succ, mul_comm] using hc

/-- The unit rank of a number field plus one is at most its degree over `ℚ`. -/
theorem numberField_unit_rank_add_one_le_degree :
    NumberField.Units.rank K + 1 ≤ Module.finrank ℚ K := by
  have hpos := Fintype.card_pos (α := InfinitePlace K)
  have hcard := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
  have hrank := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  unfold NumberField.Units.rank
  omega

end
end CCDN
