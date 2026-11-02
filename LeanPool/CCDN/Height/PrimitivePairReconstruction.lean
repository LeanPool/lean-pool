/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A primitive coordinate pair generates the function field over the constant
field. Every finite family of functions then has polynomial reconstruction
identities with one nonzero denominator. No bound on its degree is asserted. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A generating polynomial tuple expresses any field element as a quotient
with a nonzero evaluated denominator. -/
lemma adjoin_top_polynomial_fraction {K F σ : Type*} [Field K] [Field F] [Algebra K F]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤) (x : F) :
    ∃ r s : MvPolynomial σ K, aeval a s ≠ 0 ∧ x = aeval a r / aeval a s := by
  by_cases hx : x = 0
  · exact ⟨0, 1, by simp, by simp [hx]⟩
  obtain ⟨r, s, he⟩ := (IntermediateField.mem_adjoin_range_iff K a x).mp
    (by rw [ha]; trivial)
  refine ⟨r, s, ?_, he⟩
  intro hs
  apply hx
  rw [he, hs, div_zero]

/-- A finite family of field elements has a common polynomial denominator in
any generating tuple, with polynomial reconstruction identities. -/
theorem exists_common_polynomial_reconstruction {K F σ ι : Type*}
    [Field K] [Field F] [Algebra K F] [Finite ι]
    (a : σ → F) (ha : IntermediateField.adjoin K (Set.range a) = ⊤)
    (x : ι → F) :
    ∃ Q : MvPolynomial σ K, ∃ P : ι → MvPolynomial σ K,
      aeval a Q ≠ 0 ∧ ∀ i, aeval a Q * x i = aeval a (P i) := by
  classical
  let := Fintype.ofFinite ι
  choose r s hs he using fun i => adjoin_top_polynomial_fraction a ha (x i)
  let Q := ∏ i, s i
  let P := fun i => r i * ∏ j ∈ Finset.univ.erase i, s j
  refine ⟨Q, P, ?_, ?_⟩
  · simpa only [Q, map_prod] using Finset.prod_ne_zero_iff.mpr (fun i _ => hs i)
  · intro i
    have hQ : Q = s i * ∏ j ∈ Finset.univ.erase i, s j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hQ, he, map_mul]
    dsimp only [P]
    rw [map_mul]
    field_simp [hs i]

end
end CCDN
