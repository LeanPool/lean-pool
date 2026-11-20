/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.HarmonicRaising

/-! # Degree arithmetic in the Boolean polynomial algebra -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

theorem booleanDegreeLE_mono {n d e : ℕ} {f : BooleanPolynomial n}
    (hf : BooleanDegreeLE f d) (hde : d ≤ e) : BooleanDegreeLE f e :=
  fun S hS ↦ (hf S hS).trans hde

theorem booleanDegreeLE_zero (n d : ℕ) : BooleanDegreeLE (0 : BooleanPolynomial n) d := by
  intro S hS
  exact False.elim (hS rfl)

theorem booleanDegreeLE_sum {n d : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → BooleanPolynomial n) (hf : ∀ i ∈ s, BooleanDegreeLE (f i) d) :
    BooleanDegreeLE (∑ i ∈ s, f i) d := by
  classical
  intro S hS
  by_contra hcard
  apply hS
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hne
  exact hcard (hf i hi S hne)

theorem booleanDegreeLE_add {n d : ℕ} {f g : BooleanPolynomial n}
    (hf : BooleanDegreeLE f d) (hg : BooleanDegreeLE g d) : BooleanDegreeLE (f + g) d := by
  intro S hS
  by_cases hfc : f.coeff S = 0
  · have hgc : g.coeff S ≠ 0 := by
      intro he
      apply hS
      simp [hfc, he]
    exact hg S hgc
  · exact hf S hfc

theorem booleanDegreeLE_smul {n d : ℕ} (a : ℝ) {f : BooleanPolynomial n}
    (hf : BooleanDegreeLE f d) : BooleanDegreeLE (a • f) d := by
  intro S hS
  apply hf S
  intro he
  apply hS
  simp [he]

theorem booleanDegreeLE_sub {n d : ℕ} {f g : BooleanPolynomial n}
    (hf : BooleanDegreeLE f d) (hg : BooleanDegreeLE g d) : BooleanDegreeLE (f - g) d := by
  rw [sub_eq_add_neg]
  exact booleanDegreeLE_add hf (by simpa using booleanDegreeLE_smul (-1) hg)

theorem booleanDegreeLE_monomial {n d : ℕ} (S : Finset (Fin n)) (a : ℝ)
    (hS : S.card ≤ d) : BooleanDegreeLE (booleanMonomial S a) d := by
  classical
  intro T hT
  rw [booleanMonomial_coeff] at hT
  have he : S = T.toFinset := by
    by_contra hne
    exact hT (ite_eq_right hne)
  change T.toFinset.card ≤ d
  exact he ▸ hS

theorem booleanDegreeLE_mul {n d e : ℕ} {f g : BooleanPolynomial n}
    (hf : BooleanDegreeLE f d) (hg : BooleanDegreeLE g e) : BooleanDegreeLE (f * g) (d + e) := by
  classical
  have hfe : f = ∑ S ∈ f.coeff.support, booleanMonomial S.toFinset (f.coeff S) :=
    (MonoidAlgebra.sum_coeff_single f).symm
  have hge : g = ∑ T ∈ g.coeff.support, booleanMonomial T.toFinset (g.coeff T) :=
    (MonoidAlgebra.sum_coeff_single g).symm
  rw [hfe, hge, Finset.sum_mul]
  apply booleanDegreeLE_sum
  intro S hS
  rw [Finset.mul_sum]
  apply booleanDegreeLE_sum
  intro T hT
  rw [booleanMonomial_mul]
  apply booleanDegreeLE_monomial
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (hf S (Finsupp.mem_support_iff.mp hS)) (hg T (Finsupp.mem_support_iff.mp hT)))

theorem booleanDegreeLE_one (n : ℕ) : BooleanDegreeLE (1 : BooleanPolynomial n) 0 := by
  rw [← booleanMonomial_empty]
  exact booleanDegreeLE_monomial _ _ (by simp)

theorem booleanDegreeLE_totalVariable (n : ℕ) : BooleanDegreeLE (totalVariable n) 1 := by
  apply booleanDegreeLE_sum
  intro i _
  exact booleanDegreeLE_monomial {i} 1 (by simp)

theorem booleanDegreeLE_total_sub (n : ℕ) (a : ℝ) :
    BooleanDegreeLE (totalVariable n - a • 1) 1 :=
  booleanDegreeLE_sub (booleanDegreeLE_totalVariable n)
    (booleanDegreeLE_smul a (booleanDegreeLE_mono (booleanDegreeLE_one n) (by omega)))

end NoncommutativeAMGM
