/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ForMathlib.StandardExponents
public import LeanPool.CCDN.Hilbert.FilteredIntersection
import LeanPool.CCDN.ForMathlib.MvPolynomial
import LeanPool.CCDN.Hilbert.StandardMonomials

/-!
# Linear-growth monomial sets

A downward-closed exponent set with a linear counting bound cannot contain a
large square. Consequently its unbounded portions lie in coordinate rays.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Bounded exponent sets are finite. -/
instance finite_boundedStandardExponents {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) :
    Finite (Ideal.boundedStandardExponents I m N) := by
  classical
  let := Fintype.ofFinite σ
  let e := Finsupp.degreeLeEquivSym σ N
  let f : Ideal.boundedStandardExponents I m N → Sym (Option σ) N :=
    fun a => e ⟨a.val, a.property.2⟩
  apply Finite.of_injective f
  intro a b h
  have he := e.injective h
  apply Subtype.ext
  exact congrArg (fun p : {p : σ →₀ ℕ // p.degree ≤ N} => p.val) he

/-- A standard monomial with two large exponents supplies an entire square of
independent quotient classes in degree at most `2B`. -/
private theorem standard_square_le_filtered {K σ : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (B : ℕ)
    {a : σ →₀ ℕ} (ha : a ∈ Ideal.standardExponents I MonomialOrder.degLex)
    {i j : σ} (hij : i ≠ j) (hi : B ≤ a i) (hj : B ≤ a j) :
    (B + 1) ^ 2 ≤ Module.finrank K (filteredCoordinateSpace I (2 * B)) := by
  classical
  let := Fintype.ofFinite σ
  let f : Fin (B + 1) × Fin (B + 1) →
      Ideal.boundedStandardExponents I MonomialOrder.degLex (2 * B) := fun t =>
    ⟨Finsupp.single i t.1.val + Finsupp.single j t.2.val, by
      constructor
      · apply Ideal.isLowerSet_standardExponents I MonomialOrder.degLex _ ha
        intro k
        by_cases hki : k = i
        · subst k
          simpa [hij, hij.symm] using (show t.1.val ≤ a i from by omega)
        by_cases hkj : k = j
        · subst k
          simpa [hij, hij.symm] using (show t.2.val ≤ a j from by omega)
        simp [hki, hkj]
      · change Finsupp.degree _ ≤ 2 * B
        rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
        omega⟩
  have hinj : Function.Injective f := by
    intro s t h
    have hval := congrArg Subtype.val h
    have h1 := congrArg (fun a : σ →₀ ℕ => a i) hval
    have h2 := congrArg (fun a : σ →₀ ℕ => a j) hval
    simp only [f, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne hij.symm, add_zero, zero_add] at h1 h2
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hc := Nat.card_le_card_of_injective f hinj
  rw [← filteredCoordinateSpace_finrank_eq_standard_card I (2 * B)] at hc
  simpa [Nat.card_prod, Nat.card_fin, pow_two] using hc

/-- Under a linear Hilbert bound, at most one exponent can exceed a fixed
threshold. This excludes every two-dimensional monomial quadrant. -/
theorem standard_at_most_one_large {K σ : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPolynomial σ K)) (C : ℕ)
    (hbound : ∀ N ≥ 14, Module.finrank K (filteredCoordinateSpace I N) ≤ C * (N + 2))
    {a : σ →₀ ℕ} (ha : a ∈ Ideal.standardExponents I MonomialOrder.degLex)
    {i j : σ} (hi : 2 * C + 14 ≤ a i) (hj : 2 * C + 14 ≤ a j) : i = j := by
  classical
  let := Fintype.ofFinite σ
  by_contra hij
  have hs := standard_square_le_filtered I (2 * C + 14) ha hij hi hj
  have hu := hbound (2 * (2 * C + 14)) (by omega)
  nlinarith

/-- A coordinate ray whose other coordinates lie in a finite box. -/
def exponentRay {σ : Type*} [Fintype σ] (B : ℕ)
    (j : σ) (b : σ → Fin B) (n : ℕ) : σ →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm (fun k => (b k).val)).update j n

/-- The ray exponent `exponentRay B j b n` has coordinate `n` at `j` and coordinate `b k` at
every other `k`. -/
@[simp] lemma exponentRay_apply {σ : Type*} [Fintype σ] [DecidableEq σ]
    (B : ℕ) (j : σ) (b : σ → Fin B) (n : ℕ) (k : σ) :
    exponentRay B j b n k = if k = j then n else (b k).val := by
  simp [exponentRay, Finsupp.update_apply, eq_comm]

/-- Uniformly over all rays based in a finite box, membership in a lower set
stabilizes to either the whole ray or the empty tail. -/
theorem lowerSet_rays_eventually_full {σ : Type*} [Fintype σ]
    (S : Set (σ →₀ ℕ)) (hS : IsLowerSet S) (B : ℕ) :
    ∃ M ≥ B, ∀ (j : σ) (b : σ → Fin B) (n : ℕ), M ≤ n →
      (exponentRay B j b n ∈ S ↔ ∀ k, exponentRay B j b k ∈ S) := by
  classical
  have hex (p : σ × (σ → Fin B)) :
      ∃ m, (∀ k, exponentRay B p.1 p.2 k ∈ S) ∨ exponentRay B p.1 p.2 m ∉ S := by
    by_cases h : ∀ k, exponentRay B p.1 p.2 k ∈ S
    · exact ⟨0, Or.inl h⟩
    · push Not at h
      obtain ⟨m, hm⟩ := h
      exact ⟨m, Or.inr hm⟩
  choose m hm using hex
  refine ⟨Finset.univ.sup m + B, by omega, ?_⟩
  intro j b n hn
  constructor
  · intro hmem
    rcases hm (j, b) with hall | hnot
    · exact hall
    · exfalso
      apply hnot
      apply hS _ hmem
      intro k
      simp only [exponentRay_apply]
      split_ifs
      · have hle := Finset.le_sup (f := m) (Finset.mem_univ (j, b))
        omega
      · exact le_rfl
  · exact fun h => h n

end
end CCDN
