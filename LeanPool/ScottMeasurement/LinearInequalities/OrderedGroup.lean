/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.LinearInequalities.ScottTheorems
public import Mathlib.Algebra.Order.Monoid.Lex

/-!
# Ordered groups after Scott's Theorem 1.4

The first result makes precise Scott's observation that every finite part of
a linearly ordered abelian group has a real-valued model.  Pair-sums are put
into the finite system, so the model preserves every addition equation visible
inside that finite part.

The second group of results records the standard lexicographic obstruction:
each finite subsystem is real-valued, but the whole ordered monoid is not.
-/

@[expose] public section

open Set

namespace Scott1964.MeasurementStructures.LinearInequalities

section Local

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

private def localBasis {S : Set G} (x : S) : S → ℝ :=
  Pi.single x 1

private def localPair {S : Set G} (p : S × S) : S → ℝ :=
  localBasis p.1 + localBasis p.2

private def localTests (S : Set G) : Set (S → ℝ) :=
  Set.range localBasis ∪ Set.range localPair

private def natCoordinates {S : Set G} (n : S → ℕ) : S → ℝ :=
  fun i ↦ n i

private def coordinateValue {S : Set G} [Fintype S] (n : S → ℕ) : G :=
  ∑ i, n i • (i : G)

omit [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] in
private theorem natCoordinates_injective {S : Set G} :
    Function.Injective (natCoordinates (S := S)) := by
  intro m n h
  funext i
  exact Nat.cast_injective (congrFun h i)

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
private theorem localBasis_coordinates {S : Set G} (x : S) :
    localBasis x = natCoordinates (Pi.single x 1) := by
  funext i
  classical
  by_cases h : i = x
  · subst i
    simp [localBasis, natCoordinates]
  · simp [localBasis, natCoordinates, h]

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
private theorem localPair_coordinates {S : Set G} (p : S × S) :
    localPair p =
      natCoordinates (Pi.single p.1 1 + Pi.single p.2 1) := by
  rw [localPair, localBasis_coordinates, localBasis_coordinates]
  funext i
  simp [natCoordinates]

omit [IsOrderedAddMonoid G] in
private theorem coordinateValue_single {S : Set G} [Fintype S] (x : S) :
    coordinateValue (Pi.single x 1) = x := by
  classical
  rw [coordinateValue, Finset.sum_eq_single x]
  · simp
  · intro b _ hbx
    simp [hbx]
  · simp

omit [LinearOrder G] [IsOrderedAddMonoid G] in
private theorem coordinateValue_add {S : Set G} [Fintype S] (m n : S → ℕ) :
    coordinateValue (m + n) = coordinateValue m + coordinateValue n := by
  classical
  simp only [coordinateValue, Pi.add_apply, add_nsmul, Finset.sum_add_distrib]

omit [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] in
private theorem natCoordinates_add {S : Set G} (m n : S → ℕ) :
    natCoordinates m + natCoordinates n = natCoordinates (m + n) := by
  funext i
  simp [natCoordinates]

private def coordinateRelation {S : Set G} [Fintype S]
    (v w : S → ℝ) : Prop :=
  ∃ m n : S → ℕ,
    natCoordinates m = v ∧ natCoordinates n = w ∧
      coordinateValue n ≤ coordinateValue m

omit [IsOrderedAddMonoid G] in
private theorem coordinateRelation_encode_iff {S : Set G} [Fintype S]
    (m n : S → ℕ) :
    coordinateRelation (natCoordinates m) (natCoordinates n) ↔
      coordinateValue n ≤ coordinateValue m := by
  constructor
  · rintro ⟨m', n', hm, hn, hle⟩
    have hmm : m' = m := natCoordinates_injective hm
    have hnn : n' = n := natCoordinates_injective hn
    simpa [hmm, hnn] using hle
  · intro hle
    exact ⟨m, n, rfl, rfl, hle⟩

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
private theorem localTests_finite {S : Set G} [Finite S] :
    (localTests S).Finite := by
  let := Fintype.ofFinite S
  exact (Set.finite_range localBasis).union (Set.finite_range localPair)

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
private theorem localTests_rational {S : Set G} :
    IsRationalSet (localTests S) := by
  rintro v (⟨x, rfl⟩ | ⟨p, rfl⟩) i
  · classical
    by_cases h : i = x
    · subst i
      exact ⟨1, by simp [localBasis]⟩
    · exact ⟨0, by simp [localBasis, h]⟩
  · classical
    by_cases h₁ : i = p.1 <;> by_cases h₂ : i = p.2
    · subst i
      have : p.1 = p.2 := h₂
      exact ⟨2, by simp [localPair, localBasis, this]; norm_num⟩
    · subst i
      exact ⟨1, by simp [localPair, localBasis, h₂]⟩
    · subst i
      exact ⟨1, by simp [localPair, localBasis, h₁]⟩
    · exact ⟨0, by simp [localPair, localBasis, h₁, h₂]⟩

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
private theorem localTests_closure_coordinates {S : Set G} {v : S → ℝ}
    (hv : v ∈ additiveClosure (localTests S)) :
    ∃ n : S → ℕ, natCoordinates n = v := by
  induction hv using AddSubmonoid.closure_induction with
  | mem v hv =>
      rcases hv with ⟨x, rfl⟩ | ⟨p, rfl⟩
      · exact ⟨Pi.single x 1, localBasis_coordinates x |>.symm⟩
      · exact ⟨Pi.single p.1 1 + Pi.single p.2 1,
          localPair_coordinates p |>.symm⟩
  | zero => exact ⟨fun _ ↦ 0, by funext i; norm_num [natCoordinates]⟩
  | add v w hv hw ihv ihw =>
      obtain ⟨m, rfl⟩ := ihv
      obtain ⟨n, rfl⟩ := ihw
      exact ⟨m + n, natCoordinates_add m n |>.symm⟩

private theorem coordinateRelation_strictlyMonotonic {S : Set G} [Fintype S] :
    StrictlyMonotonic (additiveClosure (localTests S))
      (coordinateRelation (S := S)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    obtain ⟨m, rfl⟩ := localTests_closure_coordinates hv
    obtain ⟨n, rfl⟩ := localTests_closure_coordinates hw
    exact (le_total (coordinateValue n) (coordinateValue m)).imp
      (coordinateRelation_encode_iff m n |>.mpr)
      (coordinateRelation_encode_iff n m |>.mpr)
  · intro v₀ w₀ v₁ w₁ hv₀ hw₀ hv₁ hw₁ h₀ h₁
    obtain ⟨m₀, n₀, rfl, rfl, h₀⟩ := h₀
    obtain ⟨m₁, n₁, hm₁, hn₁, h₁⟩ := h₁
    subst v₁
    subst w₁
    rw [natCoordinates_add m₀ m₁, natCoordinates_add n₀ n₁,
      coordinateRelation_encode_iff, coordinateValue_add, coordinateValue_add]
    exact add_le_add h₀ h₁
  · intro v₀ w₀ v₁ w₁ hv₀ hw₀ hv₁ hw₁ heq h₁
    obtain ⟨m₀, rfl⟩ := localTests_closure_coordinates hv₀
    obtain ⟨n₀, rfl⟩ := localTests_closure_coordinates hw₀
    obtain ⟨m₁, rfl⟩ := localTests_closure_coordinates hv₁
    obtain ⟨n₁, rfl⟩ := localTests_closure_coordinates hw₁
    have hmn : m₀ + m₁ = n₀ + n₁ := by
      apply natCoordinates_injective
      rw [← natCoordinates_add, ← natCoordinates_add]
      exact heq
    have hvalue :
        coordinateValue m₀ + coordinateValue m₁ =
          coordinateValue n₀ + coordinateValue n₁ := by
      rw [← coordinateValue_add, ← coordinateValue_add, hmn]
    have htail : coordinateValue n₁ ≤ coordinateValue m₁ :=
      (coordinateRelation_encode_iff m₁ n₁).mp h₁
    apply (coordinateRelation_encode_iff n₀ m₀).mpr
    apply (add_le_add_iff_right (coordinateValue m₁)).mp
    rw [hvalue]
    simpa [add_comm] using add_le_add_left htail (coordinateValue n₀)

/-- Every finite subset of a linearly ordered abelian group admits a local
real embedding. It reflects the ambient order and preserves every equation
`x + y = z` all three of whose terms belong to the finite set. -/
theorem finite_local_real_embedding (S : Set G) (hS : S.Finite) :
    ∃ f : S → ℝ,
      (∀ x y : S, x ≤ y ↔ f x ≤ f y) ∧
      (∀ x y z : S, (x : G) + y = z → f x + f y = f z) := by
  let : Fintype S := hS.fintype
  have hext :
      ∃ Rplus : (S → ℝ) → (S → ℝ) → Prop,
        ExtendsOn (localTests S) (additiveClosure (localTests S))
          (coordinateRelation (S := S)) Rplus ∧
        StrictlyMonotonic (additiveClosure (localTests S)) Rplus :=
    ⟨coordinateRelation, ⟨AddSubmonoid.subset_closure, fun _ _ _ _ ↦ Iff.rfl⟩,
      coordinateRelation_strictlyMonotonic⟩
  obtain ⟨φ, hφ⟩ :=
    (scott_theorem_1_4 (localTests_finite (S := S))
      (localTests_rational (S := S))).mpr hext
  refine ⟨fun x ↦ φ (localBasis x), ?_, ?_⟩
  · intro x y
    have hx : localBasis x ∈ localTests S := Or.inl ⟨x, rfl⟩
    have hy : localBasis y ∈ localTests S := Or.inl ⟨y, rfl⟩
    rw [← hφ (localBasis y) hy (localBasis x) hx]
    rw [localBasis_coordinates, localBasis_coordinates,
      coordinateRelation_encode_iff, coordinateValue_single,
      coordinateValue_single]
    rfl
  · intro x y z hxy
    have hp : localPair (x, y) ∈ localTests S := Or.inr ⟨(x, y), rfl⟩
    have hz : localBasis z ∈ localTests S := Or.inl ⟨z, rfl⟩
    have hpz : coordinateRelation (localPair (x, y)) (localBasis z) := by
      rw [localPair_coordinates, localBasis_coordinates,
        coordinateRelation_encode_iff, coordinateValue_add,
        coordinateValue_single, coordinateValue_single, coordinateValue_single,
        hxy]
    have hzp : coordinateRelation (localBasis z) (localPair (x, y)) := by
      rw [localPair_coordinates, localBasis_coordinates,
        coordinateRelation_encode_iff, coordinateValue_add,
        coordinateValue_single, coordinateValue_single, coordinateValue_single,
        hxy]
    have hle := (hφ (localPair (x, y)) hp (localBasis z) hz).mp hpz
    have hge := (hφ (localBasis z) hz (localPair (x, y)) hp).mp hzp
    simpa [localPair, map_add] using le_antisymm hge hle

end Local

section Lexicographic

/-- The ordered abelian group used to obstruct a global real representation. -/
abbrev LexIntPair := ℤ ×ₗ ℤ

/-- The two positive coordinate generators of the lexicographic example. -/
def lexGenerators : Set LexIntPair :=
  {toLex (1, 0), toLex (0, 1)}

/-- Comparison oriented as preference, with the first coordinate taking priority. -/
def lexPreference (x y : LexIntPair) : Prop :=
  (ofLex y).1 < (ofLex x).1 ∨
    (ofLex y).1 = (ofLex x).1 ∧ (ofLex y).2 ≤ (ofLex x).2

theorem lexPreference_strictlyMonotonic :
    StrictlyMonotonic (additiveClosure lexGenerators) lexPreference := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [lexPreference, ofLex]
    omega
  · intro x₀ y₀ x₁ y₁ _ _ _ _ h₀ h₁
    rcases x₀ with ⟨x₀₁, x₀₂⟩
    rcases y₀ with ⟨y₀₁, y₀₂⟩
    rcases x₁ with ⟨x₁₁, x₁₂⟩
    rcases y₁ with ⟨y₁₁, y₁₂⟩
    change y₀₁ < x₀₁ ∨ y₀₁ = x₀₁ ∧ y₀₂ ≤ x₀₂ at h₀
    change y₁₁ < x₁₁ ∨ y₁₁ = x₁₁ ∧ y₁₂ ≤ x₁₂ at h₁
    change y₀₁ + y₁₁ < x₀₁ + x₁₁ ∨
      y₀₁ + y₁₁ = x₀₁ + x₁₁ ∧ y₀₂ + y₁₂ ≤ x₀₂ + x₁₂
    omega
  · intro x₀ y₀ x₁ y₁ _ _ _ _ heq h₁
    rcases x₀ with ⟨x₀₁, x₀₂⟩
    rcases y₀ with ⟨y₀₁, y₀₂⟩
    rcases x₁ with ⟨x₁₁, x₁₂⟩
    rcases y₁ with ⟨y₁₁, y₁₂⟩
    change y₁₁ < x₁₁ ∨ y₁₁ = x₁₁ ∧ y₁₂ ≤ x₁₂ at h₁
    change x₀₁ < y₀₁ ∨ x₀₁ = y₀₁ ∧ x₀₂ ≤ y₀₂
    change (x₀₁ + x₁₁, x₀₂ + x₁₂) =
      (y₀₁ + y₁₁, y₀₂ + y₁₂) at heq
    have hfirst := congrArg Prod.fst heq
    have hsecond := congrArg Prod.snd heq
    simp only at hfirst hsecond
    omega

/-- No additive real-valued functional realizes lexicographic comparison on
the whole lexicographically ordered group `ℤ × ℤ`. The obstruction already
uses the positive additive closure of the two nonzero generators: `(0,1) > 0`,
while every natural multiple `(0,n)` remains below `(1,0)`. -/
theorem no_global_real_additive_lex_realization :
    ¬ ∃ f : LexIntPair →+ ℝ,
      ∀ x y, lexPreference x y ↔ f y ≤ f x := by
  rintro ⟨f, hf⟩
  let e₁ : LexIntPair := toLex (1, 0)
  let e₂ : LexIntPair := toLex (0, 1)
  have he₂pos : 0 < f e₂ := by
    have hstrict : lexPreference e₂ 0 ∧ ¬lexPreference 0 e₂ := by
      constructor
      · right
        norm_num [lexPreference, e₂]
      · intro h
        rcases h with h | h <;> norm_num [lexPreference, e₂] at h
    have hnonneg := (hf e₂ 0).mp hstrict.1
    have hne : f e₂ ≠ 0 := by
      intro hzero
      apply hstrict.2
      apply (hf 0 e₂).mpr
      simp [hzero]
    have hnonneg' : 0 ≤ f e₂ := by simpa using hnonneg
    exact lt_of_le_of_ne hnonneg' (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (f e₁ / f e₂)
  have hlex : lexPreference e₁ (n • e₂) := by
    left
    change (0 : ℤ) < 1
    norm_num
  have hbound := (hf e₁ (n • e₂)).mp hlex
  simp only [map_nsmul] at hbound
  have hlarge : f e₁ < n * f e₂ := by
    have := (mul_lt_mul_of_pos_right hn he₂pos)
    field_simp at this
    simpa [mul_comm] using this
  exact (not_lt_of_ge hbound) (by simpa [nsmul_eq_mul] using hlarge)

end Lexicographic

end Scott1964.MeasurementStructures.LinearInequalities
