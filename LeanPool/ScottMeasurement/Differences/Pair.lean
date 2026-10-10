/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.FinHead
public import LeanPool.ScottMeasurement.LinearInequalities.ScottTheorems

/-!
# Additive utility for pairs

This is Scott 1964, Theorem 3.1.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

open scoped BigOperators

open Classical in
/-- The incidence vector of a pair, with one coordinate in each summand. -/
noncomputable def pairVector {A : Type u} {A' : Type v} (x : A) (x' : A') :
    Sum A A' → ℝ :=
  Pi.single (Sum.inl x) 1 + Pi.single (Sum.inr x') 1

theorem pairVector_injective {A : Type u} {A' : Type v} :
    Function.Injective (Function.uncurry (@pairVector A A')) := by
  classical
  rintro ⟨x, x'⟩ ⟨y, y'⟩ h
  have hx : x = y := by
    simpa [pairVector, Pi.single_apply] using congrFun h (Sum.inl x)
  have hx' : x' = y' := by
    simpa [pairVector, Pi.single_apply] using congrFun h (Sum.inr x')
  exact Prod.ext hx hx'

/-- Equality of sums of incidence vectors gives the two independent
permutations of coordinates used in condition `(2_V)`. -/
theorem pairVector_sum_eq_permutations {A : Type u} {A' : Type v}
    {ι : Type*} [Fintype ι] (x y : ι → A) (x' y' : ι → A')
    (h : ∑ i, pairVector (x i) (x' i) =
      ∑ i, pairVector (y i) (y' i)) :
    ∃ π σ : Equiv.Perm ι,
      (∀ i, y i = x (π i)) ∧ (∀ i, y' i = x' (σ i)) := by
  classical
  have hleft (a : A) :
      Fintype.card {i // y i = a} = Fintype.card {i // x i = a} := by
    have ha := congrFun h (Sum.inl a)
    simp only [Fintype.sum_apply, pairVector, Pi.add_apply, Pi.single_apply,
      Sum.inl.injEq, Sum.inl_ne_inr, ↓reduceIte, add_zero] at ha
    have hy :
        Fintype.card {i // y i = a} =
          (Finset.univ.filter fun i ↦ y i = a).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun i ↦ by simp)
    have hx :
        Fintype.card {i // x i = a} =
          (Finset.univ.filter fun i ↦ x i = a).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun i ↦ by simp)
    rw [hy, hx]
    rw [Finset.card_filter, Finset.card_filter]
    exact_mod_cast (by simpa [eq_comm] using ha.symm)
  have hright (a : A') :
      Fintype.card {i // y' i = a} = Fintype.card {i // x' i = a} := by
    have ha := congrFun h (Sum.inr a)
    simp only [Fintype.sum_apply, pairVector, Pi.add_apply, Pi.single_apply,
      Sum.inr.injEq, Sum.inr_ne_inl, ↓reduceIte, zero_add] at ha
    have hy :
        Fintype.card {i // y' i = a} =
          (Finset.univ.filter fun i ↦ y' i = a).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun i ↦ by simp)
    have hx :
        Fintype.card {i // x' i = a} =
          (Finset.univ.filter fun i ↦ x' i = a).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr
        (Equiv.subtypeEquivRight fun i ↦ by simp)
    rw [hy, hx]
    rw [Finset.card_filter, Finset.card_filter]
    exact_mod_cast (by simpa [eq_comm] using ha.symm)
  let π : Equiv.Perm ι :=
    Equiv.ofFiberEquiv fun a ↦ Fintype.equivOfCardEq (hleft a)
  let σ : Equiv.Perm ι :=
    Equiv.ofFiberEquiv fun a ↦ Fintype.equivOfCardEq (hright a)
  refine ⟨π, σ, ?_, ?_⟩
  · intro i
    change y i = x ((Equiv.ofFiberEquiv
      (fun a ↦ Fintype.equivOfCardEq (hleft a))) i)
    exact ((Fintype.equivOfCardEq (hleft (y i)))
      ((Equiv.sigmaFiberEquiv y).symm i).2).2.symm
  · intro i
    change y' i = x' ((Equiv.ofFiberEquiv
      (fun a ↦ Fintype.equivOfCardEq (hright a))) i)
    exact ((Fintype.equivOfCardEq (hright (y' i)))
      ((Equiv.sigmaFiberEquiv y').symm i).2).2.symm

/-- A relation on pairs is represented by the sum of two utility functions. -/
def RealizableUtilityPair {A : Type u} {A' : Type v}
    (V : A → A' → A → A' → Prop) : Prop :=
  ∃ f : A → ℝ, ∃ f' : A' → ℝ,
    ∀ x x' y y', V x x' y y' ↔ f x + f' x' ≥ f y + f' y'

/-- Scott 1964, condition `(1_V)`. -/
def PairTotal {A : Type u} {A' : Type v}
    (V : A → A' → A → A' → Prop) : Prop :=
  ∀ x x' y y', V x x' y y' ∨ V y y' x x'

/-- Scott 1964, condition `(2_V)`, indexed at length `n + 1` so that the
distinguished index `0` always exists. -/
def PairPermutation {A : Type u} {A' : Type v}
    (V : A → A' → A → A' → Prop) : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → A) (x' : Fin (n + 1) → A')
    (π σ : Equiv.Perm (Fin (n + 1))),
    (∀ i, i ≠ finHead n → V (x i) (x' i) (x (π i)) (x' (σ i))) →
      V (x (π (finHead n))) (x' (σ (finHead n))) (x (finHead n)) (x' (finHead n))

/-- Scott's observation following `(2_V)`: the permutation condition already
implies transitivity. -/
theorem PairPermutation.transitive {A : Type u} {A' : Type v}
    {V : A → A' → A → A' → Prop} (hV : PairPermutation V) :
    ∀ p q r : A × A',
      V p.1 p.2 q.1 q.2 → V q.1 q.2 r.1 r.2 → V p.1 p.2 r.1 r.2 := by
  rintro ⟨x, x'⟩ ⟨y, y'⟩ ⟨z, z'⟩ hxy hyz
  let p : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective ![1, 2, 0] (by decide +kernel)
  apply hV 2 ![z, x, y] ![z', x', y'] p p
  intro i hi
  have hi0 : i ≠ 0 := by simpa [finHead_eq_zero] using hi
  fin_cases i
  · contradiction
  · simpa [p] using hxy
  · simpa [p] using hyz

theorem RealizableUtilityPair.total {A : Type u} {A' : Type v}
    {V : A → A' → A → A' → Prop} (hV : RealizableUtilityPair V) :
    PairTotal V := by
  rcases hV with ⟨f, f', hrep⟩
  intro x x' y y'
  rcases le_total (f y + f' y') (f x + f' x') with h | h
  · exact Or.inl ((hrep x x' y y').2 h)
  · exact Or.inr ((hrep y y' x x').2 h)

theorem RealizableUtilityPair.permutation {A : Type u} {A' : Type v}
    {V : A → A' → A → A' → Prop} (hV : RealizableUtilityPair V) :
    PairPermutation V := by
  rcases hV with ⟨f, f', hrep⟩
  intro n x x' π σ h
  let s : Fin (n + 1) → ℝ := fun i ↦ f (x i) + f' (x' i)
  let t : Fin (n + 1) → ℝ := fun i ↦ f (x (π i)) + f' (x' (σ i))
  have hπ : ∑ i, f (x (π i)) = ∑ i, f (x i) :=
    Fintype.sum_equiv π _ _ (fun _ ↦ rfl)
  have hσ : ∑ i, f' (x' (σ i)) = ∑ i, f' (x' i) :=
    Fintype.sum_equiv σ _ _ (fun _ ↦ rfl)
  have hsum : ∑ i, s i = ∑ i, t i := by
    simp only [s, t, Finset.sum_add_distrib]
    rw [hπ, hσ]
  have hrest :
      ∑ i ∈ (Finset.univ.erase (finHead n)), t i ≤
        ∑ i ∈ (Finset.univ.erase (finHead n)), s i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi0 : i ≠ finHead n := by
      simpa using (Finset.mem_erase.mp hi).1
    exact (hrep _ _ _ _).1 (h i hi0)
  apply (hrep _ _ _ _).2
  have hzero : finHead n ∈ Finset.univ := Finset.mem_univ _
  have hs := Finset.sum_erase_add _ s hzero
  have ht := Finset.sum_erase_add _ t hzero
  dsimp only [s, t] at *
  linarith

theorem RealizableUtilityPair.necessary {A : Type u} {A' : Type v}
    {V : A → A' → A → A' → Prop} (hV : RealizableUtilityPair V) :
    PairTotal V ∧ PairPermutation V :=
  ⟨hV.total, hV.permutation⟩

/-- **Scott 1964, Theorem 3.1 (additive utility for pairs).**
The result also holds when either coordinate type is empty. -/
theorem theorem_3_1 {A : Type u} {A' : Type v}
    [Finite A] [Finite A']
    (V : A → A' → A → A' → Prop) :
    RealizableUtilityPair V ↔ PairTotal V ∧ PairPermutation V := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite A'
  constructor
  · exact RealizableUtilityPair.necessary
  · rintro ⟨htotal, hperm⟩
    classical
    let Y : Set (Sum A A' → ℝ) :=
      Set.range (Function.uncurry (@pairVector A A'))
    let R : (Sum A A' → ℝ) → (Sum A A' → ℝ) → Prop :=
      fun z w ↦ ∀ x x' y y',
        z = pairVector x x' → w = pairVector y y' → V x x' y y'
    have hR_pair (x : A) (x' : A') (y : A) (y' : A') :
        R (pairVector x x') (pairVector y y') ↔ V x x' y y' := by
      constructor
      · intro h
        exact h x x' y y' rfl rfl
      · intro h a a' b b' ha hb
        have hxa : (x, x') = (a, a') :=
          pairVector_injective ha
        have hyb : (y, y') = (b, b') :=
          pairVector_injective hb
        have hxa₁ : x = a := congrArg Prod.fst hxa
        have hxa₂ : x' = a' := congrArg Prod.snd hxa
        have hyb₁ : y = b := congrArg Prod.fst hyb
        have hyb₂ : y' = b' := congrArg Prod.snd hyb
        simpa [← hxa₁, ← hxa₂, ← hyb₁, ← hyb₂] using h
    have hYfinite : Y.Finite := Set.finite_range _
    have hYrat : LinearInequalities.IsRationalSet Y := by
      rintro z ⟨⟨x, x'⟩, rfl⟩ s
      rcases s with a | a'
      · by_cases ha : a = x
        · exact ⟨1, by simp [pairVector, ha]⟩
        · exact ⟨0, by simp [pairVector, ha]⟩
      · by_cases ha : a' = x'
        · exact ⟨1, by simp [pairVector, ha]⟩
        · exact ⟨0, by simp [pairVector, ha]⟩
    have hcomplete : LinearInequalities.RelationComplete Y R := by
      rintro z ⟨⟨x, x'⟩, rfl⟩ w ⟨⟨y, y'⟩, rfl⟩
      change R (pairVector x x') (pairVector y y') ∨
        R (pairVector y y') (pairVector x x')
      rw [hR_pair, hR_pair]
      exact htotal x x' y y'
    have hcancel : LinearInequalities.RelationSequenceCancellation Y R := by
      intro n z w hz hw hR hsum
      choose p hp using hz
      choose q hq using hw
      let x : Fin (n + 1) → A := fun i ↦ (p i).1
      let x' : Fin (n + 1) → A' := fun i ↦ (p i).2
      let y : Fin (n + 1) → A := fun i ↦ (q i).1
      let y' : Fin (n + 1) → A' := fun i ↦ (q i).2
      have hx (i) : z i = pairVector (x i) (x' i) := by
        have hi := hp i
        change pairVector (p i).1 (p i).2 = z i at hi
        simpa [x, x'] using hi.symm
      have hy (i) : w i = pairVector (y i) (y' i) := by
        have hi := hq i
        change pairVector (q i).1 (q i).2 = w i at hi
        simpa [y, y'] using hi.symm
      have hsum' :
          ∑ i, pairVector (x i) (x' i) =
            ∑ i, pairVector (y i) (y' i) := by
        simpa only [hx, hy] using hsum
      obtain ⟨π, σ, hπ, hσ⟩ :=
        pairVector_sum_eq_permutations x y x' y' hsum'
      intro i
      let τ : Equiv.Perm (Fin (n + 1)) := Equiv.swap (finHead n) i
      let π' : Equiv.Perm (Fin (n + 1)) := τ.trans (π.trans τ)
      let σ' : Equiv.Perm (Fin (n + 1)) := τ.trans (σ.trans τ)
      have hconcl := hperm n (fun j ↦ x (τ j)) (fun j ↦ x' (τ j)) π' σ' (by
        intro j hj
        have hτj : τ j ≠ i := by
          intro heq
          have : j = finHead n := τ.injective (by simpa [τ] using heq)
          exact hj this
        have hvR := hR (τ j)
        rw [hx (τ j), hy (τ j), hR_pair] at hvR
        have hv := hvR
        simpa [π', σ', τ, hπ (τ j), hσ (τ j)] using hv)
      rw [hy i, hx i, hR_pair]
      simpa [π', σ', τ, hπ i, hσ i] using hconcl
    obtain ⟨φ, hφ⟩ :=
      (LinearInequalities.scott_theorem_1_3 hYfinite hYrat).2
        ⟨hcomplete, hcancel⟩
    refine ⟨fun x ↦ φ (Pi.single (Sum.inl x) 1),
      fun x' ↦ φ (Pi.single (Sum.inr x') 1), ?_⟩
    intro x x' y y'
    have hxy := hφ (pairVector x x') ⟨(x, x'), rfl⟩
      (pairVector y y') ⟨(y, y'), rfl⟩
    rw [hR_pair] at hxy
    simpa only [pairVector, map_add] using hxy

end Scott1964.MeasurementStructures
