/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.NormalizedStates
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convex.Farkas
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Catalyst
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Spectrum.Coordinates
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!+# Finite obstructions to normalized additive states

The state equations are homogeneous integer inequalities, except for the
normalization at the unit. Their finite certificates are interpreted in the
additive group completion, preserving catalysts in the original semiring.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open Set

variable {S : Type*} [CommSemiring S] [Preorder S]

/-- The homogeneous inequalities defining a normalized additive state. Both
signs of the additive relation are included. -/
inductive StateConstraint (S : Type*) [Preorder S] where
  | lower (x : S)
  | upper (x : S)
  | addPos (x y : S)
  | addNeg (x y : S)
  | order (x y : S) (h : x ≤ y)
  | detector (x : S)

/-- Integer coefficient vector of a homogeneous state constraint. -/
def stateConstraintVector (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) : S →₀ ℤ := by
  classical
  exact match c with
  | .lower x => Finsupp.single x 1
  | .upper x => Finsupp.single (1 : S) (R x : ℤ) - Finsupp.single x 1
  | .addPos x y => Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1
  | .addNeg x y => -(Finsupp.single (x + y) 1 - Finsupp.single x 1 - Finsupp.single y 1)
  | .order x y _ => Finsupp.single y 1 - Finsupp.single x 1
  | .detector x => Finsupp.single (d * x) 1 - Finsupp.single x (k : ℤ)

/-- Evaluation of a finite integer coefficient vector on a real-valued function. -/
def statePairing (f : S → ℝ) : (S →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ f

omit [CommSemiring S] [Preorder S] in
theorem statePairing_apply (f : S → ℝ) (v : S →₀ ℤ) :
    statePairing f v = ∑ x ∈ v.support, (v x : ℝ) * f x := by
  simp [statePairing, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
@[simp] theorem statePairing_single (f : S → ℝ) (x : S) (n : ℤ) :
    statePairing f (Finsupp.single x n) = (n : ℝ) * f x := by
  simp [statePairing, zsmul_eq_mul]

omit [CommSemiring S] [Preorder S] in
theorem continuous_statePairing (v : S →₀ ℤ) :
    Continuous (fun f : S → ℝ ↦ statePairing f v) := by
  simp only [statePairing_apply]
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul (continuous_apply x)

theorem normalizedStates_iff_stateConstraint (R : S → ℕ) (d : S) (k : ℕ)
    (f : S → ℝ) :
    f ∈ normalizedStates (fun x ↦ (R x : ℝ)) d k ↔
      f 1 = 1 ∧ ∀ c : StateConstraint S, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  constructor
  · intro hf
    refine ⟨hf.2.1, ?_⟩
    intro c
    cases c with
    | lower x => simpa [stateConstraintVector] using (hf.1 x).1
    | upper x =>
      simp only [stateConstraintVector, map_sub, statePairing_single, Int.cast_natCast,
        Int.cast_one, one_mul, hf.2.1, mul_one, sub_nonneg]
      exact (hf.1 x).2
    | addPos x y => simp [stateConstraintVector, hf.2.2.1]
    | addNeg x y => simp [stateConstraintVector, hf.2.2.1]
    | order x y h => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.1 x y h
    | detector x => simpa [stateConstraintVector, sub_nonneg] using hf.2.2.2.2 x
  · rintro ⟨hn, hc⟩
    refine ⟨?_, hn, ?_, ?_, ?_⟩
    · intro x
      constructor
      · simpa [stateConstraintVector] using hc (.lower x)
      · simpa [stateConstraintVector, hn, sub_nonneg] using hc (.upper x)
    · intro x y
      have hp := hc (.addPos x y)
      have hm := hc (.addNeg x y)
      simp [stateConstraintVector] at hp hm
      linarith
    · intro x y hxy
      simpa [stateConstraintVector, sub_nonneg] using hc (.order x y hxy)
    · intro x
      simpa [stateConstraintVector, sub_nonneg] using hc (.detector x)

/-- The ordinary monotonicity difference in a state constraint. -/
def stateConstraintLower (c : StateConstraint S) : S :=
  match c with
  | .lower _ => 0
  | .upper x => x
  | .order x _ _ => x
  | _ => 0

/-- The semiring element providing the upper endpoint of a state constraint. -/
def stateConstraintUpper (R : S → ℕ) (c : StateConstraint S) : S :=
  match c with
  | .lower x => x
  | .upper x => R x
  | .order _ y _ => y
  | _ => 0

/-- The multiplier of the distinguished detector difference. -/
def stateConstraintDetector (c : StateConstraint S) : S :=
  match c with
  | .detector x => x
  | _ => 0

theorem stateConstraintLower_le_upper (R : S → ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (c : StateConstraint S) :
    stateConstraintLower c ≤ stateConstraintUpper R c := by
  cases c with
  | lower x => exact hzero x
  | upper x => exact hbound x
  | order _ _ h => exact h
  | addPos _ _ => exact le_rfl
  | addNeg _ _ => exact le_rfl
  | detector _ => exact le_rfl

/-- Interpreting a constraint in the group completion separates its ordinary
order difference from its detector difference. -/
theorem stateConstraintVector_completion (R : S → ℕ) (d : S) (k : ℕ)
    (c : StateConstraint S) :
    Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))
        (stateConstraintVector R d k c) =
      Algebra.GrothendieckAddGroup.of (stateConstraintUpper R c) -
        Algebra.GrothendieckAddGroup.of (stateConstraintLower c) +
      Algebra.GrothendieckAddGroup.of (d * stateConstraintDetector c) -
        k • Algebra.GrothendieckAddGroup.of (stateConstraintDetector c) := by
  classical
  have hcast (n : ℕ) : Algebra.GrothendieckAddGroup.of (n : S) =
      n • Algebra.GrothendieckAddGroup.of (1 : S) := by
    rw [← nsmul_one, map_nsmul]
  cases c <;>
    simp [stateConstraintVector, stateConstraintLower, stateConstraintUpper,
      stateConstraintDetector, hcast, Nat.cast_smul_eq_nsmul, map_add] <;> abel

/-- In the absence of a catalytic obstruction, no positive multiple of the
negative unit is a natural combination of state-constraint vectors. -/
theorem no_stateConstraint_certificate (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Fintype I] (cs : I → StateConstraint S) :
    ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∑ i, n i • stateConstraintVector R d k (cs i) =
        -(m : ℤ) • Finsupp.single (1 : S) (1 : ℤ) := by
  classical
  rintro ⟨m, hm, n, hn⟩
  have heq := congrArg
    (Finsupp.linearCombination ℤ (Algebra.GrothendieckAddGroup.of (M := S))) hn
  simp only [map_sum, map_nsmul, map_smul, Finsupp.linearCombination_single,
    one_smul, stateConstraintVector_completion] at heq
  obtain ⟨D, hD⟩ := exists_catalyst_of_completion_sum_eq hadd m k d n
    (fun i ↦ stateConstraintLower (cs i)) (fun i ↦ stateConstraintUpper R (cs i))
    (fun i ↦ stateConstraintDetector (cs i))
    (fun i ↦ stateConstraintLower_le_upper R hzero hbound (cs i)) heq.symm
  exact hno D _ m hm hD

/-- Every finite family of constraints supported on `H` has a normalized
solution that vanishes outside `H`, provided no positive catalyst exists. -/
theorem finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    {I : Type*} [Finite I] (cs : I → StateConstraint S) (H : Finset S) (hOne : (1 : S) ∈ H)
    (hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H) :
    ∃ f : S → ℝ, f 1 = 1 ∧
      (∀ i, 0 ≤ statePairing f (stateConstraintVector R d k (cs i))) ∧
      ∀ x ∉ H, f x = 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let A : I → H → ℤ := fun i j ↦ stateConstraintVector R d k (cs i) j
  let u : H → ℤ := fun j ↦ (Finsupp.single (1 : S) (1 : ℤ)) j
  have hcert : ¬∃ m : ℕ, 0 < m ∧ ∃ n : I → ℕ,
      ∀ j, ∑ i, (n i : ℤ) * A i j = -(m : ℤ) * u j := by
    rintro ⟨m, hm, n, hn⟩
    apply no_stateConstraint_certificate R d k hzero hbound hadd hno cs
    refine ⟨m, hm, n, ?_⟩
    ext x
    by_cases hx : x ∈ H
    · have heq := hn ⟨x, hx⟩
      by_cases hx1 : (1 : S) = x <;>
        simpa [A, u, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, nsmul_eq_mul, zsmul_eq_mul, Finsupp.single_apply, hx1] using heq
    · have hz : ∀ i, stateConstraintVector R d k (cs i) x = 0 := by
        intro i
        apply Finsupp.notMem_support_iff.mp
        exact fun h ↦ hx (hH i h)
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        hz, smul_zero, Finset.sum_const_zero]
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hx hOne
      simp [hx1]
  obtain ⟨L, hLu, hLA⟩ :=
    exists_normalized_nonneg_linear_of_no_nat_certificate A u hcert
  let f := finiteCoordinateState H L
  refine ⟨f, ?_, ?_, ?_⟩
  · have heq := linearCombination_finiteCoordinateState H L
      (Finsupp.single (1 : S) (1 : ℤ))
    simpa [f, u] using heq.trans hLu
  · intro i
    simpa only [statePairing, f, linearCombination_finiteCoordinateState, A] using hLA i
  · intro x hx
    exact finiteCoordinateState_eq_zero_of_not_mem H L hx

/-- A finite collection of state constraints can be solved while keeping all
coordinates in their rank intervals. -/
theorem bounded_finite_stateConstraint_solution (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s)
    (F : Finset (StateConstraint S)) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ R x) ∧ f 1 = 1 ∧
      ∀ c ∈ F, 0 ≤ statePairing f (stateConstraintVector R d k c) := by
  classical
  let H : Finset S := insert 1 (F.biUnion fun c ↦ (stateConstraintVector R d k c).support)
  have hOne : (1 : S) ∈ H := Finset.mem_insert_self _ _
  let cs : F ⊕ (Bool × H) → StateConstraint S
    | .inl c => c
    | .inr (false, x) => .lower x
    | .inr (true, x) => .upper x
  have hH : ∀ i, (stateConstraintVector R d k (cs i)).support ⊆ H := by
    intro i a ha
    cases i with
    | inl c =>
      exact Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨c, c.property, ha⟩)
    | inr i =>
      rcases i with ⟨tag, x⟩
      by_contra hnot
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hnot hOne
      have hax : a ≠ (x : S) := by
        rintro rfl
        exact hnot x.property
      have ha0 := Finsupp.mem_support_iff.mp ha
      cases tag <;>
        simp [cs, stateConstraintVector, ha1, hax] at ha0
  obtain ⟨f, hf1, hfc, hfzero⟩ :=
    finite_stateConstraint_solution R d k hzero hbound hadd hno cs H hOne hH
  refine ⟨f, ?_, hf1, ?_⟩
  · intro x
    by_cases hx : x ∈ H
    · have hlo := hfc (.inr (false, ⟨x, hx⟩))
      have hhi := hfc (.inr (true, ⟨x, hx⟩))
      constructor
      · simpa [cs, stateConstraintVector] using hlo
      · simpa [cs, stateConstraintVector, hf1, sub_nonneg] using hhi
    · rw [hfzero x hx]
      exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro c hc
    exact hfc (.inl ⟨c, hc⟩)

/-- Absence of positive scalar-gain catalysts guarantees the existence of a
normalized additive monotone state satisfying the detector inequality. -/
theorem normalizedStates_nonempty_of_no_catalyst (R : S → ℕ) (d : S) (k : ℕ)
    (hzero : ∀ x : S, 0 ≤ x) (hbound : ∀ x : S, x ≤ (R x : S))
    (hadd : ∀ a b c e : S, a ≤ b → c ≤ e → a + c ≤ b + e)
    (hno : ∀ (D s : S) (m : ℕ), 0 < m →
      ¬D + (m : S) + d * s ≤ D + (k : S) * s) :
    (normalizedStates (fun x ↦ (R x : ℝ)) d k).Nonempty := by
  let B : Set (S → ℝ) := {f | ∀ x, 0 ≤ f x ∧ f x ≤ R x}
  let K : Set (S → ℝ) := B ∩ {f | f 1 = 1}
  let t : StateConstraint S → Set (S → ℝ) :=
    fun c ↦ {f | 0 ≤ statePairing f (stateConstraintVector R d k c)}
  have hBcompact : IsCompact B :=
    isCompact_pi_infinite (fun x ↦ isCompact_Icc (a := (0 : ℝ)) (b := (R x : ℝ)))
  have hKcompact : IsCompact K :=
    hBcompact.inter_right (isClosed_eq (continuous_apply 1) continuous_const)
  have htclosed : ∀ c, IsClosed (t c) := fun c ↦
    isClosed_le continuous_const (continuous_statePairing (stateConstraintVector R d k c))
  have hfinite : ∀ F : Finset (StateConstraint S), (K ∩ ⋂ c ∈ F, t c).Nonempty := by
    intro F
    obtain ⟨f, hfb, hf1, hfc⟩ :=
      bounded_finite_stateConstraint_solution R d k hzero hbound hadd hno F
    refine ⟨f, ⟨hfb, hf1⟩, ?_⟩
    simp only [Set.mem_iInter]
    exact hfc
  obtain ⟨f, hfK, hft⟩ := hKcompact.inter_iInter_nonempty t htclosed hfinite
  refine ⟨f, (normalizedStates_iff_stateConstraint R d k f).mpr ?_⟩
  exact ⟨hfK.2, fun c ↦ Set.mem_iInter.mp hft c⟩

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
