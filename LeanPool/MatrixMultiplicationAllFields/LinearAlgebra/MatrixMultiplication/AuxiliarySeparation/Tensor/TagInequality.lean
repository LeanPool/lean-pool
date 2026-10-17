/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/TagInequality.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; `[IsAlgClosed K]` is assumed by the
declarations that use it.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Entropy.Tag
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.FiniteSeparation
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SharedPadding
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The shared-input tensor tag inequality

Exact type words in a power of a matched-sector tensor are obtained by explicit
coordinate pullbacks. Their character values depend only on the type counts.
The finite auxiliary separation inequality therefore supplies the integral
bounds required by the entropy limit.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation

variable {s : ℕ} {X Y Z : Type}
  [Fintype X] [Fintype Y] [Fintype Z]

/-- A word prescribes one branch tensor at each tensor-product position. -/
def branchWordTensor (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, B (w i) (x i) (y i) (z i)

/-- The canonical branch word tensor evaluates multiplicatively. -/
theorem Character.value_branchWordTensor (χ : Character K)
    (B : Fin s → Tensor K X Y Z) {n : ℕ} (w : Fin n → Fin s) :
    χ.value (branchWordTensor B w) = ∏ i, χ.value (B (w i)) := by
  induction n with
  | zero =>
      have hzero : branchWordTensor B w = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (unitTensor K) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, unitTensor]
      rw [hzero, χ.value_reindex, χ.map_one]
      simp
  | succ n ih =>
      have heq : branchWordTensor B w = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product (B (w 0)) (branchWordTensor B (Fin.tail w))) := by
        funext x y z
        simp [branchWordTensor, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, Fin.prod_univ_succ]
      rfl

/-- All words of an exact type have the same character value. -/
theorem Character.value_exact_branchWordTensor (χ : Character K)
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ) (w : ExactWords counts) :
    χ.value (branchWordTensor B w.val) = ∏ a, χ.value (B a) ^ counts a := by
  rw [χ.value_branchWordTensor,
    ← Fintype.prod_fiberwise' w.val (fun a => χ.value (B a))]
  simp only [Finset.prod_const, Finset.card_univ]
  apply Finset.prod_congr rfl
  intro a _
  rw [show Fintype.card {i // w.val i = a} = counts a from w.property a]

/-- A coordinate on a retained split leg remembers its type word. -/
def typeWordCoordinate (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts)
    {U : Type} (y : Fin (Fintype.card (ExactWords counts)) ×
      (Fin (∑ a, counts a) → U)) : Fin (∑ a, counts a) → (Fin s × U) :=
  fun i => ((e y.1).val i, y.2 i)

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting both split legs to one exact type produces a shared-first
tensor whose branches are precisely the prescribed branch products. -/
theorem exactType_power_pullback (B : Fin s → Tensor K X Y Z)
    (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    Tensor.pullback id (typeWordCoordinate counts e) (typeWordCoordinate counts e)
        (Tensor.power (sharedFirstTensor B) (∑ a, counts a)) =
      sharedFirstTensor (fun h => branchWordTensor B (e h).val) := by
  funext x y z
  by_cases h : y.1 = z.1
  · simp [Tensor.pullback, Tensor.power, typeWordCoordinate, sharedFirstTensor,
      branchWordTensor, h]
  · have hword : (e y.1).val ≠ (e z.1).val := by
      intro heq
      exact h (e.injective (Subtype.ext heq))
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hword
    simp only [Tensor.pullback, Tensor.power, sharedFirstTensor, h, ↓reduceIte,
      typeWordCoordinate, id_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- The exact-type restriction never exceeds the source power in character. -/
theorem Character.exactType_value_le_power (χ : Character K)
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ)
    (e : Fin (Fintype.card (ExactWords counts)) ≃ ExactWords counts) :
    χ.value (sharedFirstTensor (fun h => branchWordTensor B (e h).val)) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  rw [← exactType_power_pullback B counts e, ← χ.value_power]
  exact χ.value_pullback_le _ _ _ _

/-- The finite separation construction and exact-type restriction give the
integral inequality, with no assumed character comparison. -/
theorem Character.integral_type_comparison [IsAlgClosed K] (χ : Character K)
    (B : Fin s → Tensor K X Y Z) (counts : Fin s → ℕ) :
    (Fintype.card (ExactWords counts) : ℝ) ^ χ.pX *
        ∏ a, χ.value (B a) ^ counts a ≤
      5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) := by
  let M := Fintype.card (ExactWords counts)
  let e : Fin M ≃ ExactWords counts := (Fintype.equivFin _).symm
  let W : Fin M → Tensor K (Fin (∑ a, counts a) → X)
      (Fin (∑ a, counts a) → Y) (Fin (∑ a, counts a) → Z) :=
    fun h => branchWordTensor B (e h).val
  have hM : 0 < M := by
    simpa only [M, Fintype.card_eq_nat_card] using exactWords_card_pos counts
  have hsep : ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX ≤
      5 * (M : ℝ) * χ.value (sharedFirstTensor W) := by
    simpa only [W, χ.value_exact_branchWordTensor, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      χ.finiteSeparation_bound hM W
  have hsource : χ.value (sharedFirstTensor W) ≤
      χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
    χ.exactType_value_le_power B counts e
  have hcancel : (M : ℝ) *
      ((M : ℝ) ^ χ.pX * ∏ a, χ.value (B a) ^ counts a) ≤
        (M : ℝ) * (5 * χ.value (sharedFirstTensor B) ^ (∑ a, counts a)) := by
    calc
      _ = ((M : ℝ) * ∏ a, χ.value (B a) ^ counts a) * (M : ℝ) ^ χ.pX := by ring
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor W) := hsep
      _ ≤ 5 * (M : ℝ) * χ.value (sharedFirstTensor B) ^ (∑ a, counts a) :=
        mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = _ := by ring
  have hbound := (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hM : (0 : ℝ) < M)).mp hcancel
  simpa only [M, Fintype.card_eq_nat_card] using hbound

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- A nonzero branch remains visible in the tensor with a shared first leg. -/
theorem sharedFirstTensor_ne_zero_of_branch (B : Fin s → Tensor K X Y Z)
    (a : Fin s) (ha : B a ≠ 0) : sharedFirstTensor B ≠ 0 := by
  intro h
  apply ha
  funext x y z
  have hxyz := congrFun (congrFun (congrFun h x) (a, y)) (a, z)
  simpa only [sharedFirstTensor, ↓reduceIte, Pi.zero_apply] using hxyz

/-- The actual shared-input tensor tag inequality, including probability laws
with zero coordinates. The branch labels are disjoint on the second and third
legs, while the first coordinate is shared. -/
theorem Character.sharedFirst_tag [IsAlgClosed K] (χ : Character K)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstTensor B) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply χ.tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

/-- The logarithmic form of the actual tensor tag inequality. -/
theorem Character.log_sharedFirst_tag [IsAlgClosed K] (χ : Character K)
    (q : FiniteLaw (Fin s)) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstTensor B)) := by
  have hs : 0 < s := by
    by_contra hn
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos hn
    subst s
    have htotal := q.total
    simp at htotal
  have hT : sharedFirstTensor B ≠ 0 :=
    sharedFirstTensor_ne_zero_of_branch B ⟨0, hs⟩ (hB ⟨0, hs⟩)
  apply χ.log_tag_of_integral_type_comparison q (sharedFirstTensor B) B χ.pX hT hB
  intro counts _hcounts
  simpa only [Fintype.card_eq_nat_card] using χ.integral_type_comparison B counts

section Dependent

variable {U V : Fin s → Type} [∀ a, Fintype (U a)] [∀ a, Fintype (V a)]

/-- Branches may have different second- and third-leg dimensions. Padding
those spaces preserves their character values and the shared-input tensor. -/
theorem Character.sharedFirstDependent_tag [IsAlgClosed K] (χ : Character K)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor K X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    Real.exp (χ.pX * finiteEntropy q.mass) *
        ∏ a, χ.value (B a) ^ q.mass a ≤ χ.value (sharedFirstDependentTensor B) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

/-- The logarithmic tag inequality for branches with varying dimensions. -/
theorem Character.log_sharedFirstDependent_tag [IsAlgClosed K] (χ : Character K)
    (q : FiniteLaw (Fin s)) (B : ∀ a, Tensor K X (U a) (V a))
    (hB : ∀ a, B a ≠ 0) :
    χ.pX * finiteEntropy q.mass + ∑ a, q.mass a * Real.log (χ.value (B a)) ≤
      Real.log (χ.value (sharedFirstDependentTensor B)) := by
  simpa only [χ.value_paddedSharedBranch, χ.value_sharedFirstTensor_padded] using
    χ.log_sharedFirst_tag q (paddedSharedBranch B)
      (fun a => paddedSharedBranch_ne_zero B a (hB a))

end Dependent

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
