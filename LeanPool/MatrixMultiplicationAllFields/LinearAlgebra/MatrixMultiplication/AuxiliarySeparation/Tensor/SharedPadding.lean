/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/SharedPadding.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Padding shared-input tensors with different branch dimensions

The finite separation construction uses fixed ambient coordinate spaces on
each leg. A family with a common first leg and varying second and third legs
embeds into that setting without changing any character values. The extra
coordinates introduced by padding have zero coefficients.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X : Type} {Y Z : Fin M → Type}
variable [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

open Classical in
/-- Branches sharing their first input but with independently sized other legs. -/
def sharedFirstDependentTensor (B : ∀ i, Tensor K X (Y i) (Z i)) :
    Tensor K X (Σ i, Y i) (Σ i, Z i) :=
  fun x y z => if h : z.1 = y.1 then B y.1 x y.2 (h ▸ z.2) else 0

open Classical in
/-- A branch in the two common sigma coordinate spaces, with zero padding. -/
def paddedSharedBranch (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M) :
    Tensor K X (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict (fun x' x => if x = x' then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (B i)

omit [Fintype X] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)] in
@[simp] theorem sharedFirstDependentTensor_matching
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    sharedFirstDependentTensor B x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  classical
  simp [sharedFirstDependentTensor]

@[simp] theorem paddedSharedBranch_matching
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Y i) (z : Z i) :
    paddedSharedBranch B i x ⟨i, y⟩ ⟨i, z⟩ = B i x y z := by
  classical
  simp [paddedSharedBranch, Tensor.restrict, ite_mul, mul_ite]

theorem paddedSharedBranch_pullback
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M) :
    Tensor.pullback id (Sigma.mk i) (Sigma.mk i) (paddedSharedBranch B i) = B i := by
  classical
  funext x y z
  exact paddedSharedBranch_matching B i x y z

/-- A nonzero branch remains nonzero after padding. -/
theorem paddedSharedBranch_ne_zero
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M) (hB : B i ≠ 0) :
    paddedSharedBranch B i ≠ 0 := by
  classical
  intro h
  apply hB
  rw [← paddedSharedBranch_pullback B i, h]
  rfl

theorem paddedSharedBranch_zero_middle
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  classical
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

theorem paddedSharedBranch_zero_right
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M)
    (x : X) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedSharedBranch B i x y z = 0 := by
  classical
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedSharedBranch, Tensor.restrict, hzero]

open Classical in
/-- Redundant branch labels zero-extend the varying-dimension shared tensor. -/
theorem sharedFirstTensor_paddedSharedBranch
    (B : ∀ i, Tensor K X (Y i) (Z i)) :
    sharedFirstTensor (paddedSharedBranch B) = Tensor.restrict
      (fun (x' : X) x => if x = x' then 1 else 0)
      (fun (y' : Fin M × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : Fin M × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (sharedFirstDependentTensor B) := by
  classical
  funext x' y' z'
  rcases y' with ⟨i, ⟨iy, y⟩⟩
  rcases z' with ⟨j, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → Fin M) (a x : A) (i : Fin M) :
      (f a, a) = (i, x) ↔ a = x ∧ f x = i := by
    constructor
    · intro h
      have ha : a = x := congrArg Prod.snd h
      refine ⟨ha, ?_⟩
      rw [← ha]
      exact congrArg Prod.fst h
    · rintro ⟨rfl, h⟩
      simp [h]
  simp only [Tensor.restrict, hgraph, ite_and]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : iy = i
  · subst iy
    by_cases hz : iz = i
    · subst iz
      by_cases hij : i = j
      · subst j
        simp [sharedFirstTensor, sharedFirstDependentTensor]
      · simp [sharedFirstTensor, hij]
    · simp [sharedFirstTensor, sharedFirstDependentTensor,
        paddedSharedBranch_zero_right B i x' ⟨i, y⟩ ⟨iz, z⟩ hz, hz]
  · simp [sharedFirstTensor,
      paddedSharedBranch_zero_middle B i x' ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]

namespace Character

/-- Padding a branch changes no character value. -/
@[simp] theorem value_paddedSharedBranch (χ : Character K)
    (B : ∀ i, Tensor K X (Y i) (Z i)) (i : Fin M) :
    χ.value (paddedSharedBranch B i) = χ.value (B i) := by
  classical
  simpa only [paddedSharedBranch, id_eq] using
    χ.value_extendByZero (B i) id (Sigma.mk i) (Sigma.mk i)
      Function.injective_id
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
      (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

/-- Passing to uniform ambient branch spaces adds no character cost. -/
@[simp] theorem value_sharedFirstTensor_padded (χ : Character K)
    (B : ∀ i, Tensor K X (Y i) (Z i)) :
    χ.value (sharedFirstTensor (paddedSharedBranch B)) =
      χ.value (sharedFirstDependentTensor B) := by
  classical
  rw [sharedFirstTensor_paddedSharedBranch]
  simpa only [id_eq] using
    χ.value_extendByZero (sharedFirstDependentTensor B) id
      (fun y => (y.1, y)) (fun z => (z.1, z)) Function.injective_id
      (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
