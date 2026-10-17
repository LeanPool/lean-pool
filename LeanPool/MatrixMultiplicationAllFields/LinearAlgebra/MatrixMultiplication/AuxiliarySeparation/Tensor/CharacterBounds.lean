/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/CharacterBounds.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexSeparatedTensorDecomposition
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Character values on powers and varying-dimension direct sums

These are consequences of the normalized restriction-monotone character
interface. Coordinate changes preserve values; permuting the three tensor
legs need not preserve an individual character.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character K)

section Embeddings

variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [DecidableEq X'] [DecidableEq Y'] [DecidableEq Z']

/-- Extending finite coordinates by zero does not change a character value. -/
theorem value_extendByZero (T : Tensor K X Y Z)
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz) :
    χ.value (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = χ.value T := by
  classical
  apply le_antisymm (χ.monotone T _ _ _)
  have h := χ.value_pullback_le (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) fx fy fz
  have heq : Tensor.pullback fx fy fz (Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0) T) = T := by
    funext x y z
    simp [Tensor.pullback, Tensor.restrict, hx.eq_iff, hy.eq_iff, hz.eq_iff,
      ite_mul, mul_ite]
  simpa only [heq] using h

end Embeddings

section Powers

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Tensor powers turn a character value into an ordinary natural power. -/
@[simp] theorem value_power (T : Tensor K X Y Z) (n : ℕ) :
    χ.value (Tensor.power T n) = χ.value T ^ n := by
  induction n with
  | zero =>
      have heq : Tensor.power T 0 = Tensor.pullback
          (Equiv.equivPUnit (Fin 0 → X))
          (Equiv.equivPUnit (Fin 0 → Y))
          (Equiv.equivPUnit (Fin 0 → Z)) (unitTensor K) := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, unitTensor]
      rw [heq, χ.value_reindex, χ.map_one, pow_zero]
  | succ n ih =>
      have heq : Tensor.power T (n + 1) = Tensor.pullback
          (Fin.consEquiv (fun _ : Fin (n + 1) => X)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Y)).symm
          (Fin.consEquiv (fun _ : Fin (n + 1) => Z)).symm
          (Tensor.product T (Tensor.power T n)) := by
        funext x y z
        simp [Tensor.power, Tensor.pullback, Tensor.product, Fin.consEquiv,
          Fin.prod_univ_succ, Fin.tail]
      rw [heq, χ.value_reindex, χ.map_product, ih, pow_succ, mul_comm]

/-- Full independent copies contribute their exact multiplicity. -/
theorem value_copies (T : Tensor K X Y Z) (r : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => T)) = r * χ.value T := by
  rw [χ.map_directSum]
  simp

/-- The character cost of an exact number of full copies of a tensor power. -/
theorem value_power_copies (T : Tensor K X Y Z) (r n : ℕ) :
    χ.value (Tensor.directSum (fun _ : Fin r => Tensor.power T n)) =
      r * χ.value T ^ n := by
  rw [χ.value_copies, χ.value_power]

end Powers

section DependentDirectSum

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X Y Z : ι → Type}
variable [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, Fintype (Z i)]

/-- A branch extended to the common ambient sigma coordinate spaces. -/
def paddedBranch (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι) :
    Tensor K (Σ i, X i) (Σ i, Y i) (Σ i, Z i) :=
  Tensor.restrict
    (fun x a => if Sigma.mk i a = x then 1 else 0)
    (fun y b => if Sigma.mk i b = y then 1 else 0)
    (fun z c => if Sigma.mk i c = z then 1 else 0) (T i)

@[simp] theorem value_paddedBranch
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι) :
    χ.value (paddedBranch T i) = χ.value (T i) := by
  simpa only [paddedBranch] using
    χ.value_extendByZero (T i) (Sigma.mk i) (Sigma.mk i) (Sigma.mk i)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)

omit [Fintype ι] in
@[simp] theorem paddedBranch_matching
    (T : ∀ i, Tensor K (X i) (Y i) (Z i))
    (i : ι) (x : X i) (y : Y i) (z : Z i) :
    paddedBranch T i ⟨i, x⟩ ⟨i, y⟩ ⟨i, z⟩ = T i x y z := by
  simp [paddedBranch, Tensor.restrict, ite_mul, mul_ite]

omit [Fintype ι] in
theorem paddedBranch_zero_left
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hx : x.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ a : X i, Sigma.mk i a ≠ x :=
    fun a h => hx (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_middle
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hy : y.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ b : Y i, Sigma.mk i b ≠ y :=
    fun b h => hy (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

omit [Fintype ι] in
theorem paddedBranch_zero_right
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) (i : ι)
    (x : Σ i, X i) (y : Σ i, Y i) (z : Σ i, Z i) (hz : z.1 ≠ i) :
    paddedBranch T i x y z = 0 := by
  have hzero : ∀ c : Z i, Sigma.mk i c ≠ z :=
    fun c h => hz (congrArg Sigma.fst h).symm
  simp [paddedBranch, Tensor.restrict, hzero]

/-- Redundant outer labels give a zero extension of the varying-dimension sum. -/
theorem directSum_paddedBranch
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    Tensor.directSum (paddedBranch T) = Tensor.restrict
      (fun (x' : ι × (Σ i, X i)) x => if (x.1, x) = x' then 1 else 0)
      (fun (y' : ι × (Σ i, Y i)) y => if (y.1, y) = y' then 1 else 0)
      (fun (z' : ι × (Σ i, Z i)) z => if (z.1, z) = z' then 1 else 0)
      (Tensor.dependentDirectSum T) := by
  funext x' y' z'
  rcases x' with ⟨i, ⟨ix, x⟩⟩
  rcases y' with ⟨j, ⟨iy, y⟩⟩
  rcases z' with ⟨k, ⟨iz, z⟩⟩
  have hgraph {A : Type} (f : A → ι) (a x : A) (i : ι) :
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
  by_cases hi : ix = i
  · subst ix
    by_cases hj : iy = i
    · subst iy
      by_cases hk : iz = i
      · subst iz
        by_cases hij : i = j
        · subst j
          by_cases hik : i = k
          · subst k
            simp [Tensor.directSum, Tensor.dependentDirectSum]
          · simp [Tensor.directSum, hik]
        · simp [Tensor.directSum, hij]
      · simp [Tensor.directSum, Tensor.dependentDirectSum,
          paddedBranch_zero_right T i ⟨i, x⟩ ⟨i, y⟩ ⟨iz, z⟩ hk,
          hk]
    · simp [Tensor.directSum, Tensor.dependentDirectSum,
        paddedBranch_zero_middle T i ⟨i, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hj,
        hj]
  · simp [Tensor.directSum,
      paddedBranch_zero_left T i ⟨ix, x⟩ ⟨iy, y⟩ ⟨iz, z⟩ hi, hi]


/-- Additivity holds even when each summand has different coordinate types. -/
theorem value_dependentDirectSum
    (T : ∀ i, Tensor K (X i) (Y i) (Z i)) :
    χ.value (Tensor.dependentDirectSum T) = ∑ i, χ.value (T i) := by
  have h := χ.value_extendByZero (Tensor.dependentDirectSum T)
    (fun x => (x.1, x)) (fun y => (y.1, y)) (fun z => (z.1, z))
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h)
    (fun _ _ h => congrArg Prod.snd h)
  rw [← directSum_paddedBranch] at h
  rw [← h, χ.map_directSum]
  simp

end DependentDirectSum

end MatrixMultiplication.AuxiliarySeparation.Character

end

end MatrixMultiplicationAllFields
