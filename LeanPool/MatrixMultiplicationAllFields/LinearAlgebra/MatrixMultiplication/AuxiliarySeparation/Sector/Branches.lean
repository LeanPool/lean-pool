/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Sector/Branches.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Sector.Degeneration
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SupportExtension
public import Mathlib.Data.Fin.Rev
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Coordinate identifications of the three retained sectors

Each outer branch is a zero extension of `C(a,h)`, using the same first-leg
coordinates. The middle branch is a zero extension after reversing the first
coordinate and exchanging the second and third tensor legs.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped Classical


namespace MatrixMultiplication.AuxiliarySeparation.Sector

/-- Embed the left second-leg interval. -/
def leftY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the left third-leg interval. -/
def leftZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle second-leg interval, which carries the convolution output. -/
def middleY (a h : ℕ) (s : Fin (a + h - 1)) : YIndex a h :=
  ⟨h + s.val, by have hs := s.isLt; unfold sourceWidth; omega⟩

/-- Embed the middle third-leg interval, which carries the second input. -/
def middleZ (a h : ℕ) (r : Fin h) : ZIndex a h :=
  ⟨h + a - 1 + r.val, by have hr := r.isLt; unfold sourceWidth; omega⟩

/-- Embed the right second-leg interval. -/
def rightY (a h : ℕ) (r : Fin h) : YIndex a h :=
  ⟨rightStart a h + r.val,
    by have hr := r.isLt; unfold rightStart sourceWidth; omega⟩

/-- Embed the right third-leg interval. -/
def rightZ (a h : ℕ) (s : Fin (a + h - 1)) : ZIndex a h :=
  ⟨rightStart a h + s.val,
    by have hs := s.isLt; unfold rightStart sourceWidth; omega⟩

theorem leftY_injective (a h : ℕ) : Function.Injective (leftY a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : YIndex a h => t.val) heq

theorem leftZ_injective (a h : ℕ) : Function.Injective (leftZ a h) := by
  intro r s heq
  apply Fin.ext
  exact congrArg (fun t : ZIndex a h => t.val) heq

theorem middleY_injective (a h : ℕ) : Function.Injective (middleY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleY] at hv
  omega

theorem middleZ_injective (a h : ℕ) : Function.Injective (middleZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [middleZ] at hv
  omega

theorem rightY_injective (a h : ℕ) : Function.Injective (rightY a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightY] at hv
  omega

theorem rightZ_injective (a h : ℕ) : Function.Injective (rightZ a h) := by
  intro r s heq
  apply Fin.ext
  have hv := congrArg Fin.val heq
  dsimp [rightZ] at hv
  omega

/-- Pulling back the left block gives ordinary convolution. -/
theorem leftTensor_pullback (a h : ℕ) :
    Tensor.pullback id (leftY a h) (leftZ a h) (leftTensor K a h) =
      convolution K a h := by
  funext i r s
  have hb : LeftBranch a h i.val r.val s.val ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      exact ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, hs.symm⟩
  simp only [Tensor.pullback, leftTensor, leftY, leftZ, id_eq, convolution, hb]

/-- Pulling back the translated right block also gives ordinary convolution. -/
theorem rightTensor_pullback (a h : ℕ) :
    Tensor.pullback id (rightY a h) (rightZ a h) (rightTensor K a h) =
      convolution K a h := by
  funext i r s
  have hb : RightBranch a h i.val (rightStart a h + r.val)
      (rightStart a h + s.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hi, hr, hs⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, i.isLt, r.isLt, rfl, rfl, ?_⟩
      omega
  simp only [Tensor.pullback, rightTensor, rightY, rightZ, id_eq, convolution, hb]

variable (K) in
/-- Exchange the two outer convolution legs while retaining the original input
order in the displayed coefficient equation. -/
def exchangedConvolution (a h : ℕ) :
    Tensor K (Fin a) (Fin (a + h - 1)) (Fin h) :=
  fun i s r => convolution K a h i r s

/-- The middle branch is exactly convolution with its last two legs exchanged;
the first-leg reversal occurs solely in this individual branch identification. -/
theorem middleTensor_pullback (a h : ℕ) :
    Tensor.pullback Fin.rev (middleY a h) (middleZ a h) (middleTensor K a h) =
      exchangedConvolution K a h := by
  funext i s r
  have hi := i.isLt
  have hr := r.isLt
  have hb : MiddleBranch a h (a - (i.val + 1)) (h + s.val)
      (h + a - 1 + r.val) ↔ i.val + r.val = s.val := by
    constructor
    · rintro ⟨u, t, hu, ht, hx, hy, hz⟩
      omega
    · intro hs
      refine ⟨i.val, r.val, hi, hr, ?_, ?_, rfl⟩ <;> omega
  simp only [Tensor.pullback, middleTensor, middleY, middleZ,
    exchangedConvolution, convolution, Fin.val_rev, hb]

/-- All nonzero left-branch coordinates lie in the displayed embeddings. -/
theorem leftTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : leftTensor K a h i j k ≠ 0) :
    (∃ r, leftY a h r = j) ∧ (∃ s, leftZ a h s = k) := by
  have hb : LeftBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [leftTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · exact ⟨⟨u + r, by omega⟩, Fin.ext hk.symm⟩

/-- All nonzero right-branch coordinates lie in the translated embeddings. -/
theorem rightTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : rightTensor K a h i j k ≠ 0) :
    (∃ r, rightY a h r = j) ∧ (∃ s, rightZ a h s = k) := by
  have hb : RightBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [rightTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  constructor
  · exact ⟨⟨r, hr⟩, Fin.ext hj.symm⟩
  · refine ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩
    dsimp [rightZ]
    omega

/-- All nonzero middle-branch coordinates lie in the exchanged embeddings. -/
theorem middleTensor_support (a h : ℕ) (i : Fin a) (j : YIndex a h)
    (k : ZIndex a h) (hn : middleTensor K a h i j k ≠ 0) :
    (∃ u, Fin.rev u = i) ∧ (∃ s, middleY a h s = j) ∧
      (∃ r, middleZ a h r = k) := by
  have hb : MiddleBranch a h i.val j.val k.val := by
    by_contra hn'
    exact hn (by simp [middleTensor, hn'])
  rcases hb with ⟨u, r, hu, hr, hi, hj, hk⟩
  refine ⟨⟨⟨u, hu⟩, Fin.ext ?_⟩, ⟨⟨u + r, by omega⟩, Fin.ext ?_⟩,
    ⟨⟨r, hr⟩, Fin.ext ?_⟩⟩
  · simp only [Fin.val_rev]
    omega
  · dsimp [middleY]
    omega
  · exact hk.symm

/-- The left block is the zero extension of the ordinary convolution tensor. -/
theorem leftTensor_eq_extension (a h : ℕ) :
    leftTensor K a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if leftY a h r = y then 1 else 0)
      (fun z s => if leftZ a h s = z then 1 else 0) (convolution K a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : leftTensor K a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (leftY a h) ∧ k ∈ Set.range (leftZ a h) := by
    exact ⟨⟨i, rfl⟩, leftTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (leftTensor K a h) id (leftY a h) (leftZ a h)
    Function.injective_id (leftY_injective a h) (leftZ_injective a h) hs
  rw [leftTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The right block is the zero extension along the translated coordinates. -/
theorem rightTensor_eq_extension (a h : ℕ) :
    rightTensor K a h = Tensor.restrict
      (fun x i => if i = x then 1 else 0)
      (fun y r => if rightY a h r = y then 1 else 0)
      (fun z s => if rightZ a h s = z then 1 else 0) (convolution K a h) := by
  have hs (i : Fin a) (j : YIndex a h) (k : ZIndex a h)
      (hn : rightTensor K a h i j k ≠ 0) :
      i ∈ Set.range (id : Fin a → Fin a) ∧
        j ∈ Set.range (rightY a h) ∧ k ∈ Set.range (rightZ a h) := by
    exact ⟨⟨i, rfl⟩, rightTensor_support a h i j k hn⟩
  classical
  have heq := tensor_eq_extendByZero_pullback (rightTensor K a h) id (rightY a h) (rightZ a h)
    Function.injective_id (rightY_injective a h) (rightZ_injective a h) hs
  rw [rightTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> (try dsimp only [id_eq]) <;> split_ifs <;> rfl

/-- The middle block is the zero extension of the exchanged convolution, with
one reversible change of basis on its first leg. -/
theorem middleTensor_eq_extension (a h : ℕ) :
    middleTensor K a h = Tensor.restrict
      (fun x i => if Fin.rev i = x then 1 else 0)
      (fun y s => if middleY a h s = y then 1 else 0)
      (fun z r => if middleZ a h r = z then 1 else 0) (exchangedConvolution K a h) := by
  classical
  have heq := tensor_eq_extendByZero_pullback (middleTensor K a h) Fin.rev (middleY a h)
    (middleZ a h) Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)
    (middleTensor_support a h)
  rw [middleTensor_pullback] at heq
  convert heq using 1
  congr 1 <;> funext x i <;> split_ifs <;> rfl

/-- Every character assigns the left branch the value of `C(a,h)`. -/
theorem value_leftTensor (χ : Character K) (a h : ℕ) :
    χ.value (leftTensor K a h) = χ.value (convolution K a h) := by
  rw [leftTensor_eq_extension]
  exact χ.value_extendByZero _ id (leftY a h) (leftZ a h) Function.injective_id
    (leftY_injective a h) (leftZ_injective a h)

/-- Translation of the outer coordinates preserves the right-branch value. -/
theorem value_rightTensor (χ : Character K) (a h : ℕ) :
    χ.value (rightTensor K a h) = χ.value (convolution K a h) := by
  rw [rightTensor_eq_extension]
  exact χ.value_extendByZero _ id (rightY a h) (rightZ a h) Function.injective_id
    (rightY_injective a h) (rightZ_injective a h)

/-- The middle-branch value is the value of the exchanged convolution tensor. -/
theorem value_middleTensor (χ : Character K) (a h : ℕ) :
    χ.value (middleTensor K a h) = χ.value (exchangedConvolution K a h) := by
  rw [middleTensor_eq_extension]
  exact χ.value_extendByZero _ Fin.rev (middleY a h) (middleZ a h)
    Fin.rev_injective (middleY_injective a h) (middleZ_injective a h)

/-- Exchanging two tensor legs preserves nonzeroness. -/
theorem exchangedConvolution_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    exchangedConvolution K a h ≠ 0 := by
  intro hz
  apply convolution_nonzero (K := K) ha hh
  funext i r s
  exact congrFun (congrFun (congrFun hz i) s) r

/-- The left retained branch is nonzero in every positive size. -/
theorem leftTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    leftTensor K a h ≠ 0 := by
  intro hz
  have hp := leftTensor_pullback (K := K) a h
  rw [hz] at hp
  exact convolution_nonzero (K := K) ha hh hp.symm

/-- The translated right branch is nonzero in every positive size. -/
theorem rightTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    rightTensor K a h ≠ 0 := by
  intro hz
  have hp := rightTensor_pullback (K := K) a h
  rw [hz] at hp
  exact convolution_nonzero (K := K) ha hh hp.symm

/-- The exchanged middle branch is nonzero in every positive size. -/
theorem middleTensor_nonzero {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    middleTensor K a h ≠ 0 := by
  intro hz
  have hp := middleTensor_pullback (K := K) a h
  rw [hz] at hp
  exact exchangedConvolution_nonzero ha hh hp.symm

end MatrixMultiplication.AuxiliarySeparation.Sector

end

end MatrixMultiplicationAllFields
