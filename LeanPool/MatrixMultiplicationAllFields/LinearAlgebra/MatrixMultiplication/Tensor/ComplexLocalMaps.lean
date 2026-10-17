/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import Mathlib.Data.Fintype.BigOperators

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation
namespace LocalMaps

open scoped BigOperators

variable {K X Y Z A B C A' B' C' : Type*}
variable [CommSemiring K] [Fintype A] [Fintype B] [Fintype C]

def fiberMatrix [DecidableEq X] (M : X → A' → A → K) :
    (X × A') → (X × A) → K :=
  fun output input => if output.1 = input.1 then M output.1 output.2 input.2 else 0

def fiberTransform (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A') (Y × B') (Z × C') :=
  fun x y z => ∑ a, ∑ b, ∑ c,
    MX x.1 x.2 a * MY y.1 y.2 b * MZ z.1 z.2 c *
      T (x.1, a) (y.1, b) (z.1, c)

def originalScale (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A) (Y × B) (Z × C) :=
  fun x y z => coefficient x.1 y.1 z.1 * T x y z

theorem fiberTransform_originalScale (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ (originalScale coefficient T) =
      originalScale coefficient (fiberTransform MX MY MZ T) := by
  funext x y z
  simp only [fiberTransform, originalScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ac_rfl

theorem fiberTransform_substitution
    (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (U : Tensor K (X × A') (Y × B') (Z × C'))
    (identity : fiberTransform MX MY MZ T = U)
    (coefficient : X → Y → Z → K) :
    fiberTransform MX MY MZ (originalScale coefficient T) =
      originalScale coefficient U := by
  rw [fiberTransform_originalScale, identity]

theorem fiberTransform_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ T =
      Tensor.restrict (fiberMatrix MX) (fiberMatrix MY) (fiberMatrix MZ) T := by
  funext x y z
  simp [fiberTransform, Tensor.restrict, fiberMatrix, Fintype.sum_prod_type,
    ite_mul, mul_ite]

noncomputable def originalMask (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A) (Y × B) (Z × C) := by
  classical
  exact fun x y z => if P x.1 y.1 z.1 then T x y z else 0

theorem fiberTransform_originalMask (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (P : X → Y → Z → Prop) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ (originalMask P T) =
      originalMask P (fiberTransform MX MY MZ T) := by
  classical
  funext x y z
  by_cases h : P x.1 y.1 z.1 <;> simp [fiberTransform, originalMask, h]

def SupportedOn (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) : Prop :=
  ∀ x y z, ¬ P x.1 y.1 z.1 → T x y z = 0

theorem fiberTransform_supportedOn (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (P : X → Y → Z → Prop) (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn P T) : SupportedOn P (fiberTransform MX MY MZ T) := by
  intro x y z h
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro c _
  simp [hT (x.1, a) (y.1, b) (z.1, c) h]

omit [Fintype A] [Fintype B] [Fintype C] in
theorem originalMask_eq_self (P : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) (hT : SupportedOn P T) :
    originalMask P T = T := by
  classical
  funext x y z
  by_cases h : P x.1 y.1 z.1
  · simp [originalMask, h]
  · simp [originalMask, h, hT x y z h]

noncomputable def localSelector (P : X → Prop) : (X × A) → (X × A) → K := by
  classical
  exact fun output input =>
    if output = input then (if P output.1 then 1 else 0) else 0

theorem factoredMask_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    originalMask (fun x y z => PX x ∧ PY y ∧ PZ z) T =
      Tensor.restrict (localSelector PX) (localSelector PY) (localSelector PZ) T := by
  classical
  funext x y z
  by_cases hx : PX x.1 <;> by_cases hy : PY y.1 <;> by_cases hz : PZ z.1 <;>
    simp [originalMask, Tensor.restrict, localSelector, ite_mul, mul_ite, hx, hy, hz]

variable {Label : Type*}

def Synchronized (lx : X → Label) (ly : Y → Label) (lz : Z → Label) :
    X → Y → Z → Prop :=
  fun x y z => lx x = ly y ∧ lx x = lz z

def InBranch (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (label : Label) : X → Y → Z → Prop :=
  fun x y z => lx x = label ∧ ly y = label ∧ lz z = label

omit [Fintype A] [Fintype B] [Fintype C] in
theorem factoredMask_synchronized
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (support : X → Y → Z → Prop)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn support T)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      Synchronized lx ly lz x y z) :
    SupportedOn (Synchronized lx ly lz)
      (originalMask (fun x y z => PX x ∧ PY y ∧ PZ z) T) := by
  classical
  intro x y z hn
  by_cases hs : support x.1 y.1 z.1
  · by_cases hw : PX x.1 ∧ PY y.1 ∧ PZ z.1
    · exact (hn (compatible x.1 y.1 z.1 hs hw.1 hw.2.1 hw.2.2)).elim
    · simp [originalMask, hw]
  · simp [originalMask, hT x y z hs]

theorem controlled_eq_sum_branches [Fintype Label]
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform (fun x => MX (lx x) x) (fun y => MY (ly y) y)
        (fun z => MZ (lz z) z) (originalMask (Synchronized lx ly lz) T) =
      fun x y z => ∑ label,
        fiberTransform (MX label) (MY label) (MZ label)
          (originalMask (InBranch lx ly lz label) T) x y z := by
  classical
  funext x y z
  by_cases h : Synchronized lx ly lz x.1 y.1 z.1
  · have hy : ly y.1 = lx x.1 := h.1.symm
    have hz : lz z.1 = lx x.1 := h.2.symm
    rw [Finset.sum_eq_single (lx x.1)]
    · simp [fiberTransform, originalMask, InBranch, h, hy, hz]
    · intro label _ hlabel
      have hn : lx x.1 ≠ label := Ne.symm hlabel
      simp [fiberTransform, originalMask, InBranch, hn]
    · simp
  · have hn (label : Label) : ¬ InBranch lx ly lz label x.1 y.1 z.1 := by
      intro hb
      exact h ⟨hb.1.trans hb.2.1.symm, hb.1.trans hb.2.2.symm⟩
    simp [fiberTransform, originalMask, h, hn]

theorem controlled_eq_sum_branches_of_supported [Fintype Label]
    (lx : X → Label) (ly : Y → Label) (lz : Z → Label)
    (MX : Label → X → A' → A → K) (MY : Label → Y → B' → B → K)
    (MZ : Label → Z → C' → C → K)
    (T : Tensor K (X × A) (Y × B) (Z × C))
    (hT : SupportedOn (Synchronized lx ly lz) T) :
    fiberTransform (fun x => MX (lx x) x) (fun y => MY (ly y) y)
        (fun z => MZ (lz z) z) T =
      fun x y z => ∑ label,
        fiberTransform (MX label) (MY label) (MZ label)
          (originalMask (InBranch lx ly lz label) T) x y z := by
  have h := controlled_eq_sum_branches lx ly lz MX MY MZ T
  rw [originalMask_eq_self _ _ hT] at h
  exact h

end LocalMaps
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
