/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.BernoulliCounts
public import Mathlib.Logic.Equiv.Prod

/-! Exact reindexing and slicing of finite product laws. All identities are
finite sums; no conditional-probability quotient is used. -/
@[expose] public section

namespace Shellsort
open scoped BigOperators

theorem mean_transport_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (w : α → ℝ) (v : β → ℝ) (F : β → ℝ)
    (hw : ∀ x, w x = v (e x)) :
    mean w (fun x => F (e x)) = mean v F := by
  unfold mean
  calc
    _ = ∑ x, v (e x) * F (e x) := Finset.sum_congr rfl (fun x _ => by rw [hw])
    _ = _ := e.sum_comp (fun y => v y * F y)

theorem bernoulli_mean_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (t : ℝ) (F : (β → Bool) → ℝ) :
    mean (productWeight (fun _ : α => bernoulliWeight t))
      (fun x => F (fun b => x (e.symm b))) =
      mean (productWeight (fun _ : β => bernoulliWeight t)) F := by
  let E := e.arrowCongr (Equiv.refl Bool)
  apply mean_transport_equiv E _ _ F
  intro x
  change (∏ a, bernoulliWeight t (x a)) = ∏ b, bernoulliWeight t (x (e.symm b))
  exact (e.symm.prod_comp _).symm

theorem bernoulli_mean_curry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (t : ℝ) (F : (∀ i, β i → Bool) → ℝ) :
    mean (productWeight (fun _ : Sigma β => bernoulliWeight t))
      (fun x => F (fun i b => x ⟨i, b⟩)) =
    mean (productWeight (fun i => productWeight (fun _ : β i => bernoulliWeight t))) F := by
  apply mean_transport_equiv (Equiv.piCurry (fun _ _ => Bool)) _ _ F
  intro x
  exact Fintype.prod_sigma (fun ib => bernoulliWeight t (x ib))

theorem productWeight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} (w : ∀ i, β i → ℝ) (i : ι) (x : ∀ i, β i) :
    productWeight w x = w i (x i) *
      productWeight (fun j : {j : ι // j ≠ i} => w j.val) (fun j => x j.val) :=
  Fintype.prod_eq_mul_prod_subtype_ne (fun j => w j (x j)) i

theorem productWeight_split_reconstruct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} (w : ∀ i, β i → ℝ) (i : ι)
    (a : β i) (z : ∀ j : {j : ι // j ≠ i}, β j.val) :
    productWeight w ((Equiv.piSplitAt i β).symm (a, z)) =
      w i a * productWeight (fun j : {j : ι // j ≠ i} => w j.val) z := by
  rw [productWeight_split w i]
  simp only [Equiv.piSplitAt_symm_apply]
  congr 1
  unfold productWeight
  apply Finset.prod_congr rfl
  intro j _
  simp only [j.property, dite_false]

theorem productWeight_mean_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (i : ι) (F : (∀ i, β i) → ℝ) :
    mean (productWeight w) F =
      mean (w i) (fun a => mean
        (productWeight (fun j : {j : ι // j ≠ i} => w j.val))
        (fun z => F ((Equiv.piSplitAt i β).symm (a, z)))) := by
  unfold mean
  rw [← (Equiv.piSplitAt i β).symm.sum_comp]
  simp only [Fintype.sum_prod_type, productWeight_split_reconstruct, mul_assoc,
    Finset.mul_sum]

theorem productWeight_mean_ignore_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (i : ι) (hw : ∑ a, w i a = 1)
    (F : (∀ j : {j : ι // j ≠ i}, β j.val) → ℝ) :
    mean (productWeight w) (fun x => F (fun j => x j.val)) =
      mean (productWeight (fun j : {j : ι // j ≠ i} => w j.val)) F := by
  rw [productWeight_mean_split w i]
  have he : ∀ a z, (fun j : {j : ι // j ≠ i} =>
      ((Equiv.piSplitAt i β).symm (a, z)) j.val) = z := by
    intro a z
    funext j
    simp only [Equiv.piSplitAt_symm_apply, j.property, dite_false]
  simp only [he]
  exact mean_const (w i) hw _

/-- The selected coordinate may choose the parameter of an observable that
ignores that coordinate. Its expectation is an exact outer weighted average. -/
theorem productWeight_owner_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (w : ∀ i, β i → ℝ) (i : ι) (hw : ∑ a, w i a = 1)
    (F : β i → (∀ i, β i) → ℝ)
    (hignore : ∀ a x z, (∀ j, j ≠ i → x j = z j) → F a x = F a z) :
    mean (productWeight w) (fun x => F (x i) x) =
      mean (w i) (fun a => mean (productWeight w) (F a)) := by
  rw [productWeight_mean_split w i]
  have hv : ∀ a z, ((Equiv.piSplitAt i β).symm (a, z)) i = a := by
    intro a z
    exact congrArg Prod.fst ((Equiv.piSplitAt i β).apply_symm_apply (a, z))
  simp only [hv]
  unfold mean at ⊢
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have he : (fun x => F a x) =
      (fun x => F a ((Equiv.piSplitAt i β).symm (a, fun j => x j.val))) := by
    funext x
    apply hignore
    intro j hj
    simp only [Equiv.piSplitAt_symm_apply, hj, dite_false]
  have hmean := productWeight_mean_ignore_coordinate w i hw
    (fun z => F a ((Equiv.piSplitAt i β).symm (a, z)))
  rw [← he] at hmean
  exact hmean.symm

end Shellsort
