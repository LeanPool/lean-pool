/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Basic

/-! # Matching permutations

Equivalences between the fibers of two labelings assemble into a matching permutation.
-/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Equivalences carrying each labelled source fibre onto the matching target fibre. -/
abbrev matchingEquiv {A B I : Type*} (f : A → I) (g : B → I) :=
  {e : A ≃ B // ∀ a, g (e a) = f a}

/-- Restrict a label-preserving bijection to the matching fibers of one label. -/
def restrictMatching {A B I : Type*} (f : A → I) (g : B → I)
    (e : matchingEquiv f g) (i : I) :
    {a // f a = i} ≃ {b // g b = i} where
  toFun a := ⟨e.val a.val, (e.property a.val).trans a.property⟩
  invFun b := ⟨e.val.symm b.val, by
    have he := e.property (e.val.symm b.val)
    simp only [Equiv.apply_symm_apply] at he
    exact he.symm.trans b.property⟩
  left_inv a := by ext; simp
  right_inv b := by ext; simp

/-- A genuine equivalence of data, not an assumption of independent random fibres. -/
def matchingEquivFibers {A B I : Type*} (f : A → I) (g : B → I) :
    matchingEquiv f g ≃ (∀ i, {a // f a = i} ≃ {b // g b = i}) where
  toFun e := restrictMatching f g e
  invFun e := ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩
  left_inv e := by
    apply Subtype.ext
    ext a
    rfl
  right_inv e := by
    funext i
    apply Equiv.ext
    rintro ⟨a, ha⟩
    cases ha
    rfl

theorem matchingEquiv_card {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (f : A → I) (g : B → I)
    (hc : ∀ i, Fintype.card {a // f a = i} = Fintype.card {b // g b = i}) :
    Fintype.card (matchingEquiv f g) =
      ∏ i, (Fintype.card {a // f a = i}).factorial := by
  classical
  rw [Fintype.card_congr (matchingEquivFibers f g), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.card_equiv (Fintype.equivOfCardEq (hc i))

end Shellsort
end
