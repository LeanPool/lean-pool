/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryHermiteDegreeOrder.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.HermiteL2Family
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Correspondence auxiliary Hermite degree order

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `degreeHermite_lt_of_degree_lt`.
-/

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Tensor orbital labels ordered first by total degree and then by their
injective natural-number encoding. -/
@[ext] structure DegreeHermiteIndex (n : ℕ) where
  /-- The underlying Hermite multi-index. -/
  val : HermiteMultiIndex n
deriving DecidableEq

/-- The total degree `∑ j, p j + ∑ j, q j` of a Hermite multi-index `(p, q)`. -/
def hermiteTotalDegree {n : ℕ} (i : HermiteMultiIndex n) : ℕ :=
  (∑ j, i.1 j) + ∑ j, i.2 j

/-- The lexicographic sort key of a label: its total degree, then its `Encodable` code. -/
def degreeHermiteKey {n : ℕ} (i : DegreeHermiteIndex n) : ℕ ×ₗ ℕ :=
  toLex (hermiteTotalDegree i.val, Encodable.encode i.val)

theorem degreeHermiteKey_injective (n : ℕ) :
    Function.Injective (@degreeHermiteKey n) := by
  intro i j h
  apply DegreeHermiteIndex.ext
  apply Encodable.encode_injective
  exact congrArg (fun k : ℕ ×ₗ ℕ => (ofLex k).2) h

instance (n : ℕ) : LinearOrder (DegreeHermiteIndex n) :=
  LinearOrder.lift' degreeHermiteKey (degreeHermiteKey_injective n)

instance (n : ℕ) : WellFoundedLT (DegreeHermiteIndex n) :=
  InvImage.wf degreeHermiteKey (wellFounded_lt (α := ℕ ×ₗ ℕ))

theorem finite_hermite_degree_sublevel (n D : ℕ) :
    {i : DegreeHermiteIndex n | hermiteTotalDegree i.val ≤ D}.Finite := by
  let f : ((Fin n → Fin (D+1)) × (Fin n → Fin (D+1))) → DegreeHermiteIndex n :=
    fun i => ⟨(fun j => (i.1 j).val, fun j => (i.2 j).val)⟩
  apply (Set.finite_range f).subset
  intro i hi
  have hp (j : Fin n) : i.val.1 j ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_add_right _ _).trans hi)
  have hq (j : Fin n) : i.val.2 j ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_add_left _ _).trans hi)
  exact ⟨(fun j => ⟨i.val.1 j, Nat.lt_succ_of_le (hp j)⟩,
    fun j => ⟨i.val.2 j, Nat.lt_succ_of_le (hq j)⟩), rfl⟩

theorem degreeHermite_finite_Iic (n : ℕ) (i : DegreeHermiteIndex n) :
    (Set.Iic i).Finite := by
  apply (finite_hermite_degree_sublevel n (hermiteTotalDegree i.val)).subset
  intro j hj
  change degreeHermiteKey j ≤ degreeHermiteKey i at hj
  rcases Prod.Lex.le_iff.mp hj with h | ⟨h, _⟩
  · exact Nat.le_of_lt h
  · exact h.le

instance (n : ℕ) : LocallyFiniteOrderBot (DegreeHermiteIndex n) :=
  LocallyFiniteOrderBot.ofIic _ (fun i => (degreeHermite_finite_Iic n i).toFinset)
    (fun i j => by simp)

/-- Any strict drop in total degree precedes the original orbital label. -/
theorem degreeHermite_lt_of_degree_lt {n : ℕ} {i j : DegreeHermiteIndex n}
    (h : hermiteTotalDegree i.val < hermiteTotalDegree j.val) : i < j :=
  Prod.Lex.lt_iff.mpr (Or.inl h)

end
end GinibrePoincare
