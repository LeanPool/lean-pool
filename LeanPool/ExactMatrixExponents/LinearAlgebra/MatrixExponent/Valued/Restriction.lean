/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Spectral.Semiring
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Restrictions with entries in a subring

The tensors themselves still have coefficients in the ambient field.
For a valuation ring this relation allows only integral substitutions.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Valued
open Spectral

variable {K S : Type} [CommRing K] [Fintype S] (O : Subring K)
variable {A B C D : Raw K S}

/-- The defining condition `∃ L : (s : S) → B.leg s → A.leg s → K, (∀ s x y, L s x y ∈ O) ∧ ∀ x,
B.coeff x = ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y`. -/
def Restricts (A B : Raw K S) : Prop :=
  ∃ L : (s : S) → B.leg s → A.leg s → K, (∀ s x y, L s x y ∈ O) ∧
    ∀ x, B.coeff x = ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y

variable {O}

theorem top_restricts (h : A.Restricts B) : Restricts ⊤ A B := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, fun _ _ _ => trivial, hL⟩

theorem restricts_iff [DecidableEq S] (A B : Raw K S) :
    Restricts O A B ↔
      ∃ L : (s : S) → B.leg s → A.leg s → K, (∀ s x y, L s x y ∈ O) ∧
        ∀ x, B.coeff x = ∑ y : ∀ s, A.leg s, (∏ s, L s (x s) (y s)) * A.coeff y := by
  simp only [Restricts, Raw.expand]

theorem Restricts.forget (h : Restricts O A B) : A.Restricts B := by
  obtain ⟨L, _, hh⟩ := h
  exact ⟨L, hh⟩

theorem Restricts.pullback (f : ∀ s, B.leg s → A.leg s)
    (h : ∀ x, B.coeff x = A.coeff (fun s => f s (x s))) : Restricts O A B := by
  classical
  refine ⟨Raw.pullbackMap f, ?_, Raw.coeff_pullbackMap f h⟩
  intro s x y
  by_cases equal : y = f s x <;> simp [Raw.pullbackMap, equal]

theorem Restricts.refl (A : Raw K S) : Restricts O A A :=
  Restricts.pullback (fun _ x => x) (fun _ => rfl)

theorem Restricts.trans (h : Restricts O A B) (g : Restricts O B C) : Restricts O A C := by
  obtain ⟨L, hl, hL⟩ := h
  obtain ⟨M, hm, hM⟩ := g
  exact ⟨Raw.composeRestrictionMaps L M,
    fun s x z => O.sum_mem (fun y _ => O.mul_mem (hm s x y) (hl s y z)),
    Raw.coeff_composeRestrictionMaps L M hL hM⟩

/-- The equiv of type `Setoid (Raw K S) where r A B` for the given inputs. -/
def equiv (O : Subring K) : Setoid (Raw K S) where
  r A B := Restricts O A B ∧ Restricts O B A
  iseqv := ⟨fun A => ⟨.refl A, .refl A⟩, fun h => ⟨h.2, h.1⟩,
    fun h g => ⟨h.1.trans g.1, g.2.trans h.2⟩⟩

theorem forget_equiv (h : (equiv O).r A B) : A ≈ B := ⟨h.1.forget, h.2.forget⟩

theorem equiv_coeff (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ x, A.coeff x = B.coeff (fun s => f s (x s))) : (equiv O).r A B := by
  refine ⟨Restricts.pullback (fun s => (f s).symm) ?_, Restricts.pullback (fun s => f s) h⟩
  intro x
  simp only [h, Equiv.apply_symm_apply]

theorem relabel (e : A.term ≃ B.term) (f : ∀ s, A.leg s ≃ B.leg s)
    (h : ∀ i s x, A.factor i s x = B.factor (e i) s (f s x)) : (equiv O).r A B := by
  refine equiv_coeff f fun x => ?_
  simp only [Raw.coeff, h]
  exact e.sum_comp (fun i => ∏ s, B.factor i s (f s (x s)))

theorem relabel_of_relabels (h : Raw.Relabels A B) : (equiv O).r A B := by
  obtain ⟨terms, legs, factors⟩ := h
  exact relabel terms legs factors

theorem Restricts.mul (h : Restricts O A B) (g : Restricts O C D) :
    Restricts O (A * C) (B * D) := by
  obtain ⟨L, hl, hL⟩ := h
  obtain ⟨M, hm, hM⟩ := g
  exact ⟨Raw.restrictMulMap L M, fun s x y => O.mul_mem (hl s x.1 y.1) (hm s x.2 y.2),
    Raw.coeff_restrictMulMap L M hL hM⟩

theorem Restricts.add (h : Restricts O A B) (g : Restricts O C D) :
    Restricts O (A + C) (B + D) := by
  obtain ⟨L, hl, hL⟩ := h
  obtain ⟨M, hm, hM⟩ := g
  refine ⟨Raw.restrictAddMap L M, ?_, Raw.coeff_restrictAddMap L M hL hM⟩
  rintro s (x | x) (y | y) <;> simp [Raw.restrictAddMap, hl, hm]

end MatrixMultiplicationAllFields.MatrixExponent.Valued
