/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.FailureOfComposition.Productiveness

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
A concrete primitive recursive normal-form predicate for Mathlib's numbering.
A witness pairs a fuel bound with the output. It is not asserted to be the
historical computation-history coding of Odifreddi or Di Paola--Montagna.
All theorems in this module concern standard natural numbers, not PA derivations.
-/

@[expose] public section

namespace FailureOfComposition
namespace Kleene

open Encodable Denumerable _root_.Nat.Partrec

/-- The eval construction in `FailureOfComposition.Kleene`. -/
def eval (e x : ℕ) : Part ℕ :=
  Code.eval (ofNat Code e) x

/-- The T₁ construction in `FailureOfComposition.Kleene`. -/
def T₁ (e x s : ℕ) : Prop :=
  Code.evaln s.unpair.1 (ofNat Code e) x = some s.unpair.2

/-- The U construction in `FailureOfComposition.Kleene`. -/
def U (s : ℕ) : ℕ :=
  s.unpair.2

instance (e x s : ℕ) : Decidable (T₁ e x s) :=
  inferInstanceAs (Decidable (Code.evaln s.unpair.1 (ofNat Code e) x = some s.unpair.2))

theorem T₁_primrec : PrimrecPred (fun p : (ℕ × ℕ) × ℕ => T₁ p.1.1 p.1.2 p.2) :=
  by
  apply Primrec.eq.comp
  · exact
      Code.primrec_evaln.comp
        (((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
              ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.fst))).pair
          (Primrec.snd.comp Primrec.fst))
  · exact Primrec.option_some.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))

theorem U_primrec : Primrec U :=
  Primrec.snd.comp Primrec.unpair

theorem normal_form (e x y : ℕ) : y ∈ eval e x ↔ ∃ s, T₁ e x s ∧ U s = y :=
  by
  rw [eval, Code.evaln_complete]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨Nat.pair k y, by simpa [T₁] using hk, by simp [U]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.unpair.1, hs⟩

theorem halts_iff (e x : ℕ) : (eval e x).Dom ↔ ∃ s, T₁ e x s :=
  by
  constructor
  · intro h
    obtain ⟨s, hs, _⟩ := (normal_form e x _).mp (Part.get_mem h)
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ((normal_form e x (U s)).mpr ⟨s, hs, rfl⟩).1

theorem output_unique {e x s t : ℕ} (hs : T₁ e x s) (ht : T₁ e x t) : U s = U t :=
  Part.mem_unique ((normal_form e x _).mpr ⟨s, hs, rfl⟩) ((normal_form e x _).mpr ⟨t, ht, rfl⟩)

/-- The least successful witness computes the same output as any successful witness. -/
theorem least_witness (e x : ℕ) (h : ∃ s, T₁ e x s) :
    T₁ e x (Nat.find h) ∧
      (∀ t < Nat.find h, ¬T₁ e x t) ∧ (∀ y, y ∈ eval e x ↔ U (Nat.find h) = y) :=
  by
  refine ⟨Nat.find_spec h, ?_, ?_⟩
  · intro t ht
    exact Nat.find_min h ht
  · intro y
    constructor
    · intro hy
      exact Part.mem_unique ((normal_form e x _).mpr ⟨_, Nat.find_spec h, rfl⟩) hy
    · intro hy
      exact (normal_form e x y).mpr ⟨_, Nat.find_spec h, hy⟩

/-- Kleene's least-witness equation, with the concrete coding above. -/
theorem normal_form_equation (e x : ℕ) :
    eval e x = (Nat.rfind (fun s => Part.some (decide (T₁ e x s)))).map U :=
  by
  apply Part.ext
  intro y
  rw [Part.mem_map_iff]
  constructor
  · intro hy
    obtain ⟨s, hs, _⟩ := (normal_form e x y).mp hy
    obtain ⟨ht, hmin, hout⟩ := least_witness e x ⟨s, hs⟩
    refine ⟨_, Nat.mem_rfind.mpr ?_, (hout y).mp hy⟩
    constructor
    · simpa using ht
    · intro m hm
      simpa using hmin m hm
  · rintro ⟨s, hs, hy⟩
    have hs' : T₁ e x s := by simpa using (Nat.mem_rfind.mp hs).1
    exact (normal_form e x y).mpr ⟨s, hs', hy⟩

/-- The comp Index construction in `FailureOfComposition.Kleene`. -/
def compIndex (f g : ℕ) : ℕ :=
  encode (Code.comp (ofNat Code f) (ofNat Code g))

theorem compIndex_primrec : Primrec₂ compIndex :=
  Primrec.encode.comp
    (Code.primrec₂_comp.comp ((Primrec.ofNat Code).comp Primrec.fst)
      ((Primrec.ofNat Code).comp Primrec.snd))

theorem eval_compIndex (f g x : ℕ) : eval (compIndex f g) x = (eval g x).bind (eval f) :=
  by
  simp only [eval, compIndex, Denumerable.ofNat_encode, Code.eval]
  rfl

theorem normal_form_comp (f g x z : ℕ) :
    (∃ s, T₁ (compIndex f g) x s ∧ U s = z) ↔
      ∃ y, (∃ s, T₁ g x s ∧ U s = y) ∧ (∃ t, T₁ f y t ∧ U t = z) :=
  by simp only [← normal_form, eval_compIndex, Part.mem_bind_iff]

theorem diagonalHalts_iff (d : ℕ) : FailureOfComposition.diagonalHalts d ↔ ∃ s, T₁ d d s :=
  halts_iff d d

end Kleene
end FailureOfComposition

end

end PointwiseComposition
