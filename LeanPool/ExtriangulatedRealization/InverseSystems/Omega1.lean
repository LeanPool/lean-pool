/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The first uncountable ordinal as an index type

We index inverse systems by `ω₁.ToType`, the well-ordered type of countable ordinals. Its initial
segments are countable, every countable subset is bounded, it has no largest element, and it
has cardinality `ℵ₁`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open Ordinal Cardinal

universe u

/-- The countable ordinals, as a well-ordered type in universe `u`. -/
abbrev Omega1 : Type u := (ω₁ : Ordinal.{u}).ToType

namespace Omega1

/-- The ordinal of an element of `Omega1`. -/
noncomputable def ord (x : Omega1.{u}) : Ordinal.{u} := (ToType.mk.symm x : Set.Iio ω₁)

lemma ord_lt (x : Omega1.{u}) : ord x < ω₁ := (ToType.mk.symm x).2

lemma ord_strictMono : StrictMono ord.{u} := fun _ _ h => ToType.mk.symm.strictMono h

lemma ord_le_ord {x y : Omega1.{u}} : ord x ≤ ord y ↔ x ≤ y := ord_strictMono.le_iff_le

lemma ord_injective : Function.Injective ord.{u} := ord_strictMono.injective

/-- The element of `Omega1` with a given countable ordinal. -/
noncomputable def ofOrd (o : Ordinal.{u}) (h : o < ω₁) : Omega1.{u} := ToType.mk ⟨o, h⟩

lemma ord_ofOrd (o : Ordinal.{u}) (h : o < ω₁) : ord (ofOrd o h) = o := by
  simp [ord, ofOrd]

/-- Initial segments are countable. -/
lemma countable_Iio (x : Omega1.{u}) : (Set.Iio x).Countable := by
  have h := (countable_Iio_of_lt_omega_one (ord_lt x)).preimage ord_injective
  exact h.mono fun y hy => ord_strictMono hy

/-- Every countable subset is bounded above. -/
lemma bddAbove_of_countable {S : Set Omega1.{u}} (hS : S.Countable) : BddAbove S := by
  have := hS.to_subtype
  let f : S → Ordinal.{u} := fun s => ord s.1
  have hsup : ⨆ s, f s < ω₁ := Ordinal.iSup_lt_omega_one fun s => ord_lt s.1
  refine ⟨ofOrd _ hsup, fun s hs => ?_⟩
  rw [← ord_le_ord, ord_ofOrd]
  exact Ordinal.le_iSup f ⟨s, hs⟩

/-- There is no largest element. -/
lemma exists_gt (x : Omega1.{u}) : ∃ y, x < y := by
  have h : ord x + 1 < ω₁ := (isSuccLimit_omega 1).add_one_lt (ord_lt x)
  refine ⟨ofOrd _ h, ?_⟩
  rw [← ord_strictMono.lt_iff_lt, ord_ofOrd]
  exact Order.lt_add_one_iff.mpr le_rfl

instance : NoMaxOrder Omega1.{u} := ⟨exists_gt⟩

instance : Nonempty Omega1.{u} := ⟨ofOrd 0 (omega_pos 1)⟩

/-- `Omega1` has cardinality `ℵ₁`. -/
lemma mk_eq : #Omega1.{u} = ℵ₁ := by
  rw [mk_toType, ← ord_aleph, card_ord]

/-- `Omega1` is uncountable. -/
lemma not_countable : ¬ Countable Omega1.{u} := by
  rw [← Cardinal.mk_le_aleph0_iff, mk_eq]
  exact not_le.mpr aleph0_lt_aleph_one

end Omega1

end ExtriangulatedRealization
