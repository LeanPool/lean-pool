/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Cantor
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Finite-coordinate counting and fair-coin probabilities

An injective choice of finitely many input coordinates has the uniform law on
binary assignments. Consequently the probability of any event on those
coordinates is its finite cardinality times the probability of one assignment.
The same statements are transported to `ZMod 2`, so finite linear-algebra counts
can be used directly with the concrete measure `Klr.fairCoin`.
-/

@[expose] public section

namespace Klr.FiniteMeasure

open MeasureTheory
open scoped ENNReal

variable {ι : Type*}

/-- Read the finite collection of coordinates specified by `e`. -/
def coordinateBits (e : ι → ℕ) (X : Cantor) : ι → Bool := fun i => X (e i)

theorem measurable_coordinateBits (e : ι → ℕ) : Measurable (coordinateBits e) := by
  unfold coordinateBits
  fun_prop

/-- Distinct coordinates have precisely the product fair-bit law. -/
theorem fairCoin_map_coordinates [Fintype ι] (e : ι → ℕ) (he : Function.Injective e) :
    fairCoin.map (coordinateBits e) = Measure.pi (fun _ : ι => fairBit) := by
  unfold fairCoin coordinateBits
  rw [Measure.map_infinitePi_infinitePi_of_inj he, Measure.infinitePi_eq_pi]

/-- Every assignment to the finite coordinates has probability `2⁻|ι|`. -/
theorem fairCoin_coordinate_singleton [Fintype ι] (e : ι → ℕ) (he : Function.Injective e)
    (b : ι → Bool) :
    fairCoin {X | coordinateBits e X = b} = (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
  change fairCoin (coordinateBits e ⁻¹' {b}) = _
  rw [← Measure.map_apply (measurable_coordinateBits e) (measurableSet_singleton b),
    fairCoin_map_coordinates e he, Measure.pi_singleton]
  simp

/-- The fair product measure on a finite set assigns equal mass to every point. -/
theorem finite_product_apply [Fintype ι] (S : Set (ι → Bool)) :
    (Measure.pi (fun _ : ι => fairBit)) S =
      (Nat.card S : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  let _ := Fintype.ofFinite S
  calc
    (Measure.pi (fun _ : ι => fairBit)) S =
        ∑ b ∈ S.toFinite.toFinset, (Measure.pi (fun _ : ι => fairBit)) {b} := by
      rw [sum_measure_singleton, S.toFinite.coe_toFinset]
    _ = (S.toFinite.toFinset.card : ℝ≥0∞) *
        (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by simp [Measure.pi_singleton]
    _ = _ := by rw [S.toFinite.card_toFinset, Nat.card_eq_fintype_card]

/-- Probability of any event depending on finitely many distinct coordinates. -/
theorem fairCoin_coordinate_event [Fintype ι] (e : ι → ℕ) (he : Function.Injective e)
    (S : Set (ι → Bool)) :
    fairCoin {X | coordinateBits e X ∈ S} =
      (Nat.card S : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
  change fairCoin (coordinateBits e ⁻¹' S) = _
  rw [← Measure.map_apply (measurable_coordinateBits e) S.toFinite.measurableSet,
    fairCoin_map_coordinates e he, finite_product_apply]

/-- The canonical identification of a bit with its value in the two-element field. -/
def boolEquivF2 : Bool ≃ ZMod 2 :=
  finTwoEquiv.symm.trans (ZMod.finEquiv 2).toEquiv

@[simp] theorem boolEquivF2_false : boolEquivF2 false = 0 := rfl

@[simp] theorem boolEquivF2_true : boolEquivF2 true = 1 := rfl

/-- Apply the bit/field identification to every coordinate. -/
def assignmentEquivF2 : (ι → Bool) ≃ (ι → ZMod 2) :=
  Equiv.piCongrRight (fun _ => boolEquivF2)

/-- Finite coordinates of a binary input, regarded as elements of `ZMod 2`. -/
def coordinateValues (e : ι → ℕ) (X : Cantor) : ι → ZMod 2 :=
  assignmentEquivF2 (coordinateBits e X)

@[simp] theorem coordinateValues_apply (e : ι → ℕ) (X : Cantor) (i : ι) :
    coordinateValues e X i = boolEquivF2 (X (e i)) := rfl

theorem measurableSet_coordinate_event_f2 [Finite ι] (e : ι → ℕ)
    (S : Set (ι → ZMod 2)) :
    MeasurableSet {X | coordinateValues e X ∈ S} := by
  exact (assignmentEquivF2 ⁻¹' S).toFinite.measurableSet.preimage
    (measurable_coordinateBits e)

/-- Linear-algebraic assignment sets have exactly their finite counting probabilities. -/
theorem fairCoin_coordinate_event_f2 [Fintype ι] (e : ι → ℕ) (he : Function.Injective e)
    (S : Set (ι → ZMod 2)) :
    fairCoin {X | coordinateValues e X ∈ S} =
      (Nat.card S : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by
  change fairCoin {X | coordinateBits e X ∈ assignmentEquivF2 ⁻¹' S} = _
  rw [fairCoin_coordinate_event e he]
  have hc : Nat.card (assignmentEquivF2 ⁻¹' S) = Nat.card S :=
    Nat.card_congr (assignmentEquivF2.subtypeEquiv (fun _ => Iff.rfl))
  rw [hc]

/-- A finite cardinality ratio by `2^r` gives the same exact fair-coin probability ratio. -/
theorem fairCoin_coordinate_factor_of_card [Finite ι] (e : ι → ℕ)
    (he : Function.Injective e)
    (A B : Set (ι → ZMod 2)) (r : ℕ)
    (hcard : Nat.card A * 2 ^ r = Nat.card B) :
    fairCoin {X | coordinateValues e X ∈ A} =
      (1 / 2 : ℝ≥0∞) ^ r * fairCoin {X | coordinateValues e X ∈ B} := by
  let _ := Fintype.ofFinite ι
  rw [fairCoin_coordinate_event_f2 e he, fairCoin_coordinate_event_f2 e he]
  have hc : (Nat.card A : ℝ≥0∞) * (2 : ℝ≥0∞) ^ r = Nat.card B := by
    exact_mod_cast hcard
  rw [← hc]
  have hcancel : (1 / 2 : ℝ≥0∞) ^ r * (2 : ℝ≥0∞) ^ r = 1 := by
    rw [← mul_pow]
    rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc
    (Nat.card A : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ Fintype.card ι =
        (Nat.card A : ℝ≥0∞) *
          ((1 / 2 : ℝ≥0∞) ^ r * (2 : ℝ≥0∞) ^ r) *
          (1 / 2 : ℝ≥0∞) ^ Fintype.card ι := by rw [hcancel, mul_one]
    _ = _ := by ac_rfl

/-- The singleton formula specialized to a finite set of input positions. -/
theorem fairCoin_restrict_singleton (G : Finset ℕ) (b : G → Bool) :
    fairCoin {X : Cantor | (fun i : G => X i) = b} =
      (1 / 2 : ℝ≥0∞) ^ G.card := by
  change fairCoin {X | coordinateBits (fun i : G => (i : ℕ)) X = b} = _
  simpa using
    fairCoin_coordinate_singleton (fun i : G => (i : ℕ)) Subtype.val_injective b

/-- The counting formula specialized to a finite set of input positions. -/
theorem fairCoin_restrict_event (G : Finset ℕ) (S : Set (G → Bool)) :
    fairCoin {X : Cantor | (fun i : G => X i) ∈ S} =
      (Nat.card S : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ G.card := by
  change fairCoin {X | coordinateBits (fun i : G => (i : ℕ)) X ∈ S} = _
  simpa using
    fairCoin_coordinate_event (fun i : G => (i : ℕ)) Subtype.val_injective S

private def splitAssignmentEquiv {κ : Type*} (S : Set (ι → Bool))
    (T : Set (κ → Bool)) :
    {z : ι ⊕ κ → Bool // (fun i => z (.inl i)) ∈ S ∧ (fun j => z (.inr j)) ∈ T} ≃
      S × T where
  toFun z := (⟨fun i => z.val (.inl i), z.property.1⟩,
    ⟨fun j => z.val (.inr j), z.property.2⟩)
  invFun z := ⟨Sum.elim z.1.val z.2.val, z.1.property, z.2.property⟩
  left_inv z := by
    apply Subtype.ext
    funext k
    cases k <;> rfl
  right_inv z := by
    rcases z with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    rfl

/-- Events on disjoint finite collections of fair-coin coordinates are independent. -/
theorem fairCoin_coordinate_events_disjoint {κ : Type*} [Finite ι] [Finite κ]
    (e : ι → ℕ) (he : Function.Injective e) (f : κ → ℕ) (hf : Function.Injective f)
    (hdisjoint : ∀ i j, e i ≠ f j) (S : Set (ι → Bool)) (T : Set (κ → Bool)) :
    fairCoin {X | coordinateBits e X ∈ S ∧ coordinateBits f X ∈ T} =
      fairCoin {X | coordinateBits e X ∈ S} *
        fairCoin {X | coordinateBits f X ∈ T} := by
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite κ
  let U : Set (ι ⊕ κ → Bool) :=
    {z | (fun i => z (.inl i)) ∈ S ∧ (fun j => z (.inr j)) ∈ T}
  change fairCoin {X | coordinateBits (Sum.elim e f) X ∈ U} = _
  rw [fairCoin_coordinate_event _ (he.sumElim hf hdisjoint),
    fairCoin_coordinate_event e he, fairCoin_coordinate_event f hf]
  have hcard : Nat.card U = Nat.card S * Nat.card T := by
    exact (Nat.card_congr (splitAssignmentEquiv S T)).trans (Nat.card_prod S T)
  rw [hcard, Nat.cast_mul, Fintype.card_sum, pow_add]
  ac_rfl

/-- Independence of finite disjoint coordinate events, in binary-field coordinates. -/
theorem fairCoin_coordinate_events_disjoint_f2 {κ : Type*} [Finite ι] [Finite κ]
    (e : ι → ℕ) (he : Function.Injective e) (f : κ → ℕ) (hf : Function.Injective f)
    (hdisjoint : ∀ i j, e i ≠ f j)
    (S : Set (ι → ZMod 2)) (T : Set (κ → ZMod 2)) :
    fairCoin {X | coordinateValues e X ∈ S ∧ coordinateValues f X ∈ T} =
      fairCoin {X | coordinateValues e X ∈ S} *
        fairCoin {X | coordinateValues f X ∈ T} :=
  fairCoin_coordinate_events_disjoint e he f hf hdisjoint
    (assignmentEquivF2 ⁻¹' S) (assignmentEquivF2 ⁻¹' T)

end Klr.FiniteMeasure
