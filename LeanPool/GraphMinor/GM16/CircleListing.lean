/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith

/-!
# Listing finite sets of points on a circle

The boundary points in XVI (8.1), Claim (4), are sorted by their
angles in one orientation. Increasing angles covering less than one
turn give the paper's notion of being listed in order. Extending a
finite list of angles supplies the sequence in XII's definition.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface
universe w
variable {S : Type w} [TopologicalSpace S]

/-- Increasing angles in a single turn list points in order on a circle.
This supplies the finite-to-infinite sequence conversion in XII's
`IsListedInOrderOn` definition, used in XVI (8.1), Claim (4). -/
theorem listedInOrderOn_of_angles {F : Set S} (φ : Circle ≃ₜ F)
    {n : ℕ} (hn : 0 < n) (ν : Fin n → S) (τ : Fin n → ℝ)
    (hMono : StrictMono τ)
    (hTurn : ∀ i, τ i < τ ⟨0, hn⟩ + 2 * Real.pi)
    (hν : ∀ i, (φ (Circle.exp (τ i))).val = ν i) :
    GM12.IsListedInOrderOn F (List.ofFn ν) := by
  let base := τ ⟨0, hn⟩ + 2 * Real.pi
  let t : ℕ → ℝ := fun k => if hk : k < n then τ ⟨k, hk⟩ else base + (k : ℝ)
  have ht : StrictMono t := by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj : j < n
      · simpa only [t, dite_eq_left hi, dite_eq_left hj] using hMono (show
        (⟨i, hi⟩ : Fin n) < ⟨j, hj⟩ from hij)
      · change (if h : i < n then τ ⟨i, h⟩ else base + (i : ℝ)) <
          (if h : j < n then τ ⟨j, h⟩ else base + (j : ℝ))
        rw [dite_eq_left hi, dite_eq_right hj]
        exact lt_of_lt_of_le (hTurn ⟨i, hi⟩) (le_add_of_nonneg_right (Nat.cast_nonneg j))
    · have hj : ¬ j < n := by omega
      dsimp only [t]
      rw [dite_eq_right hi, dite_eq_right hj]
      simpa only [add_comm] using add_lt_add_left (Nat.cast_lt.mpr hij) base
  refine ⟨φ, t, ht, ?_, ?_⟩
  · intro i hi
    rw [List.length_ofFn] at hi
    simpa only [t, dite_eq_left hi, dite_eq_left hn] using hTurn ⟨i, hi⟩
  · intro i hi
    have hin : i < n := by simpa only [List.length_ofFn] using hi
    simpa only [t, dite_eq_left hin, List.getElem_ofFn] using hν ⟨i, hin⟩

/-- An injective family of points on a circle can be put in increasing
angle order by permuting its indices. The angles lie in `(-π,π]`. -/
theorem exists_increasing_circle_angles {F : Set S} (φ : Circle ≃ₜ F)
    {n : ℕ} (ν : Fin n → S) (hν : Function.Injective ν) (hF : ∀ i, ν i ∈ F) :
    ∃ (e : Fin n → Fin n) (τ : Fin n → ℝ), Function.Bijective e ∧ StrictMono τ ∧
      (∀ i, -Real.pi < τ i ∧ τ i ≤ Real.pi) ∧
      ∀ i, (φ (Circle.exp (τ i))).val = ν (e i) := by
  classical
  let pt : Fin n → Circle := fun i => φ.symm ⟨ν i, hF i⟩
  let angle : Fin n → ℝ := fun i => Complex.arg (pt i).val
  have hEq : ∀ i, (φ (Circle.exp (angle i))).val = ν i := by
    intro i
    rw [show Circle.exp (angle i) = pt i from Circle.exp_arg (pt i)]
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨ν i, hF i⟩)
  have hAngle : Function.Injective angle := by
    intro i j hij
    exact hν ((hEq i).symm.trans ((congrArg (fun t => (φ (Circle.exp t)).val) hij).trans (hEq j)))
  let vals : Finset ℝ := Finset.univ.image angle
  have hcard : vals.card = n := by
    rw [Finset.card_image_of_injective _ hAngle, Finset.card_univ, Fintype.card_fin]
  let τ : Fin n → ℝ := vals.orderEmbOfFin hcard
  have hex : ∀ i : Fin n, ∃ j : Fin n, angle j = τ i := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (vals.orderEmbOfFin_mem hcard i)
    exact ⟨j, hj⟩
  choose e he using hex
  have heInj : Function.Injective e := by
    intro i j hij
    exact (vals.orderEmbOfFin hcard).injective ((he i).symm.trans ((congrArg angle hij).trans
      (he j)))
  refine ⟨e, τ, ⟨heInj, Finite.surjective_of_injective heInj⟩,
    (vals.orderEmbOfFin hcard).strictMono, ?_, ?_⟩
  · intro i
    rw [← he i]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  · intro i
    rw [← he i]
    exact hEq (e i)

end GraphMinor.GM16
