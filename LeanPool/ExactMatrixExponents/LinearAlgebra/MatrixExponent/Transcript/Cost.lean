/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Seats
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transcript.Route.Packets
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Encoding processor records without multiplicity

A transcript need only satisfy the aggregate and pointwise bounds when
it is accepted. The unused slots have prescribed contents.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Transcript
open Finset

variable {P V k : ℕ} {R : Type}

open Classical in
/-- The indexed operation `Fin.lastCases none (fun p => some (p, x p))`. -/
def readRecord (x : Fin P → R) : Fin (P + 1) → Option (Fin P × R) :=
  Fin.lastCases none (fun p => some (p, x p))

open Classical in
/-- In the case `none`, this construction gives `Fin.last P`. -/
def name : Option (Fin P × R) → Fin (P + 1)
  | none => Fin.last P
  | some (p, _) => p.castSucc

open Classical in
@[simp] theorem name_read (x : Fin P → R) (p : Fin (P + 1)) : name (readRecord x p) = p := by
  induction p using Fin.lastCases <;> simp [name, readRecord]

open Classical in
/-- Indexes the records by the coordinates of `Slot P V k → Option (Fin P × R)`. -/
abbrev Records (P V k : ℕ) (R : Type) := Slot P V k → Option (Fin P × R)

open Classical in
/-- All occupied positions have the right charge and payload. An inactive
position carries no payload. -/
def Encodes (c : Fin P → R → ℕ) (x : Fin P → R) (y : Records P V k R) : Prop :=
  (∀ j : Fin (k + 1), OrderedSeats (bucket (fun p => c p (x p)) j.val)
    (fun s => name (y ⟨j, s⟩))) ∧
  ∀ s, y s = readRecord x (name (y s))

open Classical in
theorem unique_encoding (c : Fin P → R → ℕ) (x : Fin P → R)
    (hp : ∀ i, 0 < c i (x i)) (hs : ∑ i, c i (x i) ≤ V) :
    ∃! y : Records P V k R, Encodes c x y := by
  have h (j : Fin (k + 1)) := unique_seats _ (bucket_capacity hp hs j)
  let y : Records P V k R := fun s => readRecord x ((h s.1).choose s.2)
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · intro j; simpa only [y, name_read] using (h j).choose_spec.1
  · intro s; simp only [y, name_read]
  · intro z hz
    funext ⟨j, t⟩
    rw [hz.2]
    have he := (h j).choose_spec.2 _ (hz.1 j)
    exact congrArg (readRecord x) (congrFun he t)

open Classical in
theorem Encodes.covers {c : Fin P → R → ℕ} {x : Fin P → R} {y : Records P V k R}
    (h : Encodes c x y) (hc : ∀ i, c i (x i) ≤ 2 ^ k) (p : Fin P) :
    ∃ s : Slot P V k, y s = some (p, x p) := by
  have hp : Nat.clog 2 (c p (x p)) ≤ k := (Nat.clog_le_iff_le_pow (by decide)).mpr (hc p)
  let j : Fin (k + 1) := ⟨_, Nat.lt_succ_of_le hp⟩
  obtain ⟨i, hi⟩ := ((h.1 j).2.1 p).mpr (by simp [bucket, j])
  refine ⟨⟨j, i⟩, ?_⟩
  change name (y ⟨j, i⟩) = p.castSucc at hi
  rw [h.2, hi]; simp [readRecord]

open Classical in
theorem Encodes.unique {c : Fin P → R → ℕ} {x z : Fin P → R} {y : Records P V k R}
    (h : Encodes c x y) (hc : ∀ i, c i (x i) ≤ 2 ^ k) (hz : Encodes c z y) : x = z := by
  funext p
  obtain ⟨s, he⟩ := h.covers hc p
  have ht := hz.2 s
  simpa [he, name, readRecord] using ht

open Classical in
/-- A bijective witness relation preserves a weighted sum in all
characteristics. Rejected configurations can have arbitrary lengths. -/
theorem encode_sum {F : Type} [AddCommMonoid F] [Fintype R]
    (c : Fin P → R → ℕ) (good : (Fin P → R) → Prop) (f : (Fin P → R) → F)
    (g : Records P V k R → F)
    (bounds : ∀ x, good x → (∀ i, 0 < c i (x i) ∧ c i (x i) ≤ 2 ^ k) ∧ ∑ i, c i (x i) ≤ V)
    (match_value : ∀ x y, good x → Encodes c x y → g y = f x)
    (reject : ∀ y, (¬∃ x, good x ∧ Encodes c x y) → g y = 0) :
    ∑ y, g y = ∑ x, if good x then f x else 0 := by
  have row (y : Records P V k R) :
      g y = ∑ x, if good x ∧ Encodes c x y then f x else 0 := by
    by_cases h : ∃ x, good x ∧ Encodes c x y
    · obtain ⟨x, hx, he⟩ := h
      have hu (z) : good z ∧ Encodes c z y ↔ z = x :=
        ⟨fun hz => (he.unique (fun i => ((bounds x hx).1 i).2) hz.2).symm,
          fun ez => ez.symm ▸ And.intro hx he⟩
      simp only [hu, sum_ite_eq', mem_univ, ite_true]
      exact match_value x y hx he
    · rw [reject y h]
      simp only [not_exists] at h
      simp only [h, ite_false, sum_const_zero]
  simp_rw [row]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : good x
  · obtain ⟨hp, hs⟩ := bounds x hx
    obtain ⟨y, hy, hu⟩ := unique_encoding (k := k) c x (fun i => (hp i).1) hs
    have hz (z) : Encodes c x z ↔ z = y := ⟨hu z, fun e => e.symm ▸ hy⟩
    simp only [hx, true_and, hz, sum_ite_eq', mem_univ, ite_true]
  · simp only [hx, false_and, ite_false, sum_const_zero]

end MatrixMultiplicationAllFields.MatrixExponent.Transcript
end
