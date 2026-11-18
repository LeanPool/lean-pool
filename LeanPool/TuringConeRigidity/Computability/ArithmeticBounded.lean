/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticBounded.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticHierarchy
public import LeanPool.TuringConeRigidity.Syntax.BoundedRecursive

/-!
# Arithmetic Bounded
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open Encodable UniformOracle BoundedRecursive

theorem recursive_bounded_all {Y P} (h : RecursivePred Y P) {b : ℕ → ℕ} (hb : Primrec b) :
    RecursivePred Y (fun x => ∀ i < b x, P (Nat.pair x i)) := by
  classical
  let f : ℕ → ℕ := fun x => if P x then 1 else 0
  have hr := total_comp (allBelow_recursive (f := f) h)
    (total_primrec (Primrec₂.natPair.comp Primrec.id hb))
  apply hr.of_eq
  intro x
  simp only [Nat.unpair_pair, id_eq]
  have hs := allBelow_spec f x (b x)
  have hbin := allBelow_binary f x (b x)
  by_cases hp : ∀ i < b x, P (Nat.pair x i)
  · have hv : allBelow f x (b x) = 1 := hs.mpr (fun i hi => by simp [f,hp i hi])
    rw [ite_eq_left hp,hv]
  · have hn : allBelow f x (b x) ≠ 1 := by
      intro h1
      apply hp
      intro i hi
      have hx := (hs.mp h1) i hi
      simpa [f] using hx
    have hz : allBelow f x (b x) = 0 := hbin.resolve_right hn
    rw [ite_eq_right hp,hz]

/-- Read an entry from a coded finite natural-number list, using zero outside its range. -/
def item (t i : ℕ) : ℕ := ((decode (α := List ℕ) t).getD []).getD i 0

theorem item_primrec : Primrec₂ item :=
  (Primrec.list_getD 0).comp
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.fst) (Primrec.const [])) Primrec.snd

theorem exists_items (b : ℕ) (P : ℕ → ℕ → Prop) :
    (∀ i < b, ∃ a, P i a) ↔ ∃ t, ∀ i < b, P i (item t i) := by
  classical
  constructor
  · intro h
    choose a ha using (fun i : Fin b => h i.val i.isLt)
    refine ⟨encode (List.ofFn a), fun i hi => ?_⟩
    simpa [item, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using ha ⟨i,hi⟩
  · rintro ⟨t,ht⟩ i hi
    exact ⟨item t i, ht i hi⟩

theorem Form.bounded_all {Y n s P} (h : Form Y n s P) {b : ℕ → ℕ} (hb : Primrec b) :
    Form Y n s (fun x => ∀ i < b x, P (Nat.pair x i)) := by
  induction n generalizing s P b with
  | zero => exact recursive_bounded_all h hb
  | succ n ih =>
    obtain ⟨Q,hQ,he⟩ := h
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    cases s with
    | false =>
      have hR := ih (hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp (f.comp f) r) (r.comp
        f)))
        (hb.comp f)
      refine ⟨_, hR, fun x => ?_⟩
      simp only [Nat.unpair_pair, Quant, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h a i hi
        exact (he _).mp (h i hi) a
      · intro h i hi
        exact (he _).mpr (fun a => h a i hi)
    | true =>
      have hR := ih (hQ.comp (Primrec₂.natPair.comp (Primrec₂.natPair.comp (f.comp f) r)
        (item_primrec.comp (r.comp f) r))) (hb.comp f)
      refine ⟨_, hR, fun x => ?_⟩
      simp only [Nat.unpair_pair, Quant, ↓reduceIte]
      exact (forall_congr' (fun i => forall_congr' (fun _ => he (Nat.pair x i)))).trans
        (exists_items (b x) (fun i a => Q (Nat.pair (Nat.pair x i) a)))

end TuringRigidity.ArithmeticHierarchy

end OAI
