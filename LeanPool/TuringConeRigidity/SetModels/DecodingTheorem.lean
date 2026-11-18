/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/DecodingTheorem.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RelationPresentation
public import LeanPool.TuringConeRigidity.Computability.OracleJump

/-!
# Decoding Theorem
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.DecodingTheorem
open IndexPresentation IndexTuples ArithmeticHierarchy RelationPresentation
open SetCoding RelationCoding BoundedDecoding OracleJump

/-- A tuple of valid presentation indices whose represented degrees satisfy the relation code. -/
def Presented {n} (Y : Oracle) (p : RelationCode n) (t : ℕ) : Prop :=
  (∀ i : Fin n, Dom Y (entry i.val t)) ∧ p.Holds (fun i => value Y (entry i.val t))

theorem presentation_exact {n} (Y : Oracle) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) (v : Fin n → Degree) :
    p.Holds v ↔ ∃ t, Presented Y p t ∧ ∀ i, value Y (entry i.val t) = v i := by
  constructor
  · intro hv
    have hb : ∀ i, v i ≤ degree Y := by
      obtain ⟨c,hc,_⟩ := hv
      exact fun i => (graph_bounded (hp.1 i) (hc i)).1
    choose e he hev using (fun i => value_surjective Y (v i) (hb i))
    obtain ⟨t,ht⟩ := tuple_surjective e
    have hv' : (fun i : Fin n => value Y (entry i.val t)) = v := by
      funext i
      rw [ht i, hev i]
    exact ⟨t, ⟨fun i => (ht i) ▸ he i, hv' ▸ hv⟩, fun i => congrFun hv' i⟩
  · rintro ⟨t,⟨_,ht⟩,hv⟩
    exact (funext hv) ▸ ht

theorem sigma5_normal_form {Y P} (h : Sigma Y 5 P) :
    ∃ M : ℕ → Prop, RecursivePred Y M ∧ ∀ x,
      P x ↔ ∃ a, ∀ b, ∃ c, ∀ d, ∃ e,
        M (Nat.pair (Nat.pair (Nat.pair (Nat.pair (Nat.pair x a) b) c) d) e) := by
  obtain ⟨A,hA,eA⟩ := h
  obtain ⟨B,hB,eB⟩ := hA
  obtain ⟨C,hC,eC⟩ := hB
  obtain ⟨D,hD,eD⟩ := hC
  obtain ⟨M,hM,eM⟩ := hD
  refine ⟨M,hM,fun x => ?_⟩
  simp only [eA, eB, eC, eD, eM, Quant, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte]

theorem decoding_theorem {n} (Y : Oracle) (R : Set (Fin n → Degree)) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) (hcode : ∀ v, p.Holds v ↔ v ∈ R) :
    ∃ P : ℕ → Prop, Sigma Y 5 P ∧ RecursivePred (iterate Y 5) P ∧
      ∀ v, v ∈ R ↔ ∃ t, P t ∧ ∀ i, value Y (entry i.val t) = v i := by
  have h := sigma5_decoding Y p hp
  refine ⟨Presented Y p, h, form_recursive h, fun v => ?_⟩
  exact (hcode v).symm.trans (presentation_exact Y p hp v)

end TuringRigidity.DecodingTheorem

end OAI
