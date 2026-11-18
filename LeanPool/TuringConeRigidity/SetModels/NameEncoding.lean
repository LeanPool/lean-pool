/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameEncoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RecursiveNames

/-!
# Name Encoding
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RecursiveNames
open Set
universe u
variable {P : Type u}

/-- Recursively encode a forcing name as the set of pairs of encoded children and condition
labels. -/
noncomputable def Name.encode (label : P → ZFSet.{u}) : Name P → ZFSet.{u}
  | .mk _ child tag => ZFSet.range (fun i => ZFSet.pair (encode label (child i)) (label (tag i)))

theorem Name.val_eq_of_encode_eq (label : P → ZFSet.{u})
    (hl : Function.Injective label) (G : Set P) (τ σ : Name P)
    (he : encode label τ = encode label σ) : val G τ = val G σ := by
  induction τ generalizing σ with
  | mk ι child tag ih =>
    cases σ with
    | mk κ other otag =>
      apply ZFSet.ext
      intro x
      rw [mem_val,mem_val]
      constructor
      · rintro ⟨i,hi,hx⟩
        have hm : ZFSet.pair (encode label (child i)) (label (tag i)) ∈
            encode label (.mk ι child tag) := ZFSet.mem_range_self i
        rw [he] at hm
        obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hm
        obtain ⟨hc,ht⟩ := ZFSet.pair_inj.mp hj
        refine ⟨j,by simpa only [hl ht] using hi,?_⟩
        exact (ih i (other j) hc.symm).symm.trans hx
      · rintro ⟨j,hj,hx⟩
        have hm : ZFSet.pair (encode label (other j)) (label (otag j)) ∈
            encode label (.mk κ other otag) := ZFSet.mem_range_self j
        rw [←he] at hm
        obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hm
        obtain ⟨hc,ht⟩ := ZFSet.pair_inj.mp hi
        refine ⟨i,by simpa only [hl ht] using hj,?_⟩
        exact (ih i (other j) hc).trans hx

/-- Set codes that arise from recursively encoding a forcing name with the supplied condition
labels. -/
def EncodedName (label : P → ZFSet.{u}) := {x : ZFSet.{u} // ∃ τ, Name.encode label τ = x}

/-- Regard a name as its set code together with the encoding witness. -/
noncomputable def Name.toEncoded (label : P → ZFSet.{u}) (τ : Name P) : EncodedName label :=
  ⟨Name.encode label τ,τ,rfl⟩

/-- Interpret an encoded name by choosing a name with that code and evaluating it in `G`. -/
noncomputable def EncodedName.val {label : P → ZFSet.{u}}
    (G : Set P) (τ : EncodedName label) : ZFSet.{u} := Name.val G τ.property.choose

theorem Name.val_toEncoded (label : P → ZFSet.{u}) (hl : Function.Injective label)
    (G : Set P) (τ : Name P) : (τ.toEncoded label).val G = τ.val G := by
  apply Name.val_eq_of_encode_eq label hl G
  exact (τ.toEncoded label).property.choose_spec

theorem encoded_check [Top P] (label : P → ZFSet.{u}) (hl : Function.Injective label)
    (G : Set P) (hG : ⊤ ∈ G) (x : ZFSet.{u}) :
    ((Name.check x : Name P).toEncoded label).val G = x := by
  rw [Name.val_toEncoded label hl,Name.val_check G hG]

end TuringRigidity.RecursiveNames

end OAI
