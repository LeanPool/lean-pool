/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/NameEvaluationGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.EvaluationNameCode
public import LeanPool.TuringConeRigidity.SetModels.NameValueCover

/-!
# Name Evaluation Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory
universe u
variable {c : ZFSet.{u}}

theorem mem_val_coverName (W : ZFSet.{u})
    (hW : ∀ x ∈ W, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (p : Conditions c) (hp : p ∈ G) (z : ZFSet.{u}) :
    z ∈ (coverName W hW p).val G ↔
      ∃ b : Name (Conditions c), b.encode (label c) ∈ W ∧ b.val G = z := by
  constructor
  · intro hz
    rw [coverName,Name.mem_val] at hz
    obtain ⟨i,_,he⟩ := hz
    exact ⟨coverChild W hW i,by rw [coverChild_code]; exact label_mem W i,he⟩
  · rintro ⟨b,hb,rfl⟩
    exact val_mem_coverName W hW G p hp b hb

variable [Top (Conditions c)]

theorem internal_name_evaluation_graph (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {V : ZFSet.{u}} (hV : V ∈ M)
    (hvalid : ∀ x ∈ V, ∃ a : Name (Conditions c), a.encode (label c) = x)
    (G : Set (Conditions c)) (htop : ⊤ ∈ G) :
    ∃ H : Name (Conditions c), H.encode (label c) ∈ M ∧ ∀ z,
      z ∈ H.val G ↔ ∃ x ∈ V, ∃ a : Name (Conditions c),
        a.encode (label c) = x ∧ z = ZFSet.pair x (a.val G) := by
  have ht := hM c hc _ (label_mem c ⊤)
  obtain ⟨B,hB,hBdef⟩ := internal_evaluation_name_codes M hM hP hU hPow hS hR hI hV ht
  have hvalidB (z : ZFSet.{u}) (hz : z ∈ B) :
      ∃ a : Name (Conditions c), a.encode (label c) = z := by
    obtain ⟨x,hx,he⟩ := (hBdef z).mp hz
    obtain ⟨a,ha⟩ := hvalid x hx
    refine ⟨orderedPairName (Name.check x) a,?_⟩
    rw [encode_orderedPairName,encode_check,ha]
    exact he
  let H := coverName B hvalidB ⊤
  have hH : H.encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS hB (singleton_mem M hM hP ht)
  refine ⟨H,hH,?_⟩
  intro z
  rw [mem_val_coverName B hvalidB G ⊤ htop]
  constructor
  · rintro ⟨b,hb,rfl⟩
    obtain ⟨x,hx,he⟩ := (hBdef _).mp hb
    obtain ⟨a,ha⟩ := hvalid x hx
    have hcode : b.encode (label c) = (orderedPairName (Name.check x) a).encode (label c) := by
      rw [encode_orderedPairName,encode_check,ha]
      exact he.symm
    have hv := Name.val_eq_of_encode_eq (label c) (label_injective c) G _ _ hcode
    rw [val_orderedPairName G htop,Name.val_check G htop] at hv
    exact ⟨x,hx,a,ha,hv⟩
  · rintro ⟨x,hx,a,ha,rfl⟩
    refine ⟨orderedPairName (Name.check x) a,?_,?_⟩
    · apply (hBdef _).mpr
      refine ⟨x,hx,?_⟩
      rw [encode_orderedPairName,encode_check,ha]
    · rw [val_orderedPairName G htop,Name.val_check G htop]

end TuringRigidity.BoundedForcing

end OAI
