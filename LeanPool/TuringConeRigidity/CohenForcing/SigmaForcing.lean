/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/SigmaForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ExtensionBasicAxioms
public import LeanPool.TuringConeRigidity.SetModels.InternalBoundedTruth

/-!
# Sigma Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

/-- Forcing for sigma formulas, with existential name codes drawn from `M`. -/
def SigmaForces (M : ZFSet.{u}) (e : ℕ → Name (Conditions c)) : SigmaFormula → Conditions c → Prop
  | .bounded φ, p => Forces e φ p
  | .existsSet φ, p => ∃ a : Name (Conditions c), a.encode (label c) ∈ M ∧ SigmaForces M (push a
    e) φ p

theorem sigma_mono (M : ZFSet.{u}) (φ : SigmaFormula) (e : ℕ → Name (Conditions c))
    {p q : Conditions c} (hqp : q ≤ p) (h : SigmaForces M e φ p) : SigmaForces M e φ q := by
  induction φ generalizing e with
  | bounded φ => exact forces_mono φ e hqp h
  | existsSet φ ih =>
    obtain ⟨a,ha,hf⟩ := h
    exact ⟨a,ha,ih _ hf⟩

theorem internal_sigma_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M) :
    φ.Realize (genericExtensionSet M c G.carrier) (fun i => (e i).val G.carrier) ↔
      ∃ p ∈ G.carrier, SigmaForces M e φ p := by
  induction φ generalizing e with
  | bounded φ =>
    exact (φ.absolute _ (genericExtensionSet_transitive M c hM G.carrier) _
      (fun i => (mem_extensionSet M c G.carrier _).mpr ⟨e i,he i,rfl⟩)).trans
      (internal_bounded_truth M hM hP hU hPow hS hR hI hc hoM ho G hG φ e he)
  | existsSet φ ih =>
    have hepush (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
        ∀ i, (push a e i).encode (label c) ∈ M := by
      intro i
      cases i with
      | zero => exact ha
      | succ i => exact he i
    have env (a : Name (Conditions c)) : (fun i => (push a e i).val G.carrier) =
        cons (a.val G.carrier) (fun i => (e i).val G.carrier) := by
      funext i
      cases i <;> rfl
    constructor
    · rintro ⟨x,hx,hφ⟩
      obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
      rw [←env a] at hφ
      obtain ⟨p,hp,hf⟩ := (ih _ (hepush a ha)).mp hφ
      exact ⟨p,hp,a,ha,hf⟩
    · rintro ⟨p,hp,a,ha,hf⟩
      refine ⟨a.val G.carrier,(mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩,?_⟩
      rw [←env a]
      exact (ih _ (hepush a ha)).mpr ⟨p,hp,hf⟩

end TuringRigidity.BoundedForcing

end OAI
