/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ExtensionWitnessCover.lean.
Also incorporates the shared witness argument from the upstream
OAI/Computability/DegreeRigidity/Constructibility/UniformExtensionWitnessCover.lean
under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.ForcingWitnessCollection
public import LeanPool.TuringConeRigidity.SetModels.NameValueCover

/-!
# Extension Witness Cover
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

theorem name_of_value_member (d : ZFSet.{u}) (hd : Transitive d)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) (G : Set (Conditions c))
    (x : ZFSet.{u}) (hx : x ∈ a.val G) :
    ∃ b : Name (Conditions c), b.encode (label c) ∈ d ∧ b.val G = x := by
  cases a with
  | mk ι child tag =>
    rw [Name.mem_val] at hx
    obtain ⟨i,_,hval⟩ := hx
    exact ⟨child i,names_childClosed d c hd (.mk ι child tag) ha (child i) ⟨i,rfl⟩,hval⟩

variable [Preorder (Conditions c)]

/-- One name bounds the required witnesses in every ground-generic filter
containing the chosen condition, without requiring a top condition. -/
theorem extension_witness_cover_for_condition (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (condition : Conditions c) :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → condition ∈ G.carrier →
      ∀ x ∈ a.val G.carrier,
        (∃ y ∈ genericExtensionSet M c G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier)))) →
        ∃ y ∈ N.val G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier))) := by
  obtain ⟨d,hd,hdt,had⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI ha
  obtain ⟨W,hW,hbound⟩ := forcing_witness_bound M hM hP hU hPow hS hR hI hAC hc hoM ho φ e he hd
  obtain ⟨N,hN,hcover⟩ := name_value_cover_for_condition M hM hP hU hPow hS hR hI hc hW condition
  refine ⟨N,hN,?_⟩
  intro G hG ht x hx hw
  obtain ⟨b,hbd,rfl⟩ := name_of_value_member d hdt a had G.carrier x hx
  have hb := hM d hd _ hbd
  obtain ⟨y,hy,hφ⟩ := hw
  obtain ⟨v,hv,rfl⟩ := (mem_extensionSet M c G.carrier y).mp hy
  have env (v : Name (Conditions c)) (hv : v.encode (label c) ∈ M) :
      ∀ i, (push v (push b e) i).encode (label c) ∈ M := by
    intro i
    rcases i with _ | i
    · exact hv
    rcases i with _ | i
    · exact hb
    exact he i
  have values (v : Name (Conditions c)) : (fun i => (push v (push b e) i).val G.carrier) =
      cons (v.val G.carrier) (cons (b.val G.carrier) (fun i => (e i).val G.carrier)) := by
    funext i
    rcases i with _ | i
    · rfl
    rcases i with _|i <;> rfl
  rw [← values v] at hφ
  obtain ⟨p,hp,hforce⟩ := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push v (push b e)) (env v hv)).mp hφ
  obtain ⟨w,hw,hforcew⟩ := hbound b hbd p ⟨v,hv,hforce⟩
  have hwM := hM W hW _ hw
  have hφw := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push w (push b e)) (env w hwM)).mpr ⟨p,hp,hforcew⟩
  rw [values w] at hφw
  exact ⟨w.val G.carrier,hcover G.carrier ht w hw,hφw⟩

theorem extension_witness_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c
      ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ x ∈ a.val G.carrier,
        (∃ y ∈ genericExtensionSet M c G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier)))) →
        ∃ y ∈ N.val G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val
            G.carrier))) := by
  obtain ⟨p,hp⟩ := G.nonempty
  obtain ⟨N,hN,hcover⟩ := extension_witness_cover_for_condition
    M hM hP hU hPow hS hR hI hAC hc hoM ho φ e he a ha p
  exact ⟨N,hN,hcover G hG hp⟩

end TuringRigidity.BoundedForcing

end OAI
