/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformOrdinalStageName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformSigmaHierarchy
public import LeanPool.TuringConeRigidity.Constructibility.UniformSigmaUniqueName
public import LeanPool.TuringConeRigidity.Constructibility.UniformOwnRealsName

/-!
# Uniform Ordinal Stage Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
open AtomicForcing BoundedForcing BoundedDefinability SetModelFunctions
universe u

theorem uniform_named_stage (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = stage (groundReals (genericExtensionSet M c G.carrier))
          (a.val G.carrier) := by
  obtain ⟨p,d,hd,hp⟩ := stageCertificate_uniformSigma M hM hT
  obtain ⟨S,hS,hSv⟩ := uniform_zero_stage_name M hM hT hc hoM ho
  let e : ℕ → Name (Conditions c) := push S (fun n => Name.check (d n))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    cases i with
    | zero => exact hS
    | succ i =>
      exact encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
        hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc (hd i)
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then
    (if i / 2 = 0 then 0 else if i / 2 = 1 then 1 else 2) else i/2+3
  apply uniform_sigma_unique_name M hM hT hc hoM ho (p.rename r) a ha e he
    (fun g => stage (groundReals (genericExtensionSet M c g)) (a.val g))
  intro G hG ht
  let E := genericExtensionSet M c G.carrier
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  have hR := groundReals_mem E hE hTE
  have haE : a.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
  have hSE : S.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨S,hS,rfl⟩
  refine ⟨stage_mem E _ _ hE hTE hR haE,?_⟩
  intro y hy
  have heval : (fun i => (e i).val G.carrier) = cons (S.val G.carrier) d := by
    funext i; cases i with
    | zero => rfl
    | succ i => exact Name.val_check G.carrier ht (d i)
  rw [heval,SigmaFormula.realize_rename]
  let v := cons y (cons (a.val G.carrier) (fun _ => S.val G.carrier))
  have hv : ∀ i, v i ∈ E := by
    intro i
    rcases i with _ | _ | i
    · exact hy
    · exact haE
    · exact hSE
  have hr : cons y (cons (a.val G.carrier) (cons (S.val G.carrier) d)) ∘ r = mix v d := by
    apply parity_ext
    · intro n
      rcases n with _|_|n
      · rfl
      · rfl
      · simp [r,v,Function.comp_apply,mix,cons,show ¬ 2 * (n+1+1) ≤ 1 by omega]
    · intro n; simp [r,Function.comp_apply,mix,Nat.add_div]
  change p.Realize E (cons y (cons (a.val G.carrier) (cons (S.val G.carrier) d)) ∘ r) ↔ _
  rw [hr,hp E hE hTE hME v hv]
  change (∃ d' ∈ E, ∃ f ∈ E, ∃ t ∈ E, a.val G.carrier ∈ d' ∧
    HierarchyGraph E (S.val G.carrier) d' t f ∧
      StageStep (S.val G.carrier) f t (a.val G.carrier) y) ↔ _
  rw [hSv G hG ht,stage_zero]
  exact stageCertificate_iff E _ _ y hE hTE hR haE

theorem uniform_ordinal_level_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (δ : Ordinal.{u}) (hδ : δ.toZFSet ∈ M) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = level (groundReals (genericExtensionSet M c G.carrier)) δ := by
  have ha := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hδ
  obtain ⟨A,hA,hAv⟩ := uniform_named_stage M hM hT hc hoM ho (Name.check δ.toZFSet) ha
  refine ⟨A,hA,?_⟩
  intro G hG ht
  simpa only [Name.val_check G.carrier ht,level] using hAv G hG ht

end TuringRigidity.RelativeConstructible

end OAI
