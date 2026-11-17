/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanDense.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanGraph

/-!
# Internal Boolean Dense
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanDense
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def basicCode (c p : ZFSet.{0}) : ZFSet.{0} := bitCode c {p}

theorem below_lower (c U : ZFSet.{0}) : Lower c (CohenInternalDecision.below c U) := by
  intro p hp q hq hpq
  obtain ⟨_,r,hr,hrp⟩ := ZFSet.mem_sep.mp hp
  exact ZFSet.mem_sep.mpr ⟨hq,r,hr,fun z hz => hpq (hrp hz)⟩

theorem mem_basicCode (c p : ZFSet.{0}) (hp : p ∈ c) : p ∈ basicCode c p := by
  apply subset_regular c _ (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c {p})
  exact ZFSet.mem_sep.mpr ⟨hp,p,ZFSet.mem_singleton.mpr rfl,fun _ h => h⟩

theorem basicCode_le_iff (c p U : ZFSet.{0}) (hp : p ∈ c) (hU : IsCode c U) :
    basicCode c p ⊆ U ↔ p ∈ U := by
  constructor
  · intro h; exact h (mem_basicCode c p hp)
  · intro hpU
    apply (regular_le_iff c _ U (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c {p}) hU).mpr
    intro q hq
    obtain ⟨hqc,r,hr,hrq⟩ := ZFSet.mem_sep.mp hq
    have hrp := ZFSet.mem_singleton.mp hr
    subst r
    exact code_lower c U hU p hpU q hqc hrq

theorem basicCode_mem (M c p : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hp : p ∈ c) : basicCode c p ∈ M :=
  bitCode_mem M c _ hM hT hc (singleton_mem M hM hT.pairing (hM c hc p hp))

def DenseCodes (A D : ZFSet.{0}) : Prop :=
  ∀ U ∈ A, U ≠ ∅ → ∃ V ∈ D, V ∈ A ∧ V ≠ ∅ ∧ V ⊆ U

theorem dense_preimage (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) : Dense {p : Conditions c | label c p ∈ ZFSet.sUnion D} := by
  classical
  intro p
  let b := basicCode c (label c p)
  have hbM : b ∈ M := basicCode_mem M c _ hM hT hc (label_mem c p)
  have hbc : IsCode c b := regular_isCode c _
  have hpb : label c p ∈ b := mem_basicCode c _ (label_mem c p)
  have hb0 : b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
  have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
  obtain ⟨V,hVD,hVA,hV0,hVP⟩ := hD _ hPA (project_nonempty c A b hbc.1 hb0)
  have hVc := ((hB V).mp (hA.1 hVA)).2
  have hex : ∃ q ∈ V, label c p ⊆ q := by
    by_contra hn
    have hpN : label c p ∈ neg c V := ZFSet.mem_sep.mpr
      ⟨label_mem c p,fun q hq hpq => hn ⟨q,hq,hpq⟩⟩
    have hbN : b ⊆ neg c V := (basicCode_le_iff c _ _ (label_mem c p) (neg_isCode c V hVc)).mpr hpN
    have hPN := (project_le_iff c A b _ hbc.1 (hA.2.1 V hVA)).mpr hbN
    apply hV0
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      have hqN := hPN (hVP hq)
      exact False.elim ((ZFSet.mem_sep.mp hqN).2 q hq (fun _ h => h))
    · exact fun h => False.elim (ZFSet.notMem_empty q h)
  obtain ⟨q,hq,hpq⟩ := hex
  obtain ⟨q,rfl⟩ := label_surjective c (hVc.1 hq)
  exact ⟨q,hpq,ZFSet.mem_sUnion.mpr ⟨V,hVD,hq⟩⟩

theorem ground_meets_dense_codes (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M) (hDM : D ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) (G : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) : ∃ U ∈ D, Hit G U := by
  obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion D) (union_mem M hM hT.union hDM)
    (dense_preimage M c B Q A D hM hT hc hBM hAM hB hQ hA hD)
  obtain ⟨U,hU,hpU⟩ := ZFSet.mem_sUnion.mp hpD
  exact ⟨U,hU,p,hp,hpU⟩

end TuringRigidity.InternalBooleanDense

end OAI
