/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenNiceNameConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenAntichainFamilySupport
public import LeanPool.TuringConeRigidity.SetModels.InternalPositiveNameFamily
public import LeanPool.TuringConeRigidity.SetModels.InternalNiceName

/-!
# Cohen Nice Name Construction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenNiceNameConstruction
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing CountableForcing
open CohenGroundPoset CohenAntichainSelector CohenInternalDecision InternalPositiveNameFamily
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

@[instance_reducible]
noncomputable def cohenTop (A : ZFSet.{0}) : OrderTop (Conditions (conditions A)) :=
  InternalCollapse.top (conditions A) (CohenGroundGeneric.empty_mem_conditions A)
attribute [local instance] cohenTop

theorem positive_downward (A : ZFSet.{0}) (τ : Name (Conditions (conditions A))) (n : ℕ)
    (p q : ZFSet.{0}) (hp : p ∈ positive τ n) (hq : q ∈ conditions A) (hpq : p ⊆ q) :
    q ∈ positive τ n := by
  obtain ⟨p,rfl⟩ := label_surjective (conditions A) (ZFSet.mem_sep.mp hp).1
  obtain ⟨q,rfl⟩ := label_surjective (conditions A) hq
  exact (label_positive τ n q).mpr
    (mem_mono (Name.check (natSet n)) τ hpq ((label_positive τ n p).mp hp))

theorem selected_hit_iff (M A U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) (hE : E ∈ M) (hUc : U ⊆ conditions A)
    (hopen : ∀ p ∈ U, ∀ q ∈ conditions A, p ⊆ q → q ∈ U)
    (hsel : Selected (conditions A) U E)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G) :
    (∃ p ∈ G.carrier, label (conditions A) p ∈ E) ↔
      ∃ p ∈ G.carrier, label (conditions A) p ∈ U := by
  have hb : below (conditions A) U = U := by
    apply ZFSet.ext; intro q
    rw [below,ZFSet.mem_sep]
    exact ⟨fun ⟨hq,p,hp,hpq⟩ => hopen p hp q hq hpq,
      fun hq => ⟨hUc hq,q,hq,fun _ h => h⟩⟩
  have hpred : ∀ p ∈ below (conditions A) U, ∃ q ∈ E, CohenAntichainStages.Comp (conditions A) p q
    := by
    rw [hb]; exact hsel.2.2
  have hd := decision_dense A U E hpred
  rw [hb] at hd
  have hDM := decision_mem M (conditions A) U E hM hT (conditions_mem M A hM hT hA) hU hE
  have hdense : Dense {p : Conditions (conditions A) | label (conditions A) p ∈ decision
    (conditions A) U E} := by
    intro p
    obtain ⟨q,hq,hpq⟩ := hd _ (label_mem _ p)
    obtain ⟨q,rfl⟩ := label_surjective (conditions A) (ZFSet.mem_sep.mp hq).1
    exact ⟨q,hpq,hq⟩
  constructor
  · rintro ⟨p,hp,hpE⟩
    exact ⟨p,hp,hsel.1 hpE⟩
  · rintro ⟨q,hq,hqU⟩
    obtain ⟨p,hp,hpD⟩ := hG _ hDM hdense
    rcases (ZFSet.mem_sep.mp hpD).2 with ⟨a,ha,hap⟩|hneg
    · obtain ⟨a,rfl⟩ := label_surjective (conditions A) (hUc (hsel.1 ha))
      exact ⟨a,G.upper hap hp,ha⟩
    · obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact False.elim (hneg _ (hopen _ hqU _ (label_mem _ r) hrq) hrp)

theorem selected_nice_value (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M)
    (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n))
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (hreal : τ.val G.carrier ⊆ ZFSet.omega) :
    (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val G.carrier
      := by
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have hB := internal_positive_family M hM hT hc ho (InternalCollapse.orderSet_pair _) τ hτ
  have hUM (n : ℕ) : positive τ n ∈ M :=
    hM _ (iterUnion_mem M hM hT.union hB 2) _
      (second_mem_doubleUnion ((orbitGraph_pair (positive τ) n _).mpr rfl))
  obtain ⟨p,hp⟩ := G.nonempty
  have htop : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  have hbits (n : ℕ) : (∃ p ∈ G.carrier, label (conditions A) p ∈ E n) ↔
      natSet n ∈ τ.val G.carrier := by
    rw [selected_hit_iff M A _ _ hM hT hA (hUM n) (hE n).1
      (fun _ h => (ZFSet.mem_sep.mp h).1) (fun p hp q hq hpq => positive_downward A τ n p q hp hq
        hpq) (hE n).2 G hG]
    have hnM := encoded_check_mem_of_container M (conditions A) ZFSet.omega hM hT.pairing
      hT.union hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
      hc (sourceT_omega_mem M hM hT) omega_transitive ((mem_omega _).mpr ⟨n,rfl⟩)
    have hh := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
      (InternalCollapse.orderSet_pair _) G hG (Name.check (natSet n)) τ hnM hτ).2
    rw [Name.val_check _ htop] at hh
    simpa only [label_positive] using hh.symm
  apply ZFSet.ext; intro x
  rw [InternalNiceName.mem_val_nice E G.carrier htop x]
  constructor
  · rintro ⟨n,p,hp,hpE,rfl⟩
    exact (hbits n).mp ⟨p,hp,hpE⟩
  · intro hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (hreal hx)
    obtain ⟨p,hp,hpE⟩ := (hbits n).mpr hx
    exact ⟨n,p,hp,hpE,rfl⟩

theorem internal_nice_name (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      (∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n)) ∧
      (InternalNiceName.nice E : Name (Conditions (conditions A))).encode (label (conditions A)) ∈
        M ∧
      (∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ CohenInternalSupport.supportSet A p) ∧
        (S = ∅ ∨ InternallyCountable M S)) ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val G.carrier ⊆ ZFSet.omega →
        (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val
          G.carrier := by
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have hB := internal_positive_family M hM hT hc ho (InternalCollapse.orderSet_pair _) τ hτ
  have hU (n : ℕ) : positive τ n ∈ M ∧ positive τ n ⊆ conditions A :=
    ⟨hM _ (iterUnion_mem M hM hT.union hB 2) _
      (second_mem_doubleUnion ((orbitGraph_pair (positive τ) n _).mpr rfl)),
      fun _ h => (ZFSet.mem_sep.mp h).1⟩
  obtain ⟨E,hgraph,hE,hS⟩ := CohenAntichainFamilySupport.selected_family_support M A hM hT hA
    (positive τ) hU hB
  exact ⟨E,hgraph,hE,InternalNiceName.nice_internal M hM hT hc E
      (fun n => ⟨(hE n).1,fun _ h => (hU n).2 ((hE n).2.1 h)⟩) hgraph,hS,
    fun G hG hreal => selected_nice_value M A hM hT hA τ hτ E hE G hG hreal⟩

end TuringRigidity.CohenNiceNameConstruction

end OAI
