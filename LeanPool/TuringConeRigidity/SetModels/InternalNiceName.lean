/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalNiceName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalNaturalCheckSequence

/-!
# Internal Nice Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalNiceName
open TransitiveNameModel BoundedSetTheory RecursiveNames CountableForcing
variable {c : ZFSet.{0}} [Top (Conditions c)]

/-- A real name tagged by the condition-label sets `E n`. -/
noncomputable def nice (E : ℕ → ZFSet.{0}) : Name (Conditions c) :=
  .mk (Σ n : ℕ, {p : Conditions c // label c p ∈ E n})
    (fun i => Name.check (natSet i.1)) (fun i => i.2.val)

theorem mem_encode_nice (E : ℕ → ZFSet.{0}) (z : ZFSet.{0}) :
    z ∈ (nice E : Name (Conditions c)).encode (label c) ↔
      ∃ n, ∃ p : Conditions c, label c p ∈ E n ∧
        z = ZFSet.pair (checkedCode (label c ⊤) (natSet n)) (label c p) := by
  simp only [nice,Name.encode,ZFSet.mem_range,encode_check]
  exact ⟨fun ⟨⟨n,p,hp⟩,hz⟩ => ⟨n,p,hp,hz.symm⟩,
    fun ⟨n,p,hp,hz⟩ => ⟨⟨n,p,hp⟩,hz.symm⟩⟩

theorem nice_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hEgraph : orbitGraph E ∈ M) :
    (nice E : Name (Conditions c)).encode (label c) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hEQ : ∀ n, E n ∈ Q := fun n => (hQ _).mpr (hE n)
  let B := orbitGraph (fun n => checkedCode (label c ⊤) (natSet n))
  have hBM : B ∈ M := InternalNaturalCheckSequence.natural_check_sequence M _ hM hT
    (hM c hc _ (label_mem c ⊤))
  let r := iterUnion 2 B
  have hrM := iterUnion_mem M hM hT.union hBM 2
  have hr (n : ℕ) : checkedCode (label c ⊤) (natSet n) ∈ r :=
    second_mem_doubleUnion ((orbitGraph_pair _ n _).mpr rfl)
  let e := cons ZFSet.omega (cons Q (cons r (cons c (cons B (fun _ => orbitGraph E)))))
  let φ : BoundedSetTheory.Formula := .existsMem 1 (.existsMem 3 (.existsMem 5 (.existsMem 7
    (.conj (.orderedPair 4 1 0) (.conj (.pairMem 3 1 9)
      (.conj (.pairMem 3 2 10) (.member 0 2)))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hω
    · exact hQM
    · exact hrM
    · exact hc
    · exact hBM
    · exact hEgraph
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      z ∈ (nice E : Name (Conditions c)).encode (label c) := by
    simp only
      [φ, BoundedSetTheory.Formula.Eval, BoundedSetTheory.Formula.eval_orderedPair,
        BoundedSetTheory.Formula.eval_pairMem, cons_zero, cons_succ, e]
    rw [mem_encode_nice]
    constructor
    · rintro ⟨n,hn,H,_,v,_,p,hp,hz,hnv,hnH,hpH⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨p,rfl⟩ := label_surjective c hp
      have hv := (orbitGraph_pair _ n v).mp hnv
      have hH := (orbitGraph_pair E n H).mp hnH
      exact ⟨n,p,hH ▸ hpH,by rw [hz,hv]⟩
    · rintro ⟨n,p,hp,rfl⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hEQ n,_,hr n,_,label_mem c p,rfl,
        (orbitGraph_pair _ n _).mpr rfl,(orbitGraph_pair E n _).mpr rfl,hp⟩
  have hs := sep_mem M hM hS φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hrM hc)
  have heq : (ZFSet.prod r c).sep (fun z => φ.Eval (cons z e)) =
      (nice E : Name (Conditions c)).encode (label c) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    refine ⟨And.right,fun hz => ⟨?_,hz⟩⟩
    obtain ⟨n,p,_,rfl⟩ := (mem_encode_nice E z).mp hz
    exact ZFSet.mem_prod.mpr ⟨_,hr n,_,label_mem c p,rfl⟩
  exact heq ▸ hs

theorem mem_val_nice (E : ℕ → ZFSet.{0}) (G : Set (Conditions c)) (hG : ⊤ ∈ G)
    (x : ZFSet.{0}) : x ∈ (nice E : Name (Conditions c)).val G ↔
      ∃ n, ∃ p ∈ G, label c p ∈ E n ∧ natSet n = x := by
  rw [nice,Name.mem_val]
  simp only [Name.val_check _ hG]
  exact ⟨fun ⟨⟨n,p,hp⟩,hpG,hx⟩ => ⟨n,p,hpG,hp,hx⟩,
    fun ⟨n,p,hpG,hp,hx⟩ => ⟨⟨n,p,hp⟩,hpG,hx⟩⟩

end TuringRigidity.InternalNiceName

end OAI
