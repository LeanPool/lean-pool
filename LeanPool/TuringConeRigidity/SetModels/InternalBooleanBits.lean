/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanBits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRealQuotient
public import LeanPool.TuringConeRigidity.SetModels.InternalGeneratedAlgebra

/-!
# Internal Boolean Bits
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanBits
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax InternalGeneratedAlgebra
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Bounded formula describing the regular Boolean-algebra value associated with a condition
family. -/
def bitFormula (c E V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (c+1) (.imp (.subset 1 0)
      (.existsMem (c+2) (.conj (.subset 1 0)
        (.existsMem (E+3) (.subset 0 1))))))))

theorem bitFormula_spec (c E V : ℕ) (e : ℕ → ZFSet.{0}) :
    (bitFormula c E V).Eval e ↔ e V = bitCode (e c) (e E) := by
  simp only [bitFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  have hb (q : ZFSet.{0}) :
      (∃ r ∈ e c, q ⊆ r ∧ ∃ s ∈ e E, s ⊆ r) ↔
      ∃ r ∈ CohenInternalDecision.below (e c) (e E), q ⊆ r := by
    simp only [CohenInternalDecision.below,ZFSet.mem_sep]
    constructor
    · rintro ⟨r,hr,hqr,hs⟩; exact ⟨r,⟨hr,hs⟩,hqr⟩
    · rintro ⟨r,⟨hr,hs⟩,hqr⟩; exact ⟨r,hr,hqr,hs⟩
  simp only [hb]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [bitCode,mem_regular]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    exact ⟨(regular_isCode _ _).1,fun p hp => (mem_regular _ _ p).trans (and_iff_right hp)⟩

/-- The members of `B` that code the Boolean values of the name's individual bit families. -/
noncomputable def seeds (c B : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ n, U = bitCode c (E n))

theorem seeds_mem (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) : seeds c B E ∈ M := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hc
  have hω := sourceT_omega_mem M hM hT
  let e := cons c (cons ZFSet.omega (cons Q (fun _ => orbitGraph E)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hc
    · exact hω
    · exact hQ
    · exact hgraph
  let φ : Formula := .existsMem 2 (.existsMem 4 (.conj (.pairMem 1 0 6) (bitFormula 3 0 2)))
  have hφ (U : ZFSet.{0}) : φ.Eval (cons U e) ↔ ∃ n, U = bitCode c (E n) := by
    simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,W,_,hp,hU⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hw := (orbitGraph_pair E n W).mp hp
      exact ⟨n,hw ▸ hU⟩
    · rintro ⟨n,hU⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,(hQdef _).mpr (hE n),
        (orbitGraph_pair E n _).mpr rfl,hU⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he hB
  simpa only [hφ,seeds] using hs

theorem bit_mem_seeds (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M) (n : ℕ) : bitCode c (E n) ∈ seeds c B E :=
  ZFSet.mem_sep.mpr ⟨(hB _).mpr ⟨bitCode_mem M c _ hM hT hc (hE n),regular_isCode c _⟩,n,rfl⟩

theorem interpret_bit (c : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ⊆ c) (n : ℕ) :
    interpret c (bitCode c (E n)) (regular_isCode c _) =
      RealGeneratedPart.bit (InternalRealQuotient.tags c E) n := by
  have hl : Lower c (CohenInternalDecision.below c (E n)) := by
    intro p hp q hq hpq
    obtain ⟨_,r,hr,hrp⟩ := ZFSet.mem_sep.mp hp
    exact ZFSet.mem_sep.mpr ⟨hq,r,hr,fun z hz => hpq (hrp hz)⟩
  have he : decode c (CohenInternalDecision.below c (E n)) hl =
      RealGeneratedPart.tagLower (InternalRealQuotient.tags c E n) := by
    apply SetLike.ext
    intro p
    exact InternalRealQuotient.label_below c (E n) (hE n) p
  apply Heyting.Regular.coe_injective
  change decode c (regular c (CohenInternalDecision.below c (E n))) (neg_lower c _) = _
  have hd := decode_regular c (CohenInternalDecision.below c (E n))
    (fun _ h => (ZFSet.mem_sep.mp h).1) hl
  apply hd.trans
  rw [he]
  rfl

theorem internal_bit_generated_part (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      (∀ n, bitCode c (E n) ∈ A) ∧
      ∀ A' ∈ Q, (∀ n, bitCode c (E n) ∈ A') → Closed c B Q A' → A ⊆ A' := by
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hBM
  have hS := seeds_mem M c B hM hT hc hBM E hE hgraph
  have hSB : seeds c B E ⊆ B := fun _ h => (ZFSet.mem_sep.mp h).1
  have hA := generated_mem M c B Q _ hM hT hc hBM hQM hS
  refine ⟨B,hBM,Q,hQM,generated c B Q (seeds c B E),hA,hB,hQ,rfl,
    generated_closed c B Q _ (algebra_closed M c B Q hM hT hc hB hQ),?_,?_⟩
  · intro n
    exact seeds_subset c B Q _ hSB (bit_mem_seeds M c B hM hT hc hB E (fun n => (hE n).1) n)
  · intro A' hA' hb hclosed
    apply generated_le c B Q _ A' hA' _ hclosed
    intro U hU
    obtain ⟨_,n,rfl⟩ := ZFSet.mem_sep.mp hU
    exact hb n

end TuringRigidity.InternalBooleanBits

end OAI
