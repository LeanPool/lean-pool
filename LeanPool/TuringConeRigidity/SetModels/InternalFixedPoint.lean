/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalFixedPoint.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedSetTheory

/-!
# Internal Fixed Point
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem internal_fixed_point (M : ZFSet.{u}) (hM : Transitive M)
    (hU : Union M) (hPow : PowerSet M) (hS : Separation M)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a : ZFSet.{u}) (ha : a ∈ M)
    (mono : ∀ f g : ZFSet.{u}, f ⊆ a → g ⊆ a → f ⊆ g →
      ∀ z ∈ a, φ.Eval (cons z (cons f e)) → φ.Eval (cons z (cons g e))) :
    ∃ g ∈ M, g ⊆ a ∧ ∀ z ∈ a,
      z ∈ g ↔ φ.Eval (cons z (cons g e)) := by
  obtain ⟨b,hb,hbdef⟩ := internal_power M hM hPow ha
  let post := Formula.allMem 0 φ
  let s := ZFSet.sep (fun f => post.Eval (cons f e)) b
  have hs : s ∈ M := sep_mem M hM hS post e he hb
  have hsdef (f : ZFSet.{u}) : f ∈ s ↔
      f ∈ M ∧ f ⊆ a ∧ ∀ z ∈ f, φ.Eval (cons z (cons f e)) := by
    simp only [s,ZFSet.mem_sep,hbdef,post,Formula.eval_allMem,cons_zero]
    exact and_assoc
  let g := ZFSet.sUnion s
  have hg : g ∈ M := union_mem M hM hU hs
  have hga : g ⊆ a := by
    intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    exact ((hsdef f).mp hf).2.1 hzf
  have hgpost : ∀ z ∈ g, φ.Eval (cons z (cons g e)) := by
    intro z hz
    obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
    have hf' := (hsdef f).mp hf
    apply mono f g hf'.2.1 hga (fun w hw => ZFSet.mem_sUnion.mpr ⟨f,hf,hw⟩) z (hga hz)
    exact hf'.2.2 z hzf
  let v := ZFSet.sep (fun z => φ.Eval (cons z (cons g e))) a
  have hv : v ∈ M := sep_mem M hM hS φ (cons g e)
    (fun i => by cases i <;> simp [hg,he]) ha
  have hva : v ⊆ a := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hgv : g ⊆ v := fun z hz => ZFSet.mem_sep.mpr ⟨hga hz,hgpost z hz⟩
  have hvpost : ∀ z ∈ v, φ.Eval (cons z (cons v e)) := by
    intro z hz
    exact mono g v hga hva hgv z (hva hz) (ZFSet.mem_sep.mp hz).2
  have hvs : v ∈ s := (hsdef v).mpr ⟨hv,hva,hvpost⟩
  refine ⟨g,hg,hga,fun z hz => ⟨hgpost z,fun h => ?_⟩⟩
  exact ZFSet.mem_sUnion.mpr ⟨v,hvs,ZFSet.mem_sep.mpr ⟨hz,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
