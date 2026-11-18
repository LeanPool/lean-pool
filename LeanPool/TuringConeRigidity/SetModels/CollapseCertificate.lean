/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapseCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRelationCollapse

/-!
# Collapse Certificate
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem internal_graph (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r)) :
    ∃ f ∈ M, Graph d r d (iterUnion 2 f) f := by
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hd
  let e := cons q (cons d (cons r (fun _ => d)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hqM
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hr
    exact hd
  have cert (x f : ZFSet.{u}) (hx : x ∈ d) (hf : f ∈ M) :
      certificate.Realize M (cons f (cons x e)) ↔
        ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f :=
    realize_certificate M d r q hM hS hd hr hqM hq hx hf
  obtain ⟨B,hB,hBdef⟩ := hR certificate e he d hd (by
    intro x hx
    obtain ⟨f,hf,hfg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
    refine ⟨f,hf,(cert x f hx hf).mpr ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
    intro g hg hcg
    obtain ⟨b,_,hgg⟩ := (cert x g hx hg).mp hcg
    exact hgg.unique wf hfg)
  have hBg (f : ZFSet.{u}) : f ∈ B ↔
      ∃ x ∈ d, ∃ b ∈ M, Graph d r (RelationHull.hull d r q x) b f := by
    constructor
    · intro hf
      have hfM := hM B hB f hf
      obtain ⟨x,hx,hc⟩ := (hBdef f hfM).mp hf
      exact ⟨x,hx,(cert x f hx hfM).mp hc⟩
    · rintro ⟨x,hx,b,hb,hg⟩
      obtain ⟨g,hgM,hgg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
      have hfM : f ∈ M := hg.unique wf hgg ▸ hgM
      exact (hBdef f hfM).mpr ⟨x,hx,(cert x f hx hfM).mpr ⟨b,hb,hg⟩⟩
  refine ⟨ZFSet.sUnion B,union_mem M hM hU hB,
    graph_of_mem_iff d r d _ wf (fun _ h => h) (fun _ _ _ h _ => h) ?_⟩
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨f,hf,hzf⟩
    obtain ⟨x,_,b,_,hfg⟩ := (hBg f).mp hf
    obtain ⟨y,hy,hz⟩ := (hfg.mem_iff wf z).mp hzf
    exact ⟨y,RelationHull.hull_subset d r q x hy,hz⟩
  · rintro ⟨x,hx,hz⟩
    obtain ⟨f,hf,hfg⟩ := internal_hull_graph M d r q hM hP hU hS hR hd hr hqM hq wf x hx
    exact ⟨f,(hBg f).mpr ⟨x,hx,_,iterUnion_mem M hM hU hf 2,hfg⟩,
      (hfg.mem_iff wf z).mpr ⟨x,RelationHull.self_mem d r q hx,hz⟩⟩

/-- The relation has both coordinates inside the designated domain. -/
def On (d r : ZFSet.{u}) : Prop := r ⊆ ZFSet.prod d d

theorem right_mem {d r x y : ZFSet.{u}} (hr : On d r) (hyx : ZFSet.pair y x ∈ r) : x ∈ d := by
  obtain ⟨a,_,b,hb,heq⟩ := ZFSet.mem_prod.mp (hr hyx)
  exact (ZFSet.pair_inj.mp heq).2 ▸ hb

theorem Graph.wellFounded {d r b f : ZFSet.{u}} (hr : On d r)
    (hg : Graph d r d b f) : WellFounded (Rel d r) := by
  classical
  let F : ZFSet.{u} → ZFSet.{u} := fun x =>
    if hx : x ∈ d then (hg.2.2.2.1 x hx).choose else ∅
  have hF (x : ZFSet.{u}) (hx : x ∈ d) :
      F x ∈ b ∧ ZFSet.pair x (F x) ∈ f := by
      simpa only [F,dite_eq_left hx] using (hg.2.2.2.1 x hx).choose_spec |>.imp_right And.left
  have wf : WellFounded (fun y x => F y ∈ F x) := InvImage.wf F ZFSet.mem_wf
  apply wf.mono
  intro y x hyx
  have hx := right_mem hr hyx.2
  exact (hg.2.2.2.2 x hx (F x) (hF x hx).1 (hF x hx).2).2
    y hyx.1 hyx.2 (F y) (hF y hyx.1).1 (hF y hyx.1).2

namespace Code

/-- A sigma formula requesting a set range for the specified collapse graph. -/
def full (d r f : ℕ) : SigmaFormula :=
  .existsSet (.bounded (graph (d+1) (r+1) (d+1) 0 (f+1)))

theorem realize_full (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (d r f : ℕ) :
    (full d r f).Realize M e ↔ ∃ b ∈ M, Graph (e d) (e r) (e d) b (e f) := by
  change (∃ b ∈ M, _) ↔ _
  apply exists_congr
  intro b
  apply and_congr_right
  intro hb
  simp only [SigmaFormula.Realize]
  rw [Formula.absolute _ M hM _ (by intro i; cases i with
    | zero => exact hb
    | succ i => exact he i)]
  exact eval_graph (d+1) (r+1) (d+1) 0 (f+1) _
end Code

end TuringRigidity.RelationCollapse

end OAI
