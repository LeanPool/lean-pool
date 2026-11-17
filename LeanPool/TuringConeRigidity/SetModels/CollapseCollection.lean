/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapseCollection.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseCertificate
public import LeanPool.TuringConeRigidity.Syntax.SigmaSeparationName

/-!
# Collapse Collection
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem collect_graphs (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ B ∈ M, ∀ f, f ∈ B ↔ f ∈ M ∧ ∃ r ∈ M, On d r ∧ ∃ b ∈ M, Graph d r d b f := by
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hPow
    (product_mem M hM hP hU hPow hS.bounded hd hd)
  let e := fun _ : ℕ => d
  let success := SigmaFormula.existsSet (Code.full 2 1 0)
  let a := ZFSet.sep (fun r => success.Realize M (cons r e)) q
  have ha : a ∈ M := sigma_sep_mem M hM hS success e (fun _ => hd) hq
  have cert (r f : ZFSet.{u}) (hr : r ∈ M) (hf : f ∈ M) :
      (Code.full 2 1 0).Realize M (cons f (cons r e)) ↔ ∃ b ∈ M, Graph d r d b f :=
    Code.realize_full M hM _ (by
      intro i
      rcases i with _ | i
      · exact hf
      rcases i with _ | i
      · exact hr
      exact hd) 2 1 0
  have ha_def (r : ZFSet.{u}) : r ∈ a ↔
      r ∈ M ∧ On d r ∧ ∃ f ∈ M, ∃ b ∈ M, Graph d r d b f := by
    rw [ZFSet.mem_sep,hqdef]
    change (r ∈ M ∧ On d r) ∧ (∃ f ∈ M, _) ↔ _
    constructor
    · rintro ⟨⟨hr,hrd⟩,f,hf,hc⟩
      exact ⟨hr,hrd,f,hf,(cert r f hr hf).mp hc⟩
    · rintro ⟨hr,hrd,f,hf,b,hb,hg⟩
      exact ⟨⟨hr,hrd⟩,f,hf,(cert r f hr hf).mpr ⟨b,hb,hg⟩⟩
  obtain ⟨B,hB,hBdef⟩ := hR (Code.full 2 1 0) e (fun _ => hd) a ha (by
    intro r hr
    obtain ⟨hrM,hrd,f,hf,b,hb,hfg⟩ := (ha_def r).mp hr
    refine ⟨f,hf,(cert r f hrM hf).mpr ⟨b,hb,hfg⟩,?_⟩
    intro g hg hcg
    obtain ⟨b',_,hgg⟩ := (cert r g hrM hg).mp hcg
    exact hgg.unique (hfg.wellFounded hrd) hfg)
  refine ⟨B,hB,fun f => ?_⟩
  constructor
  · intro hf
    have hfM := hM B hB f hf
    obtain ⟨r,hr,hc⟩ := (hBdef f hfM).mp hf
    obtain ⟨hrM,hrd,_⟩ := (ha_def r).mp hr
    exact ⟨hfM,r,hrM,hrd,(cert r f hrM hfM).mp hc⟩
  · rintro ⟨hf,r,hr,hrd,b,hb,hg⟩
    exact (hBdef f hf).mpr ⟨r,(ha_def r).mpr ⟨hr,hrd,f,hf,b,hb,hg⟩,
      (cert r f hr hf).mpr ⟨b,hb,hg⟩⟩

theorem internal_value_bound (M d : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hd : d ∈ M) :
    ∃ W ∈ M, ∀ r ∈ M, On d r → ∀ wf : WellFounded (Rel d r),
      ∀ x ∈ d, value d r wf x ∈ W := by
  obtain ⟨B,hB,hBdef⟩ := collect_graphs M d hM hP hU hPow hS hR hd
  let W := iterUnion 2 (ZFSet.sUnion B)
  have hW : W ∈ M := iterUnion_mem M hM hU (union_mem M hM hU hB) 2
  refine ⟨W,hW,?_⟩
  intro r hr hrd wf x hx
  obtain ⟨f,hf,hfg⟩ := internal_graph M d r hM hP hU hPow hS.bounded hR hd hr wf
  have hfB := (hBdef f).mpr ⟨hf,r,hr,hrd,_,iterUnion_mem M hM hU hf 2,hfg⟩
  have hpair := (hfg.mem_iff wf _).mpr ⟨x,hx,rfl⟩
  exact second_mem_doubleUnion (ZFSet.mem_sUnion.mpr ⟨f,hfB,hpair⟩)

end TuringRigidity.RelationCollapse

end OAI
