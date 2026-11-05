/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MaximumDegree
public import LeanPool.GoldbergSeymour.MissingColors
public import Mathlib.Data.Fintype.EquivFin

/-!
# Missing Colors Nonempty Of Maximum Degree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma MissingColorsNonemptyOfMaximumDegree
    {V E : Type*} [Fintype V] [Fintype E] (G : LooplessMultigraph V E) {k : Nat}
    (phi : PartialEdgeColoring E k)
    (hdegree : MaximumDegree G + 1 <= k) (v : V) :
    (MissingColors G phi v).Nonempty := by
  classical
  have hdeg : Degree G v <= MaximumDegree G := by
    unfold MaximumDegree
    exact Finset.le_max' _ _ (Finset.mem_insert.mpr (Or.inr
      (Finset.mem_image.mpr <| Exists.intro v (by simp))))
  have present_le_degree : (PresentColors G phi v).card <= Degree G v := by
    have chooseData (c : {c : Fin k // c ∈ PresentColors G phi v}) :
        exists e, Incident G v e /\ phi e = some c.1 := by
      simpa [PresentColors] using c.property
    let choices : {c : Fin k // c ∈ PresentColors G phi v} ->
        {e : E // Incident G v e} := fun c =>
      Subtype.mk (Classical.choose (chooseData c))
        (Classical.choose_spec (chooseData c)).1
    have choice_spec : forall c : {c : Fin k // c ∈ PresentColors G phi v},
        phi (choices c).1 = some c.1 := by
      intro c
      exact (Classical.choose_spec (chooseData c)).2
    have hinj : Function.Injective choices := by
      intro a b hab
      apply Subtype.ext
      apply Option.some.inj
      calc
        some (a : Fin k) = phi (choices a).1 := (choice_spec a).symm
        _ = phi (choices b).1 := by rw [hab]
        _ = some (b : Fin k) := choice_spec b
    let : Fintype {c : Fin k // c ∈ PresentColors G phi v} :=
      Fintype.ofFinite _
    have hc := Fintype.card_le_of_injective choices hinj
    change (PresentColors G phi v).card <=
      (Finset.univ.filter (fun e => Incident G v e)).card
    simpa [Fintype.card_subtype] using hc
  by_contra hn
  have hempty : MissingColors G phi v = Finset.empty :=
    Finset.not_nonempty_iff_eq_empty.mp hn
  have hall : PresentColors G phi v = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    by_contra hc
    have hm : c ∈ MissingColors G phi v := by simp [MissingColors, hc]
    rw [hempty] at hm
    exact Finset.notMem_empty c hm
  have hk : k <= Degree G v := by
    simpa [hall] using present_le_degree
  have : MaximumDegree G + 1 <= MaximumDegree G :=
    hdegree.trans (hk.trans hdeg)
  omega

end GoldbergSeymour

end
