/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseSupportClass
public import LeanPool.GoldbergSeymour.SupportingPEColorChain

/-!
# Extension Base Support Class Colors

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseSupportClassColors {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (q : Fin ett.rounds) (_ : q.val + 1 = ett.rounds)
    (w : V)
    (hw : w ∈ TreeSequenceVertexSet
      (ett.series.data.tree q.succ.castSucc))
    (p : ℕ) (indices : Fin (p + 1) → Fin ett.rounds)
    (hincreasing : ∀ a b, a.val < b.val →
      (indices a).val < (indices b).val)
    (_ : ∀ r : Fin ett.rounds,
      r ∈ ExtensionBaseSupportClass ett terminalSupport hterminalSupport w ↔
        ∃ a : Fin (p + 1), indices a = r)
    (henumerates : ∀ r : Fin ett.rounds,
      (r.val ≤ q.val ∧
        ett.series.data.kind r.succ = some TashkinovExtensionKind.PE ∧
        ett.series.data.chosenVertex r.succ = some w) ↔
      ∃ a : Fin (p + 1), indices a = r)
    (gamma delta : Fin (p + 1) → Fin k)
    (hgamma : ∀ a, ett.series.data.gamma (indices a).succ = some (gamma a))
    (hdelta : ∀ a, ett.series.data.delta (indices a).succ = some (delta a))
    (hdeltaAvoidsEarlierGamma : ∀ a b, a.val ≤ b.val →
      delta b ≠ gamma a) :
    (∀ a : Fin p, gamma a.succ = delta a.castSucc) ∧
      Function.Injective (Fin.cons (gamma 0) delta) := by
  classical
  constructor
  · intro a
    have chain := SupportingPEColorChain G k ett.rounds p e0 input ett.series q w hw
      indices hincreasing henumerates a
    rw [hgamma, hdelta] at chain
    exact Option.some.inj chain
  · intro a b
    revert b
    refine Fin.cases ?_ (fun a => ?_) a
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · intro hab
        rfl
      · intro hab
        exfalso
        apply hdeltaAvoidsEarlierGamma 0 b (Nat.zero_le _)
        simpa only [Fin.cons_zero, Fin.cons_succ] using hab.symm
    · intro b
      refine Fin.cases ?_ (fun b => ?_) b
      · intro hab
        exfalso
        apply hdeltaAvoidsEarlierGamma 0 a (Nat.zero_le _)
        simpa only [Fin.cons_zero, Fin.cons_succ] using hab
      · intro hab
        rcases lt_trichotomy a b with hlt | heq | hgt
        · have ha : a.val < p := by omega
          let x : Fin p := ⟨a.val, ha⟩
          have hxa : x.castSucc = a := by
            apply Fin.ext
            rfl
          have hxval : x.val = a.val := rfl
          have hxb : x.succ.val ≤ b.val := by
            change a.val + 1 ≤ b.val
            omega
          have he : delta a = delta b := by
            simpa only [Fin.cons_succ] using hab
          have hx : delta a = gamma x.succ := by
            rw [← hxa]
            have chain := SupportingPEColorChain G k ett.rounds p e0 input ett.series q w hw
              indices hincreasing henumerates x
            rw [hgamma, hdelta] at chain
            exact (Option.some.inj chain).symm
          exfalso
          apply hdeltaAvoidsEarlierGamma x.succ b hxb
          exact he ▸ hx
        · exact congrArg Fin.succ heq
        · exfalso
          have hb : b.val < p := by omega
          let x : Fin p := ⟨b.val, hb⟩
          have hxb : x.castSucc = b := by
            apply Fin.ext
            rfl
          have hxval : x.val = b.val := rfl
          have hxa : x.succ.val ≤ a.val := by
            change b.val + 1 ≤ a.val
            omega
          have he : delta b = delta a := by
            simpa only [Fin.cons_succ] using hab.symm
          have hx : delta b = gamma x.succ := by
            rw [← hxb]
            have chain := SupportingPEColorChain G k ett.rounds p e0 input ett.series q w hw
              indices hincreasing henumerates x
            rw [hgamma, hdelta] at chain
            exact (Option.some.inj chain).symm
          apply hdeltaAvoidsEarlierGamma x.succ a hxa
          exact he ▸ hx

end GoldbergSeymour

end
