/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeSequenceAdjoinEdge

/-!
# Tree Sequence Adjoin Edge Unique

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

theorem TreeSequenceAdjoinEdgeUnique
    {V E : Type*} {G : LooplessMultigraph V E} {e0 : E}
    (T : TreeSequence G e0) (f : E) (U W : TreeSequence G e0)
    (hU : TreeSequenceAdjoinEdge T f U)
    (hW : TreeSequenceAdjoinEdge T f W) : U = W := by
  cases U with
  | mk ulen upos uvertex uedge uvinj ueinj ufirst uattaches =>
    cases W with
    | mk wlen wpos wvertex wedge wvinj weinj wfirst wattaches =>
      rcases hU with ⟨hlenU, hinitU, hedgeU⟩
      rcases hW with ⟨hlenW, hinitW, hedgeW⟩
      change ulen = T.length + 1 at hlenU
      change wlen = T.length + 1 at hlenW
      subst ulen
      subst wlen
      rcases hinitU with ⟨_, hvertU, hedgesU⟩
      rcases hinitW with ⟨_, hvertW, hedgesW⟩
      rw [TreeSequence.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · apply heq_of_eq
        funext i
        by_cases hi : i.val < T.length + 1
        · let iT : Fin (T.length + 1) := ⟨i.val, hi⟩
          have hcastU :
              Fin.castLE (Nat.succ_le_succ (by omega : T.length ≤ T.length + 1)) iT =
                i := by
            apply Fin.ext
            rfl
          have hcastW :
              Fin.castLE (Nat.succ_le_succ (by omega : T.length ≤ T.length + 1)) iT =
                i := by
            apply Fin.ext
            rfl
          calc
            uvertex i = uvertex (Fin.castLE _ iT) :=
              congrArg uvertex hcastU.symm
            _ = T.vertex iT := by simpa using hvertU iT
            _ = wvertex (Fin.castLE _ iT) := by
              simpa using (hvertW iT).symm
            _ = wvertex i := congrArg wvertex hcastW
        · have hilast : i = Fin.last (T.length + 1) := by
            apply Fin.ext
            simp only [Fin.last]
            omega
          subst i
          let j : Fin (T.length + 1) := Fin.last T.length
          obtain ⟨qU, hqU⟩ := uattaches j
          obtain ⟨qW, hqW⟩ := wattaches j
          have hedgeU' : uedge j = f := by
            simpa [j] using hedgeU
          have hedgeW' : wedge j = f := by
            simpa [j] using hedgeW
          have hvertUq :
              uvertex (Fin.castLT qU (by omega)) = T.vertex qU := by
            have hcast :
                Fin.castLE
                    (Nat.succ_le_succ (by omega : T.length ≤ T.length + 1)) qU =
                  Fin.castLT qU (by omega) := by
              apply Fin.ext
              rfl
            rw [← hcast]
            simpa using hvertU qU
          have hvertWq :
              wvertex (Fin.castLT qW (by omega)) = T.vertex qW := by
            have hcast :
                Fin.castLE
                    (Nat.succ_le_succ (by omega : T.length ≤ T.length + 1)) qW =
                  Fin.castLT qW (by omega) := by
              apply Fin.ext
              rfl
            rw [← hcast]
            simpa using hvertW qW
          have hvertUqW :
              uvertex (Fin.castLT qW (by omega)) = T.vertex qW := by
            have hcast :
                Fin.castLE
                    (Nat.succ_le_succ (by omega : T.length ≤ T.length + 1)) qW =
                  Fin.castLT qW (by omega) := by
              apply Fin.ext
              rfl
            rw [← hcast]
            simpa using hvertU qW
          have hends :
              Sym2.mk (uvertex (Fin.last (T.length + 1))) (T.vertex qU) =
                Sym2.mk (wvertex (Fin.last (T.length + 1))) (T.vertex qW) := by
            have hu : G.ends f =
                Sym2.mk (uvertex (Fin.last (T.length + 1))) (T.vertex qU) := by
              rw [← hedgeU']
              simpa [j, hvertUq] using hqU
            have hw : G.ends f =
                Sym2.mk (wvertex (Fin.last (T.length + 1))) (T.vertex qW) := by
              rw [← hedgeW']
              simpa [j, hvertWq] using hqW
            exact hu.symm.trans hw
          rcases (Sym2.eq_iff.mp hends) with horiented | hswapped
          · exact horiented.1
          · exfalso
            have hnewFresh :
                uvertex (Fin.last (T.length + 1)) ≠
                  uvertex (Fin.castLT qW (by omega)) := by
              intro heq
              have hind := uvinj heq
              have : (Fin.last (T.length + 1) : Fin (T.length + 2)).val = qW.val :=
                congrArg Fin.val hind
              simp only [Fin.last] at this
              omega
            apply hnewFresh
            exact hswapped.1.trans hvertUqW.symm
      · apply heq_of_eq
        funext i
        by_cases hi : i.val < T.length
        · let iT : Fin T.length := ⟨i.val, hi⟩
          have hcastU :
              Fin.castLE (by omega : T.length ≤ T.length + 1) iT = i := by
            apply Fin.ext
            rfl
          have hcastW :
              Fin.castLE (by omega : T.length ≤ T.length + 1) iT = i := by
            apply Fin.ext
            rfl
          calc
            uedge i = uedge (Fin.castLE _ iT) := congrArg uedge hcastU.symm
            _ = T.edge iT := by simpa using hedgesU iT
            _ = wedge (Fin.castLE _ iT) := by simpa using (hedgesW iT).symm
            _ = wedge i := congrArg wedge hcastW
        · have hilast : i = Fin.last T.length := by
            apply Fin.ext
            simp only [Fin.last]
            omega
          subst i
          exact hedgeU.trans hedgeW.symm

end GoldbergSeymour

end
