/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import LeanPool.DynamicMcs.Exec

/-!
# CardEqNeigh

Bridges the executable adjacency model (`Exec.cardC`) to the abstract
cardinality count (`Greedy.UGraph.neigh`) on the `Fin`-valued image of a
`List ℕ` of vertex ids.
-/

@[expose] public section

open DynamicMcs.Greedy

namespace DynamicMcs

namespace CardBridge

/-- Embed a `List ℕ` of ids into `Fin n`, carrying the bound proof. -/
def chosenFin (n : ℕ) (chosen : List ℕ) (h : ∀ v ∈ chosen, v < n) : List (Fin n) :=
  chosen.pmap (fun (v : ℕ) (hv : v < n) => ⟨v, hv⟩) h

/-- `chosenFin` preserves `Nodup` (the id embedding is injective). -/
lemma chosenFin_nodup (n : ℕ) (chosen : List ℕ) (hnd : chosen.Nodup)
    (hchosen : ∀ v ∈ chosen, v < n) : (chosenFin n chosen hchosen).Nodup := by
  unfold chosenFin
  exact List.Nodup.pmap
    (fun a ha b hb h => by
      show a = b
      exact congrArg Fin.val h)
    hnd

/-- Bridging the counting sets: filtering the `Fin`-image of `chosen` by
`w ↦ (getAdj a w b.val = true)` counts the same vertices as filtering `chosen`
by `v ↦ getAdj a v w`, using symmetry of the adjacency matrix. -/
lemma cardC_filter_bridge (n : ℕ) (a : Adj n)
    (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
    (chosen : List ℕ) (hchosen : ∀ v ∈ chosen, v < n) (w : ℕ) :
    (List.filter (fun b : Fin n => Exec.getAdj a w b.val)
        (chosenFin n chosen hchosen)).length
      = (List.filter (fun v => Exec.getAdj a v w) chosen).length := by
  induction chosen with
  | nil => simp [chosenFin]
  | cons v vs ih =>
      have hsymvw : Exec.getAdj a w v = Exec.getAdj a v w := hsymm w v
      unfold chosenFin
      have hh : ∀ b ∈ vs, b < n := fun x hx => hchosen x (List.mem_cons.mpr (Or.inr hx))
      have ihvs : (List.filter (fun b : Fin n => Exec.getAdj a w b.val)
            (List.pmap (fun v hv => ⟨v, hv⟩) vs hh)).length
          = (List.filter (fun v => Exec.getAdj a v w) vs).length := by
        exact ih hh
      rw [List.pmap_cons]
      by_cases hcv : Exec.getAdj a v w = true
      · have hcvw : Exec.getAdj a w v = true := by rw [hsymvw]; exact hcv
        simp [hcvw, hcv, ihvs]
      · have hcnw : ¬ Exec.getAdj a w v = true := by rw [hsymvw]; exact hcv
        simp [hcnw, hcv, ihvs]

lemma cardC_eq_neigh (n : ℕ) (a : Adj n) (hsymm : ∀ u v : ℕ, Exec.getAdj a u v = Exec.getAdj a v u)
    (hloop : ∀ u : ℕ, Exec.getAdj a u u = false)
    (chosen : List ℕ) (hchosen : ∀ v ∈ chosen, v < n) (hnd : chosen.Nodup)
    (w : ℕ) (hw : w < n) :
    Greedy.UGraph.neigh (Exec.toUGraph a hsymm hloop)
      (chosenFin n chosen hchosen).toFinset ⟨w, hw⟩ = Exec.cardC a chosen w := by
  classical
  let G : Greedy.UGraph n := Exec.toUGraph a hsymm hloop
  let cf : List (Fin n) := chosenFin n chosen hchosen
  have hcn : cf.Nodup := by
    exact chosenFin_nodup n chosen hnd hchosen
  have hT_card : (cf.toFinset.filter (fun x => G.adj ⟨w, hw⟩ x)).card = Exec.cardC a chosen w := by
    calc
      (cf.toFinset.filter (fun x => G.adj ⟨w, hw⟩ x)).card
          = (List.filter (fun b : Fin n => decide (G.adj ⟨w, hw⟩ b)) cf).length := by
              rw [List.filter_toFinset]
              rw [List.toFinset_card_of_nodup
                (List.Nodup.filter (fun b : Fin n => decide (G.adj ⟨w, hw⟩ b)) hcn)]
      _ = (List.filter (fun b : Fin n => Exec.getAdj a w b.val) cf).length := by
              congr 1
              apply List.filter_congr
              intro b hb
              simp [G, Exec.toUGraph]
      _ = Exec.cardC a chosen w := by
              unfold Exec.cardC
              rw [cardC_filter_bridge n a hsymm chosen hchosen w]
  unfold Greedy.UGraph.neigh
  let T : Finset (Fin n) := cf.toFinset.filter (fun x => G.adj ⟨w, hw⟩ x)
  let N : Finset (Fin n) := cf.toFinset.filter (fun x => ¬ G.adj ⟨w, hw⟩ x)
  have hsplit : T.card + N.card = cf.toFinset.card := by
    unfold T N
    exact Finset.card_filter_add_card_filter_not (fun x : Fin n => G.adj ⟨w, hw⟩ x)
  have hT : cf.toFinset.card - N.card = T.card := Nat.sub_eq_of_eq_add hsplit.symm
  calc
    (Exec.toUGraph a hsymm hloop).neigh cf.toFinset ⟨w, hw⟩
        = cf.toFinset.card - N.card := by rfl
    _ = T.card := hT
    _ = Exec.cardC a chosen w := hT_card

end CardBridge
end DynamicMcs
