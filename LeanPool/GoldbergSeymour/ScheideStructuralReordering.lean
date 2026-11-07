/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import LeanPool.GoldbergSeymour.ScheideStructuralReorderingData

/-!
# Scheide Structural Reordering

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev structuralSumFin (m n : ℕ) : Fin m ⊕ Fin n ≃ Fin (m + n) :=
  finSumFinEquiv

private abbrev structuralPairFin (m : ℕ) : Fin m × Fin 2 ≃ Fin (m * 2) :=
  { toFun := fun x =>
      ⟨x.1.val * 2 + x.2.val, by
        have hi := x.1.isLt
        have hj := x.2.isLt
        omega⟩
    invFun := fun x => (x.divNat, x.modNat)
    left_inv := by
      intro x
      apply Prod.ext <;> apply Fin.ext
      · simp [Fin.divNat]
        omega
      · simp [Fin.modNat]
        omega
    right_inv := by
      intro x
      apply Fin.ext
      simp [Fin.divNat, Fin.modNat]
      omega }

private abbrev helperContinuation521Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
    ∀ (blockIndex_bijective : Function.Bijective blockIndex),
    let sumFin : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let pairFin : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s := (sumFin D.absorbedCount
        D.retainedCount).symm.trans (Equiv.ofBijective blockIndex blockIndex_bijective);
    let reorderCore : (b : ℕ) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) ≃ Fin (b +
        C.s * (2 : ℕ)) := fun (b : ℕ) ↦ ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ))).symm.trans ((Equiv.refl (Fin b)).sumCongr ((pairFin (D.absorbedCount +
        D.retainedCount)).symm.trans ((blockOrder.prodCongr (Equiv.refl (Fin (2 : ℕ)))).trans
        (pairFin C.s))))).trans (sumFin b (C.s * (2 : ℕ)));
    ∀ (vertexNewSize : T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ))
        (vertexOldSize : T.length + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (edgeNewSize : T.length = C.p -
        (1 : ℕ) + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (edgeOldSize : T.length = C.p -
        (1 : ℕ) + C.s * (2 : ℕ)),
    let vertexOrder : Equiv.Perm (Fin (T.length + (1 : ℕ))) := (finCongr vertexNewSize).trans
        ((reorderCore C.p).trans (finCongr vertexOldSize).symm);
    let edgeOrder : Equiv.Perm (Fin T.length) := (finCongr edgeNewSize).trans ((reorderCore (C.p -
        (1 : ℕ))).trans (finCongr edgeOldSize).symm);
    ∀ (edge_cases :
    ∀ (x : Fin T.length), (
    ∃ (q : Fin (C.p - (1 : ℕ))), (↑x : ℕ) = (↑q : ℕ)) ∨ (
    ∃ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) +
        (↑j : ℕ)) ∨
    ∃ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) *
        D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)),
    let newVertex : Fin (T.length + (1 : ℕ)) → V := fun (i : Fin (T.length + (1 : ℕ))) ↦ T.vertex
        ((vertexOrder : (a : Fin (T.length + (1 : ℕ))) → Fin (T.length + (1 : ℕ))) i);
    let newEdge : Fin T.length → E := fun (i : Fin T.length) ↦ T.edge ((edgeOrder : (a : Fin
        T.length) → Fin T.length) i);
    ∀ (newVertex_base :
    ∀ (x : Fin (T.length + (1 : ℕ))) (hx : (↑x : ℕ) < C.p), newVertex x = T.vertex x)
        (newEdge_base :
    ∀ (x : Fin T.length) (hx : (↑x : ℕ) < C.p - (1 : ℕ)), newEdge x = T.edge x)
        (newVertex_absorbed :
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), newVertex (⟨C.p + (2 : ℕ) * (↑h : ℕ) + (↑j :
        ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = C.blockVertex (↑((D.absorbedEquiv : (a : Fin D.absorbedCount)
        → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) j) (newVertex_retained :
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), newVertex (⟨C.p + (2 : ℕ) * D.absorbedCount +
        (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 :
        ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = C.blockVertex (D.retained t) j) (newEdge_absorbed :
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), newEdge (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) +
        (↑j : ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length) = C.blockEdge (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) j) (newEdge_retained :
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), newEdge (⟨C.p - (1 : ℕ) + (2 : ℕ) *
        D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) <
        T.length) ↦
    by omega
    ⟩ : Fin T.length) = C.blockEdge (D.retained t) j) (newVertex_base_position :
    ∀ (q : Fin C.p), newVertex (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p := q.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = C.y q) (newEdge_base_position :
    ∀ (q : Fin (C.p - (1 : ℕ))), newEdge (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p - (1 : ℕ) := q.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length) = C.baseEdge q) (newAttaches :
    ∀ (x : Fin T.length),
    ∃ (i : Fin ((↑x : ℕ) + (1 : ℕ))), G.ends (newEdge x) = s(newVertex x.succ, newVertex (i.castLT
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ x.isLt))))),
    ∃ (T' : TreeSequence G e0), Nonempty (ScheideStructuralReorderingData G k e0 phi T C D T')

private abbrev helperContinuation503Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
    ∀ (blockIndex_bijective : Function.Bijective blockIndex),
    let sumFin : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let pairFin : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s := (sumFin D.absorbedCount
        D.retainedCount).symm.trans (Equiv.ofBijective blockIndex blockIndex_bijective);
    let reorderCore : (b : ℕ) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) ≃ Fin (b +
        C.s * (2 : ℕ)) := fun (b : ℕ) ↦ ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ))).symm.trans ((Equiv.refl (Fin b)).sumCongr ((pairFin (D.absorbedCount +
        D.retainedCount)).symm.trans ((blockOrder.prodCongr (Equiv.refl (Fin (2 : ℕ)))).trans
        (pairFin C.s))))).trans (sumFin b (C.s * (2 : ℕ)));
    ∀ (vertexNewSize : T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ))
        (vertexOldSize : T.length + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (edgeNewSize : T.length = C.p -
        (1 : ℕ) + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (edgeOldSize : T.length = C.p -
        (1 : ℕ) + C.s * (2 : ℕ)),
    let vertexOrder : Equiv.Perm (Fin (T.length + (1 : ℕ))) := (finCongr vertexNewSize).trans
        ((reorderCore C.p).trans (finCongr vertexOldSize).symm);
    let edgeOrder : Equiv.Perm (Fin T.length) := (finCongr edgeNewSize).trans ((reorderCore (C.p -
        (1 : ℕ))).trans (finCongr edgeOldSize).symm);
    ∀ (vertexOrder_base :
    ∀ (q : Fin C.p), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) → Fin (T.length + (1 : ℕ)))
        (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p := q.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p := q.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (vertexOrder_absorbed :
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) →
        Fin (T.length + (1 : ℕ))) (⟨C.p + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨C.p + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j :
        ℕ),
    have hh : (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) < C.s :=
        (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (vertexOrder_retained :
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) →
        Fin (T.length + (1 : ℕ))) (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j :
        ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨C.p + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ),
    have ht : (↑(D.retained t) : ℕ) < C.s := (D.retained t).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (edgeOrder_base :
    ∀ (q : Fin (C.p - (1 : ℕ))), (edgeOrder : (a : Fin T.length) → Fin T.length) (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p - (1 : ℕ) := q.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length) = (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p - (1 : ℕ) := q.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length)) (edgeOrder_absorbed :
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (edgeOrder : (a : Fin T.length) → Fin T.length)
        (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length) = (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j :
        ℕ),
    have hh : (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) < C.s :=
        (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length)) (edgeOrder_retained :
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (edgeOrder : (a : Fin T.length) → Fin T.length)
        (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) <
        T.length) ↦
    by omega
    ⟩ : Fin T.length) = (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ),
    have ht : (↑(D.retained t) : ℕ) < C.s := (D.retained t).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ) < T.length) ↦
    by
            omega
    ⟩ : Fin T.length)) (edge_cases :
    ∀ (x : Fin T.length), (
    ∃ (q : Fin (C.p - (1 : ℕ))), (↑x : ℕ) = (↑q : ℕ)) ∨ (
    ∃ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) +
        (↑j : ℕ)) ∨
    ∃ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) *
        D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)),
    ∃ (T' : TreeSequence G e0), Nonempty (ScheideStructuralReorderingData G k e0 phi T C D T')

private abbrev helperContinuation309Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
    ∀ (blockIndex_bijective : Function.Bijective blockIndex),
    let sumFin : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let pairFin : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s := (sumFin D.absorbedCount
        D.retainedCount).symm.trans (Equiv.ofBijective blockIndex blockIndex_bijective);
    let reorderCore : (b : ℕ) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) ≃ Fin (b +
        C.s * (2 : ℕ)) := fun (b : ℕ) ↦ ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ))).symm.trans ((Equiv.refl (Fin b)).sumCongr ((pairFin (D.absorbedCount +
        D.retainedCount)).symm.trans ((blockOrder.prodCongr (Equiv.refl (Fin (2 : ℕ)))).trans
        (pairFin C.s))))).trans (sumFin b (C.s * (2 : ℕ)));
    ∀ (reorderCore_base :
    ∀ (b : ℕ) (q : Fin b), (reorderCore b : (a : Fin (b + (D.absorbedCount + D.retainedCount) * (2
        : ℕ))) → Fin (b + C.s * (2 : ℕ))) ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ)) : (a : Fin b ⊕ Fin ((D.absorbedCount + D.retainedCount) * (2 : ℕ))) → Fin (b +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ))) (Sum.inl q)) = (sumFin b (C.s * (2 : ℕ)) :
        (a : Fin b ⊕ Fin (C.s * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) (Sum.inl q))
        (reorderCore_absorbed :
    ∀ (b : ℕ) (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (reorderCore b : (a : Fin (b +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) ((sumFin b
        ((D.absorbedCount + D.retainedCount) * (2 : ℕ)) : (a : Fin b ⊕ Fin ((D.absorbedCount +
        D.retainedCount) * (2 : ℕ))) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        (Sum.inr ((pairFin (D.absorbedCount + D.retainedCount) : (a : Fin (D.absorbedCount +
        D.retainedCount) × Fin (2 : ℕ)) → Fin ((D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        ((sumFin D.absorbedCount D.retainedCount : (a : Fin D.absorbedCount ⊕ Fin D.retainedCount)
        → Fin (D.absorbedCount + D.retainedCount)) (Sum.inl h), j)))) = (sumFin b (C.s * (2 : ℕ))
        : (a : Fin b ⊕ Fin (C.s * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) (Sum.inr ((pairFin C.s : (a
        : Fin C.s × Fin (2 : ℕ)) → Fin (C.s * (2 : ℕ))) ((↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s), j))))
        (reorderCore_retained :
    ∀ (b : ℕ) (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (reorderCore b : (a : Fin (b +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) ((sumFin b
        ((D.absorbedCount + D.retainedCount) * (2 : ℕ)) : (a : Fin b ⊕ Fin ((D.absorbedCount +
        D.retainedCount) * (2 : ℕ))) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        (Sum.inr ((pairFin (D.absorbedCount + D.retainedCount) : (a : Fin (D.absorbedCount +
        D.retainedCount) × Fin (2 : ℕ)) → Fin ((D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        ((sumFin D.absorbedCount D.retainedCount : (a : Fin D.absorbedCount ⊕ Fin D.retainedCount)
        → Fin (D.absorbedCount + D.retainedCount)) (Sum.inr t), j)))) = (sumFin b (C.s * (2 : ℕ))
        : (a : Fin b ⊕ Fin (C.s * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) (Sum.inr ((pairFin C.s : (a
        : Fin C.s × Fin (2 : ℕ)) → Fin (C.s * (2 : ℕ))) (D.retained t, j)))) (vertexNewSize :
        T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (vertexOldSize :
        T.length + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (edgeNewSize : T.length = C.p - (1 : ℕ) +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (edgeOldSize : T.length = C.p - (1 : ℕ) +
        C.s * (2 : ℕ)),
    let vertexOrder : Equiv.Perm (Fin (T.length + (1 : ℕ))) := (finCongr vertexNewSize).trans
        ((reorderCore C.p).trans (finCongr vertexOldSize).symm);
    let edgeOrder : Equiv.Perm (Fin T.length) := (finCongr edgeNewSize).trans ((reorderCore (C.p -
        (1 : ℕ))).trans (finCongr edgeOldSize).symm);
    ∀ (vertexOrder_base :
    ∀ (q : Fin C.p), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) → Fin (T.length + (1 : ℕ)))
        (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p := q.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨(↑q : ℕ),
    have hq : (↑q : ℕ) < C.p := q.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (vertexOrder_absorbed :
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) →
        Fin (T.length + (1 : ℕ))) (⟨C.p + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨C.p + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j :
        ℕ),
    have hh : (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) < C.s :=
        (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j : ℕ) < T.length + (1
        : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (vertexOrder_retained :
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (vertexOrder : (a : Fin (T.length + (1 : ℕ))) →
        Fin (T.length + (1 : ℕ))) (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j :
        ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 :
        ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) = (⟨C.p + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ),
    have ht : (↑(D.retained t) : ℕ) < C.s := (D.retained t).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) ↦
    by
            omega
    ⟩ : Fin (T.length + (1 : ℕ)))),
    ∃ (T' : TreeSequence G e0), Nonempty (ScheideStructuralReorderingData G k e0 phi T C D T')

private theorem helper_blockIndex_injective_45.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : Fin D.absorbedCount →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained; Function.Injective
        blockIndex := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex x y hxy
  cases x with
  | inl h =>
      cases y with
      | inl h' =>
          congr 1
          apply D.absorbedEquiv.injective
          apply Subtype.ext
          exact hxy
      | inr t =>
          exfalso
          exact (D.absorbedEquiv h).2 ⟨t, hxy.symm⟩
  | inr t =>
      cases y with
      | inl h =>
          exfalso
          exact (D.absorbedEquiv h).2 ⟨t, hxy⟩
      | inr t' =>
          congr 1
          exact D.retained_injective hxy

private theorem helper_blockIndex_surjective_84.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : Fin D.absorbedCount →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
        Function.Surjective blockIndex := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex i
  rcases D.partition i with h | h
  · obtain ⟨a, ha, -⟩ := h
    exact ⟨Sum.inl a, ha⟩
  · obtain ⟨r, hr, -⟩ := h
    exact ⟨Sum.inr r, hr⟩

private theorem helper_continuation_521.{u_1, u_2} :
    helperContinuation521Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex blockIndex_bijective sumFin pairFin blockOrder
      reorderCore vertexNewSize vertexOldSize edgeNewSize edgeOldSize vertexOrder edgeOrder
      edge_cases newVertex newEdge newVertex_base newEdge_base newVertex_absorbed
      newVertex_retained newEdge_absorbed newEdge_retained newVertex_base_position
      newEdge_base_position newAttaches
  let T' : TreeSequence G e0 :=
    { length := T.length
      positive := T.positive
      vertex := newVertex
      edge := newEdge
      vertex_injective := T.vertex_injective.comp vertexOrder.injective
      edge_injective := T.edge_injective.comp edgeOrder.injective
      first_edge := by
        rw [newEdge_base _ (by have hp := C.p_ge_two; simp; omega)]
        exact T.first_edge
      attaches := newAttaches }
  have newTashkinov : TashkinovTree G e0 phi T' := by
    intro x hxnonzero
    change ∃ i : Fin (x.val + 1), ∃ c : Fin k,
      phi (newEdge x) = some c ∧
        c ∈ MissingColors G phi
          (newVertex (Fin.castLT i
            (Nat.lt_trans i.isLt (Nat.succ_lt_succ x.isLt))))
    rcases edge_cases x with ⟨q, hx⟩ | ⟨h, j, hx⟩ | ⟨t, j, hx⟩
    · obtain ⟨i, c, hc, hm⟩ := C.globally_maximum.2.1 x hxnonzero
      refine ⟨i, c, ?_, ?_⟩
      · rw [newEdge_base x (by omega)]
        exact hc
      · rw [newVertex_base _ (by
            have hp := C.p_ge_two
            simp
            omega)]
        exact hm
    · obtain ⟨q, hmissing⟩ :=
        C.block_color_missing_on_base (D.absorbedEquiv h).1
      let i : Fin (x.val + 1) := ⟨q.val, by have hq := q.isLt; omega⟩
      refine ⟨i, C.gamma (D.absorbedEquiv h).1, ?_, ?_⟩
      · have hxeq : x = ⟨C.p - 1 + 2 * h.val + j.val, by
            have hh := h.isLt
            have hj := j.isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hd := D.count_eq
            omega⟩ := Fin.ext hx
        rw [hxeq, newEdge_absorbed]
        exact C.block_color (D.absorbedEquiv h).1 j
      · rw [newVertex_base _ (by have hq := q.isLt; simp [i])]
        have hindex : (Fin.castLT i (Nat.lt_trans i.isLt
            (Nat.succ_lt_succ x.isLt))) =
            ⟨q.val, by have hq := q.isLt; have hc := C.length_eq; omega⟩ :=
          Fin.ext rfl
        rw [hindex, C.base_vertex_position]
        exact hmissing
    · obtain ⟨q, hmissing⟩ :=
        C.block_color_missing_on_base (D.retained t)
      let i : Fin (x.val + 1) := ⟨q.val, by have hq := q.isLt; omega⟩
      refine ⟨i, C.gamma (D.retained t), ?_, ?_⟩
      · have hxeq : x =
            ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
              have ht := t.isLt
              have hj := j.isLt
              have hp := C.p_ge_two
              have hc := C.length_eq
              have hd := D.count_eq
              omega⟩ := Fin.ext hx
        rw [hxeq, newEdge_retained]
        exact C.block_color (D.retained t) j
      · rw [newVertex_base _ (by have hq := q.isLt; simp [i])]
        have hindex : (Fin.castLT i (Nat.lt_trans i.isLt
            (Nat.succ_lt_succ x.isLt))) =
            ⟨q.val, by have hq := q.isLt; have hc := C.length_eq; omega⟩ :=
          Fin.ext rfl
        rw [hindex, C.base_vertex_position]
        exact hmissing
  have vertexSetEq : TreeSequenceVertexSet T' = TreeSequenceVertexSet T := by
    ext v
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨vertexOrder i, by simpa [T', newVertex] using hi⟩
    · rintro ⟨i, hi⟩
      refine ⟨vertexOrder.symm i, ?_⟩
      simpa [T', newVertex] using hi
  refine ⟨T', ⟨?_⟩⟩
  refine
    { length_eq := rfl
      base_vertex_position := ?_
      absorbed_vertex_position := ?_
      retained_vertex_position := ?_
      base_edge_position := ?_
      absorbed_edge_position := ?_
      retained_edge_position := ?_
      tashkinov := newTashkinov
      vertex_set_eq := vertexSetEq
      exit_set_eq := ?_ }
  · intro q
    simpa [T'] using newVertex_base_position q
  · intro h j
    simpa [T'] using newVertex_absorbed h j
  · intro t j
    simpa [T'] using newVertex_retained t j
  · intro q
    simpa [T'] using newEdge_base_position q
  · intro h j
    simpa [T'] using newEdge_absorbed h j
  · intro t j
    simpa [T'] using newEdge_retained t j
  · classical
    unfold ScheideExitVertices
    apply Finset.filter_congr
    intro v hv
    simp only [ScheideExitVertex, ScheideDefectiveChainPath, vertexSetEq]

private theorem helper_continuation_503.{u_1, u_2} :
    helperContinuation503Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex blockIndex_bijective sumFin pairFin blockOrder
      reorderCore vertexNewSize vertexOldSize edgeNewSize edgeOldSize vertexOrder edgeOrder
      vertexOrder_base vertexOrder_absorbed vertexOrder_retained edgeOrder_base
      edgeOrder_absorbed edgeOrder_retained edge_cases
  let newVertex : Fin (T.length + 1) → V := fun i => T.vertex (vertexOrder i)
  let newEdge : Fin T.length → E := fun i => T.edge (edgeOrder i)
  have newVertex_base (x : Fin (T.length + 1)) (hx : x.val < C.p) :
      newVertex x = T.vertex x := by
    let q : Fin C.p := ⟨x.val, hx⟩
    have horder := vertexOrder_base q
    have hqx : (⟨q.val, by
        have hq := q.isLt
        have hc := C.length_eq
        omega⟩ : Fin (T.length + 1)) = x := Fin.ext rfl
    simpa [newVertex, hqx] using congrArg T.vertex horder
  have newEdge_base (x : Fin T.length) (hx : x.val < C.p - 1) :
      newEdge x = T.edge x := by
    let q : Fin (C.p - 1) := ⟨x.val, hx⟩
    have horder := edgeOrder_base q
    have hqx : (⟨q.val, by
        have hq := q.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        omega⟩ : Fin T.length) = x := Fin.ext rfl
    simpa [newEdge, hqx] using congrArg T.edge horder
  have newVertex_absorbed (h : Fin D.absorbedCount) (j : Fin 2) :
      newVertex ⟨C.p + 2 * h.val + j.val, by
        have hh := h.isLt
        have hj := j.isLt
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ = C.blockVertex (D.absorbedEquiv h).1 j := by
    change T.vertex (vertexOrder _) = _
    rw [vertexOrder_absorbed]
    exact C.block_vertex_position (D.absorbedEquiv h).1 j
  have newVertex_retained (t : Fin D.retainedCount) (j : Fin 2) :
      newVertex
        ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
          have ht := t.isLt
          have hj := j.isLt
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ = C.blockVertex (D.retained t) j := by
    change T.vertex (vertexOrder _) = _
    rw [vertexOrder_retained]
    exact C.block_vertex_position (D.retained t) j
  have newEdge_absorbed (h : Fin D.absorbedCount) (j : Fin 2) :
      newEdge ⟨C.p - 1 + 2 * h.val + j.val, by
        have hh := h.isLt
        have hj := j.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ = C.blockEdge (D.absorbedEquiv h).1 j := by
    change T.edge (edgeOrder _) = _
    rw [edgeOrder_absorbed]
    exact C.block_edge_position (D.absorbedEquiv h).1 j
  have newEdge_retained (t : Fin D.retainedCount) (j : Fin 2) :
      newEdge
        ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
          have ht := t.isLt
          have hj := j.isLt
          have hp := C.p_ge_two
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ = C.blockEdge (D.retained t) j := by
    change T.edge (edgeOrder _) = _
    rw [edgeOrder_retained]
    exact C.block_edge_position (D.retained t) j
  have newVertex_base_position (q : Fin C.p) :
      newVertex ⟨q.val, by
        have hq := q.isLt
        have hc := C.length_eq
        omega⟩ = C.y q := by
    change T.vertex (vertexOrder _) = _
    rw [vertexOrder_base]
    exact C.base_vertex_position q
  have newEdge_base_position (q : Fin (C.p - 1)) :
      newEdge ⟨q.val, by
        have hq := q.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        omega⟩ = C.baseEdge q := by
    change T.edge (edgeOrder _) = _
    rw [edgeOrder_base]
    exact C.base_edge_position q
  have newAttaches :
    ∀ x : Fin T.length,
    ∃ i : Fin (x.val + 1), G.ends (newEdge x) = s(newVertex x.succ, newVertex (Fin.castLT i
        (Nat.lt_trans i.isLt (Nat.succ_lt_succ x.isLt)))) := by
    intro x
    rcases edge_cases x with ⟨q, hx⟩ | ⟨h, j, hx⟩ | ⟨t, j, hx⟩
    · obtain ⟨i, hi⟩ := T.attaches x
      refine ⟨i, ?_⟩
      have hp := C.p_ge_two
      rw [newEdge_base x (by omega)]
      rw [newVertex_base x.succ (by simp; omega)]
      rw [newVertex_base
        (Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ x.isLt)))
        (by simp; omega)]
      exact hi
    · have hxeq : x = ⟨C.p - 1 + 2 * h.val + j.val, by
          have hh := h.isLt
          have hj := j.isLt
          have hp := C.p_ge_two
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ := Fin.ext hx
      obtain ⟨q, hends⟩ := C.block_attaches_to_base
        (D.absorbedEquiv h).1 j
      let i : Fin (x.val + 1) :=
        ⟨q.val, by have hq := q.isLt; omega⟩
      refine ⟨i, ?_⟩
      have hedge : newEdge x = C.blockEdge (D.absorbedEquiv h).1 j := by
        rw [hxeq, newEdge_absorbed]
      rw [hedge]
      have hsucc : x.succ =
          ⟨C.p + 2 * h.val + j.val, by
            have hh := h.isLt
            have hj := j.isLt
            have hc := C.length_eq
            have hd := D.count_eq
            omega⟩ := Fin.ext (by simp; omega)
      rw [hsucc, newVertex_absorbed]
      rw [newVertex_base _ (by have hq := q.isLt; simp [i])]
      have hindex : (Fin.castLT i (Nat.lt_trans i.isLt
          (Nat.succ_lt_succ x.isLt))) =
          ⟨q.val, by have hq := q.isLt; have hc := C.length_eq; omega⟩ :=
        Fin.ext rfl
      rw [hindex, C.base_vertex_position]
      exact hends.trans Sym2.eq_swap
    · have hxeq : x =
          ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
            have ht := t.isLt
            have hj := j.isLt
            have hp := C.p_ge_two
            have hc := C.length_eq
            have hd := D.count_eq
            omega⟩ := Fin.ext hx
      obtain ⟨q, hends⟩ := C.block_attaches_to_base (D.retained t) j
      let i : Fin (x.val + 1) := ⟨q.val, by have hq := q.isLt; omega⟩
      refine ⟨i, ?_⟩
      have hedge : newEdge x = C.blockEdge (D.retained t) j := by
        rw [hxeq, newEdge_retained]
      rw [hedge]
      have hsucc : x.succ =
          ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
            have ht := t.isLt
            have hj := j.isLt
            have hc := C.length_eq
            have hd := D.count_eq
            omega⟩ := Fin.ext (by simp; omega)
      rw [hsucc, newVertex_retained]
      rw [newVertex_base _ (by have hq := q.isLt; simp [i])]
      have hindex : (Fin.castLT i (Nat.lt_trans i.isLt
          (Nat.succ_lt_succ x.isLt))) =
          ⟨q.val, by have hq := q.isLt; have hc := C.length_eq; omega⟩ :=
        Fin.ext rfl
      rw [hindex, C.base_vertex_position]
      exact hends.trans Sym2.eq_swap
  exact @helper_continuation_521 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@blockIndex_bijective)
      (@vertexNewSize) (@vertexOldSize) (@edgeNewSize) (@edgeOldSize) (@edge_cases)
      (@newVertex_base) (@newEdge_base) (@newVertex_absorbed) (@newVertex_retained)
      (@newEdge_absorbed) (@newEdge_retained) (@newVertex_base_position) (@newEdge_base_position)
      (@newAttaches)
private theorem helper_edgeOrder_absorbed_972.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
    ∀ (blockIndex_bijective : Function.Bijective blockIndex),
    let sumFin : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let pairFin : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s := (sumFin D.absorbedCount
        D.retainedCount).symm.trans (Equiv.ofBijective blockIndex blockIndex_bijective);
    let reorderCore : (b : ℕ) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) ≃ Fin (b +
        C.s * (2 : ℕ)) := fun (b : ℕ) ↦ ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ))).symm.trans ((Equiv.refl (Fin b)).sumCongr ((pairFin (D.absorbedCount +
        D.retainedCount)).symm.trans ((blockOrder.prodCongr (Equiv.refl (Fin (2 : ℕ)))).trans
        (pairFin C.s))))).trans (sumFin b (C.s * (2 : ℕ)));
    ∀ (_ :
    ∀ (b : ℕ) (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (reorderCore b : (a : Fin (b +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) ((sumFin b
        ((D.absorbedCount + D.retainedCount) * (2 : ℕ)) : (a : Fin b ⊕ Fin ((D.absorbedCount +
        D.retainedCount) * (2 : ℕ))) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        (Sum.inr ((pairFin (D.absorbedCount + D.retainedCount) : (a : Fin (D.absorbedCount +
        D.retainedCount) × Fin (2 : ℕ)) → Fin ((D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        ((sumFin D.absorbedCount D.retainedCount : (a : Fin D.absorbedCount ⊕ Fin D.retainedCount)
        → Fin (D.absorbedCount + D.retainedCount)) (Sum.inl h), j)))) = (sumFin b (C.s * (2 : ℕ))
        : (a : Fin b ⊕ Fin (C.s * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) (Sum.inr ((pairFin C.s : (a
        : Fin C.s × Fin (2 : ℕ)) → Fin (C.s * (2 : ℕ))) ((↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s), j))))
        (vertexNewSize : T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ))
        (vertexOldSize : T.length + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (edgeNewSize : T.length = C.p -
        (1 : ℕ) + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (edgeOldSize : T.length = C.p -
        (1 : ℕ) + C.s * (2 : ℕ)),
    let edgeOrder : Equiv.Perm (Fin T.length) := (finCongr edgeNewSize).trans ((reorderCore (C.p -
        (1 : ℕ))).trans (finCongr edgeOldSize).symm);
    ∀ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (edgeOrder : (a : Fin T.length) → Fin T.length)
        (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
    have hh : (↑h : ℕ) < D.absorbedCount := h.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have _ : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have _ : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have _ : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) < T.length) ↦
    by
              omega
    ⟩ : Fin T.length) = (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin
        D.absorbedCount) → { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j :
        ℕ),
    have hh : (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) < C.s :=
        (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have _ : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have _ : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑(↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s) : ℕ) + (↑j : ℕ) < T.length) ↦
    by
            omega
    ⟩ : Fin T.length) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex blockIndex_bijective sumFin pairFin blockOrder
      reorderCore reorderCore_absorbed vertexNewSize vertexOldSize edgeNewSize edgeOldSize
      edgeOrder h j
  apply Fin.ext
  simp only [edgeOrder, Equiv.trans_apply]
  have hinput : (⟨C.p - 1 + 2 * h.val + j.val, by
        have hh := h.isLt
        have hj := j.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ : Fin ((C.p - 1) +
          (D.absorbedCount + D.retainedCount) * 2)) =
      sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inr (pairFin (D.absorbedCount + D.retainedCount)
          (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j))) := by
    apply Fin.ext
    simp [sumFin, pairFin]
    omega
  have hcast : (finCongr edgeNewSize)
        ⟨C.p - 1 + 2 * h.val + j.val, by
          have hh := h.isLt
          have hj := j.isLt
          have hp := C.p_ge_two
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ =
      sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inr (pairFin (D.absorbedCount + D.retainedCount)
          (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j))) := by
    exact hinput
  rw [hcast, reorderCore_absorbed]
  simp [sumFin, pairFin]
  omega

private theorem helper_edgeOrder_retained_1017.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s := Sum.elim (fun (h : Fin
        D.absorbedCount) ↦ (↑((D.absorbedEquiv : (a : Fin D.absorbedCount) →
        { i : Fin C.s // i ∉ Set.range D.retained }) h) : Fin C.s)) D.retained;
    ∀ (blockIndex_bijective : Function.Bijective blockIndex),
    let sumFin : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let pairFin : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s := (sumFin D.absorbedCount
        D.retainedCount).symm.trans (Equiv.ofBijective blockIndex blockIndex_bijective);
    let reorderCore : (b : ℕ) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) ≃ Fin (b +
        C.s * (2 : ℕ)) := fun (b : ℕ) ↦ ((sumFin b ((D.absorbedCount + D.retainedCount) * (2 :
        ℕ))).symm.trans ((Equiv.refl (Fin b)).sumCongr ((pairFin (D.absorbedCount +
        D.retainedCount)).symm.trans ((blockOrder.prodCongr (Equiv.refl (Fin (2 : ℕ)))).trans
        (pairFin C.s))))).trans (sumFin b (C.s * (2 : ℕ)));
    ∀ (_ :
    ∀ (b : ℕ) (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (reorderCore b : (a : Fin (b +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) ((sumFin b
        ((D.absorbedCount + D.retainedCount) * (2 : ℕ)) : (a : Fin b ⊕ Fin ((D.absorbedCount +
        D.retainedCount) * (2 : ℕ))) → Fin (b + (D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        (Sum.inr ((pairFin (D.absorbedCount + D.retainedCount) : (a : Fin (D.absorbedCount +
        D.retainedCount) × Fin (2 : ℕ)) → Fin ((D.absorbedCount + D.retainedCount) * (2 : ℕ)))
        ((sumFin D.absorbedCount D.retainedCount : (a : Fin D.absorbedCount ⊕ Fin D.retainedCount)
        → Fin (D.absorbedCount + D.retainedCount)) (Sum.inr t), j)))) = (sumFin b (C.s * (2 : ℕ))
        : (a : Fin b ⊕ Fin (C.s * (2 : ℕ))) → Fin (b + C.s * (2 : ℕ))) (Sum.inr ((pairFin C.s : (a
        : Fin C.s × Fin (2 : ℕ)) → Fin (C.s * (2 : ℕ))) (D.retained t, j)))) (vertexNewSize :
        T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (vertexOldSize :
        T.length + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (edgeNewSize : T.length = C.p - (1 : ℕ) +
        (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (edgeOldSize : T.length = C.p - (1 : ℕ) +
        C.s * (2 : ℕ)),
    let edgeOrder : Equiv.Perm (Fin T.length) := (finCongr edgeNewSize).trans ((reorderCore (C.p -
        (1 : ℕ))).trans (finCongr edgeOldSize).symm);
    ∀ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (edgeOrder : (a : Fin T.length) → Fin T.length)
        (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
    have ht : (↑t : ℕ) < D.retainedCount := t.isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have _ : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have _ : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
    have _ : C.s = D.absorbedCount + D.retainedCount := D.count_eq; Decidable.byContradiction fun
        (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) <
        T.length) ↦
    by
              omega
    ⟩ : Fin T.length) = (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ),
    have ht : (↑(D.retained t) : ℕ) < C.s := (D.retained t).isLt;
    have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
    have _ : (2 : ℕ) ≤ C.p := C.p_ge_two;
    have _ : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq; Decidable.byContradiction
        fun (a : ¬C.p - (1 : ℕ) + (2 : ℕ) * (↑(D.retained t) : ℕ) + (↑j : ℕ) < T.length) ↦
    by
            omega
    ⟩ : Fin T.length) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex blockIndex_bijective sumFin pairFin blockOrder
      reorderCore reorderCore_retained vertexNewSize vertexOldSize edgeNewSize edgeOldSize
      edgeOrder t j
  apply Fin.ext
  simp only [edgeOrder, Equiv.trans_apply]
  have hinput :
      (⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
        have ht := t.isLt
        have hj := j.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ : Fin ((C.p - 1) +
          (D.absorbedCount + D.retainedCount) * 2)) =
      sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inr (pairFin (D.absorbedCount + D.retainedCount)
          (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j))) := by
    apply Fin.ext
    simp [sumFin, pairFin]
    omega
  have hcast : (finCongr edgeNewSize)
        ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
          have ht := t.isLt
          have hj := j.isLt
          have hp := C.p_ge_two
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ =
      sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inr (pairFin (D.absorbedCount + D.retainedCount)
          (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j))) := by
    exact hinput
  rw [hcast, reorderCore_retained]
  simp [sumFin, pairFin]
  omega

private theorem helper_edge_cases_1064.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (C : ScheideStructuralConfiguration G k e0 phi T) (D :
        ScheideStructuralSelectionData G k e0 phi T C),
    let _ : (m n : ℕ) → Fin m ⊕ Fin n ≃ Fin (m + n) := structuralSumFin;
    let _ : (m : ℕ) → Fin m × Fin (2 : ℕ) ≃ Fin (m * (2 : ℕ)) := structuralPairFin;
    ∀ (_ : T.length + (1 : ℕ) = C.p + (D.absorbedCount + D.retainedCount) * (2 : ℕ)) (_ : T.length
        + (1 : ℕ) = C.p + C.s * (2 : ℕ)) (_ : T.length = C.p - (1 : ℕ) + (D.absorbedCount +
        D.retainedCount) * (2 : ℕ)) (x : Fin T.length), (
    ∃ (q : Fin (C.p - (1 : ℕ))), (↑x : ℕ) = (↑q : ℕ)) ∨ (
    ∃ (h : Fin D.absorbedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) +
        (↑j : ℕ)) ∨
    ∃ (t : Fin D.retainedCount) (j : Fin (2 : ℕ)), (↑x : ℕ) = C.p - (1 : ℕ) + (2 : ℕ) *
        D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D sumFin pairFin vertexNewSize vertexOldSize edgeNewSize x
  let xn := finCongr edgeNewSize x
  generalize hout :
    (sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)).symm xn =
      outer
  cases outer with
  | inl q =>
      left
      refine ⟨q, ?_⟩
      have heq : xn =
          sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
            (Sum.inl q) := by
        rw [← hout]
        exact (sumFin (C.p - 1)
          ((D.absorbedCount + D.retainedCount) * 2)).apply_symm_apply xn |>.symm
      exact congrArg Fin.val heq
  | inr z =>
      right
      generalize hpair :
        (pairFin (D.absorbedCount + D.retainedCount)).symm z = ij
      obtain ⟨i, j⟩ := ij
      generalize hslot :
        (sumFin D.absorbedCount D.retainedCount).symm i = slot
      cases slot with
      | inl h =>
          left
          refine ⟨h, j, ?_⟩
          have hi : i = sumFin D.absorbedCount D.retainedCount
              (Sum.inl h) := by
            rw [← hslot]
            exact (sumFin D.absorbedCount
              D.retainedCount).apply_symm_apply i |>.symm
          have hz : z = pairFin (D.absorbedCount + D.retainedCount)
              (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j) := by
            calc
              z = pairFin (D.absorbedCount + D.retainedCount) (i, j) := by
                rw [← hpair]
                exact (pairFin
                  (D.absorbedCount + D.retainedCount)).apply_symm_apply z |>.symm
              _ = _ := by rw [hi]
          have hx : xn =
              sumFin (C.p - 1)
                ((D.absorbedCount + D.retainedCount) * 2)
                (Sum.inr (pairFin
                  (D.absorbedCount + D.retainedCount)
                  (sumFin D.absorbedCount D.retainedCount
                    (Sum.inl h), j))) := by
            calc
              xn = sumFin (C.p - 1)
                  ((D.absorbedCount + D.retainedCount) * 2)
                  (Sum.inr z) := by
                rw [← hout]
                exact (sumFin (C.p - 1)
                  ((D.absorbedCount + D.retainedCount) * 2)).apply_symm_apply xn |>.symm
              _ = _ := by rw [hz]
          have hv := congrArg Fin.val hx
          simp [xn, sumFin, pairFin] at hv
          omega
      | inr t =>
          right
          refine ⟨t, j, ?_⟩
          have hi : i = sumFin D.absorbedCount D.retainedCount
              (Sum.inr t) := by
            rw [← hslot]
            exact (sumFin D.absorbedCount
              D.retainedCount).apply_symm_apply i |>.symm
          have hz : z = pairFin (D.absorbedCount + D.retainedCount)
              (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j) := by
            calc
              z = pairFin (D.absorbedCount + D.retainedCount) (i, j) := by
                rw [← hpair]
                exact (pairFin
                  (D.absorbedCount + D.retainedCount)).apply_symm_apply z |>.symm
              _ = _ := by rw [hi]
          have hx : xn =
              sumFin (C.p - 1)
                ((D.absorbedCount + D.retainedCount) * 2)
                (Sum.inr (pairFin
                  (D.absorbedCount + D.retainedCount)
                  (sumFin D.absorbedCount D.retainedCount
                    (Sum.inr t), j))) := by
            calc
              xn = sumFin (C.p - 1)
                  ((D.absorbedCount + D.retainedCount) * 2)
                  (Sum.inr z) := by
                rw [← hout]
                exact (sumFin (C.p - 1)
                  ((D.absorbedCount + D.retainedCount) * 2)).apply_symm_apply xn |>.symm
              _ = _ := by rw [hz]
          have hv := congrArg Fin.val hx
          simp [xn, sumFin, pairFin] at hv
          omega

private theorem helper_continuation_309.{u_1, u_2} :
    helperContinuation309Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D blockIndex blockIndex_bijective sumFin pairFin blockOrder
      reorderCore reorderCore_base reorderCore_absorbed reorderCore_retained vertexNewSize
      vertexOldSize edgeNewSize edgeOldSize vertexOrder edgeOrder vertexOrder_base
      vertexOrder_absorbed vertexOrder_retained
  have edgeOrder_base (q : Fin (C.p - 1)) :
      edgeOrder ⟨q.val, by
        have hq := q.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        omega⟩ = ⟨q.val, by
        have hq := q.isLt
        have hp := C.p_ge_two
        have hc := C.length_eq
        omega⟩ := by
    apply Fin.ext
    change ((reorderCore (C.p - 1))
      (sumFin (C.p - 1) ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inl q))).val = q.val
    rw [reorderCore_base]
    rfl
  have edgeOrder_absorbed := @helper_edgeOrder_absorbed_972 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@blockIndex_bijective)
      (@reorderCore_absorbed) (@vertexNewSize) (@vertexOldSize) (@edgeNewSize) (@edgeOldSize)
  have edgeOrder_retained := @helper_edgeOrder_retained_1017 (@V) (@E) inferInstance inferInstance
      inferInstance inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@blockIndex_bijective)
      (@reorderCore_retained) (@vertexNewSize) (@vertexOldSize) (@edgeNewSize) (@edgeOldSize)
  have edge_cases := @helper_edge_cases_1064 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@vertexNewSize) (@vertexOldSize)
      (@edgeNewSize)
  exact @helper_continuation_503 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@blockIndex_bijective)
      (@vertexNewSize) (@vertexOldSize) (@edgeNewSize) (@edgeOldSize) (@vertexOrder_base)
      (@vertexOrder_absorbed) (@vertexOrder_retained) (@edgeOrder_base) (@edgeOrder_absorbed)
      (@edgeOrder_retained) (@edge_cases)
theorem ScheideStructuralReordering {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C) :
    ∃ T' : TreeSequence G e0,
      Nonempty (ScheideStructuralReorderingData G k e0 phi T C D T') := by
  let blockIndex : Fin D.absorbedCount ⊕ Fin D.retainedCount → Fin C.s :=
    Sum.elim (fun h => (D.absorbedEquiv h).1) D.retained
  have blockIndex_injective : Function.Injective blockIndex := by
    apply helper_blockIndex_injective_45
  have blockIndex_surjective : Function.Surjective blockIndex := by
    apply helper_blockIndex_surjective_84
  have blockIndex_bijective : Function.Bijective blockIndex :=
    ⟨blockIndex_injective, blockIndex_surjective⟩
  let sumFin := structuralSumFin
  let pairFin := structuralPairFin
  let blockOrder : Fin (D.absorbedCount + D.retainedCount) ≃ Fin C.s :=
    (sumFin D.absorbedCount D.retainedCount).symm.trans
      (Equiv.ofBijective blockIndex blockIndex_bijective)
  have blockOrder_absorbed (h : Fin D.absorbedCount) :
      blockOrder (sumFin D.absorbedCount D.retainedCount (Sum.inl h)) =
        (D.absorbedEquiv h).1 := by
    simp only [blockOrder, Equiv.trans_apply]
    rw [(sumFin D.absorbedCount D.retainedCount).symm_apply_apply]
    exact (Equiv.ofBijective_apply blockIndex blockIndex_bijective _).trans rfl
  have blockOrder_retained (t : Fin D.retainedCount) :
      blockOrder (sumFin D.absorbedCount D.retainedCount (Sum.inr t)) =
        D.retained t := by
    simp only [blockOrder, Equiv.trans_apply]
    rw [(sumFin D.absorbedCount D.retainedCount).symm_apply_apply]
    exact (Equiv.ofBijective_apply blockIndex blockIndex_bijective _).trans rfl
  let reorderCore (b : ℕ) :
      Fin (b + (D.absorbedCount + D.retainedCount) * 2) ≃
        Fin (b + C.s * 2) :=
    (sumFin b ((D.absorbedCount + D.retainedCount) * 2)).symm |>.trans
      (Equiv.sumCongr (Equiv.refl (Fin b))
        ((pairFin (D.absorbedCount + D.retainedCount)).symm |>.trans
          ((Equiv.prodCongr blockOrder (Equiv.refl (Fin 2))).trans
            (pairFin C.s)))) |>.trans
      (sumFin b (C.s * 2))
  have reorderCore_base (b : ℕ) (q : Fin b) :
      reorderCore b
          (sumFin b ((D.absorbedCount + D.retainedCount) * 2) (Sum.inl q)) =
        sumFin b (C.s * 2) (Sum.inl q) := by
    simp [reorderCore]
  have reorderCore_absorbed (b : ℕ) (h : Fin D.absorbedCount)
      (j : Fin 2) :
      reorderCore b
          (sumFin b ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
            (pairFin (D.absorbedCount + D.retainedCount)
              (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j)))) =
        sumFin b (C.s * 2) (Sum.inr
          (pairFin C.s ((D.absorbedEquiv h).1, j))) := by
    simp [reorderCore, blockOrder_absorbed]
  have reorderCore_retained (b : ℕ) (t : Fin D.retainedCount)
      (j : Fin 2) :
      reorderCore b
          (sumFin b ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
            (pairFin (D.absorbedCount + D.retainedCount)
              (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j)))) =
        sumFin b (C.s * 2) (Sum.inr
          (pairFin C.s (D.retained t, j))) := by
    simp [reorderCore, blockOrder_retained]
  have vertexNewSize :
      T.length + 1 = C.p + (D.absorbedCount + D.retainedCount) * 2 := by
    have hc := C.length_eq
    have hd := D.count_eq
    omega
  have vertexOldSize : T.length + 1 = C.p + C.s * 2 := by
    have hc := C.length_eq
    omega
  have edgeNewSize :
      T.length = (C.p - 1) + (D.absorbedCount + D.retainedCount) * 2 := by
    have hc := C.length_eq
    have hd := D.count_eq
    have hp := C.p_ge_two
    omega
  have edgeOldSize : T.length = (C.p - 1) + C.s * 2 := by
    have hc := C.length_eq
    have hp := C.p_ge_two
    omega
  let vertexOrder : Equiv.Perm (Fin (T.length + 1)) :=
    (finCongr vertexNewSize).trans
      ((reorderCore C.p).trans (finCongr vertexOldSize).symm)
  let edgeOrder : Equiv.Perm (Fin T.length) :=
    (finCongr edgeNewSize).trans
      ((reorderCore (C.p - 1)).trans (finCongr edgeOldSize).symm)
  have vertexOrder_base (q : Fin C.p) :
      vertexOrder ⟨q.val, by
        have hq := q.isLt
        have hc := C.length_eq
        omega⟩ = ⟨q.val, by
        have hq := q.isLt
        have hc := C.length_eq
        omega⟩ := by
    apply Fin.ext
    change ((reorderCore C.p)
      (sumFin C.p ((D.absorbedCount + D.retainedCount) * 2)
        (Sum.inl q))).val = q.val
    rw [reorderCore_base]
    rfl
  have vertexOrder_absorbed (h : Fin D.absorbedCount) (j : Fin 2) :
      vertexOrder ⟨C.p + 2 * h.val + j.val, by
        have hh := h.isLt
        have hj := j.isLt
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ =
      ⟨C.p + 2 * (D.absorbedEquiv h).1.val + j.val, by
        have hh := (D.absorbedEquiv h).1.isLt
        have hj := j.isLt
        have hc := C.length_eq
        omega⟩ := by
    apply Fin.ext
    simp only [vertexOrder, Equiv.trans_apply]
    have hinput : (⟨C.p + 2 * h.val + j.val, by
          have hh := h.isLt
          have hj := j.isLt
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ : Fin (C.p + (D.absorbedCount + D.retainedCount) * 2)) =
        sumFin C.p ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
          (pairFin (D.absorbedCount + D.retainedCount)
            (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j))) := by
      apply Fin.ext
      simp [sumFin, pairFin]
      omega
    have hcast : (finCongr vertexNewSize) ⟨C.p + 2 * h.val + j.val, by
          have hh := h.isLt
          have hj := j.isLt
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ =
        sumFin C.p ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
          (pairFin (D.absorbedCount + D.retainedCount)
            (sumFin D.absorbedCount D.retainedCount (Sum.inl h), j))) := by
      exact hinput
    rw [hcast, reorderCore_absorbed]
    simp [sumFin, pairFin]
    omega
  have vertexOrder_retained (t : Fin D.retainedCount) (j : Fin 2) :
      vertexOrder ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
        have ht := t.isLt
        have hj := j.isLt
        have hc := C.length_eq
        have hd := D.count_eq
        omega⟩ =
      ⟨C.p + 2 * (D.retained t).val + j.val, by
        have ht := (D.retained t).isLt
        have hj := j.isLt
        have hc := C.length_eq
        omega⟩ := by
    apply Fin.ext
    simp only [vertexOrder, Equiv.trans_apply]
    have hinput : (⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
          have ht := t.isLt
          have hj := j.isLt
          have hc := C.length_eq
          have hd := D.count_eq
          omega⟩ : Fin (C.p + (D.absorbedCount + D.retainedCount) * 2)) =
        sumFin C.p ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
          (pairFin (D.absorbedCount + D.retainedCount)
            (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j))) := by
      apply Fin.ext
      simp [sumFin, pairFin]
      omega
    have hcast : (finCongr vertexNewSize)
          ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
            have ht := t.isLt
            have hj := j.isLt
            have hc := C.length_eq
            have hd := D.count_eq
            omega⟩ =
        sumFin C.p ((D.absorbedCount + D.retainedCount) * 2) (Sum.inr
          (pairFin (D.absorbedCount + D.retainedCount)
            (sumFin D.absorbedCount D.retainedCount (Sum.inr t), j))) := by
      exact hinput
    rw [hcast, reorderCore_retained]
    simp [sumFin, pairFin]
    omega
  exact @helper_continuation_309 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@C) (@D) (@blockIndex_bijective)
      (@reorderCore_base) (@reorderCore_absorbed) (@reorderCore_retained) (@vertexNewSize)
      (@vertexOldSize) (@edgeNewSize) (@edgeOldSize) (@vertexOrder_base) (@vertexOrder_absorbed)
      (@vertexOrder_retained)
end GoldbergSeymour

end
