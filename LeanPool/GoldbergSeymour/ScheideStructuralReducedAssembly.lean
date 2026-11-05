/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralReorderingData
public import LeanPool.GoldbergSeymour.ScheideStructuralSelectionData
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet

/-!
# Scheide Structural Reduced Assembly

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private abbrev helperBranch504Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  let newP : ℕ := C.p + (2 : ℕ) * D.absorbedCount;
  let newS : ℕ := D.retainedCount;
  let newVertex : Fin newP → V := fun (q : Fin newP) =>
   T'.vertex
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP := q.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a + (1 : ℕ)) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) => by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newGamma : Fin newS → Fin k := fun (t : Fin newS) => C.gamma (D.retained t);
  let newBlockVertex : Fin newS → Fin (2 : ℕ) → V := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.vertex
    (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a + (1 : ℕ))
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) =>
        by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newBaseEdge : Fin (newP - (1 : ℕ)) → E := fun (q : Fin (newP - (1 : ℕ))) =>
   T'.edge
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP - (1 : ℕ) := q.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) => by omega)⟩ :
     Fin T'.length);
  let newBlockEdge : Fin newS → Fin (2 : ℕ) → E := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.edge
    (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a)
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length) =>
        by omega)⟩ :
     Fin T'.length);
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ (q : Fin C.p), C.y q = v),
   let assembled : ScheideReducedConfiguration G k e0 phi T' :=
    {
     p := newP, s := newS,
     p_ge_two :=
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      id
       (Decidable.byContradiction fun (a : ¬(2 : ℕ) ≤ C.p + (2 : ℕ) * D.absorbedCount) => by omega),
     gamma := newGamma,
     gamma_injective := fun ⦃a b : Fin newS⦄ (hab : newGamma a = newGamma b) =>
      D.retained_injective (C.gamma_injective hab),
     y := newVertex, baseEdge := newBaseEdge, blockVertex := newBlockVertex,
     blockEdge := newBlockEdge,
     length_eq :=
      id
       (have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
       have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
       Eq.mpr
        (id
         (congrArg
          (fun (_a : ℕ) =>
           _a + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount)
          Q.length_eq))
        (Decidable.byContradiction
         fun
          (a : ¬T.length + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount) =>
         by omega)),
     base_vertex_position := fun (q : Fin newP) =>
      Eq.refl
       (T'.vertex
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     block_vertex_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.refl
       (T'.vertex
        (⟨newP + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
          (by
           have := (t).isLt
           have := (j).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     base_edge_position := fun (q : Fin (newP - (1 : ℕ))) =>
      Eq.refl
       (T'.edge
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin T'.length)),
     block_edge_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      id
       (congrArg T'.edge
        (Fin.ext
         (id
          (have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
          Decidable.byContradiction
           fun
            (a :
             ¬C.p + (2 : ℕ) * D.absorbedCount - (1 : ℕ) + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) =
               C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)) =>
           by omega)))),
     block_attaches_to_base := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      have h :
       ∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j) :=
       C.block_attaches_to_base (D.retained t) j;
      Exists.casesOn h
       fun (q : Fin C.p)
        (hq : G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j)) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : E) => G.ends _a = s(newVertex qnew, newBlockVertex t j))
           (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
            id (Q.retained_edge_position t j);
           this)))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(_a, newBlockVertex t j))
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id
            (congrArg (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(C.y q, _a))
             (have this : newBlockVertex t j = C.blockVertex (D.retained t) j :=
              id (Q.retained_vertex_position t j);
             this)))
           hq))),
     block_color := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.mpr
       (id
        (congrArg (fun (_a : E) => phi _a = some (newGamma t))
         (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
          id (Q.retained_edge_position t j);
         this)))
       (C.block_color (D.retained t) j),
     block_color_missing_on_base := fun (t : Fin newS) =>
      let v : V := (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V);
      have hv : v ∈ ScheideExitVertices T phi :=
       ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property;
      Exists.casesOn (oldExitBase v hv) fun (q : Fin C.p) (hq : C.y q = v) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : Fin k) => _a ∈ MissingColors G phi (newVertex qnew))
           (have this : newGamma t = C.gamma (D.retained t) := Eq.refl (newGamma t);
           this)))
         (Eq.mpr
          (id
           (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a)
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a) hq))
           (D.retained_missing t)))),
     initial_nonfirst_avoids_blocks :=
      fun (q : Fin (newP - (1 : ℕ))) (hq : (1 : ℕ) ≤ (↑q : ℕ)) (c : Fin k)
       (hc : phi (newBaseEdge q) = some c) (r : Fin newS) =>
      let split : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount) :=
       (⟨(↑q : ℕ), by omega⟩ : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount));
      have core :
       ∀ (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
        (1 : ℕ) ≤ (↑n : ℕ) →
         ∀ (d : Fin k),
          phi
             (T'.edge
              (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d →
           ∀ (r : Fin D.retainedCount), d ≠ C.gamma (D.retained r) :=
       fun (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) (hn : (1 : ℕ) ≤ (↑n : ℕ))
        (d : Fin k)
        (hdedge :
         phi
           (T'.edge
            (⟨(↑n : ℕ),
              have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
              have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
              have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
              have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
              Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
               (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
             Fin T'.length)) =
          some d)
        (rr : Fin D.retainedCount) =>
       Fin.addCases (motive := fun (x : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) =>
        (1 : ℕ) ≤ (↑x : ℕ) →
         ∀ (x_2 : Fin k),
          phi
             (T'.edge
              (⟨(↑x : ℕ),
                have hn : (↑x : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := x.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑x : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑x : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some x_2 →
           ∀ (x : Fin D.retainedCount), x_2 ≠ C.gamma (D.retained x))
        (fun (u : Fin (C.p - (1 : ℕ)))
          (hn : (1 : ℕ) ≤ (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ),
                have hn :
                 (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.castAdd ((2 : ℕ) * D.absorbedCount) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : ℕ) => (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < T.length) => by
                  omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         have hold :
          T'.edge
            (⟨(↑u : ℕ),
              (by
               have := (u).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.baseEdge u :=
          Q.base_edge_position u;
         id
          (fun (hn : (1 : ℕ) ≤ (↑u : ℕ)) =>
           C.initial_nonfirst_avoids_blocks u hn d
            (Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hold))) hdedge)
            (D.retained rr))
          hn)
        (fun (u : Fin ((2 : ℕ) * D.absorbedCount))
          (hn : (1 : ℕ) ≤ (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ),
                have hn :
                 (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         let paired : Fin (D.absorbedCount * (2 : ℕ)) :=
          Fin.cast (Nat.mul_comm (2 : ℕ) D.absorbedCount) u;
         let h : Fin D.absorbedCount := paired.divNat;
         let j : Fin (2 : ℕ) := paired.modNat;
         have huv : (↑u : ℕ) = (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) :=
          id
           (Decidable.byContradiction
            fun (a : ¬(↑u : ℕ) = (2 : ℕ) * ((↑u : ℕ) / (2 : ℕ)) + (↑u : ℕ) % (2 : ℕ)) => by omega);
         have hedge :
          T'.edge
            (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
              (by
               have := (h).isLt
               have := (j).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.blockEdge
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s)
            j :=
          Q.absorbed_edge_position h j;
         have hblock :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some d :=
          Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hedge)))
           (Eq.mpr
            (id
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ))
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (Nat.add_assoc (C.p - (1 : ℕ)) ((2 : ℕ) * (↑h : ℕ)) (↑j : ℕ))
                  ((by
                   have := (h).isLt
                   have := (j).isLt
                   have := C.length_eq
                   have := D.count_eq
                   have := Q.length_eq
                   have := C.p_ge_two
                   omega))))))
              (some d)))
            (Eq.mp
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (congrArg (HAdd.hAdd (C.p - (1 : ℕ))) huv)
                  (have hn :
                   (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                    C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                   (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                  have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                  have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                  have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                  Eq.mpr
                   (id
                    (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                     Q.length_eq))
                   (Decidable.byContradiction
                    fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega))))))
              (some d))
             hdedge));
         have hcolor :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)) :=
          C.block_color
           (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
              h) :
            Fin C.s)
           j;
         have heq :
          d =
           C.gamma
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s) :=
          Eq.mp
           (Option.some.injEq d
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)))
           (Eq.symm (Eq.mp (congrArg (fun (_a : Option (Fin k)) => _a = some d) hcolor) hblock));
         fun (hbad : d = C.gamma (D.retained rr)) =>
         ((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
            h).property
          (Exists.intro rr
           (C.gamma_injective
            (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) (Eq.symm heq)))
             (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) hbad))
              (Eq.refl (C.gamma (D.retained rr))))))))
        n hn d hdedge rr;
      core split hq c (id hc) r,
     exit_covered := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (Eq.mpr (id (congrArg (fun (_a : V) => newGamma t ∈ MissingColors G phi _a) (Eq.symm htv)))
         (D.retained_missing t)),
     no_isolated := C.no_isolated,
     globally_maximum :=
      (⟨C.globally_maximum.left,
        (⟨Q.tashkinov,
          Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = TashkinovOrder G) Q.vertex_set_eq))
           C.globally_maximum.right.right⟩ :
         TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G)⟩ :
       KTriple G k e0 phi ∧
        TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G),
     exit_card_eq :=
      Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = newS) Q.exit_set_eq))
       (Eq.symm D.exit_count_eq),
     exit_exactly_one := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (⟨Eq.mpr
           (id
            (congrArg
             (fun (_a : V) => (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi _a) t)
             (Eq.symm htv)))
           (D.retained_missing t),
          fun (t' : Fin newS) (hm : newGamma t' ∈ MissingColors G phi v) =>
          D.selected_unique t t'
           (Eq.mp (congrArg (fun (_a : V) => newGamma t' ∈ MissingColors G phi _a) (Eq.symm htv))
            hm)⟩ :
         (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) t ∧
          ∀ (y : Fin newS), (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) y → y = t),
     every_block_color_at_exit := fun (t : Fin newS) =>
      Exists.intro (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)
       (⟨Eq.mpr
          (id
           (congrArg
            (fun (_a : Finset V) =>
             (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈ _a)
            Q.exit_set_eq))
          ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property,
         D.retained_missing t⟩ :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈
          ScheideExitVertices T' phi ∧
         newGamma t ∈
          MissingColors G phi
           (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)) :
     ScheideReducedConfiguration G k e0 phi T' };
   ∀ (i : Fin C.s),
    (∃! h : Fin D.absorbedCount,
      (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained }) h) :
        Fin C.s) =
       i) →
     (∃ (r : Fin assembled.s),
       C.gamma i = assembled.gamma r ∧
        ∀ (j : Fin (2 : ℕ)),
         C.blockVertex i j = assembled.blockVertex r j ∧
          C.blockEdge i j = assembled.blockEdge r j) ∨
      ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperBranch516Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  let newP : ℕ := C.p + (2 : ℕ) * D.absorbedCount;
  let newS : ℕ := D.retainedCount;
  let newVertex : Fin newP → V := fun (q : Fin newP) =>
   T'.vertex
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP := q.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a + (1 : ℕ)) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) => by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newGamma : Fin newS → Fin k := fun (t : Fin newS) => C.gamma (D.retained t);
  let newBlockVertex : Fin newS → Fin (2 : ℕ) → V := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.vertex
    (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a + (1 : ℕ))
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) =>
        by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newBaseEdge : Fin (newP - (1 : ℕ)) → E := fun (q : Fin (newP - (1 : ℕ))) =>
   T'.edge
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP - (1 : ℕ) := q.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) => by omega)⟩ :
     Fin T'.length);
  let newBlockEdge : Fin newS → Fin (2 : ℕ) → E := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.edge
    (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a)
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length) =>
        by omega)⟩ :
     Fin T'.length);
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ (q : Fin C.p), C.y q = v),
   let assembled : ScheideReducedConfiguration G k e0 phi T' :=
    {
     p := newP, s := newS,
     p_ge_two :=
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      id
       (Decidable.byContradiction fun (a : ¬(2 : ℕ) ≤ C.p + (2 : ℕ) * D.absorbedCount) => by omega),
     gamma := newGamma,
     gamma_injective := fun ⦃a b : Fin newS⦄ (hab : newGamma a = newGamma b) =>
      D.retained_injective (C.gamma_injective hab),
     y := newVertex, baseEdge := newBaseEdge, blockVertex := newBlockVertex,
     blockEdge := newBlockEdge,
     length_eq :=
      id
       (have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
       have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
       Eq.mpr
        (id
         (congrArg
          (fun (_a : ℕ) =>
           _a + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount)
          Q.length_eq))
        (Decidable.byContradiction
         fun
          (a : ¬T.length + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount) =>
         by omega)),
     base_vertex_position := fun (q : Fin newP) =>
      Eq.refl
       (T'.vertex
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     block_vertex_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.refl
       (T'.vertex
        (⟨newP + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
          (by
           have := (t).isLt
           have := (j).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     base_edge_position := fun (q : Fin (newP - (1 : ℕ))) =>
      Eq.refl
       (T'.edge
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin T'.length)),
     block_edge_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      id
       (congrArg T'.edge
        (Fin.ext
         (id
          (have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
          Decidable.byContradiction
           fun
            (a :
             ¬C.p + (2 : ℕ) * D.absorbedCount - (1 : ℕ) + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) =
               C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)) =>
           by omega)))),
     block_attaches_to_base := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      have h :
       ∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j) :=
       C.block_attaches_to_base (D.retained t) j;
      Exists.casesOn h
       fun (q : Fin C.p)
        (hq : G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j)) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : E) => G.ends _a = s(newVertex qnew, newBlockVertex t j))
           (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
            id (Q.retained_edge_position t j);
           this)))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(_a, newBlockVertex t j))
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id
            (congrArg (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(C.y q, _a))
             (have this : newBlockVertex t j = C.blockVertex (D.retained t) j :=
              id (Q.retained_vertex_position t j);
             this)))
           hq))),
     block_color := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.mpr
       (id
        (congrArg (fun (_a : E) => phi _a = some (newGamma t))
         (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
          id (Q.retained_edge_position t j);
         this)))
       (C.block_color (D.retained t) j),
     block_color_missing_on_base := fun (t : Fin newS) =>
      let v : V := (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V);
      have hv : v ∈ ScheideExitVertices T phi :=
       ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property;
      Exists.casesOn (oldExitBase v hv) fun (q : Fin C.p) (hq : C.y q = v) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : Fin k) => _a ∈ MissingColors G phi (newVertex qnew))
           (have this : newGamma t = C.gamma (D.retained t) := Eq.refl (newGamma t);
           this)))
         (Eq.mpr
          (id
           (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a)
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a) hq))
           (D.retained_missing t)))),
     initial_nonfirst_avoids_blocks :=
      fun (q : Fin (newP - (1 : ℕ))) (hq : (1 : ℕ) ≤ (↑q : ℕ)) (c : Fin k)
       (hc : phi (newBaseEdge q) = some c) (r : Fin newS) =>
      let split : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount) :=
       (⟨(↑q : ℕ), by omega⟩ : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount));
      have core :
       ∀ (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
        (1 : ℕ) ≤ (↑n : ℕ) →
         ∀ (d : Fin k),
          phi
             (T'.edge
              (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d →
           ∀ (r : Fin D.retainedCount), d ≠ C.gamma (D.retained r) :=
       fun (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) (hn : (1 : ℕ) ≤ (↑n : ℕ))
        (d : Fin k)
        (hdedge :
         phi
           (T'.edge
            (⟨(↑n : ℕ),
              have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
              have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
              have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
              have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
              Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
               (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
             Fin T'.length)) =
          some d)
        (rr : Fin D.retainedCount) =>
       Fin.addCases (motive := fun (x : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) =>
        (1 : ℕ) ≤ (↑x : ℕ) →
         ∀ (x_2 : Fin k),
          phi
             (T'.edge
              (⟨(↑x : ℕ),
                have hn : (↑x : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := x.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑x : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑x : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some x_2 →
           ∀ (x : Fin D.retainedCount), x_2 ≠ C.gamma (D.retained x))
        (fun (u : Fin (C.p - (1 : ℕ)))
          (hn : (1 : ℕ) ≤ (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ),
                have hn :
                 (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.castAdd ((2 : ℕ) * D.absorbedCount) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : ℕ) => (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < T.length) => by
                  omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         have hold :
          T'.edge
            (⟨(↑u : ℕ),
              (by
               have := (u).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.baseEdge u :=
          Q.base_edge_position u;
         id
          (fun (hn : (1 : ℕ) ≤ (↑u : ℕ)) =>
           C.initial_nonfirst_avoids_blocks u hn d
            (Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hold))) hdedge)
            (D.retained rr))
          hn)
        (fun (u : Fin ((2 : ℕ) * D.absorbedCount))
          (hn : (1 : ℕ) ≤ (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ),
                have hn :
                 (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         let paired : Fin (D.absorbedCount * (2 : ℕ)) :=
          Fin.cast (Nat.mul_comm (2 : ℕ) D.absorbedCount) u;
         let h : Fin D.absorbedCount := paired.divNat;
         let j : Fin (2 : ℕ) := paired.modNat;
         have huv : (↑u : ℕ) = (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) :=
          id
           (Decidable.byContradiction
            fun (a : ¬(↑u : ℕ) = (2 : ℕ) * ((↑u : ℕ) / (2 : ℕ)) + (↑u : ℕ) % (2 : ℕ)) => by omega);
         have hedge :
          T'.edge
            (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
              (by
               have := (h).isLt
               have := (j).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.blockEdge
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s)
            j :=
          Q.absorbed_edge_position h j;
         have hblock :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some d :=
          Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hedge)))
           (Eq.mpr
            (id
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ))
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (Nat.add_assoc (C.p - (1 : ℕ)) ((2 : ℕ) * (↑h : ℕ)) (↑j : ℕ))
                  ((by
                   have := (h).isLt
                   have := (j).isLt
                   have := C.length_eq
                   have := D.count_eq
                   have := Q.length_eq
                   have := C.p_ge_two
                   omega))))))
              (some d)))
            (Eq.mp
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (congrArg (HAdd.hAdd (C.p - (1 : ℕ))) huv)
                  (have hn :
                   (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                    C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                   (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                  have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                  have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                  have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                  Eq.mpr
                   (id
                    (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                     Q.length_eq))
                   (Decidable.byContradiction
                    fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega))))))
              (some d))
             hdedge));
         have hcolor :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)) :=
          C.block_color
           (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
              h) :
            Fin C.s)
           j;
         have heq :
          d =
           C.gamma
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s) :=
          Eq.mp
           (Option.some.injEq d
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)))
           (Eq.symm (Eq.mp (congrArg (fun (_a : Option (Fin k)) => _a = some d) hcolor) hblock));
         fun (hbad : d = C.gamma (D.retained rr)) =>
         ((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
            h).property
          (Exists.intro rr
           (C.gamma_injective
            (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) (Eq.symm heq)))
             (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) hbad))
              (Eq.refl (C.gamma (D.retained rr))))))))
        n hn d hdedge rr;
      core split hq c (id hc) r,
     exit_covered := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (Eq.mpr (id (congrArg (fun (_a : V) => newGamma t ∈ MissingColors G phi _a) (Eq.symm htv)))
         (D.retained_missing t)),
     no_isolated := C.no_isolated,
     globally_maximum :=
      (⟨C.globally_maximum.left,
        (⟨Q.tashkinov,
          Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = TashkinovOrder G) Q.vertex_set_eq))
           C.globally_maximum.right.right⟩ :
         TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G)⟩ :
       KTriple G k e0 phi ∧
        TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G),
     exit_card_eq :=
      Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = newS) Q.exit_set_eq))
       (Eq.symm D.exit_count_eq),
     exit_exactly_one := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (⟨Eq.mpr
           (id
            (congrArg
             (fun (_a : V) => (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi _a) t)
             (Eq.symm htv)))
           (D.retained_missing t),
          fun (t' : Fin newS) (hm : newGamma t' ∈ MissingColors G phi v) =>
          D.selected_unique t t'
           (Eq.mp (congrArg (fun (_a : V) => newGamma t' ∈ MissingColors G phi _a) (Eq.symm htv))
            hm)⟩ :
         (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) t ∧
          ∀ (y : Fin newS), (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) y → y = t),
     every_block_color_at_exit := fun (t : Fin newS) =>
      Exists.intro (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)
       (⟨Eq.mpr
          (id
           (congrArg
            (fun (_a : Finset V) =>
             (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈ _a)
            Q.exit_set_eq))
          ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property,
         D.retained_missing t⟩ :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈
          ScheideExitVertices T' phi ∧
         newGamma t ∈
          MissingColors G phi
           (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)) :
     ScheideReducedConfiguration G k e0 phi T' };
   ∀ (i : Fin C.s),
    (∃! t : Fin D.retainedCount, D.retained t = i) →
     (∃ (r : Fin assembled.s),
       C.gamma i = assembled.gamma r ∧
        ∀ (j : Fin (2 : ℕ)),
         C.blockVertex i j = assembled.blockVertex r j ∧
          C.blockEdge i j = assembled.blockEdge r j) ∨
      ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperBranch513Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  let newP : ℕ := C.p + (2 : ℕ) * D.absorbedCount;
  let newS : ℕ := D.retainedCount;
  let newVertex : Fin newP → V := fun (q : Fin newP) =>
   T'.vertex
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP := q.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a + (1 : ℕ)) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) => by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newGamma : Fin newS → Fin k := fun (t : Fin newS) => C.gamma (D.retained t);
  let newBlockVertex : Fin newS → Fin (2 : ℕ) → V := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.vertex
    (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a + (1 : ℕ))
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) =>
        by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newBaseEdge : Fin (newP - (1 : ℕ)) → E := fun (q : Fin (newP - (1 : ℕ))) =>
   T'.edge
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP - (1 : ℕ) := q.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) => by omega)⟩ :
     Fin T'.length);
  let newBlockEdge : Fin newS → Fin (2 : ℕ) → E := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.edge
    (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a)
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length) =>
        by omega)⟩ :
     Fin T'.length);
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ (q : Fin C.p), C.y q = v),
   let assembled : ScheideReducedConfiguration G k e0 phi T' :=
    {
     p := newP, s := newS,
     p_ge_two :=
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      id
       (Decidable.byContradiction fun (a : ¬(2 : ℕ) ≤ C.p + (2 : ℕ) * D.absorbedCount) => by omega),
     gamma := newGamma,
     gamma_injective := fun ⦃a b : Fin newS⦄ (hab : newGamma a = newGamma b) =>
      D.retained_injective (C.gamma_injective hab),
     y := newVertex, baseEdge := newBaseEdge, blockVertex := newBlockVertex,
     blockEdge := newBlockEdge,
     length_eq :=
      id
       (have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
       have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
       Eq.mpr
        (id
         (congrArg
          (fun (_a : ℕ) =>
           _a + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount)
          Q.length_eq))
        (Decidable.byContradiction
         fun
          (a : ¬T.length + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount) =>
         by omega)),
     base_vertex_position := fun (q : Fin newP) =>
      Eq.refl
       (T'.vertex
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     block_vertex_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.refl
       (T'.vertex
        (⟨newP + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
          (by
           have := (t).isLt
           have := (j).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     base_edge_position := fun (q : Fin (newP - (1 : ℕ))) =>
      Eq.refl
       (T'.edge
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin T'.length)),
     block_edge_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      id
       (congrArg T'.edge
        (Fin.ext
         (id
          (have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
          Decidable.byContradiction
           fun
            (a :
             ¬C.p + (2 : ℕ) * D.absorbedCount - (1 : ℕ) + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) =
               C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)) =>
           by omega)))),
     block_attaches_to_base := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      have h :
       ∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j) :=
       C.block_attaches_to_base (D.retained t) j;
      Exists.casesOn h
       fun (q : Fin C.p)
        (hq : G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j)) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : E) => G.ends _a = s(newVertex qnew, newBlockVertex t j))
           (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
            id (Q.retained_edge_position t j);
           this)))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(_a, newBlockVertex t j))
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id
            (congrArg (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(C.y q, _a))
             (have this : newBlockVertex t j = C.blockVertex (D.retained t) j :=
              id (Q.retained_vertex_position t j);
             this)))
           hq))),
     block_color := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.mpr
       (id
        (congrArg (fun (_a : E) => phi _a = some (newGamma t))
         (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
          id (Q.retained_edge_position t j);
         this)))
       (C.block_color (D.retained t) j),
     block_color_missing_on_base := fun (t : Fin newS) =>
      let v : V := (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V);
      have hv : v ∈ ScheideExitVertices T phi :=
       ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property;
      Exists.casesOn (oldExitBase v hv) fun (q : Fin C.p) (hq : C.y q = v) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : Fin k) => _a ∈ MissingColors G phi (newVertex qnew))
           (have this : newGamma t = C.gamma (D.retained t) := Eq.refl (newGamma t);
           this)))
         (Eq.mpr
          (id
           (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a)
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a) hq))
           (D.retained_missing t)))),
     initial_nonfirst_avoids_blocks :=
      fun (q : Fin (newP - (1 : ℕ))) (hq : (1 : ℕ) ≤ (↑q : ℕ)) (c : Fin k)
       (hc : phi (newBaseEdge q) = some c) (r : Fin newS) =>
      let split : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount) :=
       (⟨(↑q : ℕ), by omega⟩ : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount));
      have core :
       ∀ (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
        (1 : ℕ) ≤ (↑n : ℕ) →
         ∀ (d : Fin k),
          phi
             (T'.edge
              (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d →
           ∀ (r : Fin D.retainedCount), d ≠ C.gamma (D.retained r) :=
       fun (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) (hn : (1 : ℕ) ≤ (↑n : ℕ))
        (d : Fin k)
        (hdedge :
         phi
           (T'.edge
            (⟨(↑n : ℕ),
              have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
              have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
              have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
              have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
              Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
               (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
             Fin T'.length)) =
          some d)
        (rr : Fin D.retainedCount) =>
       Fin.addCases (motive := fun (x : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) =>
        (1 : ℕ) ≤ (↑x : ℕ) →
         ∀ (x_2 : Fin k),
          phi
             (T'.edge
              (⟨(↑x : ℕ),
                have hn : (↑x : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := x.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑x : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑x : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some x_2 →
           ∀ (x : Fin D.retainedCount), x_2 ≠ C.gamma (D.retained x))
        (fun (u : Fin (C.p - (1 : ℕ)))
          (hn : (1 : ℕ) ≤ (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ),
                have hn :
                 (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.castAdd ((2 : ℕ) * D.absorbedCount) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : ℕ) => (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < T.length) => by
                  omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         have hold :
          T'.edge
            (⟨(↑u : ℕ),
              (by
               have := (u).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.baseEdge u :=
          Q.base_edge_position u;
         id
          (fun (hn : (1 : ℕ) ≤ (↑u : ℕ)) =>
           C.initial_nonfirst_avoids_blocks u hn d
            (Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hold))) hdedge)
            (D.retained rr))
          hn)
        (fun (u : Fin ((2 : ℕ) * D.absorbedCount))
          (hn : (1 : ℕ) ≤ (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ),
                have hn :
                 (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         let paired : Fin (D.absorbedCount * (2 : ℕ)) :=
          Fin.cast (Nat.mul_comm (2 : ℕ) D.absorbedCount) u;
         let h : Fin D.absorbedCount := paired.divNat;
         let j : Fin (2 : ℕ) := paired.modNat;
         have huv : (↑u : ℕ) = (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) :=
          id
           (Decidable.byContradiction
            fun (a : ¬(↑u : ℕ) = (2 : ℕ) * ((↑u : ℕ) / (2 : ℕ)) + (↑u : ℕ) % (2 : ℕ)) => by omega);
         have hedge :
          T'.edge
            (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
              (by
               have := (h).isLt
               have := (j).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.blockEdge
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s)
            j :=
          Q.absorbed_edge_position h j;
         have hblock :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some d :=
          Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hedge)))
           (Eq.mpr
            (id
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ))
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (Nat.add_assoc (C.p - (1 : ℕ)) ((2 : ℕ) * (↑h : ℕ)) (↑j : ℕ))
                  ((by
                   have := (h).isLt
                   have := (j).isLt
                   have := C.length_eq
                   have := D.count_eq
                   have := Q.length_eq
                   have := C.p_ge_two
                   omega))))))
              (some d)))
            (Eq.mp
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (congrArg (HAdd.hAdd (C.p - (1 : ℕ))) huv)
                  (have hn :
                   (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                    C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                   (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                  have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                  have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                  have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                  Eq.mpr
                   (id
                    (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                     Q.length_eq))
                   (Decidable.byContradiction
                    fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega))))))
              (some d))
             hdedge));
         have hcolor :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)) :=
          C.block_color
           (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
              h) :
            Fin C.s)
           j;
         have heq :
          d =
           C.gamma
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s) :=
          Eq.mp
           (Option.some.injEq d
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)))
           (Eq.symm (Eq.mp (congrArg (fun (_a : Option (Fin k)) => _a = some d) hcolor) hblock));
         fun (hbad : d = C.gamma (D.retained rr)) =>
         ((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
            h).property
          (Exists.intro rr
           (C.gamma_injective
            (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) (Eq.symm heq)))
             (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) hbad))
              (Eq.refl (C.gamma (D.retained rr))))))))
        n hn d hdedge rr;
      core split hq c (id hc) r,
     exit_covered := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (Eq.mpr (id (congrArg (fun (_a : V) => newGamma t ∈ MissingColors G phi _a) (Eq.symm htv)))
         (D.retained_missing t)),
     no_isolated := C.no_isolated,
     globally_maximum :=
      (⟨C.globally_maximum.left,
        (⟨Q.tashkinov,
          Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = TashkinovOrder G) Q.vertex_set_eq))
           C.globally_maximum.right.right⟩ :
         TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G)⟩ :
       KTriple G k e0 phi ∧
        TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G),
     exit_card_eq :=
      Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = newS) Q.exit_set_eq))
       (Eq.symm D.exit_count_eq),
     exit_exactly_one := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (⟨Eq.mpr
           (id
            (congrArg
             (fun (_a : V) => (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi _a) t)
             (Eq.symm htv)))
           (D.retained_missing t),
          fun (t' : Fin newS) (hm : newGamma t' ∈ MissingColors G phi v) =>
          D.selected_unique t t'
           (Eq.mp (congrArg (fun (_a : V) => newGamma t' ∈ MissingColors G phi _a) (Eq.symm htv))
            hm)⟩ :
         (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) t ∧
          ∀ (y : Fin newS), (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) y → y = t),
     every_block_color_at_exit := fun (t : Fin newS) =>
      Exists.intro (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)
       (⟨Eq.mpr
          (id
           (congrArg
            (fun (_a : Finset V) =>
             (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈ _a)
            Q.exit_set_eq))
          ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property,
         D.retained_missing t⟩ :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈
          ScheideExitVertices T' phi ∧
         newGamma t ∈
          MissingColors G phi
           (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)) :
     ScheideReducedConfiguration G k e0 phi T' };
   ∀ (i : Fin C.s),
    (∃ (r : Fin assembled.s),
      C.gamma i = assembled.gamma r ∧
       ∀ (j : Fin (2 : ℕ)),
        C.blockVertex i j = assembled.blockVertex r j ∧ C.blockEdge i j = assembled.blockEdge r j) ∨
     ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperContinuation263Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  let newP : ℕ := C.p + (2 : ℕ) * D.absorbedCount;
  let newS : ℕ := D.retainedCount;
  let newVertex : Fin newP → V := fun (q : Fin newP) =>
   T'.vertex
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP := q.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a + (1 : ℕ)) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length + (1 : ℕ)) => by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newGamma : Fin newS → Fin k := fun (t : Fin newS) => C.gamma (D.retained t);
  let newBlockVertex : Fin newS → Fin (2 : ℕ) → V := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.vertex
    (⟨C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a + (1 : ℕ))
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length + (1 : ℕ)) =>
        by omega)⟩ :
     Fin (T'.length + (1 : ℕ)));
  let newBaseEdge : Fin (newP - (1 : ℕ)) → E := fun (q : Fin (newP - (1 : ℕ))) =>
   T'.edge
    (⟨(↑q : ℕ),
      have hq : (↑q : ℕ) < newP - (1 : ℕ) := q.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑q : ℕ) < _a) Q.length_eq))
       (Decidable.byContradiction fun (a : ¬(↑q : ℕ) < T.length) => by omega)⟩ :
     Fin T'.length);
  let newBlockEdge : Fin newS → Fin (2 : ℕ) → E := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
   T'.edge
    (⟨C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
      have ht : (↑t : ℕ) < newS := t.isLt;
      have hj : (↑j : ℕ) < (2 : ℕ) := j.isLt;
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
      have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
      Eq.mpr
       (id
        (congrArg
         (fun (_a : ℕ) =>
          C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < _a)
         Q.length_eq))
       (Decidable.byContradiction
        fun
         (a :
          ¬C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) < T.length) =>
        by omega)⟩ :
     Fin T'.length);
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ (q : Fin C.p), C.y q = v),
   let assembled : ScheideReducedConfiguration G k e0 phi T' :=
    {
     p := newP, s := newS,
     p_ge_two :=
      have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
      id
       (Decidable.byContradiction fun (a : ¬(2 : ℕ) ≤ C.p + (2 : ℕ) * D.absorbedCount) => by omega),
     gamma := newGamma,
     gamma_injective := fun ⦃a b : Fin newS⦄ (hab : newGamma a = newGamma b) =>
      D.retained_injective (C.gamma_injective hab),
     y := newVertex, baseEdge := newBaseEdge, blockVertex := newBlockVertex,
     blockEdge := newBlockEdge,
     length_eq :=
      id
       (have hc : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
       have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
       Eq.mpr
        (id
         (congrArg
          (fun (_a : ℕ) =>
           _a + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount)
          Q.length_eq))
        (Decidable.byContradiction
         fun
          (a : ¬T.length + (1 : ℕ) = C.p + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * D.retainedCount) =>
         by omega)),
     base_vertex_position := fun (q : Fin newP) =>
      Eq.refl
       (T'.vertex
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     block_vertex_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.refl
       (T'.vertex
        (⟨newP + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ),
          (by
           have := (t).isLt
           have := (j).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin (T'.length + (1 : ℕ)))),
     base_edge_position := fun (q : Fin (newP - (1 : ℕ))) =>
      Eq.refl
       (T'.edge
        (⟨(↑q : ℕ),
          (by
           have := (q).isLt
           have := C.length_eq
           have := D.count_eq
           have := Q.length_eq
           have := C.p_ge_two
           dsimp only [newP, newS] at *
           omega)⟩ :
         Fin T'.length)),
     block_edge_position := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      id
       (congrArg T'.edge
        (Fin.ext
         (id
          (have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
          Decidable.byContradiction
           fun
            (a :
             ¬C.p + (2 : ℕ) * D.absorbedCount - (1 : ℕ) + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ) =
               C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount + (2 : ℕ) * (↑t : ℕ) + (↑j : ℕ)) =>
           by omega)))),
     block_attaches_to_base := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      have h :
       ∃ (q : Fin C.p),
        G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j) :=
       C.block_attaches_to_base (D.retained t) j;
      Exists.casesOn h
       fun (q : Fin C.p)
        (hq : G.ends (C.blockEdge (D.retained t) j) = s(C.y q, C.blockVertex (D.retained t) j)) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : E) => G.ends _a = s(newVertex qnew, newBlockVertex t j))
           (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
            id (Q.retained_edge_position t j);
           this)))
         (Eq.mpr
          (id
           (congrArg
            (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(_a, newBlockVertex t j))
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id
            (congrArg (fun (_a : V) => G.ends (C.blockEdge (D.retained t) j) = s(C.y q, _a))
             (have this : newBlockVertex t j = C.blockVertex (D.retained t) j :=
              id (Q.retained_vertex_position t j);
             this)))
           hq))),
     block_color := fun (t : Fin newS) (j : Fin (2 : ℕ)) =>
      Eq.mpr
       (id
        (congrArg (fun (_a : E) => phi _a = some (newGamma t))
         (have this : newBlockEdge t j = C.blockEdge (D.retained t) j :=
          id (Q.retained_edge_position t j);
         this)))
       (C.block_color (D.retained t) j),
     block_color_missing_on_base := fun (t : Fin newS) =>
      let v : V := (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V);
      have hv : v ∈ ScheideExitVertices T phi :=
       ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property;
      Exists.casesOn (oldExitBase v hv) fun (q : Fin C.p) (hq : C.y q = v) =>
       let qnew : Fin newP := (⟨(↑q : ℕ), by omega⟩ : Fin newP);
       Exists.intro qnew
        (Eq.mpr
         (id
          (congrArg (fun (_a : Fin k) => _a ∈ MissingColors G phi (newVertex qnew))
           (have this : newGamma t = C.gamma (D.retained t) := Eq.refl (newGamma t);
           this)))
         (Eq.mpr
          (id
           (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a)
            (have this : newVertex qnew = C.y q := id (Q.base_vertex_position q);
            this)))
          (Eq.mpr
           (id (congrArg (fun (_a : V) => C.gamma (D.retained t) ∈ MissingColors G phi _a) hq))
           (D.retained_missing t)))),
     initial_nonfirst_avoids_blocks :=
      fun (q : Fin (newP - (1 : ℕ))) (hq : (1 : ℕ) ≤ (↑q : ℕ)) (c : Fin k)
       (hc : phi (newBaseEdge q) = some c) (r : Fin newS) =>
      let split : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount) :=
       (⟨(↑q : ℕ), by omega⟩ : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount));
      have core :
       ∀ (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
        (1 : ℕ) ≤ (↑n : ℕ) →
         ∀ (d : Fin k),
          phi
             (T'.edge
              (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d →
           ∀ (r : Fin D.retainedCount), d ≠ C.gamma (D.retained r) :=
       fun (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) (hn : (1 : ℕ) ≤ (↑n : ℕ))
        (d : Fin k)
        (hdedge :
         phi
           (T'.edge
            (⟨(↑n : ℕ),
              have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
              have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
              have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
              have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
              Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
               (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
             Fin T'.length)) =
          some d)
        (rr : Fin D.retainedCount) =>
       Fin.addCases (motive := fun (x : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)) =>
        (1 : ℕ) ≤ (↑x : ℕ) →
         ∀ (x_2 : Fin k),
          phi
             (T'.edge
              (⟨(↑x : ℕ),
                have hn : (↑x : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := x.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑x : ℕ) < _a) Q.length_eq))
                 (Decidable.byContradiction fun (a : ¬(↑x : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some x_2 →
           ∀ (x : Fin D.retainedCount), x_2 ≠ C.gamma (D.retained x))
        (fun (u : Fin (C.p - (1 : ℕ)))
          (hn : (1 : ℕ) ≤ (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ),
                have hn :
                 (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.castAdd ((2 : ℕ) * D.absorbedCount) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg
                   (fun (_a : ℕ) => (↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.castAdd ((2 : ℕ) * D.absorbedCount) u) : ℕ) < T.length) => by
                  omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         have hold :
          T'.edge
            (⟨(↑u : ℕ),
              (by
               have := (u).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.baseEdge u :=
          Q.base_edge_position u;
         id
          (fun (hn : (1 : ℕ) ≤ (↑u : ℕ)) =>
           C.initial_nonfirst_avoids_blocks u hn d
            (Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hold))) hdedge)
            (D.retained rr))
          hn)
        (fun (u : Fin ((2 : ℕ) * D.absorbedCount))
          (hn : (1 : ℕ) ≤ (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)) (d : Fin k)
          (hdedge :
           phi
             (T'.edge
              (⟨(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ),
                have hn :
                 (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                  C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                 (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr
                 (id
                  (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                   Q.length_eq))
                 (Decidable.byContradiction
                  fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega)⟩ :
               Fin T'.length)) =
            some d)
          (rr : Fin D.retainedCount) =>
         let paired : Fin (D.absorbedCount * (2 : ℕ)) :=
          Fin.cast (Nat.mul_comm (2 : ℕ) D.absorbedCount) u;
         let h : Fin D.absorbedCount := paired.divNat;
         let j : Fin (2 : ℕ) := paired.modNat;
         have huv : (↑u : ℕ) = (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ) :=
          id
           (Decidable.byContradiction
            fun (a : ¬(↑u : ℕ) = (2 : ℕ) * ((↑u : ℕ) / (2 : ℕ)) + (↑u : ℕ) % (2 : ℕ)) => by omega);
         have hedge :
          T'.edge
            (⟨C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ),
              (by
               have := (h).isLt
               have := (j).isLt
               have := C.length_eq
               have := D.count_eq
               have := Q.length_eq
               have := C.p_ge_two
               dsimp only [newP, newS] at *
               omega)⟩ :
             Fin T'.length) =
           C.blockEdge
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s)
            j :=
          Q.absorbed_edge_position h j;
         have hblock :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some d :=
          Eq.mpr (id (congrArg (fun (_a : E) => phi _a = some d) (Eq.symm hedge)))
           (Eq.mpr
            (id
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (C.p - (1 : ℕ) + (2 : ℕ) * (↑h : ℕ) + (↑j : ℕ))
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (Nat.add_assoc (C.p - (1 : ℕ)) ((2 : ℕ) * (↑h : ℕ)) (↑j : ℕ))
                  ((by
                   have := (h).isLt
                   have := (j).isLt
                   have := C.length_eq
                   have := D.count_eq
                   have := Q.length_eq
                   have := C.p_ge_two
                   omega))))))
              (some d)))
            (Eq.mp
             (congrFun'
              (congrArg Eq
               (congrArg phi
                (congrArg T'.edge
                 (Fin.mk.congr_simp (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ)
                  (C.p - (1 : ℕ) + ((2 : ℕ) * (↑h : ℕ) + (↑j : ℕ)))
                  (congrArg (HAdd.hAdd (C.p - (1 : ℕ))) huv)
                  (have hn :
                   (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) <
                    C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount :=
                   (Fin.natAdd (C.p - (1 : ℕ)) u).isLt;
                  have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                  have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                  have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                  Eq.mpr
                   (id
                    (congrArg (fun (_a : ℕ) => (↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < _a)
                     Q.length_eq))
                   (Decidable.byContradiction
                    fun (a : ¬(↑(Fin.natAdd (C.p - (1 : ℕ)) u) : ℕ) < T.length) => by omega))))))
              (some d))
             hdedge));
         have hcolor :
          phi
            (C.blockEdge
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)
             j) =
           some
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)) :=
          C.block_color
           (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
              h) :
            Fin C.s)
           j;
         have heq :
          d =
           C.gamma
            (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
               h) :
             Fin C.s) :=
          Eq.mp
           (Option.some.injEq d
            (C.gamma
             (↑((D.absorbedEquiv :
                 Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
                h) :
              Fin C.s)))
           (Eq.symm (Eq.mp (congrArg (fun (_a : Option (Fin k)) => _a = some d) hcolor) hblock));
         fun (hbad : d = C.gamma (D.retained rr)) =>
         ((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained })
            h).property
          (Exists.intro rr
           (C.gamma_injective
            (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) (Eq.symm heq)))
             (Eq.mpr (id (congrArg (fun (_a : Fin k) => C.gamma (D.retained rr) = _a) hbad))
              (Eq.refl (C.gamma (D.retained rr))))))))
        n hn d hdedge rr;
      core split hq c (id hc) r,
     exit_covered := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (Eq.mpr (id (congrArg (fun (_a : V) => newGamma t ∈ MissingColors G phi _a) (Eq.symm htv)))
         (D.retained_missing t)),
     no_isolated := C.no_isolated,
     globally_maximum :=
      (⟨C.globally_maximum.left,
        (⟨Q.tashkinov,
          Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = TashkinovOrder G) Q.vertex_set_eq))
           C.globally_maximum.right.right⟩ :
         TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G)⟩ :
       KTriple G k e0 phi ∧
        TashkinovTree G e0 phi T' ∧ (TreeSequenceVertexSet T').card = TashkinovOrder G),
     exit_card_eq :=
      Eq.mpr (id (congrArg (fun (_a : Finset V) => _a.card = newS) Q.exit_set_eq))
       (Eq.symm D.exit_count_eq),
     exit_exactly_one := fun (v : V) (hv : v ∈ ScheideExitVertices T' phi) =>
      Exists.casesOn
       (Equiv.surjective D.exitEquiv
        (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
         ↥(ScheideExitVertices T phi)))
       fun (t : Fin D.retainedCount)
        (ht :
         (D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t =
          (⟨v, Eq.mp (congrArg (fun (_a : Finset V) => v ∈ _a) Q.exit_set_eq) hv⟩ :
           ↥(ScheideExitVertices T phi))) =>
       have htv :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) = v :=
        congrArg Subtype.val ht;
       Exists.intro t
        (⟨Eq.mpr
           (id
            (congrArg
             (fun (_a : V) => (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi _a) t)
             (Eq.symm htv)))
           (D.retained_missing t),
          fun (t' : Fin newS) (hm : newGamma t' ∈ MissingColors G phi v) =>
          D.selected_unique t t'
           (Eq.mp (congrArg (fun (_a : V) => newGamma t' ∈ MissingColors G phi _a) (Eq.symm htv))
            hm)⟩ :
         (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) t ∧
          ∀ (y : Fin newS), (fun (i : Fin newS) => newGamma i ∈ MissingColors G phi v) y → y = t),
     every_block_color_at_exit := fun (t : Fin newS) =>
      Exists.intro (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)
       (⟨Eq.mpr
          (id
           (congrArg
            (fun (_a : Finset V) =>
             (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈ _a)
            Q.exit_set_eq))
          ((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t).property,
         D.retained_missing t⟩ :
        (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V) ∈
          ScheideExitVertices T' phi ∧
         newGamma t ∈
          MissingColors G phi
           (↑((D.exitEquiv : Fin D.retainedCount → ↥(ScheideExitVertices T phi)) t) : V)) :
     ScheideReducedConfiguration G k e0 phi T' };
   ∃ (R : ScheideReducedConfiguration G k e0 phi T'),
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
     (∀ (q : Fin C.p), C.y q ∈ Finset.image R.y Finset.univ) ∧
      ∀ (i : Fin C.s),
       (∃ (r : Fin R.s),
         C.gamma i = R.gamma r ∧
          ∀ (j : Fin (2 : ℕ)),
           C.blockVertex i j = R.blockVertex r j ∧ C.blockEdge i j = R.blockEdge r j) ∨
        ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image R.y Finset.univ

private theorem helper_branch_504.{u_1, u_2} :
    helperBranch504Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q newP newS newVertex newGamma newBlockVertex newBaseEdge
      newBlockEdge oldExitBase assembled i ha
  obtain ⟨h, hi, _⟩ := ha
  right
  intro j
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨C.p + 2 * h.val + j.val, ?_⟩, ?_⟩
  · change C.p + 2 * h.val + j.val < C.p + 2 * D.absorbedCount
    have hh := h.isLt
    have hj := j.isLt
    omega
  · dsimp [assembled, newVertex]
    rw [Q.absorbed_vertex_position h j]
    rw [hi]

private theorem helper_branch_516.{u_1, u_2} :
    helperBranch516Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q newP newS newVertex newGamma newBlockVertex newBaseEdge
      newBlockEdge oldExitBase assembled i hr
  obtain ⟨t, ht, _⟩ := hr
  left
  refine ⟨t, ?_, ?_⟩
  · dsimp [assembled, newGamma]
    rw [ht]
  · intro j
    constructor
    · dsimp [assembled, newBlockVertex]
      rw [← ht]
      exact (Q.retained_vertex_position t j).symm
    · dsimp [assembled, newBlockEdge]
      rw [← ht]
      exact (Q.retained_edge_position t j).symm

private theorem helper_branch_513.{u_1, u_2} :
    helperBranch513Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q newP newS newVertex newGamma newBlockVertex newBaseEdge
      newBlockEdge oldExitBase assembled i
  rcases D.partition i with ha | hr
  · exact @helper_branch_504 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase i ha
  · exact @helper_branch_516 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase i hr
private theorem helper_continuation_263.{u_1, u_2} :
    helperContinuation263Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q newP newS newVertex newGamma newBlockVertex newBaseEdge
      newBlockEdge oldExitBase assembled
  refine ⟨assembled, Q.vertex_set_eq, ?_, ?_⟩
  · intro q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨q.val, ?_⟩, ?_⟩
    · have hq := q.isLt
      change q.val < C.p + 2 * D.absorbedCount
      omega
    · dsimp [assembled, newVertex]
      exact Q.base_vertex_position q
  · exact @helper_branch_513 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase
private theorem helper_oldExitBase_593.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideStructuralConfiguration G k e0 phi T),
    ∀ v ∈ ScheideExitVertices T phi,
    ∃ (q : Fin C.p),
    C.y q = v := by
  classical
  intro V E _ _ _ G k e0 phi T C v hv
  have hstructure := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    hstructure.2.2.2.1
  have hvertex : v ∈ TreeSequenceVertexSet T := by
    let : DecidablePred (fun w : V => ScheideExitVertex T phi w) := Classical.decPred _
    rcases (Finset.mem_filter.mp hv).2 with ⟨u, color, defect, hu, hmiss, hdefect,
      z, path, hpath, index, hindex, hvertex, hafter⟩
    exact hvertex
  have baseInTree : ∀ q : Fin C.p, C.y q ∈ TreeSequenceVertexSet T := by
    intro q
    have hlength := C.length_eq
    have witness :=
      (@Finset.mem_image (Fin (T.length + 1)) V (Classical.decEq V)).mpr
        (⟨⟨q.val, by omega⟩, Finset.mem_univ _, C.base_vertex_position q⟩ :
          ∃ a ∈ (Finset.univ : Finset (Fin (T.length + 1))), T.vertex a = C.y q)
    simpa only [TreeSequenceVertexSet] using witness
  obtain ⟨colorIndex, hcolor⟩ := C.exit_covered v hv
  obtain ⟨base, hbase⟩ := C.block_color_missing_on_base colorIndex
  have hne : v = C.y base := by
    by_contra hne
    have hdisjoint := helementary hvertex (baseInTree base) hne
    exact (Finset.disjoint_left.mp hdisjoint) hcolor hbase
  exact ⟨base, hne.symm⟩

private theorem helper_core_699.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
      [ DecidableEq V] [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ)
      (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideStructuralConfiguration G k e0 phi T)
      (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
      (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
    let newP : ℕ := C.p + (2 : ℕ) * D.absorbedCount;
    ∀ (_ : Fin (newP - (1 : ℕ))) (n : Fin (C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount)),
    (1 : ℕ) ≤ (↑n : ℕ) →
    ∀ (d : Fin k),
    phi
          (T'.edge
            (⟨(↑n : ℕ),
                have hn : (↑n : ℕ) < C.p - (1 : ℕ) + (2 : ℕ) * D.absorbedCount := n.isLt;
                have hp : (2 : ℕ) ≤ C.p := C.p_ge_two;
                have hl : T.length + (1 : ℕ) = C.p + (2 : ℕ) * C.s := C.length_eq;
                have hd : C.s = D.absorbedCount + D.retainedCount := D.count_eq;
                Eq.mpr (id (congrArg (fun (_a : ℕ) => (↑n : ℕ) < _a) Q.length_eq))
                  (Decidable.byContradiction fun (a : ¬(↑n : ℕ) < T.length) => by omega)⟩ :
              Fin T'.length)) =
        some d →
    ∀ (r : Fin D.retainedCount),
    d ≠ C.gamma (D.retained r) := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q newP q n hn d hdedge rr
  refine Fin.addCases ?_ ?_ n hn d hdedge rr
  · intro u hn d hdedge rr
    have hold := Q.base_edge_position u
    change 1 ≤ u.val at hn
    apply C.initial_nonfirst_avoids_blocks u hn d (by
      rw [← hold]
      exact hdedge) (D.retained rr)
  · intro u hn d hdedge rr
    let paired : Fin (D.absorbedCount * 2) :=
      Fin.cast (Nat.mul_comm 2 D.absorbedCount) u
    let h := paired.divNat
    let j := paired.modNat
    have huv : u.val = 2 * h.val + j.val := by
      dsimp [h, j, paired, Fin.divNat, Fin.modNat]
      omega
    have hedge := Q.absorbed_edge_position h j
    have hblock : phi (C.blockEdge (D.absorbedEquiv h).1 j) = some d := by
      rw [← hedge]
      simpa [huv, Nat.add_assoc] using hdedge
    have hcolor := C.block_color (D.absorbedEquiv h).1 j
    have heq : d = C.gamma (D.absorbedEquiv h).1 := by
      rw [hcolor] at hblock
      simpa using hblock.symm
    intro hbad
    apply (D.absorbedEquiv h).2
    refine ⟨rr, ?_⟩
    apply C.gamma_injective
    rw [← heq, hbad]

theorem ScheideStructuralReducedAssembly {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C)
    (T' : TreeSequence G e0)
    (Q : ScheideStructuralReorderingData G k e0 phi T C D T') :
    ∃ R : ScheideReducedConfiguration G k e0 phi T',
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
        (∀ i : Fin C.s,
          (∃ r : Fin R.s,
              C.gamma i = R.gamma r ∧
                ∀ j : Fin 2,
                  C.blockVertex i j = R.blockVertex r j ∧
                    C.blockEdge i j = R.blockEdge r j) ∨
            ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
  let newP := C.p + 2 * D.absorbedCount
  let newS := D.retainedCount
  let newVertex : Fin newP → V := fun q =>
    T'.vertex ⟨q.val, by
      have hq := q.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newGamma : Fin newS → Fin k := fun t => C.gamma (D.retained t)
  let newBlockVertex : Fin newS → Fin 2 → V := fun t j =>
    T'.vertex ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBaseEdge : Fin (newP - 1) → E := fun q =>
    T'.edge ⟨q.val, by
      have hq := q.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBlockEdge : Fin newS → Fin 2 → E := fun t j =>
    T'.edge ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  have oldExitBase := @helper_oldExitBase_593 V E inferInstance inferInstance inferInstance G k e0
      phi T C
  let assembled : ScheideReducedConfiguration G k e0 phi T' := {
    p := newP,
    s := newS,
    p_ge_two := by have hp := C.p_ge_two; dsimp [newP]; omega,
    gamma := newGamma,
    gamma_injective := by
      intro a b hab
      apply D.retained_injective
      apply C.gamma_injective
      exact hab,
    y := newVertex,
    baseEdge := newBaseEdge,
    blockVertex := newBlockVertex,
    blockEdge := newBlockEdge,
    length_eq := by
      dsimp [newP, newS]
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega,
    base_vertex_position := by
      intro q
      rfl,
    block_vertex_position := by
      intro t j
      rfl,
    base_edge_position := by
      intro q
      rfl,
    block_edge_position := by
      intro t j
      dsimp [newBlockEdge, newP]
      apply congrArg T'.edge
      apply Fin.ext
      change C.p + 2 * D.absorbedCount - 1 + 2 * t.val + j.val =
        C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val
      have hp := C.p_ge_two
      omega,
    block_attaches_to_base := by
      intro t j
      have h := C.block_attaches_to_base (D.retained t) j
      obtain ⟨q, hq⟩ := h
      let qnew : Fin newP := ⟨q.val, by
        dsimp [newP]
        omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [show newBlockVertex t j = C.blockVertex (D.retained t) j by
        dsimp [newBlockVertex]
        exact Q.retained_vertex_position t j]
      exact hq,
    block_color := by
      intro t j
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      exact C.block_color (D.retained t) j,
    block_color_missing_on_base := by
      intro t
      let v := (D.exitEquiv t).1
      have hv : v ∈ ScheideExitVertices T phi := (D.exitEquiv t).2
      obtain ⟨q, hq⟩ := oldExitBase v hv
      let qnew : Fin newP := ⟨q.val, by dsimp [newP]; omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newGamma t = C.gamma (D.retained t) by rfl]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [hq]
      exact D.retained_missing t,
    initial_nonfirst_avoids_blocks := by
      intro q hq c hc r
      let split : Fin ((C.p - 1) + 2 * D.absorbedCount) := ⟨q.val, by
        dsimp [newP] at q ⊢
        omega⟩
      have core := @helper_core_699 V E inferInstance inferInstance inferInstance inferInstance G k
          e0 phi T C D T' Q q
      apply core split (by exact hq) c
      · simpa [split, newBaseEdge] using hc
    exit_covered := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := (D.exitEquiv.surjective ⟨v, hv⟩)
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_⟩
      rw [← htv]
      exact D.retained_missing t,
    no_isolated := C.no_isolated,
    globally_maximum := by
      refine ⟨C.globally_maximum.1, Q.tashkinov, ?_⟩
      rw [Q.vertex_set_eq]
      exact C.globally_maximum.2.2,
    exit_card_eq := by
      rw [Q.exit_set_eq]
      exact D.exit_count_eq.symm,
    exit_exactly_one := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := D.exitEquiv.surjective ⟨v, hv⟩
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_, ?_⟩
      · rw [← htv]
        exact D.retained_missing t
      · intro t' hm
        apply D.selected_unique t t'
        rw [← htv] at hm
        exact hm,
    every_block_color_at_exit := by
      intro t
      refine ⟨(D.exitEquiv t).1, ?_, ?_⟩
      · rw [Q.exit_set_eq]
        exact (D.exitEquiv t).2
      · exact D.retained_missing t
    }
  exact @helper_continuation_263 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D T' Q oldExitBase
end GoldbergSeymour

end
