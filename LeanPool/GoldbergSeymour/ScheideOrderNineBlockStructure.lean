/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideOrderNineRebasingPreparation
public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple

/-!
# Scheide Order Nine Block Structure

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open ScheideRebasing

private abbrev scheideBlockContinuationStatement.{u_1, u_2} : Prop :=
 open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k)
   (T : TreeSequence G e0) (_ : NormalGlobalMaximumTriple G k e0 phi T),
  ScheideGraphHeight G = (5 : ℕ) →
  let Good :
  {e : E} →
  (psi : PartialEdgeColoring E k) →
  (S : TreeSequence G e) →
  NormalGlobalMaximumTriple G k e psi S →
  Prop :=
   fun {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
    (M : NormalGlobalMaximumTriple G k e psi S) ↦
   ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma
    :
  Fin (2 : ℕ) →
  Fin k),
    Function.Injective gamma ∧
     (
  ∀ (i j : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
          G.ends
            (S.edge
             (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt i
  have := Fin.isLt j
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
              Fin S.length)) =
           s(S.vertex
             (⟨(↑q : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt q
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
              Fin (S.length + (1 : ℕ))),
            S.vertex
             (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt i
  have := Fin.isLt j
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
              Fin (S.length + (1 : ℕ))))) ∧
      (
  ∀ (i j : Fin (2 : ℕ)),
  psi
            (S.edge
             (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt i
  have := Fin.isLt j
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
              Fin S.length)) =
           some (gamma i)) ∧
       (
  ∀ (i : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
            gamma i ∈
             MissingColors G psi
              (S.vertex
               (⟨(↑q : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt q
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
                Fin (S.length + (1 : ℕ))))) ∧
  ∀ (i : Fin (4 : ℕ)),
  (1 : ℕ) ≤ (↑i : ℕ) →
  ∀ (c : Fin k),
  psi
                (S.edge
                 (⟨(↑i : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := Fin.isLt i
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
                  Fin S.length)) =
               some c →
  ∀ (r : Fin (2 : ℕ)),
  c ≠ gamma r;
  ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
   (M : NormalGlobalMaximumTriple G k e psi S),
  BalancedGlobalMaximumTriple M →
  ∀ (hlen : S.length = (8 : ℕ)),
  M.height = (5 : ℕ) →
  ∀ (g0 : Fin k),
  TashkinovOrder G = (TreeSequenceVertexSet S).card ∧
    (3 : ℕ) ≤ (TreeSequenceVertexSet S).card ∧
     Odd (TreeSequenceVertexSet S).card ∧
      ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) ∧
       ColoredVertexSetClosed G psi (TreeSequenceVertexSet S) →
  let y0 : V :=
   S.vertex
    (⟨(0 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y1 : V :=
   S.vertex
    (⟨(1 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y2 : V :=
   S.vertex
    (⟨(2 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y3 : V :=
   S.vertex
    (⟨(3 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y4 : V :=
   S.vertex
    (⟨(4 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y5 : V :=
   S.vertex
    (⟨(5 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y6 : V :=
   S.vertex
    (⟨(6 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y7 : V :=
   S.vertex
    (⟨(7 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let y8 : V :=
   S.vertex
    (⟨(8 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin (S.length + (1 : ℕ)));
  let a1 : E :=
   S.edge
    (⟨(1 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let a2 : E :=
   S.edge
    (⟨(2 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let a3 : E :=
   S.edge
    (⟨(3 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let b0 : E :=
   S.edge
    (⟨(4 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let b1 : E :=
   S.edge
    (⟨(5 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let c0 : E :=
   S.edge
    (⟨(6 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  let c1 : E :=
   S.edge
    (⟨(7 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
     Fin S.length);
  g0 ∈ MissingColors G psi y0 →
  ∀
   (_ :
    Fin
     ((↑(⟨(4 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
         Fin S.length) :
       ℕ) +
      (1 : ℕ)))
   (_ :
    Fin
     ((↑(⟨(5 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
         Fin S.length) :
       ℕ) +
      (1 : ℕ)))
   (f1 f2 : E) (v1 v2 : V),
  psi f1 = some g0 →
  psi f2 = some g0 →
  v1 ≠
    S.vertex
     (⟨(0 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
      Fin (S.length + (1 : ℕ))) →
  v1 ≠
    S.vertex
     (⟨(4 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  by
  have := GoldbergSeymour.TreeSequence.positive S
  have := GoldbergSeymour.TreeSequence.positive S
  omega⟩ :
      Fin (S.length + (1 : ℕ))) →
  G.ends f1 = s(y1, v1) →
  G.ends f2 = s(y4, v2) →
  b0 ≠ b1 →
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  ∀ (beta56 : E),
  G.ends beta56 = s(v1, v2) →
  psi beta56 = some M.beta →
  G.ends a1 = s(y1, y2) →
  G.ends a2 = s(y2, y3) →
  G.ends a3 = s(y3, y4) →
  G.ends M.closingEdge = s(y4, y0) →
  psi a1 = some M.alpha →
  psi a2 = some M.beta →
  psi a3 = some M.alpha →
  psi M.closingEdge = some M.beta →
  M.alpha ≠ M.beta →
  g0 ≠ M.alpha →
  g0 ≠ M.beta →
  let r6' : Fin S.length :=
   (⟨(6 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  Decidable.byContradiction fun (a : ¬(6 : ℕ) < S.length) ↦ by
   omega⟩ :
    Fin S.length);
  let _ : Fin S.length :=
   (⟨(7 : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  Decidable.byContradiction fun (a : ¬(7 : ℕ) < S.length) ↦ by
   omega⟩ :
    Fin S.length);
  ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))) (g1 : Fin k),
  psi c1 = some g1 →
  psi c0 = some g1 →
  g1 ∈
    MissingColors G psi
     (S.vertex
      (⟨(↑w : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  have this : (↑r6' : ℕ) < S.length := r6'.isLt;
  have this_1 : (↑w : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := by
   have := GoldbergSeymour.TreeSequence.positive S
   have := Fin.isLt r6'
   have := Fin.isLt w
   have := GoldbergSeymour.TreeSequence.positive S
   omega;
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  Decidable.byContradiction
   fun (a : ¬(↑w : ℕ) < S.length + (1 : ℕ)) ↦ by omega⟩ :
       Fin (S.length + (1 : ℕ)))) →
  ∀ (pc : Fin ((↑r6' : ℕ) + (1 : ℕ))),
  let pc' : Fin (7 : ℕ) :=
   (⟨(↑pc : ℕ),
  have this : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := by
   have := GoldbergSeymour.TreeSequence.positive S
   have := Fin.isLt r6'
   have := Fin.isLt pc
   have := GoldbergSeymour.TreeSequence.positive S
   omega;
  this⟩ :
    Fin (7 : ℕ));
  G.ends c0 =
    s(y7,
     S.vertex
      (⟨(↑pc' : ℕ),
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  have _ : (↑r6' : ℕ) < S.length := r6'.isLt;
  have _ : (↑pc : ℕ) < (↑r6' : ℕ) + (1 : ℕ) := by
   have := GoldbergSeymour.TreeSequence.positive S
   have := Fin.isLt r6'
   have := Fin.isLt pc
   have := GoldbergSeymour.TreeSequence.positive S
   omega;
  have this : (↑pc' : ℕ) < (7 : ℕ) := pc'.isLt;
  have _ : (1 : ℕ) ≤ S.length := S.positive;
  Decidable.byContradiction
   fun (a : ¬(↑pc' : ℕ) < S.length + (1 : ℕ)) ↦ by
   omega⟩ :
       Fin (S.length + (1 : ℕ)))) →
  g1 ≠ g0 →
  g1 ≠ M.alpha →
  g1 ≠ M.beta →
  ∀ (g0last : E),
  G.ends g0last = s(y7, y8) →
  psi g0last = some g0 →
  ∀ (alphaLast : E),
  G.ends alphaLast = s(y7, y8) →
  psi alphaLast = some M.alpha →
  ∀ (betaLast : E),
  G.ends betaLast = s(y7, y8) →
  psi betaLast = some M.beta →
  let a0 : E :=
   S.edge
    (⟨(0 : ℕ),
      by
      have :=
       GoldbergSeymour.TreeSequence.positive S
      have :=
       GoldbergSeymour.TreeSequence.positive S
      omega⟩ :
     Fin S.length);
  a0 = e →
  ∀
   (_ :
    Fin
     ((↑(⟨(0 : ℕ),
          by
          have :=
           GoldbergSeymour.TreeSequence.positive
            S
          have :=
           GoldbergSeymour.TreeSequence.positive
            S
          omega⟩ :
         Fin S.length) :
       ℕ) +
      (1 : ℕ))),
  G.ends a0 = s(y1, y0) →
  beta56 ≠ a0 →
  beta56 ≠ f1 →
  ∃ (e' : E) (psi' : PartialEdgeColoring E k)
   (S' : TreeSequence G e') (M' :
   NormalGlobalMaximumTriple G k e' psi' S'),
   Good psi' S' M'

private abbrev scheideRebasedTreeCertificateStatement.{u_1, u_2} : Prop :=
 open scoped Classical Sym2 in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
   (G : LooplessMultigraph V E) (k : ℕ),
  ScheideGraphHeight G = 5 →
  ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
   (M : NormalGlobalMaximumTriple G k e psi S),
  BalancedGlobalMaximumTriple M →
  ∀ (hlen : S.length = 8),
  M.height = 5 →
  ∀ (g0 : Fin k),
  TashkinovOrder G = (TreeSequenceVertexSet S).card ∧
    3 ≤ (TreeSequenceVertexSet S).card ∧
     Odd (TreeSequenceVertexSet S).card ∧
      ColoredVertexSetElementary G psi (TreeSequenceVertexSet S) ∧
       ColoredVertexSetClosed G psi (TreeSequenceVertexSet S) →
  ∀ (y0 : V),
  ∀ (y1 : V),
  ∀ (y2 : V),
  ∀ (y3 : V),
  ∀ (y4 : V),
  ∀ (y5 : V),
  ∀ (y6 : V),
  ∀ (y7 : V),
  ∀ (y8 : V),
  ∀ (a1 : E),
  ∀ (a2 : E),
  ∀ (a3 : E),
  ∀ (b0 : E),
  ∀ (b1 : E),
  ∀ (c0 : E),
  ∀ (c1 : E),
  g0 ∈ MissingColors G psi y0 →
  ∀
   (p0 :
    Fin
     ((↑(⟨4, by simpa only [hlen] using (show 4 < (8 : ℕ) from by decide)⟩ :
         Fin S.length) :
       ℕ) +
      1))
   (p1 :
    Fin
     ((↑(⟨5, by simpa only [hlen] using (show 5 < (8 : ℕ) from by decide)⟩ :
         Fin S.length) :
       ℕ) +
      1))
   (f1 f2 : E) (v1 v2 : V),
  psi f1 = some g0 →
  psi f2 = some g0 →
  v1 ≠ y0 →
  v1 ≠ y4 →
  ∀ (hf1ends' : G.ends f1 = s(y1, v1)) (hf2ends' : G.ends f2 = s(y4, v2)),
  b0 ≠ b1 →
  b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2 ∨ b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1 →
  ∀ (beta56 : E) (hbeta56ends : G.ends beta56 = s(v1, v2)),
  psi beta56 = some M.beta →
  ∀ (ha1ends : G.ends a1 = s(y1, y2)),
  G.ends a2 = s(y2, y3) →
  ∀ (ha3ends : G.ends a3 = s(y3, y4)),
  G.ends M.closingEdge = s(y4, y0) →
  psi a1 = some M.alpha →
  psi a2 = some M.beta →
  psi a3 = some M.alpha →
  psi M.closingEdge = some M.beta →
  M.alpha ≠ M.beta →
  g0 ≠ M.alpha →
  g0 ≠ M.beta →
  ∀ (r6' : Fin S.length),
  ∀ (r7' : Fin S.length),
  ∀ (w : Fin ((↑r6' : ℕ) + 1)) (g1 : Fin k),
  psi c1 = some g1 →
  psi c0 = some g1 →
  g1 ∈
    MissingColors G psi
     (S.vertex
      (⟨(↑w : ℕ), by clear * - hlen; omega⟩ :
       Fin (S.length + 1))) →
  ∀ (pc : Fin ((↑r6' : ℕ) + 1)),
  ∀ (pc' : Fin 7),
  ∀
   (hc0ends :
    G.ends c0 =
     s(y7,
      S.vertex
       (⟨(↑pc' : ℕ), by clear * - hlen; omega⟩ :
        Fin (S.length + 1)))),
  g1 ≠ g0 →
  g1 ≠ M.alpha →
  g1 ≠ M.beta →
  ∀ (g0last : E),
  G.ends g0last = s(y7, y8) →
  psi g0last = some g0 →
  ∀ (alphaLast : E),
  G.ends alphaLast = s(y7, y8) →
  psi alphaLast = some M.alpha →
  ∀ (betaLast : E),
  G.ends betaLast = s(y7, y8) →
  psi betaLast = some M.beta →
  ∀ (a0 : E),
  ∀ (ha0eq : a0 = e)
   (pa0 :
    Fin
     ((↑(⟨0, by simpa only [hlen] using (show 0 < (8 : ℕ) from by decide)⟩ :
         Fin S.length) :
       ℕ) +
      1))
   (ha0ends : G.ends a0 = s(y1, y0)),
  beta56 ≠ a0 →
  beta56 ≠ f1 →
  beta56 ≠ f2 →
  beta56 ≠ a1 →
  beta56 ≠ a3 →
  beta56 ≠ c0 →
  beta56 ≠ c1 →
  5 ≤ (↑w : ℕ) →
  (↑w : ℕ) = 5 ∨ (↑w : ℕ) = 6 →
  ∀ (cast9 : Fin 9 ≃ Fin (S.length + 1)),
  ∀ (permA : Equiv.Perm (Fin 9)),
  ∀ (permB : Equiv.Perm (Fin 9)),
  ∀ (newVertex :
  Fin 9 →
  V),
  ∀ (edgeList : List E),
  ∀
   (hedgeListLength :
    edgeList.length = 8),
  ∀ (newEdge :
  Fin 8 →
  E),
  (
  b0 = f1 →
  y5 = v1 ∧ b1 = f2 ∧ y6 = v2) →
  (
  b0 ≠ f1 →
  y5 = v2 ∧ b1 = f1 ∧ y6 = v1) →
  (
  ∀ (i : Fin 9)
   (q : Fin (S.length + 1)),
  (↑i : ℕ) = (↑q : ℕ) →
  S.vertex
         ((cast9 :
  Fin 9 →
  Fin (S.length + 1))
          i) =
        S.vertex q) →
  ∀ (nv0 : newVertex 0 = y0)
   (nv1 : newVertex 1 = y1)
   (nv2 : newVertex 2 = v1)
   (nv3 : newVertex 3 = v2)
   (nv4 : newVertex 4 = y4)
   (nv5 : newVertex 5 = y2)
   (nv6 : newVertex 6 = y3)
   (nv7 : newVertex 7 = y7)
   (nv8 : newVertex 8 = y8)
   (ne0 : newEdge 0 = a0)
   (ne1 : newEdge 1 = f1)
   (ne2 : newEdge 2 = beta56)
   (ne3 : newEdge 3 = f2)
   (ne4 : newEdge 4 = a1)
   (ne5 : newEdge 5 = a3)
   (ne6 : newEdge 6 = c0)
   (ne7 : newEdge 7 = c1),
  (
  ∀ (i j : Fin (S.length + 1)),
  S.vertex i = S.vertex j ↔
   i = j) →
  (
  ∀ (i j : Fin S.length),
  S.edge i = S.edge j ↔ i = j) →
  ∀
   (newVertex_injective :
    Function.Injective newVertex)
   (newEdge_injective :
    Function.Injective newEdge),
  (
  ∀ (q : Fin 7),
  ∃ (t : Fin 7),
   newVertex
     (Fin.castLE
      (Mathlib.Meta.NormNum.isNat_le_true
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 7))
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 9))
       (Eq.refl true))
      t) =
    S.vertex
     (⟨(↑q : ℕ), by clear * - hlen; omega⟩ :
      Fin (S.length + 1))) →
  ∀ (pc1 : Fin ((↑r7' : ℕ) + 1)),
  G.ends (S.edge r7') =
    s(S.vertex r7'.succ,
     S.vertex
      (pc1.castLT
       (Nat.lt_trans pc1.isLt
        (Nat.succ_lt_succ
         r7'.isLt)))) →
  ∀ (pc1' : Fin 8),
  pc1.castLT
     (Nat.lt_trans pc1.isLt
      (Nat.succ_lt_succ
       r7'.isLt)) =
    (⟨(↑pc1' : ℕ), by clear * - hlen; omega⟩ :
     Fin (S.length + 1)) →
  ∀
   (hc1ends :
    G.ends c1 =
     s(y8,
      S.vertex
       (⟨(↑pc1' : ℕ), by clear * - hlen; omega⟩ :
        Fin (S.length + 1)))),
  (
  ∀ (q : Fin 8),
  ∃ (t : Fin 8),
   newVertex
     (Fin.castLE
      (Mathlib.Meta.NormNum.isNat_le_true
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 8))
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 9))
       (Eq.refl true))
      t) =
    S.vertex
     (⟨(↑q : ℕ), by clear * - hlen; omega⟩ :
      Fin
       (S.length + 1))) →
  ∀ (tc0 : Fin 7)
   (htc0 :
    newVertex
      (Fin.castLE
       (Mathlib.Meta.NormNum.isNat_le_true
        (Mathlib.Meta.NormNum.isNat_ofNat
         ℕ (Eq.refl 7))
        (Mathlib.Meta.NormNum.isNat_ofNat
         ℕ (Eq.refl 9))
        (Eq.refl true))
       tc0) =
     S.vertex
      (⟨(↑pc' : ℕ), by clear * - hlen; omega⟩ :
       Fin (S.length + 1)))
   (tc1 : Fin 8)
   (htc1 :
    newVertex
      (Fin.castLE
       (Mathlib.Meta.NormNum.isNat_le_true
        (Mathlib.Meta.NormNum.isNat_ofNat
         ℕ (Eq.refl 8))
        (Mathlib.Meta.NormNum.isNat_ofNat
         ℕ (Eq.refl 9))
        (Eq.refl true))
       tc1) =
     S.vertex
      (⟨(↑pc1' : ℕ), by clear * - hlen; omega⟩ :
       Fin (S.length + 1)))
   (tw : Fin 7),
  newVertex
     (Fin.castLE
      (Mathlib.Meta.NormNum.isNat_le_true
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 7))
       (Mathlib.Meta.NormNum.isNat_ofNat
        ℕ (Eq.refl 9))
       (Eq.refl true))
      tw) =
    S.vertex
     (⟨(↑w : ℕ), by clear * - hlen; omega⟩ :
      Fin (S.length + 1)) →
  ∀ (S' : TreeSequence G e),
  ∀
   (hS'length :
    S'.length = 8),
  (
  ∀ (i : Fin 9),
  S'.vertex (Fin.cast (by omega : 9 = S'.length + 1) i) =
   newVertex i) →
  (
  ∀ (i : Fin 8),
  S'.edge (Fin.cast hS'length.symm i) =
   newEdge i) →
  g1 ∈
    MissingColors G psi
     (S'.vertex
      (⟨(↑tw : ℕ), by omega⟩ :
       Fin
        (S'.length +
         1))) →
  TashkinovTree G e psi S' →
  M.beta ∈ MissingColors G psi y1 →
  ∃ (S' : TreeSequence G e)
    (M' : NormalGlobalMaximumTriple G k e psi S')
    (_ : S'.length = 8) (_ : M'.height = 5),
    BalancedGlobalMaximumTriple M' ∧
    S'.vertex ⟨0, by omega⟩ = y0 ∧
    S'.vertex ⟨1, by omega⟩ = y1 ∧
    S'.vertex ⟨2, by omega⟩ = v1 ∧
    S'.vertex ⟨3, by omega⟩ = v2 ∧
    S'.vertex ⟨4, by omega⟩ = y4 ∧
    S'.vertex ⟨5, by omega⟩ = y2 ∧
    S'.vertex ⟨6, by omega⟩ = y3 ∧
    S'.vertex ⟨7, by omega⟩ = y7 ∧
    S'.vertex ⟨8, by omega⟩ = y8 ∧
    S'.edge ⟨0, by omega⟩ = a0 ∧
    S'.edge ⟨1, by omega⟩ = f1 ∧
    S'.edge ⟨2, by omega⟩ = beta56 ∧
    S'.edge ⟨3, by omega⟩ = f2 ∧
    S'.edge ⟨4, by omega⟩ = a1 ∧
    S'.edge ⟨5, by omega⟩ = a3 ∧
    S'.edge ⟨6, by omega⟩ = c0 ∧
    S'.edge ⟨7, by omega⟩ = c1 ∧
    M'.alpha = g0 ∧ M'.beta = M.beta

private theorem scheideRebasedTreeCertificate.{u_1, u_2} :
    scheideRebasedTreeCertificateStatement.{u_1, u_2} := by
  classical
  intro V E inst inst_1 inst_2 G k hgraphHeight e psi S M hbal hlen hheight g0 horderM y0 y1 y2 y3
      y4 y5 y6 y7 y8 a1 a2 a3 b0 b1 c0 c1 hg0' p0 p1 f1 f2 v1 v2 hf1color hf2color hv10 hv14
      hf1ends' hf2ends' hb01ne horient beta56 hbeta56ends hbeta56color ha1ends ha2ends ha3ends
      hclosingEnds ha1color ha2color ha3color hclosingColor hab hg0alpha hg0beta r6' r7' w g1
      hc1color hc0color' hwmissing' pc pc' hc0ends hg10 hg1alpha hg1beta g0last hg0lastEnds
      hg0lastColor alphaLast halphaLastEnds halphaLastColor betaLast hbetaLastEnds hbetaLastColor a0
      ha0eq pa0 ha0ends hbeta_a0 hbeta_f1 hbeta_f2 hbeta_a1 hbeta_a3 hbeta_c0 hbeta_c1 hwbase
      hwcases cast9 permA permB newVertex edgeList hedgeListLength newEdge hselectA hselectB
      vertex_cast9 nv0 nv1 nv2 nv3 nv4 nv5 nv6 nv7 nv8 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 hvertex_iff
      hedge_iff newVertex_injective newEdge_injective firstSeven pc1 hpc1 pc1' hpc1cast hc1ends
      firstEight tc0 htc0 tc1 htc1 tw htw S' hS'length hS'vertex hS'edge htwMissing hS'tash
      hbetaMissing
  rcases S' with ⟨size, positive, vertices, edges, vertexInjective, edgeInjective,
    firstEdge, attaches⟩
  change size = 8 at hS'length
  subst size
  have vertexEquality : vertices = newVertex := funext hS'vertex
  have edgeEquality : edges = newEdge := funext hS'edge
  subst vertices edges
  let S' : TreeSequence G e :=
    ⟨8, positive, newVertex, newEdge, vertexInjective, edgeInjective, firstEdge, attaches⟩
  have hS'length : S'.length = 8 := rfl
  have horderNine : TashkinovOrder G = 9 := by
    calc
      TashkinovOrder G = (TreeSequenceVertexSet S).card := horderM.1
      _ = S.length + 1 := by
        simp [TreeSequenceVertexSet, Finset.card_image_of_injective, S.vertex_injective]
      _ = 9 := by omega
  have hS'card : (TreeSequenceVertexSet S').card = 9 := by
    calc
      (TreeSequenceVertexSet S').card = S'.length + 1 := by
        simp [TreeSequenceVertexSet, Finset.card_image_of_injective, S'.vertex_injective]
      _ = 9 := by rw [hS'length]
  have hS'global : GlobalMaximumTriple G k e psi S' := by
    refine ⟨M.global.1, hS'tash, ?_⟩
    rw [hS'card, horderNine]
  have hf1f2 : f1 ≠ f2 := by
    intro equality
    have indices := newEdge_injective (show newEdge 1 = newEdge 3 by rw [ne1, ne3, equality])
    have values := congrArg Fin.val indices
    norm_num at values
  have hf1close : f1 ≠ M.closingEdge := by
    intro hh
    have hc : some g0 = some M.beta := by rw [← hf1color, hh, hclosingColor]
    exact hg0beta (Option.some.inj hc)
  have hf2close : f2 ≠ M.closingEdge := by
    intro hh
    have hc : some g0 = some M.beta := by rw [← hf2color, hh, hclosingColor]
    exact hg0beta (Option.some.inj hc)
  have hbetaClose : beta56 ≠ M.closingEdge := by
    intro equality
    have ends : s(v1, v2) = s(y4, y0) := by rw [← hbeta56ends, equality, hclosingEnds]
    rcases Sym2.eq_iff.mp ends with first | second
    · exact hv14 first.1
    · exact hv10 second.1
  let H := TwoColorIncidenceGraph G psi g0 M.beta
  let pathNodes : List (Sum V E) :=
    [Sum.inl y1, Sum.inr f1, Sum.inl v1, Sum.inr beta56, Sum.inl v2, Sum.inr f2, Sum.inl y4,
      Sum.inr M.closingEdge, Sum.inl y0]
  have hy1f1 : Incident G y1 f1 := by simp [Incident, hf1ends']
  have hv1f1 : Incident G v1 f1 := by simp [Incident, hf1ends']
  have hv1beta : Incident G v1 beta56 := by simp [Incident, hbeta56ends]
  have hv2beta : Incident G v2 beta56 := by simp [Incident, hbeta56ends]
  have hv2f2 : Incident G v2 f2 := by simp [Incident, hf2ends']
  have hy4f2 : Incident G y4 f2 := by simp [Incident, hf2ends']
  have hy4close : Incident G y4 M.closingEdge := by simp [Incident, hclosingEnds]
  have hy0close : Incident G y0 M.closingEdge := by simp [Incident, hclosingEnds]
  have hpathChain : pathNodes.IsChain H.Adj := by
    simp [pathNodes, H, TwoColorIncidenceGraph, hy1f1, hv1f1, hv1beta, hv2beta, hv2f2, hy4f2,
      hy4close, hy0close, hf1color, hf2color, hbeta56color, hclosingColor]
  have hpathNodesNonempty : pathNodes ≠ [] := by simp [pathNodes]
  let rawPath := SimpleGraph.Walk.ofSupport pathNodes hpathNodesNonempty hpathChain
  have hpathStart : pathNodes.head hpathNodesNonempty = Sum.inl (S'.vertex ⟨1, by omega⟩) := by
    change Sum.inl y1 = Sum.inl (newVertex 1)
    rw [nv1]
  have hpathEnd : pathNodes.getLast hpathNodesNonempty = Sum.inl (S'.vertex ⟨0, by omega⟩) := by
    change Sum.inl y0 = Sum.inl (newVertex 0)
    rw [nv0]
  let closingPath :
    H.Walk (Sum.inl (S'.vertex ⟨1, by omega⟩)) (Sum.inl (S'.vertex ⟨0, by omega⟩)) :=
    rawPath.copy hpathStart hpathEnd
  have hpathSupport : closingPath.support = pathNodes := by
    calc
      closingPath.support = rawPath.support := by
        simpa only [closingPath] using SimpleGraph.Walk.support_copy rawPath hpathStart hpathEnd
      _ = pathNodes := by
        simpa only [rawPath] using SimpleGraph.Walk.support_ofSupport hpathNodesNonempty hpathChain
  have hpathLength : closingPath.length = 8 := by
    calc
      closingPath.length = rawPath.length := by
        simpa only [closingPath] using SimpleGraph.Walk.length_copy rawPath hpathStart hpathEnd
      _ = pathNodes.length - 1 := by
        simpa only [rawPath] using SimpleGraph.Walk.length_ofSupport hpathNodesNonempty hpathChain
      _ = 8 := by simp [pathNodes]
  have hpathNodesNodup : pathNodes.Nodup := by
    simp [pathNodes, ← nv0, ← nv1, ← nv2, ← nv3, ← nv4, newVertex_injective.eq_iff, hf1f2, hf1close,
      hf2close, hbeta_f2, hbetaClose, Ne.symm hbeta_f1]
  have hpathIsPath : closingPath.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hpathSupport]
    exact hpathNodesNodup
  have hpathVertexSupport :
    ∀ v : V,
      Sum.inl v ∈ closingPath.support ↔
        ∃ i : Fin 5, v = S'.vertex (Fin.castLE (by norm_num : 5 ≤ 9) i) := by
    intro v
    rw [hpathSupport]
    let vertex5 : Fin 5 → V := fun i => newVertex (Fin.castLE (by norm_num : 5 ≤ 9) i)
    change _ ↔ ∃ i : Fin 5, v = vertex5 i
    have v0 : vertex5 0 = y0 := (mappedCastLE newVertex (by norm_num : 5 ≤ 9) 0 0 rfl).trans nv0
    have v1' : vertex5 1 = y1 := (mappedCastLE newVertex (by norm_num : 5 ≤ 9) 1 1 rfl).trans nv1
    have v2' : vertex5 2 = v1 := (mappedCastLE newVertex (by norm_num : 5 ≤ 9) 2 2 rfl).trans nv2
    have v3 : vertex5 3 = v2 := (mappedCastLE newVertex (by norm_num : 5 ≤ 9) 3 3 rfl).trans nv3
    have v4 : vertex5 4 = y4 := (mappedCastLE newVertex (by norm_num : 5 ≤ 9) 4 4 rfl).trans nv4
    simpa only [pathNodes, v0, v1', v2', v3, v4] using
      alternatingVertexSupport vertex5 f1 beta56 f2 M.closingEdge v
  have hpathEdgeSupport :
    ∀ f : E,
      Sum.inr f ∈ closingPath.support ↔
        f = M.closingEdge ∨ ∃ j : Fin S'.length, 1 ≤ j.val ∧ j.val + 2 ≤ 5 ∧ f = S'.edge j := by
    intro f
    rw [hpathSupport]
    change _ ↔ f = M.closingEdge ∨ ∃ j : Fin 8, 1 ≤ j.val ∧ j.val + 2 ≤ 5 ∧ f = newEdge j
    exact alternatingEdgeSupport y0 y1 v1 v2 y4 f1 beta56 f2 M.closingEdge newEdge ne1 ne2 ne3 f
  have htrunkEnds :
    ∀ j : Fin S'.length,
      1 ≤ j.val →
        j.val + 2 ≤ 5 →
          G.ends (S'.edge j) = s(S'.vertex ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, S'.vertex j.succ) :=
    by
    intro j hj hjbound
    fin_cases j <;> simp at hj hjbound
    · change G.ends (newEdge 1) = s(newVertex 1, newVertex 2)
      rw [ne1, nv1, nv2]
      exact hf1ends'
    · change G.ends (newEdge 2) = s(newVertex 2, newVertex 3)
      rw [ne2, nv2, nv3]
      exact hbeta56ends
    · change G.ends (newEdge 3) = s(newVertex 3, newVertex 4)
      rw [ne3, nv3, nv4]
      exact hf2ends'.trans Sym2.eq_swap
  let M' : NormalGlobalMaximumTriple G k e psi S' := by
    exact
      { global := hS'global
        height := 5
        height_lower := by omega
        height_upper := by rw [hS'length]; omega
        alpha := g0
        beta := M.beta
        alpha_missing := by
          change g0 ∈ MissingColors G psi (newVertex 0)
          rw [nv0]
          exact hg0'
        beta_missing := by
          change M.beta ∈ MissingColors G psi (newVertex 1)
          rw [nv1]
          exact hbetaMissing
        closingEdge := M.closingEdge
        lastIndex := ⟨4, by rw [hS'length]; omega⟩
        lastIndex_height := by norm_num
        closing_ends := by
          change G.ends M.closingEdge = s(newVertex 4, newVertex 0)
          rw [nv4, nv0]
          exact hclosingEnds
        closingPath := by simpa only [H] using closingPath
        closingPath_isPath := by simpa only [H] using hpathIsPath
        closingPath_length := by simpa using hpathLength
        closingPath_vertices := hpathVertexSupport
        closingPath_edges := hpathEdgeSupport
        trunk_edge_ends := htrunkEnds }
  have hM'height : M'.height = 5 := rfl
  have hM'bal : BalancedGlobalMaximumTriple M' := by
    constructor
    · change 5 = ScheideGraphHeight G
      exact hgraphHeight.symm
    · intro q hlow hupp
      have hq : q = 3 ∨ q = 4 := by
        change 5 < 2 * q at hlow
        change 2 * q < 8 + 1 at hupp
        omega
      rcases hq with rfl | rfl
      · change psi (newEdge 4) = psi (newEdge 5)
        rw [ne4, ne5, ha1color, ha3color]
      · change psi (newEdge 6) = psi (newEdge 7)
        rw [ne6, ne7, hc0color', hc1color]
  exact
    ⟨S', M', hS'length, hM'height, hM'bal, nv0, nv1, nv2, nv3, nv4, nv5, nv6, nv7, nv8, ne0, ne1,
      ne2, ne3, ne4, ne5, ne6, ne7, rfl, rfl⟩

private theorem helper_continuation_1913.{u_1, u_2} : scheideBlockContinuationStatement.{u_1, u_2}
    := by
  classical
  intro V E _ _ _ G k e0 phi T N hgraphHeight Good e psi S M hbal hlen hheight g0 horderM y0 y1
      y2 y3 y4 y5 y6 y7 y8 a1 a2 a3 b0 b1 c0 c1 hg0' p0 p1 f1 f2 v1 v2 hf1color hf2color hv10
      hv14 hf1ends' hf2ends' hb01ne horient beta56 hbeta56ends hbeta56color ha1ends ha2ends
      ha3ends hclosingEnds ha1color ha2color ha3color hclosingColor hab hg0alpha hg0beta r6' r7'
      w g1 hc1color hc0color' hwmissing' pc pc' hc0ends hg10 hg1alpha hg1beta g0last hg0lastEnds
      hg0lastColor alphaLast halphaLastEnds halphaLastColor betaLast hbetaLastEnds hbetaLastColor
      a0 ha0eq pa0 ha0ends hbeta_a0 hbeta_f1
  have hbeta_f2 : beta56 ≠ f2 := by
    intro hEq
    have hc : some M.beta = some g0 := by
      rw [← hbeta56color, hEq, hf2color]
    exact hg0beta (Option.some.inj hc).symm
  have hbeta_a1 : beta56 ≠ a1 := by
    intro hEq
    have hc : some M.beta = some M.alpha := by
      rw [← hbeta56color, hEq, ha1color]
    exact hab (Option.some.inj hc).symm
  have hbeta_a3 : beta56 ≠ a3 := by
    intro hEq
    have hc : some M.beta = some M.alpha := by
      rw [← hbeta56color, hEq, ha3color]
    exact hab (Option.some.inj hc).symm
  have hbeta_c0 : beta56 ≠ c0 := by
    intro hEq
    have hc : some M.beta = some g1 := by
      rw [← hbeta56color, hEq, hc0color']
    exact hg1beta (Option.some.inj hc).symm
  have hbeta_c1 : beta56 ≠ c1 := by
    intro hEq
    have hc : some M.beta = some g1 := by
      rw [← hbeta56color, hEq, hc1color]
    exact hg1beta (Option.some.inj hc).symm
  have rebase (hwbase : 5 ≤ w.val) :
      ∃ (S' : TreeSequence G e)
        (M' : NormalGlobalMaximumTriple G k e psi S')
        (_ : S'.length = 8) (_ : M'.height = 5),
        BalancedGlobalMaximumTriple M' ∧
        S'.vertex ⟨0, by omega⟩ = y0 ∧
        S'.vertex ⟨1, by omega⟩ = y1 ∧
        S'.vertex ⟨2, by omega⟩ = v1 ∧
        S'.vertex ⟨3, by omega⟩ = v2 ∧
        S'.vertex ⟨4, by omega⟩ = y4 ∧
        S'.vertex ⟨5, by omega⟩ = y2 ∧
        S'.vertex ⟨6, by omega⟩ = y3 ∧
        S'.vertex ⟨7, by omega⟩ = y7 ∧
        S'.vertex ⟨8, by omega⟩ = y8 ∧
        S'.edge ⟨0, by omega⟩ = a0 ∧
        S'.edge ⟨1, by omega⟩ = f1 ∧
        S'.edge ⟨2, by omega⟩ = beta56 ∧
        S'.edge ⟨3, by omega⟩ = f2 ∧
        S'.edge ⟨4, by omega⟩ = a1 ∧
        S'.edge ⟨5, by omega⟩ = a3 ∧
        S'.edge ⟨6, by omega⟩ = c0 ∧
        S'.edge ⟨7, by omega⟩ = c1 ∧
        M'.alpha = g0 ∧ M'.beta = M.beta := by
    have hwcases : w.val = 5 ∨ w.val = 6 := by
      have hwlt : w.val < 7 := by simp [r6']
      omega
    let cast9 : Fin 9 ≃ Fin (S.length + 1) := finCongr (by omega)
    let permA : Equiv.Perm (Fin 9) :=
      (Equiv.swap 2 5).trans (Equiv.swap 3 6)
    let permB : Equiv.Perm (Fin 9) :=
      ((Equiv.swap 2 6).trans (Equiv.swap 2 3)).trans (Equiv.swap 2 5)
    let newVertex : Fin 9 → V := fun i ↦
      if b0 = f1 then S.vertex (cast9 (permA i))
      else S.vertex (cast9 (permB i))
    let edgeList : List E := [a0, f1, beta56, f2, a1, a3, c0, c1]
    have hedgeListLength : edgeList.length = 8 := by rfl
    let newEdge : Fin 8 → E := fun i ↦
      edgeList.get (Fin.cast hedgeListLength.symm i)
    have hselectA (hb : b0 = f1) :
        y5 = v1 ∧ b1 = f2 ∧ y6 = v2 := by
      apply helper_hselectA_3623 <;> assumption
    have hselectB (hb : b0 ≠ f1) :
        y5 = v2 ∧ b1 = f1 ∧ y6 = v1 := by
      rcases horient with ho | ho
      · exact (hb ho.1).elim
      · exact ⟨ho.2.1, ho.2.2.1, ho.2.2.2⟩
    have vertex_cast9 (i : Fin 9) (q : Fin (S.length + 1))
        (hv : i.val = q.val) : S.vertex (cast9 i) = S.vertex q := by
      apply congrArg S.vertex
      apply Fin.ext
      simpa [cast9] using hv
    have nv0 : newVertex 0 = y0 := by
      apply helper_nv0_3642 <;> assumption
    have nv1 : newVertex 1 = y1 := by
      apply helper_nv1_3650 <;> assumption
    have nv2 : newVertex 2 = v1 := by
      apply helper_nv2_3221 <;> assumption
    have nv3 : newVertex 3 = v2 := by
      apply helper_nv3_3235 <;> assumption
    have nv4 : newVertex 4 = y4 := by
      apply helper_nv4_3666 <;> assumption
    have nv5 : newVertex 5 = y2 := by
      apply helper_nv5_3674 <;> assumption
    have nv6 : newVertex 6 = y3 := by
      apply helper_nv6_3682 <;> assumption
    have nv7 : newVertex 7 = y7 := by
      apply helper_nv7_3690 <;> assumption
    have nv8 : newVertex 8 = y8 := by
      apply helper_nv8_3698 <;> assumption
    have ne0 : newEdge 0 = a0 := rfl
    have ne1 : newEdge 1 = f1 := rfl
    have ne2 : newEdge 2 = beta56 := rfl
    have ne3 : newEdge 3 = f2 := rfl
    have ne4 : newEdge 4 = a1 := rfl
    have ne5 : newEdge 5 = a3 := rfl
    have ne6 : newEdge 6 = c0 := rfl
    have ne7 : newEdge 7 = c1 := rfl
    have hvertex_iff (i j : Fin (S.length + 1)) :
        S.vertex i = S.vertex j ↔ i = j := S.vertex_injective.eq_iff
    have hedge_iff (i j : Fin S.length) :
        S.edge i = S.edge j ↔ i = j := S.edge_injective.eq_iff
    have newVertex_injective : Function.Injective newVertex := by
      apply helper_hedge_iff_3716 <;> assumption
    have newEdge_injective : Function.Injective newEdge := by
      apply helper_newEdge_injective_3726 <;> assumption
    have firstSeven : ∀ q : Fin 7, ∃ t : Fin 7,
        newVertex (Fin.castLE (by norm_num : 7 ≤ 9) t) =
          S.vertex ⟨q.val, by omega⟩ := by
      apply helper_firstSeven_3311 <;> assumption
    obtain ⟨pc1, hpc1⟩ := S.attaches r7'
    let pc1' : Fin 8 := ⟨pc1.val, by simp [r7']⟩
    have hpc1cast : Fin.castLT pc1
        (Nat.lt_trans pc1.isLt (Nat.succ_lt_succ r7'.isLt)) =
        (⟨pc1'.val, by omega⟩ : Fin (S.length + 1)) := by
      apply Fin.ext
      rfl
    have hc1ends : G.ends c1 = s(y8, S.vertex ⟨pc1'.val, by omega⟩) := by
      simpa [c1, r7', y8, hpc1cast] using hpc1
    have firstEight : ∀ q : Fin 8, ∃ t : Fin 8,
        newVertex (Fin.castLE (by norm_num : 8 ≤ 9) t) =
          S.vertex ⟨q.val, by omega⟩ := by
      apply helper_firstEight_3682 <;> assumption
    obtain ⟨tc0, htc0⟩ := firstSeven pc'
    obtain ⟨tc1, htc1⟩ := firstEight pc1'
    obtain ⟨tw, htw⟩ := firstSeven w
    let S' : TreeSequence G e := by
      exact @helperS3810 (@V) (@E) inferInstance (@G) (@e)
           (@S) (@hlen) (@f1) (@f2) (@v1) (@v2) (@hf1ends') (@hf2ends') (@beta56)
          (@hbeta56ends) (@ha1ends) (@ha3ends) (@w) (@pc) (@hc0ends) (@ha0eq) (@ha0ends)
          (@hedgeListLength) (@nv0) (@nv1) (@nv2) (@nv3) (@nv4) (@nv5) (@nv6) (@nv7) (@nv8)
          (@ne0) (@ne1) (@ne2) (@ne3) (@ne4) (@ne5) (@ne6) (@ne7) (@newVertex_injective)
          (@newEdge_injective) (@pc1) (@hc1ends) (@tc0) (@htc0) (@tc1) (@htc1)
    have hS'length : S'.length = 8 := rfl
    have hS'vertex (i : Fin 9) : S'.vertex i = newVertex i := rfl
    have hS'edge (i : Fin 8) : S'.edge i = newEdge i := rfl
    have htwMissing : g1 ∈ MissingColors G psi
        (S'.vertex ⟨tw.val, by omega⟩) := by
      change g1 ∈ MissingColors G psi
        (newVertex (Fin.castLE (by omega) tw))
      rw [htw]
      exact hwmissing'
    have hS'tash : TashkinovTree G e psi S' := by apply helper_hS'tash_4523 <;> assumption
    have hbetaMissing : M.beta ∈ MissingColors G psi y1 := by
      simpa [y1] using M.beta_missing
    exact @scheideRebasedTreeCertificate (@«V») (@«E») inferInstance inferInstance inferInstance
        (@«G») (@«k») (@«hgraphHeight») (@«e») (@«psi») (@«S») (@«M») (@«hbal») (@«hlen»)
        (@«hheight») (@«g0») (@«horderM») (@«y0») (@«y1») (@«y2») (@«y3») (@«y4») (@«y5») (@«y6»)
        (@«y7») (@«y8») (@«a1») (@«a2») (@«a3») (@«b0») (@«b1») (@«c0») (@«c1») (@«hg0'») (@«p0»)
        (@«p1») (@«f1») (@«f2») (@«v1») (@«v2») (@«hf1color») (@«hf2color») (@«hv10») (@«hv14»)
        (@«hf1ends'») (@«hf2ends'») (@«hb01ne») (@«horient») (@«beta56») (@«hbeta56ends»)
        (@«hbeta56color») (@«ha1ends») (@«ha2ends») (@«ha3ends») (@«hclosingEnds») (@«ha1color»)
        (@«ha2color») (@«ha3color») (@«hclosingColor») (@«hab») (@«hg0alpha») (@«hg0beta») (@«r6'»)
        (@«r7'») (@«w») (@«g1») (@«hc1color») (@«hc0color'») (@«hwmissing'») (@«pc») (@«pc'»)
        (@«hc0ends») (@«hg10») (@«hg1alpha») (@«hg1beta») (@«g0last») (@«hg0lastEnds»)
        (@«hg0lastColor») (@«alphaLast») (@«halphaLastEnds») (@«halphaLastColor») (@«betaLast»)
        (@«hbetaLastEnds») (@«hbetaLastColor») (@«a0») (@«ha0eq») (@«pa0») (@«ha0ends»)
        (@«hbeta_a0») (@«hbeta_f1») (@«hbeta_f2») (@«hbeta_a1») (@«hbeta_a3») (@«hbeta_c0»)
        (@«hbeta_c1») (@«hwbase») (@«hwcases») (@«cast9») (@«permA») (@«permB») (@«newVertex»)
        (@«edgeList») (@«hedgeListLength») (@«newEdge») (@«hselectA») (@«hselectB»)
        (@«vertex_cast9») (@«nv0») (@«nv1») (@«nv2») (@«nv3») (@«nv4») (@«nv5») (@«nv6») (@«nv7»)
        (@«nv8») (@«ne0») (@«ne1») (@«ne2») (@«ne3») (@«ne4») (@«ne5») (@«ne6») (@«ne7»)
        (@«hvertex_iff») (@«hedge_iff») (@«newVertex_injective») (@«newEdge_injective»)
        (@«firstSeven») (@«pc1») (@«hpc1») (@«pc1'») (@«hpc1cast») (@«hc1ends») (@«firstEight»)
        (@«tc0») (@«htc0») (@«tc1») (@«htc1») (@«tw») (@«htw») (@«S'») (@«hS'length») (@«hS'vertex»)
        (@«hS'edge») (@«htwMissing») (@hS'tash) (@hbetaMissing)
  exact @helper_continuation_2887 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@hgraphHeight) (@e) (@psi) (@S) (@M) (@hbal) (@hlen) (@hheight) (@g0) (@hg0') (@f1) (@f2)
      (@v1) (@v2) (@hf1color) (@hf2color) (@hf1ends') (@hf2ends') (@horient) (@beta56)
      (@hbeta56ends) (@hbeta56color) (@ha1ends) (@ha2ends) (@ha3ends) (@ha1color) (@ha2color)
      (@ha3color) (@hab) (@hg0alpha) (@hg0beta) (@w) (@g1) (@hc1color) (@hc0color') (@hwmissing')
      (@hg10) (@hg1alpha) (@hg1beta) (@g0last) (@hg0lastEnds) (@hg0lastColor) (@alphaLast)
      (@halphaLastEnds) (@halphaLastColor) (@betaLast) (@hbetaLastEnds) (@hbetaLastColor) (@rebase)

private theorem helper_second_ne_of_matching_4215.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E]
  (G : LooplessMultigraph V E) (k : ℕ) {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence
      G e)
  (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)) (_ :
      IsProperEdgeColoring G psi)
  (_ : ColoredVertexSetElementary G psi (TreeSequenceVertexSet S)),
  let y7 : V :=
    S.vertex
      (⟨(7 : ℕ), by
          omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let c0 : E :=
    S.edge
      (⟨(6 : ℕ), by
          omega⟩ :
        Fin S.length);
  ∀ (_ :
  ∀ {i j : Fin (S.length + (1 : ℕ))},
  i ≠ j →
  S.vertex i ≠ S.vertex j)
    (_ :
  ∀ (i : Fin (S.length + (1 : ℕ))),
  S.vertex i ∈ TreeSequenceVertexSet S)
    (_ :
  ∀ {c : Fin k} {v : V} {f : E},
  c ∈ MissingColors G psi v →
  Incident G v
    f →
  psi f ≠ some c)
    (_ :
      Fin
        ((↑(⟨(4 : ℕ), by
                  omega⟩ :
                Fin S.length) :
            ℕ) +
          (1 : ℕ)))
    (_ :
      Fin
        ((↑(⟨(5 : ℕ), by
                  omega⟩ :
                Fin S.length) :
            ℕ) +
          (1 : ℕ))),
  let r6' : Fin S.length :=
    (⟨(6 : ℕ), by
        omega⟩ :
      Fin S.length);
  ∀ (w : Fin ((↑r6' : ℕ) + (1 : ℕ))) (g1 : Fin k) (_ : psi c0 = some g1)
    (_ :
      g1 ∈
        MissingColors G psi
          (S.vertex
            (⟨(↑w : ℕ), by
                omega⟩ :
              Fin (S.length + (1 : ℕ)))))
    (pc : Fin ((↑r6' : ℕ) + (1 : ℕ))),
  let pc' : Fin (7 : ℕ) :=
    (⟨(↑pc : ℕ), by
        first
        | omega
        | ( have := GoldbergSeymour.TreeSequence.positive S
            have := Fin.isLt pc
            have := GoldbergSeymour.TreeSequence.positive S
            all_goals omega)⟩ :
      Fin (7 : ℕ));
  ∀
    (_ :
      G.ends c0 =
        s(y7,
          S.vertex
            (⟨(↑pc' : ℕ), by
                omega⟩ :
              Fin (S.length + (1 : ℕ)))))
    (c : Fin k) (m : Fin (7 : ℕ))
    (_ :
      c ∈
        MissingColors G psi
          (S.vertex
            (⟨(↑m : ℕ), by
                omega⟩ :
              Fin (S.length + (1 : ℕ)))))
    (_ :
  ∀ (q : Fin (7 : ℕ)),
  q ≠ m →
  ∃ (f : E),
    f ≠ c0 ∧
      Incident G
          (S.vertex
            (⟨(↑q : ℕ), by
                omega⟩ :
              Fin (S.length + (1 : ℕ))))
          f ∧
        psi f = some c ∧ ¬Incident G y7 f),
  g1 ≠ c := by
  classical
  intro V E _ _ _ G k e psi S M hlen hproper helem y7 c0 hvertex_ne hmem missing_excludes p0 p1 r6'
      w g1 hc0color' hwmissing' pc pc' hc0ends c m hcmiss hcover hEq
  have hwEq : w.val = m.val := by
    by_contra hne
    have hvne : S.vertex ⟨w.val, by omega⟩ ≠
        S.vertex ⟨m.val, by omega⟩ := by
      apply hvertex_ne
      exact Fin.ne_of_val_ne hne
    have hd := helem (hmem (⟨w.val, by omega⟩ : Fin (S.length + 1)))
      (hmem (⟨m.val, by omega⟩ : Fin (S.length + 1))) hvne
    exact (Finset.disjoint_left.mp hd) hwmissing'
      (by simpa [hEq] using hcmiss)
  have hpcne : pc' ≠ m := by
    intro hpm
    have hinc : Incident G (S.vertex ⟨m.val, by omega⟩) c0 := by
      rw [Incident, hc0ends]
      have hv : S.vertex ⟨pc'.val, by omega⟩ =
          S.vertex ⟨m.val, by omega⟩ := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa using congrArg Fin.val hpm
      rw [hv]
      simp
    exact (missing_excludes hcmiss hinc) (by simpa [hEq] using hc0color')
  obtain ⟨f, hfc0, hincf, hfcolor, _⟩ := hcover pc' hpcne
  have hincc : Incident G (S.vertex ⟨pc'.val, by omega⟩) c0 := by
    rw [Incident, hc0ends]
    simp
  exact (hproper hfc0.symm ⟨S.vertex ⟨pc'.val, by omega⟩, hincc,
    hincf⟩ (by simpa [hEq] using hc0color')) hfcolor

private theorem helper_continuation_1474.{u_1, u_2} :
    helperContinuation1474Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hgraphHeight Good e psi S M hbal hlen hheight g0 hproper horderM
      helem hclosed y0 y1 y2 y3 y4 y5 y6 y7 y8 a1 a2 a3 b0 b1 c0 c1 hvertex_ne hedge_ne hmem
      missing_excludes h4' h5' hg0' p0 hb0ends p1 hb1ends hp1not5 f1 f2 f3 v1 v2 hf1color
      hf2color hf3color hv10 hv14 hf1ends' hf2ends' hf3ends' hb01ne horient alpha56 beta56
      halpha56color hbeta56ends hbeta56color halpha56ends' hbeta56ends' ha1ends ha2ends ha3ends
      hclosingEnds ha1color ha2color ha3color hclosingColor hab hg0alpha hg0beta r6' r7' w g1
      hc1color hc0color' hwmissing' pc pc' hc0ends hc0_ne_f3 hc0_ne_alpha56 hc0_ne_beta56
      hc0_ne_closing no_y7_of_ends hy0_7 hy1_7 hy2_7 hy3_7 hy4_7 hy5_7 hy6_7 hv1_7 hv2_7
  have hno_f1 : ¬ Incident G y7 f1 :=
    no_y7_of_ends hf1ends' hy1_7 hv1_7
  have hno_f2 : ¬ Incident G y7 f2 :=
    no_y7_of_ends hf2ends' hy4_7 hv2_7
  have hno_f3 : ¬ Incident G y7 f3 :=
    no_y7_of_ends hf3ends' hy2_7 hy3_7
  have hno_a1 : ¬ Incident G y7 a1 :=
    no_y7_of_ends ha1ends hy1_7 hy2_7
  have hno_a2 : ¬ Incident G y7 a2 :=
    no_y7_of_ends ha2ends hy2_7 hy3_7
  have hno_a3 : ¬ Incident G y7 a3 :=
    no_y7_of_ends ha3ends hy3_7 hy4_7
  have hno_close : ¬ Incident G y7 M.closingEdge :=
    no_y7_of_ends hclosingEnds hy4_7 hy0_7
  have hno_alpha56 : ¬ Incident G y7 alpha56 :=
    no_y7_of_ends halpha56ends' hy5_7 hy6_7
  have hno_beta56 : ¬ Incident G y7 beta56 :=
    no_y7_of_ends hbeta56ends' hy5_7 hy6_7
  have hp0lt : p0.val < 5 := by simp
  have hp1lt : p1.val < 5 := by
    have hp : p1.val < 6 := by simp
    omega
  have hp0vertex_ne7 : S.vertex (Fin.castLT p0
      (Nat.lt_trans p0.isLt
        (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt))) ≠ y7 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change p0.val ≠ 7
    omega
  have hp1vertex_ne7 : S.vertex (Fin.castLT p1
      (Nat.lt_trans p1.isLt
        (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt))) ≠ y7 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change p1.val ≠ 7
    omega
  have hno_b0 : ¬ Incident G y7 b0 :=
    no_y7_of_ends hb0ends hy5_7 hp0vertex_ne7
  have hno_b1 : ¬ Incident G y7 b1 :=
    no_y7_of_ends hb1ends hy6_7 hp1vertex_ne7
  have second_ne_of_matching (c : Fin k) (m : Fin 7)
      (hcmiss : c ∈ MissingColors G psi
        (S.vertex ⟨m.val, by omega⟩))
      (hcover : ∀ q : Fin 7, q ≠ m →
        ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
          psi f = some c ∧ ¬ Incident G y7 f) : g1 ≠ c := by
    exact @helper_second_ne_of_matching_4215 (@V) (@E) inferInstance inferInstance inferInstance
        (@G) (@k) (@e) (@psi) (@S) (@M) (@hlen) (@hproper) (@helem) (@hvertex_ne) (@hmem)
        (@missing_excludes) (@p0) (@p1) (@w) (@g1) (@hc0color') (@hwmissing') (@pc) (@hc0ends) (@c)
        (@m) (@hcmiss) (@hcover)
  have hcoverG0 : ∀ q : Fin 7, q ≠ (0 : Fin 7) →
      ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
        psi f = some g0 ∧ ¬ Incident G y7 f := by
    exact @helper_hcoverG0_732 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (@hlen) (@g0) (@hedge_ne) (@h4') (@h5') (@p0)
        (@hb0ends) (@p1) (@hb1ends) (@f1) (@f2) (@f3) (@v1) (@v2) (@hf1color) (@hf2color)
        (@hf3color) (@hf1ends') (@hf2ends') (@hf3ends') (@horient) (@hc0_ne_f3) (@hno_f1) (@hno_f2)
        (@hno_f3) (@hno_b0) (@hno_b1)
  have hcoverAlpha : ∀ q : Fin 7, q ≠ (0 : Fin 7) →
      ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
        psi f = some M.alpha ∧ ¬ Incident G y7 f := by
    exact @helper_hcoverAlpha_795 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (@hlen) (@hedge_ne) (@p0) (@p1) (@alpha56)
        (@halpha56color) (@halpha56ends') (@ha1ends) (@ha3ends) (@ha1color) (@ha3color)
        (@hc0_ne_alpha56) (@hno_a1) (@hno_a3) (@hno_alpha56)
  have hcoverBeta : ∀ q : Fin 7, q ≠ (1 : Fin 7) →
      ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
        psi f = some M.beta ∧ ¬ Incident G y7 f := by
    exact @helper_hcoverBeta_834 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (@hlen) (@hedge_ne) (@p0) (@p1) (@beta56)
        (@hbeta56color) (@hbeta56ends') (@ha2ends) (@hclosingEnds) (@ha2color) (@hclosingColor)
        (@hc0_ne_beta56) (@hc0_ne_closing) (@hno_a2) (@hno_close) (@hno_beta56)
  have hg10 : g1 ≠ g0 :=
    second_ne_of_matching g0 (0 : Fin 7) (by simpa [y0] using hg0') hcoverG0
  have hg1alpha : g1 ≠ M.alpha :=
    second_ne_of_matching M.alpha (0 : Fin 7)
      (by simpa [y0] using M.alpha_missing) hcoverAlpha
  have hg1beta : g1 ≠ M.beta :=
    second_ne_of_matching M.beta (1 : Fin 7)
      (by simpa [y1] using M.beta_missing) hcoverBeta
  have last_pair_edge (c : Fin k) (m : Fin 7)
      (hcmiss : c ∈ MissingColors G psi
        (S.vertex ⟨m.val, by omega⟩))
      (hcover : ∀ q : Fin 7, q ≠ m →
        ∃ f : E, f ≠ c0 ∧ Incident G (S.vertex ⟨q.val, by omega⟩) f ∧
          psi f = some c ∧ ¬ Incident G y7 f) :
      ∃ f : E, G.ends f = s(y7, y8) ∧ psi f = some c := by
    apply helper_last_pair_edge_881 <;> assumption
  obtain ⟨g0last, hg0lastEnds, hg0lastColor⟩ :=
    last_pair_edge g0 (0 : Fin 7) (by simpa [y0] using hg0') hcoverG0
  obtain ⟨alphaLast, halphaLastEnds, halphaLastColor⟩ :=
    last_pair_edge M.alpha (0 : Fin 7)
      (by simpa [y0] using M.alpha_missing) hcoverAlpha
  obtain ⟨betaLast, hbetaLastEnds, hbetaLastColor⟩ :=
    last_pair_edge M.beta (1 : Fin 7)
      (by simpa [y1] using M.beta_missing) hcoverBeta
  have hg0AlphaLast : g0last ≠ alphaLast := by
    intro hEq
    have hc : some g0 = some M.alpha := by
      rw [← hg0lastColor, hEq, halphaLastColor]
    exact hg0alpha (Option.some.inj hc)
  have hg0BetaLast : g0last ≠ betaLast := by
    intro hEq
    have hc : some g0 = some M.beta := by
      rw [← hg0lastColor, hEq, hbetaLastColor]
    exact hg0beta (Option.some.inj hc)
  have hAlphaBetaLast : alphaLast ≠ betaLast := by
    intro hEq
    have hc : some M.alpha = some M.beta := by
      rw [← halphaLastColor, hEq, hbetaLastColor]
    exact hab (Option.some.inj hc)
  let a0 : E := S.edge ⟨0, by omega⟩
  have ha0eq : a0 = e := by simpa [a0] using S.first_edge
  have ha0color : psi a0 = none := by
    rw [ha0eq]
    exact M.global.1.2.2.2.2.1
  obtain ⟨pa0, hpa0⟩ := S.attaches (⟨0, by omega⟩ : Fin S.length)
  have hpa0zero : pa0 = 0 := Fin.eq_zero pa0
  have hpa0cast :
      (Fin.castLT pa0 (Nat.lt_trans pa0.isLt
        (Nat.succ_lt_succ (show 0 < S.length by omega))) :
          Fin (S.length + 1)) =
        (⟨0, Nat.zero_lt_succ S.length⟩ : Fin (S.length + 1)) := by
    apply Fin.ext
    simp [hpa0zero]
  have ha0ends : G.ends a0 = s(y1, y0) := by
    simpa [a0, y0, y1, hpa0cast] using hpa0
  have hbeta_a0 : beta56 ≠ a0 := by
    intro hEq
    rw [hEq, ha0color] at hbeta56color
    simp at hbeta56color
  have hbeta_f1 : beta56 ≠ f1 := by
    intro hEq
    have hc : some M.beta = some g0 := by
      rw [← hbeta56color, hEq, hf1color]
    exact hg0beta (Option.some.inj hc).symm
  exact @helper_continuation_1913 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hgraphHeight) (@e) (@psi) (@S) (@M) (@hbal) (@hlen) (@hheight)
      (@g0) (@horderM) (@hg0') (@p0) (@p1) (@f1) (@f2) (@v1) (@v2) (@hf1color) (@hf2color)
      (@hv10) (@hv14) (@hf1ends') (@hf2ends') (@hb01ne) (@horient) (@beta56) (@hbeta56ends)
      (@hbeta56color) (@ha1ends) (@ha2ends) (@ha3ends) (@hclosingEnds) (@ha1color) (@ha2color)
      (@ha3color) (@hclosingColor) (@hab) (@hg0alpha) (@hg0beta) (@w) (@g1) (@hc1color)
      (@hc0color') (@hwmissing') (@pc) (@hc0ends) (@hg10) (@hg1alpha) (@hg1beta) (@g0last)
      (@hg0lastEnds) (@hg0lastColor) (@alphaLast) (@halphaLastEnds) (@halphaLastColor)
      (@betaLast) (@hbetaLastEnds) (@hbetaLastColor) (@ha0eq) (@pa0) (@ha0ends) (@hbeta_a0)
      (@hbeta_f1)
private theorem helper_continuation_995.{u_1, u_2} :
    helperContinuation995Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hgraphHeight this Good e psi S M hbal hlen hheight g0 hproper
      horderM helem hclosed y0 y1 y2 y3 y4 y5 y6 y7 y8 a1 a2 a3 b0 b1 c0 c1 hvertex_ne hedge_ne
      hmem missing_excludes h4' h5' hg0' p0 hb0ends p1 hb1ends hp1not5 f1 f2 f3 v1 v2 hf1ends
      hf2ends hf1color hf2color hf3color hv1T hv2T hv10 hv11 hv12 hv13 hv14 hv20 hv21 hv22 hv23
      hv24 hf1ends' hf2ends' hf3ends' classifyFirst
  have hb01ne : b0 ≠ b1 := by
    apply hedge_ne
    norm_num
  have horient :
      (b0 = f1 ∧ y5 = v1 ∧ b1 = f2 ∧ y6 = v2) ∨
      (b0 = f2 ∧ y5 = v2 ∧ b1 = f1 ∧ y6 = v1) := by
    exact @helper_horient_1122 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e)
        (@psi) (@S) (@M) (@hlen) (@f1) (@f2) (@v1) (@v2) (@classifyFirst) (@hb01ne)
  obtain ⟨alpha56, beta56, halpha56ends, halpha56color,
      hbeta56ends, hbeta56color, hab56ne⟩ :=
    ScheideHeightFiveOutsideLinks G k e psi S M hheight hgraphHeight g0
      (by simpa [y0] using hg0') f1 f2 v1 v2 hf1ends hf2ends
      hf1color hf2color hv1T hv2T hv10 hv11 hv12 hv13 hv14 hv20 hv21
      hv22 hv23 hv24
  have halpha56ends' : G.ends alpha56 = s(y5, y6) := by
    rcases horient with h | h
    · simpa [h.2.1, h.2.2.2] using halpha56ends
    · simpa [h.2.1, h.2.2.2, Sym2.eq_swap] using halpha56ends
  have hbeta56ends' : G.ends beta56 = s(y5, y6) := by
    rcases horient with h | h
    · simpa [h.2.1, h.2.2.2] using hbeta56ends
    · simpa [h.2.1, h.2.2.2, Sym2.eq_swap] using hbeta56ends
  have ha1ends : G.ends a1 = s(y1, y2) := by
    exact @helper_ha1ends_1148 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e)
        (@psi) (@S) (@M) (@hlen) (@hheight)
  have ha2ends : G.ends a2 = s(y2, y3) := by
    exact @helper_ha2ends_1154 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e)
        (@psi) (@S) (@M) (@hlen) (@hheight)
  have ha3ends : G.ends a3 = s(y3, y4) := by
    exact @helper_ha3ends_1160 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e)
        (@psi) (@S) (@M) (@hlen) (@hheight)
  have hlast : M.lastIndex = (⟨4, by omega⟩ : Fin (S.length + 1)) := by
    apply Fin.ext
    have hm := M.lastIndex_height
    rw [hheight] at hm
    simpa using hm
  have hclosingEnds : G.ends M.closingEdge = s(y4, y0) := by
    simpa [y4, y0, hlast] using M.closing_ends
  have hcycle := ScheideTrunkRotationCycle G k e psi S M hbal
  have ha1cycle : NormalCycleEdge M (⟨1, by omega⟩ : Fin M.height) = a1 := by
    simp [NormalCycleEdge, a1, hheight]
  have ha2cycle : NormalCycleEdge M (⟨2, by omega⟩ : Fin M.height) = a2 := by
    simp [NormalCycleEdge, a2, hheight]
  have ha3cycle : NormalCycleEdge M (⟨3, by omega⟩ : Fin M.height) = a3 := by
    simp [NormalCycleEdge, a3, hheight]
  have hcloseCycle : NormalCycleEdge M (⟨4, by omega⟩ : Fin M.height) =
      M.closingEdge := by
    simp [NormalCycleEdge, hheight]
  have ha1color : psi a1 = some M.alpha := by
    have hc := hcycle.2.2.2.2 (⟨1, by omega⟩ : Fin M.height) (by norm_num)
    simpa [ha1cycle] using hc
  have ha2color : psi a2 = some M.beta := by
    have hc := hcycle.2.2.2.2 (⟨2, by omega⟩ : Fin M.height) (by norm_num)
    have heven : ¬ Odd (2 : ℕ) := by decide
    simpa [ha2cycle, heven] using hc
  have ha3color : psi a3 = some M.alpha := by
    have hc := hcycle.2.2.2.2 (⟨3, by omega⟩ : Fin M.height) (by norm_num)
    have hodd : Odd (3 : ℕ) := by decide
    simpa [ha3cycle, hodd] using hc
  have hclosingColor : psi M.closingEdge = some M.beta := by
    have hc := hcycle.2.2.2.2 (⟨4, by omega⟩ : Fin M.height) (by norm_num)
    have heven : ¬ Odd (4 : ℕ) := by decide
    simpa [hcloseCycle, heven] using hc
  have hab : M.alpha ≠ M.beta := by
    exact @helper_hab_1198 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e)
        (@psi) (@S) (@M) (@hlen) (@helem) (@hvertex_ne) (@hmem)
  have hg0alpha : g0 ≠ M.alpha := by
    exact @helper_hg0alpha_524 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
      assumption) (@g0) (by
      assumption) (by
      assumption) (@f1) (@f2) (@v1) (@v2) (by
      assumption) (by
      assumption) (by
      assumption) (@alpha56) (by
      assumption) (by
      assumption)
  have hg0beta : g0 ≠ M.beta := by
    exact @helper_hg0beta_547 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
      assumption) (@g0) (by
      assumption) (by
      assumption) (@f1) (@f2) (@v1) (@v2) (by
      assumption) (by
      assumption) (by
      assumption) (@beta56) (by
      assumption) (by
      assumption)
  let r6' : Fin S.length := ⟨6, by omega⟩
  let r7' : Fin S.length := ⟨7, by omega⟩
  obtain ⟨w, g1, hc0color, hwmissing⟩ := M.global.2.1 r6' (by simp [r6'])
  have hc1color : psi c1 = some g1 := by
    have hp := hbal.2 4 (by omega) (by omega)
    have hc0' : psi c0 = some g1 := by simpa [c0, r6'] using hc0color
    simpa [c0, c1, r6', r7'] using hp.symm.trans hc0'
  have hc0color' : psi c0 = some g1 := by simpa [c0, r6'] using hc0color
  have hwmissing' : g1 ∈ MissingColors G psi
      (S.vertex ⟨w.val, by omega⟩) := by
    have hi : Fin.castLT w
        (Nat.lt_trans w.isLt (Nat.succ_lt_succ r6'.isLt)) =
        (⟨w.val, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
    simpa [hi] using hwmissing
  obtain ⟨pc, hpc⟩ := S.attaches r6'
  let pc' : Fin 7 := ⟨pc.val, by simp [r6']⟩
  have hc0ends : G.ends c0 = s(y7, S.vertex ⟨pc'.val, by omega⟩) := by
    have hi : Fin.castLT pc
        (Nat.lt_trans pc.isLt (Nat.succ_lt_succ r6'.isLt)) =
        (⟨pc'.val, by omega⟩ : Fin (S.length + 1)) := Fin.ext rfl
    simpa [c0, y7, r6', hi] using hpc
  have hc0_ne_f3 : c0 ≠ f3 := by
    intro hEq
    have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y2, y3) := by
      rw [← hc0ends, hEq, hf3ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨2, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y2] using hd.1)
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨3, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y3] using hs.1)
  have hc0_ne_alpha56 : c0 ≠ alpha56 := by
    intro hEq
    have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y5, y6) := by
      rw [← hc0ends, hEq, halpha56ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y5] using hd.1)
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y6] using hs.1)
  have hc0_ne_beta56 : c0 ≠ beta56 := by
    intro hEq
    have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y5, y6) := by
      rw [← hc0ends, hEq, hbeta56ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨5, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y5] using hd.1)
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨6, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y6] using hs.1)
  have hc0_ne_closing : c0 ≠ M.closingEdge := by
    intro hEq
    have hpairs : s(y7, S.vertex ⟨pc'.val, by omega⟩) = s(y4, y0) := by
      rw [← hc0ends, hEq, hclosingEnds]
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨4, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y4] using hd.1)
    · exact (hvertex_ne (i := (⟨7, by omega⟩ : Fin (S.length + 1)))
        (j := (⟨0, by omega⟩ : Fin (S.length + 1))) (by norm_num))
        (by simpa [y7, y0] using hs.1)
  have no_y7_of_ends {f : E} {u v : V} (hf : G.ends f = s(u, v))
      (hu : u ≠ y7) (hv : v ≠ y7) : ¬ Incident G y7 f := by
    exact @helper_no_y7_of_ends_1435 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e) (@psi) (@S) (@M) (@hlen) (@f) (@u) (@v) (@hf) (@hu) (@hv)
  have hy0_7 : y0 ≠ y7 := by apply hvertex_ne; norm_num
  have hy1_7 : y1 ≠ y7 := by apply hvertex_ne; norm_num
  have hy2_7 : y2 ≠ y7 := by apply hvertex_ne; norm_num
  have hy3_7 : y3 ≠ y7 := by apply hvertex_ne; norm_num
  have hy4_7 : y4 ≠ y7 := by apply hvertex_ne; norm_num
  have hy5_7 : y5 ≠ y7 := by apply hvertex_ne; norm_num
  have hy6_7 : y6 ≠ y7 := by apply hvertex_ne; norm_num
  have hv1_7 : v1 ≠ y7 := by
    rcases horient with h | h
    · exact h.2.1 ▸ hy5_7
    · exact h.2.2.2 ▸ hy6_7
  have hv2_7 : v2 ≠ y7 := by
    rcases horient with h | h
    · exact h.2.2.2 ▸ hy6_7
    · exact h.2.1 ▸ hy5_7
  exact @helper_continuation_1474 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hgraphHeight) (@e) (@psi) (@S) (@M) (@hbal) (@hlen) (@hheight)
      (@g0) (@hproper) (@horderM) (@helem) (@hclosed) (@hvertex_ne) (@hedge_ne) (@hmem)
      (@missing_excludes) (@h4') (@h5') (@hg0') (@p0) (@hb0ends) (@p1) (@hb1ends) (@hp1not5)
      (@f1) (@f2) (@f3) (@v1) (@v2) (@hf1color) (@hf2color) (@hf3color) (@hv10) (@hv14)
      (@hf1ends') (@hf2ends') (@hf3ends') (@hb01ne) (@horient) (@alpha56) (@beta56)
      (@halpha56color) (@hbeta56ends) (@hbeta56color) (@halpha56ends') (@hbeta56ends') (@ha1ends)
      (@ha2ends) (@ha3ends) (@hclosingEnds) (@ha1color) (@ha2color) (@ha3color) (@hclosingColor)
      (@hab) (@hg0alpha) (@hg0beta) (@w) (@g1) (@hc1color) (@hc0color') (@hwmissing') (@pc)
      (@hc0ends) (@hc0_ne_f3) (@hc0_ne_alpha56) (@hc0_ne_beta56) (@hc0_ne_closing)
      (@no_y7_of_ends) (@hy0_7) (@hy1_7) (@hy2_7) (@hy3_7) (@hy4_7) (@hy5_7) (@hy6_7) (@hv1_7)
      (@hv2_7)
private theorem helper_missing_excludes_2266.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E]
  (G : LooplessMultigraph V E) (k : ℕ) (psi : PartialEdgeColoring E k) {c : Fin k}
  {v : V} {f : E},
  c ∈ MissingColors G psi v →
  Incident G v f →
  psi f ≠ some c := by
  classical
  intro V E _ _ G k psi c v f hc hinc hfc
  let _ := Fintype.ofFinite V
  have hp : c ∈ PresentColors G psi v := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨f, hinc, hfc⟩
  have hn : c ∉ PresentColors G psi v := by
    simpa [MissingColors] using hc
  exact hn hp

private theorem helper_hq0cases_2300.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) {e : E}
  (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
  (_ : NormalGlobalMaximumTriple G k e psi S) (hlen : S.length = (8 : ℕ)),
  let y5 : V :=
    S.vertex
      (⟨(5 : ℕ), by
          have := GoldbergSeymour.TreeSequence.positive S
          omega⟩ :
        Fin (S.length + (1 : ℕ)));
  let b0 : E :=
    S.edge
      (⟨(4 : ℕ), by
          have := GoldbergSeymour.TreeSequence.positive S
          omega⟩ :
        Fin S.length);
  ∀ (q0 : Fin (5 : ℕ)),
  G.ends
        (S.edge
          (⟨(4 : ℕ) + (↑(0 : Fin (2 : ℕ)) : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      s(S.vertex
          (⟨(↑q0 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))),
        S.vertex
          (⟨(5 : ℕ) + (↑(0 : Fin (2 : ℕ)) : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ)))) →
  G.ends b0 =
      s(S.vertex
          (⟨(0 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))),
        y5) ∨
    G.ends b0 =
        s(S.vertex
            (⟨(1 : ℕ), by
                have := GoldbergSeymour.TreeSequence.positive S
                omega⟩ :
              Fin (S.length + (1 : ℕ))),
          y5) ∨
      G.ends b0 =
          s(S.vertex
              (⟨(2 : ℕ), by
                  have := GoldbergSeymour.TreeSequence.positive S
                  omega⟩ :
                Fin (S.length + (1 : ℕ))),
            y5) ∨
        G.ends b0 =
            s(S.vertex
                (⟨(3 : ℕ), by
                    have := GoldbergSeymour.TreeSequence.positive S
                    omega⟩ :
                  Fin (S.length + (1 : ℕ))),
              y5) ∨
          G.ends b0 =
            s(S.vertex
                (⟨(4 : ℕ), by
                    have := GoldbergSeymour.TreeSequence.positive S
                    omega⟩ :
                  Fin (S.length + (1 : ℕ))),
              y5) := by
  classical
  intro V E _ _ _ G k e psi S M hlen y5 b0 q0 hq0ends
  have hcases : q0.val = 0 ∨ q0.val = 1 ∨ q0.val = 2 ∨
      q0.val = 3 ∨ q0.val = 4 := by omega
  rcases hcases with h | h | h | h | h
  · left; simpa [b0, y5, h] using hq0ends
  · right; left; simpa [b0, y5, h] using hq0ends
  · right; right; left; simpa [b0, y5, h] using hq0ends
  · right; right; right; left; simpa [b0, y5, h] using hq0ends
  · right; right; right; right; simpa [b0, y5, h] using hq0ends

private theorem helper_classifyFirst_2342.{u_1, u_2} :
    helperClassifyFirst2342Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N e psi S M hlen g0 hproper y0 y1 y2 y3 y4 b0 b1 hvertex_ne
      missing_excludes h4' h5' hg0' hfirstAttach f1 f2 f3 v1 v2 hf1color hf2color hf3color
      hf1ends' hf2ends' hf3ends' j
  obtain ⟨q, hq⟩ := hfirstAttach j
  let bj : E := S.edge ⟨4 + j.val, by omega⟩
  let z : V := S.vertex ⟨5 + j.val, by omega⟩
  have hbjends : G.ends bj = s(S.vertex ⟨q.val, by omega⟩, z) := by
    simpa [bj, z] using hq
  have hbjcolor : psi bj = some g0 := by
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with hj | hj
    · have : j = (0 : Fin 2) := Fin.ext hj
      subst j
      simpa [bj, b0] using h4'
    · have : j = (1 : Fin 2) := Fin.ext hj
      subst j
      simpa [bj, b1] using h5'
  have hz0 : z ≠ y0 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change 5 + j.val ≠ 0
    omega
  have hz1 : z ≠ y1 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change 5 + j.val ≠ 1
    omega
  have hz2 : z ≠ y2 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change 5 + j.val ≠ 2
    omega
  have hz3 : z ≠ y3 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change 5 + j.val ≠ 3
    omega
  have hz4 : z ≠ y4 := by
    apply hvertex_ne
    apply Fin.ne_of_val_ne
    change 5 + j.val ≠ 4
    omega
  have hq0 : q.val ≠ 0 := by
    intro hqv
    have hinc : Incident G y0 bj := by
      rw [Incident, hbjends]
      have hv : S.vertex ⟨q.val, by omega⟩ = y0 := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y0] using hqv
      rw [hv]
      simp
    exact (missing_excludes hg0' hinc) hbjcolor
  have hbjf3 : bj ≠ f3 := by
    intro hEq
    have hpairs : s(S.vertex ⟨q.val, by omega⟩, z) = s(y2, y3) := by
      rw [← hbjends, hEq, hf3ends']
    rcases Sym2.eq_iff.mp hpairs with hd | hs
    · exact hz3 hd.2
    · exact hz2 hs.2
  have hq2 : q.val ≠ 2 := by
    intro hqv
    have hincb : Incident G y2 bj := by
      rw [Incident, hbjends]
      have hv : S.vertex ⟨q.val, by omega⟩ = y2 := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y2] using hqv
      rw [hv]
      simp
    have hincf : Incident G y2 f3 := by
      rw [Incident, hf3ends']
      simp
    exact (hproper hbjf3 ⟨y2, hincb, hincf⟩ hbjcolor) hf3color
  have hq3 : q.val ≠ 3 := by
    intro hqv
    have hincb : Incident G y3 bj := by
      rw [Incident, hbjends]
      have hv : S.vertex ⟨q.val, by omega⟩ = y3 := by
        apply congrArg S.vertex
        apply Fin.ext
        simpa [y3] using hqv
      rw [hv]
      simp
    have hincf : Incident G y3 f3 := by
      rw [Incident, hf3ends']
      simp
    exact (hproper hbjf3 ⟨y3, hincb, hincf⟩ hbjcolor) hf3color
  have hqcases : q.val = 1 ∨ q.val = 4 := by omega
  rcases hqcases with hq1 | hq4
  · exact @helper_branch_380 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
    assumption) (@g0) (by
    assumption) (@f1) (@f2) (@v1) (@v2) (by
    assumption) (by
    assumption) (@j) (@q) (by
    assumption) (by
    assumption) (by
    assumption) (by
    assumption)
  · exact @helper_branch_409 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
    assumption) (@g0) (by
    assumption) (@f1) (@f2) (@v1) (@v2) (by
    assumption) (by
    assumption) (@j) (@q) (by
    assumption) (by
    assumption) (by
    assumption) (by
    assumption)

private theorem helper_finish_837.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (_ : NormalGlobalMaximumTriple G k e0 phi T),
  ScheideGraphHeight G = (5 : ℕ) →
  let _ : DecidableEq V := Classical.decEq V;
  let Good :
  {e : E} →
  (psi : PartialEdgeColoring E k) →
  (S : TreeSequence G e) →
  NormalGlobalMaximumTriple G k e psi S →
  Prop :=
    fun {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ :
      M.height = (5 : ℕ)) (gamma :
  Fin (2 : ℕ) →
  Fin k),
      Function.Injective gamma ∧
        (
  ∀ (i j : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    G.ends
        (S.edge
          (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ), by omega⟩ :
            Fin S.length)) =
      s(S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))),
        S.vertex
          (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ), by omega⟩ :
            Fin (S.length + (1 : ℕ))))) ∧
          (
  ∀ (i j : Fin (2 : ℕ)),
  psi
      (S.edge
        (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ), by omega⟩ :
          Fin S.length)) =
    some (gamma i)) ∧
            (
  ∀ (i : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    gamma i ∈
      MissingColors G psi
        (S.vertex (⟨(↑q : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ))))) ∧
  ∀ (i : Fin (4 : ℕ)),
  (1 : ℕ) ≤ (↑i : ℕ) →
  ∀ (c : Fin k),
  psi (S.edge (⟨(↑i : ℕ), by omega⟩ : Fin S.length)) = some c →
  ∀ (r : Fin (2 : ℕ)),
  c ≠ gamma r;
  ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
    (M : NormalGlobalMaximumTriple G k e psi S),
  BalancedGlobalMaximumTriple M →
  ∀ (hlen : S.length = (8 : ℕ)),
  M.height = (5 : ℕ) →
  ∀ (g0 : Fin k),
  psi (S.edge (⟨(4 : ℕ), by omega⟩ : Fin S.length)) = some g0 →
  psi (S.edge (⟨(5 : ℕ), by omega⟩ : Fin S.length)) = some g0 →
  g0 ∈ MissingColors G psi (S.vertex (⟨(0 : ℕ), by omega⟩ : Fin (S.length + (1 : ℕ)))) →
  ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e') (M' :
    NormalGlobalMaximumTriple G k e' psi' S'),
  Good psi' S' M' := by
  classical
  intro V E _ _ _ G k e0 phi T N hgraphHeight this Good e psi S M hbal hlen hheight g0 h4 h5 hg0
  have hproper : IsProperEdgeColoring G psi := M.global.1.2.2.2.1
  have horderM := ScheideGlobalMaximumOrder G k e psi S M.global
  have helem : ColoredVertexSetElementary G psi
      (TreeSequenceVertexSet S) := horderM.2.2.2.1
  have hclosed : ColoredVertexSetClosed G psi
      (TreeSequenceVertexSet S) := horderM.2.2.2.2
  let y0 : V := S.vertex ⟨0, by omega⟩
  let y1 : V := S.vertex ⟨1, by omega⟩
  let y2 : V := S.vertex ⟨2, by omega⟩
  let y3 : V := S.vertex ⟨3, by omega⟩
  let y4 : V := S.vertex ⟨4, by omega⟩
  let y5 : V := S.vertex ⟨5, by omega⟩
  let y6 : V := S.vertex ⟨6, by omega⟩
  let y7 : V := S.vertex ⟨7, by omega⟩
  let y8 : V := S.vertex ⟨8, by omega⟩
  let a1 : E := S.edge ⟨1, by omega⟩
  let a2 : E := S.edge ⟨2, by omega⟩
  let a3 : E := S.edge ⟨3, by omega⟩
  let b0 : E := S.edge ⟨4, by omega⟩
  let b1 : E := S.edge ⟨5, by omega⟩
  let c0 : E := S.edge ⟨6, by omega⟩
  let c1 : E := S.edge ⟨7, by omega⟩
  have hvertex_ne {i j : Fin (S.length + 1)} (hij : i ≠ j) :
      S.vertex i ≠ S.vertex j := fun h => hij (S.vertex_injective h)
  have hedge_ne {i j : Fin S.length} (hij : i ≠ j) :
      S.edge i ≠ S.edge j := fun h => hij (S.edge_injective h)
  have hmem (i : Fin (S.length + 1)) :
      S.vertex i ∈ TreeSequenceVertexSet S := by
    simp [TreeSequenceVertexSet]
  have missing_excludes {c : Fin k} {v : V} {f : E}
      (hc : c ∈ MissingColors G psi v) (hinc : Incident G v f) :
      psi f ≠ some c := by
    exact @helper_missing_excludes_2266 (@V) (@E) inferInstance inferInstance (@G) (@k) (@psi)
        (@c) (@v) (@f) (@hc) (@hinc)
  have h4' : psi b0 = some g0 := by simpa [b0] using h4
  have h5' : psi b1 = some g0 := by simpa [b1] using h5
  have hg0' : g0 ∈ MissingColors G psi y0 := by simpa [y0] using hg0
  obtain ⟨p0, hp0⟩ := S.attaches (⟨4, by omega⟩ : Fin S.length)
  have hb0ends : G.ends b0 = s(y5,
      S.vertex (Fin.castLT p0
        (Nat.lt_trans p0.isLt
          (Nat.succ_lt_succ (⟨4, by omega⟩ : Fin S.length).isLt)))) := by
    simpa [b0, y5] using hp0
  obtain ⟨p1, hp1⟩ := S.attaches (⟨5, by omega⟩ : Fin S.length)
  have hb1ends : G.ends b1 = s(y6,
      S.vertex (Fin.castLT p1
        (Nat.lt_trans p1.isLt
          (Nat.succ_lt_succ (⟨5, by omega⟩ : Fin S.length).isLt)))) := by
    simpa [b1, y6] using hp1
  have hp1not5 : p1.val ≠ 5 := by
    exact @helper_hp1not5_194 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
      assumption) (@g0) (by
      assumption) (by
      assumption) (by
      assumption) (by
      assumption) (@p0) (by
      assumption) (@p1) (by
      assumption)
  have hfirstAttach : ∀ j : Fin 2, ∃ q : Fin 5,
      G.ends (S.edge ⟨4 + j.val, by omega⟩) =
        s(S.vertex ⟨q.val, by omega⟩,
          S.vertex ⟨5 + j.val, by omega⟩) := by
    exact @helper_hfirstAttach_212 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (by
      assumption) (@p0) (by
      assumption) (@p1) (by
      assumption) (by
      assumption)
  obtain ⟨q0, hq0ends⟩ := hfirstAttach (0 : Fin 2)
  have hq0cases :
      G.ends b0 = s(S.vertex ⟨0, by omega⟩, y5) ∨
      G.ends b0 = s(S.vertex ⟨1, by omega⟩, y5) ∨
      G.ends b0 = s(S.vertex ⟨2, by omega⟩, y5) ∨
      G.ends b0 = s(S.vertex ⟨3, by omega⟩, y5) ∨
      G.ends b0 = s(S.vertex ⟨4, by omega⟩, y5) := by
    exact @helper_hq0cases_2300 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
        (@e) (@psi) (@S) (@M) (@hlen) (@q0) (@hq0ends)
  have hy5T : y5 ∈ TreeSequenceVertexSet S := by
    simpa [y5] using hmem (⟨5, by omega⟩ : Fin (S.length + 1))
  have hy50 : y5 ≠ y0 := by
    apply hvertex_ne
    norm_num
  have hy51 : y5 ≠ y1 := by
    apply hvertex_ne
    norm_num
  have hy52 : y5 ≠ y2 := by
    apply hvertex_ne
    norm_num
  have hy53 : y5 ≠ y3 := by
    apply hvertex_ne
    norm_num
  have hy54 : y5 ≠ y4 := by
    apply hvertex_ne
    norm_num
  obtain ⟨f1, f2, f3, v1, v2, hf1ends, hf2ends, hf3ends,
      hf1color, hf2color, hf3color, hv1T, hv2T, hv10, hv11, hv12,
      hv13, hv14, hv20, hv21, hv22, hv23, hv24⟩ :=
    ScheideHeightFiveGammaEdges G k e psi S M hheight hgraphHeight g0
      (by simpa [y0] using hg0') b0 y5 h4' hq0cases hy5T
      (by simpa [y0] using hy50) (by simpa [y1] using hy51)
      (by simpa [y2] using hy52) (by simpa [y3] using hy53)
      (by simpa [y4] using hy54)
  have hf1ends' : G.ends f1 = s(y1, v1) := by simpa [y1] using hf1ends
  have hf2ends' : G.ends f2 = s(y4, v2) := by simpa [y4] using hf2ends
  have hf3ends' : G.ends f3 = s(y2, y3) := by simpa [y2, y3] using hf3ends
  have classifyFirst : ∀ j : Fin 2,
      (S.edge ⟨4 + j.val, by omega⟩ = f1 ∧
        S.vertex ⟨5 + j.val, by omega⟩ = v1) ∨
      (S.edge ⟨4 + j.val, by omega⟩ = f2 ∧
        S.vertex ⟨5 + j.val, by omega⟩ = v2) := by
    exact @helper_classifyFirst_2342 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@e) (@psi) (@S) (@M) (@hlen) (@g0) (@hproper) (@hvertex_ne)
        (@missing_excludes) (@h4') (@h5') (@hg0') (@hfirstAttach) (@f1) (@f2) (@f3) (@v1) (@v2)
        (@hf1color) (@hf2color) (@hf3color) (@hf1ends') (@hf2ends') (@hf3ends')
  exact @helper_continuation_995 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hgraphHeight) (@e) (@psi) (@S) (@M) (@hbal) (@hlen) (@hheight)
      (@g0) (@hproper) (@horderM) (@helem) (@hclosed) (@hvertex_ne) (@hedge_ne) (@hmem)
      (@missing_excludes) (@h4') (@h5') (@hg0') (@p0) (@hb0ends) (@p1) (@hb1ends) (@hp1not5)
      (@f1) (@f2) (@f3) (@v1) (@v2) (@hf1ends) (@hf2ends) (@hf1color) (@hf2color) (@hf3color)
      (@hv1T) (@hv2T) (@hv10) (@hv11) (@hv12) (@hv13) (@hv14) (@hv20) (@hv21) (@hv22) (@hv23)
      (@hv24) (@hf1ends') (@hf2ends') (@hf3ends') (@classifyFirst)
private theorem helper_branch_2521.{u_1, u_2} :
    open scoped Classical in
  ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (N : NormalGlobalMaximumTriple G k e0 phi T),
  BalancedGlobalMaximumTriple N →
  N.height = (5 : ℕ) →
  ∀ (hlength : T.length = (8 : ℕ)),
  let r4 : Fin T.length :=
    (⟨(4 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  let r5 : Fin T.length :=
    (⟨(5 : ℕ), by
        have := GoldbergSeymour.TreeSequence.positive T
        omega⟩ :
      Fin T.length);
  ∀ (w0 : Fin ((↑r4 : ℕ) + (1 : ℕ))) (gamma0 : Fin k),
  phi (T.edge r4) = some gamma0 →
  gamma0 ∈
      MissingColors G phi
        (T.vertex
          (w0.castLT
            (by
              have := GoldbergSeymour.TreeSequence.positive T
              omega))) →
  phi (T.edge r5) = some gamma0 →
  let Good :
  {e : E} →
  (psi : PartialEdgeColoring E k) →
  (S : TreeSequence G e) →
  NormalGlobalMaximumTriple G k e psi S →
  Prop :=
    fun {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S) ↦
    ∃ (_ : BalancedGlobalMaximumTriple M) (x : S.length = (8 : ℕ)) (_ :
      M.height = (5 : ℕ)) (gamma :
  Fin (2 : ℕ) →
  Fin k),
      Function.Injective gamma ∧
        (
  ∀ (i j : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    G.ends
        (S.edge
          (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      s(S.vertex
          (⟨(↑q : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))),
        S.vertex
          (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))))) ∧
          (
  ∀ (i j : Fin (2 : ℕ)),
  psi
      (S.edge
        (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
            by
            have := GoldbergSeymour.TreeSequence.positive S
            omega⟩ :
          Fin S.length)) =
    some (gamma i)) ∧
            (
  ∀ (i : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    gamma i ∈
      MissingColors G psi
        (S.vertex
          (⟨(↑q : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))))) ∧
  ∀ (i : Fin (4 : ℕ)),
  (1 : ℕ) ≤ (↑i : ℕ) →
  ∀ (c : Fin k),
  psi
        (S.edge
          (⟨(↑i : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      some c →
  ∀ (r : Fin (2 : ℕ)),
  c ≠ gamma r;
  (
  ∀ {e : E} (psi : PartialEdgeColoring E k) (S : TreeSequence G e)
     (M : NormalGlobalMaximumTriple G k e psi S),
  BalancedGlobalMaximumTriple M →
  ∀ (hlen : S.length = (8 : ℕ)),
  M.height = (5 : ℕ) →
  ∀ (g0 : Fin k),
  psi
        (S.edge
          (⟨(4 : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      some g0 →
  psi
        (S.edge
          (⟨(5 : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      some g0 →
  g0 ∈
      MissingColors G psi
        (S.vertex
          (⟨(0 : ℕ), Nat.zero_lt_succ S.length⟩ :
            Fin (S.length + (1 : ℕ)))) →
  ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e')
    (M' : NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M') →
  (↑w0 : ℕ) = (0 : ℕ) →
  ∃ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1) (M :
    NormalGlobalMaximumTriple G k e1 psi S) (_ : BalancedGlobalMaximumTriple M) (x :
    S.length = (8 : ℕ)) (_ : M.height = (5 : ℕ)) (gamma :
  Fin (2 : ℕ) →
  Fin k),
  Function.Injective gamma ∧
  (
  ∀ (i j : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    G.ends
        (S.edge
          (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      s(S.vertex
          (⟨(↑q : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))),
        S.vertex
          (⟨(5 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
              by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))))) ∧
  (
  ∀ (i j : Fin (2 : ℕ)),
  psi
      (S.edge
        (⟨(4 : ℕ) + (2 : ℕ) * (↑i : ℕ) + (↑j : ℕ),
            by
            have := GoldbergSeymour.TreeSequence.positive S
            omega⟩ :
          Fin S.length)) =
    some (gamma i)) ∧
  (
  ∀ (i : Fin (2 : ℕ)),
  ∃ (q : Fin (5 : ℕ)),
    gamma i ∈
      MissingColors G psi
        (S.vertex
          (⟨(↑q : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin (S.length + (1 : ℕ))))) ∧
  ∀ (i : Fin (4 : ℕ)),
  (1 : ℕ) ≤ (↑i : ℕ) →
  ∀ (c : Fin k),
  psi
        (S.edge
          (⟨(↑i : ℕ), by
              have := GoldbergSeymour.TreeSequence.positive S
              omega⟩ :
            Fin S.length)) =
      some c →
  ∀ (r : Fin (2 : ℕ)),
  c ≠ gamma r := by
  classical
  intro V E _ _ _ G k e0 phi T N hbalanced hNheight hlength r4 r5 w0 gamma0 hr4color hw0missing
      hr5color Good finish hw0zero
  have hw0vertex :
      T.vertex (Fin.castLT w0
        (Nat.lt_trans w0.isLt (Nat.succ_lt_succ r4.isLt))) =
        T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    apply congrArg T.vertex
    apply Fin.ext
    simpa using hw0zero
  exact finish phi T N hbalanced hlength hNheight gamma0
    (by simpa [r4] using hr4color)
    (by simpa [r5] using hr5color)
    (by simpa [hw0vertex] using hw0missing)

private theorem helper_branch_4561.{u_1, u_2} :
    helperBranch4561Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hbalanced this hNheight hlength r4 r5 w0 gamma0 hr4color
      hw0missing hr5color Good finish hw0zero
  let j : Fin N.height := ⟨w0.val, by
      have hw : w0.val < 5 := by simp [r4]
      rw [hNheight]
      exact hw⟩
  have hj : 1 ≤ j.val := by
    simp [j]
    omega
  obtain ⟨psi, A, B, hAB, hA, hB, hproper, hone, hmissA, hmissB,
      hshift, hfixed, htailColor⟩ :=
    ScheideTrunkRotationColoring G k e0 phi T N hbalanced j hj
  obtain ⟨S, hglobalS, hlengthS, hverticesS, htrunkVerticesS,
      htailVerticesS, htrunkEdgesS, htailEdgesS⟩ :=
    ScheideTrunkRotationTree G k e0 phi psi T N hbalanced j hj A B
      hAB hA hB hproper hone hmissA hmissB hshift hfixed
  obtain ⟨M, hheightM, halphaM, hbetaM, pred, hpred, hclosingM⟩ :=
    ScheideTrunkRotationNormal G k e0 phi psi T N hbalanced j hj A B
      hAB hA hB hshift hfixed S hglobalS hmissA hmissB hlengthS
      htrunkVerticesS htrunkEdgesS
  have hbalM : BalancedGlobalMaximumTriple M := by
    constructor
    · rw [hheightM]
      exact hbalanced.1
    · intro q hlow hupp
      have hlow' : N.height < 2 * q := by
        rw [hheightM] at hlow
        exact hlow
      have hupp' : 2 * q < T.length + 1 := by
        rw [hlengthS] at hupp
        exact hupp
      have hqbound : 6 ≤ 2 * q := by
        rw [hNheight] at hlow'
        omega
      let s4 : Fin S.length := ⟨2 * q - 2, by omega⟩
      let s5 : Fin S.length := ⟨2 * q - 1, by omega⟩
      obtain ⟨t4, ht4val, ht4edge⟩ := htailEdgesS s4 (by
        dsimp [s4]
        omega)
      obtain ⟨t5, ht5val, ht5edge⟩ := htailEdgesS s5 (by
        dsimp [s5]
        omega)
      have ht4 : t4 = (⟨2 * q - 2, by omega⟩ : Fin T.length) := by
        apply Fin.ext
        simpa [s4] using ht4val
      have ht5 : t5 = (⟨2 * q - 1, by omega⟩ : Fin T.length) := by
        apply Fin.ext
        simpa [s5] using ht5val
      change psi (S.edge s4) = psi (S.edge s5)
      calc
        psi (S.edge s4) = psi (T.edge t4) := congrArg psi ht4edge
        _ = phi (T.edge t4) := htailColor t4 (by
          rw [ht4, hNheight]
          change 4 ≤ 2 * q - 2
          omega)
        _ = phi (T.edge t5) := by
          rw [ht4, ht5]
          exact hbalanced.2 q hlow' hupp'
        _ = psi (T.edge t5) := (htailColor t5 (by
          rw [ht5, hNheight]
          change 4 ≤ 2 * q - 1
          omega)).symm
        _ = psi (S.edge s5) := congrArg psi ht5edge.symm
  have hnewZero : S.vertex ⟨0, Nat.zero_lt_succ S.length⟩ =
      T.vertex (Fin.castLE N.height_upper j) := by
    obtain ⟨i, hi, hv⟩ := htrunkVerticesS
      (⟨0, Nat.zero_lt_succ S.length⟩ : Fin (S.length + 1))
      (by simp [hNheight])
    have hij : i = j := by
      apply Fin.ext
      simpa [j, Nat.mod_eq_of_lt j.isLt] using hi
    simpa [hij] using hv
  have holdMissing : gamma0 ∈ MissingColors G phi
      (T.vertex (Fin.castLE N.height_upper j)) := by
    have hidx : Fin.castLT w0
        (Nat.lt_trans w0.isLt (Nat.succ_lt_succ r4.isLt)) =
        Fin.castLE N.height_upper j := by
      apply Fin.ext
      rfl
    simpa [hidx] using hw0missing
  have horderData := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have helem : ColoredVertexSetElementary G phi
      (TreeSequenceVertexSet T) := horderData.2.2.2.1
  have hgammaAlpha : gamma0 ≠ N.alpha := by
    intro hga
    have hzeroMem : T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ∈
        TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
    have hjMem : T.vertex (Fin.castLE N.height_upper j) ∈
        TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
    have hne : T.vertex (Fin.castLE N.height_upper j) ≠
        T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
      intro hv
      have hi := T.vertex_injective hv
      have hiv := congrArg Fin.val hi
      have hz : j.val = 0 := by simpa using hiv
      exact (Nat.ne_of_gt hj) hz
    have hd := helem hjMem hzeroMem hne
    exact (Finset.disjoint_left.mp hd) holdMissing
      (by simpa [hga] using N.alpha_missing)
  have hgammaNew : gamma0 ∈ MissingColors G psi
      (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩) := by
    rw [hnewZero]
    by_cases hgb : gamma0 = N.beta
    · have hjone : j.val = 1 := by
        by_contra hne
        have honeMem : T.vertex ⟨1, by omega⟩ ∈
            TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        have hjMem : T.vertex (Fin.castLE N.height_upper j) ∈
            TreeSequenceVertexSet T := by simp [TreeSequenceVertexSet]
        have hvne : T.vertex (Fin.castLE N.height_upper j) ≠
            T.vertex ⟨1, by omega⟩ := by
          intro hv
          have hi := T.vertex_injective hv
          exact hne (by simpa using congrArg Fin.val hi)
        have hd := helem hjMem honeMem hvne
        exact (Finset.disjoint_left.mp hd) holdMissing
          (by simpa [hgb] using N.beta_missing)
      have hjodd : Odd j.val := by
        rw [hjone]
        exact odd_one
      have hAeq : A = gamma0 := by simpa [hgb, hjodd] using hA
      simpa [hAeq] using hmissA
    · have hgammaBeta : gamma0 ≠ N.beta := hgb
      rw [MissingColors, Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hpresent
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
        true_and] at hpresent
      obtain ⟨f, hfinc, hfcolor⟩ := hpresent
      by_cases haffected : ∃ i : Fin (j.val + 1),
          f = NormalCycleEdge N
            (Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i)
      · obtain ⟨i, rfl⟩ := haffected
        by_cases hilast : i.val = j.val
        · have hieq : Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i = j := by
            apply Fin.ext
            simpa using hilast
          have hu := hone.1
          rw [hieq] at hfcolor
          rw [hfcolor] at hu
          simp at hu
        · let t : Fin j.val := ⟨i.val, by omega⟩
          have hcast : Fin.castLE (Nat.le_of_lt j.isLt) t =
              Fin.castLE (Nat.succ_le_iff.mpr j.isLt) i := by
            apply Fin.ext
            rfl
          have hs := hshift t
          rw [hcast, hfcolor] at hs
          have hcycle :=
            (ScheideTrunkRotationCycle G k e0 phi T N hbalanced).2.2.2.2
              (⟨t.val + 1, by
                have htj := t.isLt
                have hjN := j.isLt
                omega⟩ : Fin N.height) (Nat.succ_le_succ (Nat.zero_le _))
          by_cases ho : Odd (t.val + 1)
          · rw [ite_eq_left ho] at hcycle
            have : gamma0 = N.alpha := Option.some.inj (hs.trans hcycle)
            exact hgammaAlpha this
          · rw [ite_eq_right ho] at hcycle
            have : gamma0 = N.beta := Option.some.inj (hs.trans hcycle)
            exact hgammaBeta this
      · have hfix := hfixed f (by
          intro i hi
          exact haffected ⟨i, hi⟩)
        have holdColor : phi f = some gamma0 := hfix.symm.trans hfcolor
        have hnotPresent : gamma0 ∉ PresentColors G phi
            (T.vertex (Fin.castLE N.height_upper j)) := by
          simpa [MissingColors] using holdMissing
        exact hnotPresent (by
          simp only [PresentColors, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨f, hfinc, holdColor⟩)
  have hS4 : psi (S.edge ⟨4, by omega⟩) = some gamma0 := by
    obtain ⟨t, htval, htedge⟩ := htailEdgesS
      (⟨4, by omega⟩ : Fin S.length) (by simp [hNheight])
    have ht : t = r4 := by
      apply Fin.ext
      simpa [r4] using htval
    calc
      psi (S.edge ⟨4, by omega⟩) = psi (T.edge t) := congrArg psi htedge
      _ = psi (T.edge r4) := congrArg (fun f => psi (T.edge f)) ht
      _ = phi (T.edge r4) := htailColor r4 (by simp [hNheight, r4])
      _ = some gamma0 := hr4color
  have hS5 : psi (S.edge ⟨5, by omega⟩) = some gamma0 := by
    obtain ⟨t, htval, htedge⟩ := htailEdgesS
      (⟨5, by omega⟩ : Fin S.length) (by simp [hNheight])
    have ht : t = r5 := by
      apply Fin.ext
      simpa [r5] using htval
    calc
      psi (S.edge ⟨5, by omega⟩) = psi (T.edge t) := congrArg psi htedge
      _ = psi (T.edge r5) := congrArg (fun f => psi (T.edge f)) ht
      _ = phi (T.edge r5) := htailColor r5 (by simp [hNheight, r5])
      _ = some gamma0 := hr5color
  exact finish psi S M hbalM
    (hlengthS.trans hlength) (hheightM.trans hNheight) gamma0 hS4 hS5
    hgammaNew

theorem ScheideOrderNineBlockStructure {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N)
    (horder : TashkinovOrder G = 9)
    (hgraphHeight : ScheideGraphHeight G = 5) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k) (S : TreeSequence G e1)
      (M : NormalGlobalMaximumTriple G k e1 psi S),
      ∃ (_ : BalancedGlobalMaximumTriple M) (_ : S.length = 8)
        (_ : M.height = 5) (gamma :
  Fin 2 →
  Fin k),
      Function.Injective gamma ∧
      (
  ∀ (i : Fin 2) (j : Fin 2),
  ∃ q : Fin 5,
    G.ends (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
      s(S.vertex ⟨q.val, by omega⟩,
        S.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (
  ∀ (i : Fin 2) (j : Fin 2),
  psi (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
    some (gamma i)) ∧
      (
  ∀ i : Fin 2,
  ∃ q : Fin 5,
    gamma i ∈ MissingColors G psi (S.vertex ⟨q.val, by omega⟩)) ∧
      (
  ∀ i : Fin 4,
  1 ≤ i.val →
  ∀ c : Fin k,
  psi (S.edge ⟨i.val, by omega⟩) = some c →
  ∀ r : Fin 2,
  c ≠ gamma r) := by
  classical
  let : DecidableEq V := Classical.decEq V
  have hNheight : N.height = 5 := hbalanced.1.trans hgraphHeight
  have hvertexCard : (TreeSequenceVertexSet T).card = T.length + 1 := by
    simp [TreeSequenceVertexSet, Finset.card_image_of_injective,
      T.vertex_injective]
  have hlength : T.length = 8 := by
    have hcard := N.global.2.2
    rw [horder] at hcard
    omega
  let r4 : Fin T.length := ⟨4, by omega⟩
  let r5 : Fin T.length := ⟨5, by omega⟩
  let r6 : Fin T.length := ⟨6, by omega⟩
  let r7 : Fin T.length := ⟨7, by omega⟩
  obtain ⟨w0, gamma0, hr4color, hw0missing⟩ :=
    N.global.2.1 r4 (by simp [r4])
  have hr5color : phi (T.edge r5) = some gamma0 := by
    have hp := hbalanced.2 3 (by omega) (by omega)
    simpa [r4, r5] using hp.symm.trans hr4color
  obtain ⟨w1, gamma1, hr6color, hw1missing⟩ :=
    N.global.2.1 r6 (by simp [r6])
  have hr7color : phi (T.edge r7) = some gamma1 := by
    have hp := hbalanced.2 4 (by omega) (by omega)
    simpa [r6, r7] using hp.symm.trans hr6color
  let Good {e : E} (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S) : Prop :=
    ∃ (_ : BalancedGlobalMaximumTriple M) (_ : S.length = 8)
      (_ : M.height = 5) (gamma : Fin 2 → Fin k),
      Function.Injective gamma ∧
      (∀ (i : Fin 2) (j : Fin 2),
        ∃ q : Fin 5,
          G.ends (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
            s(S.vertex ⟨q.val, by omega⟩,
              S.vertex ⟨5 + 2 * i.val + j.val, by omega⟩)) ∧
      (∀ (i : Fin 2) (j : Fin 2),
        psi (S.edge ⟨4 + 2 * i.val + j.val, by omega⟩) =
          some (gamma i)) ∧
      (∀ i : Fin 2, ∃ q : Fin 5,
        gamma i ∈ MissingColors G psi (S.vertex ⟨q.val, by omega⟩)) ∧
      (∀ i : Fin 4, 1 ≤ i.val →
        ∀ c : Fin k, psi (S.edge ⟨i.val, by omega⟩) = some c →
          ∀ r : Fin 2, c ≠ gamma r)
  have finish {e : E} (psi : PartialEdgeColoring E k)
      (S : TreeSequence G e)
      (M : NormalGlobalMaximumTriple G k e psi S)
      (hbal : BalancedGlobalMaximumTriple M)
      (hlen : S.length = 8) (hheight : M.height = 5)
      (g0 : Fin k)
      (h4 : psi (S.edge ⟨4, by omega⟩) = some g0)
      (h5 : psi (S.edge ⟨5, by omega⟩) = some g0)
      (hg0 : g0 ∈ MissingColors G psi
        (S.vertex ⟨0, Nat.zero_lt_succ S.length⟩)) :
      ∃ (e' : E) (psi' : PartialEdgeColoring E k) (S' : TreeSequence G e')
        (M' : NormalGlobalMaximumTriple G k e' psi' S'), Good psi' S' M' := by
    exact @helper_finish_837 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
        (@phi) (@T) (@N) (by
      assumption) (@e) (@psi) (@S) (@M) (by
      assumption) (by
      assumption) (by
      assumption) (@g0) (by
      assumption) (by
      assumption) (by
      assumption)
  by_cases hw0zero : w0.val = 0
  · exact @helper_branch_2521 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hbalanced) (@hNheight) (@hlength) (@w0) (@gamma0) (@hr4color)
      (@hw0missing) (@hr5color) (@finish) (@hw0zero)
  · exact @helper_branch_4561 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hbalanced) (@hNheight) (@hlength) (@w0) (@gamma0) (@hr4color)
      (@hw0missing) (@hr5color) (@finish) (@hw0zero)
end GoldbergSeymour

end
