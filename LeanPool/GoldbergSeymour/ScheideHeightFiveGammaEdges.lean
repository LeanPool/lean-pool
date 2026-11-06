/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.SharedFacts.ScheideHeightFiveGammaEdges

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideKempePathHeightBound

/-!
# Scheide Height Five Gamma Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private abbrev helperContinuation2789Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (g : E) (v : V) (hgcolor : phi g = some gamma) (hgends : G.ends g = s(T.vertex
        (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(1 : ℕ),
    by
           first
           | omega
           | (
             have := GoldbergSeymour.TreeSequence.positive T
             have := GoldbergSeymour.TreeSequence.positive T
             have := N.height_upper
             all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(2 : ℕ),
    by
            first
            | omega
            | (
              have := GoldbergSeymour.TreeSequence.positive T
              have := GoldbergSeymour.TreeSequence.positive T
              have := N.height_upper
              all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(3 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := GoldbergSeymour.TreeSequence.positive T
               have := N.height_upper
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(4 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := GoldbergSeymour.TreeSequence.positive T
               have := N.height_upper
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v)) (x : v ∈ TreeSequenceVertexSet T) (hv1 : v ≠ T.vertex (⟨(1
        : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive T
          have := N.height_upper
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv2 : v ≠ T.vertex (⟨(2 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive T
          have := N.height_upper
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv3 : v ≠ T.vertex (⟨(3 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive T
          have := N.height_upper
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv4 : v ≠ T.vertex (⟨(4 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := GoldbergSeymour.TreeSequence.positive T
          have := N.height_upper
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (hgamma0 : gamma ∈ MissingColors G phi y0) (f1 : E) (hf1inc : Incident G y1 f1) (hf1color :
        phi f1 = some gamma) (f2 : E) (hf2inc : Incident G y2 f2) (hf2color : phi f2 = some gamma)
        (f3 : E) (hf3inc : Incident G y3 f3) (hf3color : phi f3 = some gamma) (f4 : E) (hf4inc :
        Incident G y4 f4) (hf4color : phi f4 = some gamma) (z1 : V) (hf1ends : G.ends f1 = s(y1,
        z1)) (z2 : V) (hf2ends : G.ends f2 = s(y2, z2)) (z3 : V) (hf3ends : G.ends f3 = s(y3, z3))
        (z4 : V) (hf4ends : G.ends f4 = s(y4, z4)) (hz2trunk : z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 =
        y3 ∨ z2 = y4) (hz3trunk : z3 = y0 ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4) (hz1T : z1 ∈
        TreeSequenceVertexSet T) (hz4T : z4 ∈ TreeSequenceVertexSet T) (hy12 : y1 ≠ y2) (hy13 : y1
        ≠ y3) (hy14 : y1 ≠ y4) (hy23 : y2 ≠ y3) (hy24 : y2 ≠ y4) (hy34 : y3 ≠ y4),
    ∃ (f1 : E) (f2 : E) (f3 : E) (v1 : V) (v2 : V), G.ends f1 = s(T.vertex (⟨(1 : ℕ),
    by
           first
           | omega
           | (
             have := GoldbergSeymour.TreeSequence.positive T
             have := GoldbergSeymour.TreeSequence.positive T
             have := N.height_upper
             all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v1) ∧ G.ends f2 = s(T.vertex (⟨(4 : ℕ),
    by
            first
            | omega
            | (
              have := GoldbergSeymour.TreeSequence.positive T
              have := GoldbergSeymour.TreeSequence.positive T
              have := N.height_upper
              all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v2) ∧ G.ends f3 = s(T.vertex (⟨(2 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := GoldbergSeymour.TreeSequence.positive T
               have := N.height_upper
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), T.vertex (⟨(3 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := GoldbergSeymour.TreeSequence.positive T
               have := N.height_upper
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ phi f1 = some gamma ∧ phi f2 = some gamma ∧ phi f3 = some
        gamma ∧ v1 ∈ TreeSequenceVertexSet T ∧ v2 ∈ TreeSequenceVertexSet T ∧ v1 ≠ T.vertex (⟨(0 :
        ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(1 : ℕ),
    by
                   first
                   | omega
                   | (
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := N.height_upper
                     all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(2 : ℕ),
    by
                    first
                    | omega
                    | (
                      have := GoldbergSeymour.TreeSequence.positive T
                      have := GoldbergSeymour.TreeSequence.positive T
                      have := N.height_upper
                      all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(3 : ℕ),
    by
                     first
                     | omega
                     | (
                       have := GoldbergSeymour.TreeSequence.positive T
                       have := GoldbergSeymour.TreeSequence.positive T
                       have := N.height_upper
                       all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(4 : ℕ),
    by
                      first
                      | omega
                      | (
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := N.height_upper
                        all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(1 : ℕ),
    by
                        first
                        | omega
                        | (
                          have := GoldbergSeymour.TreeSequence.positive T
                          have := GoldbergSeymour.TreeSequence.positive T
                          have := N.height_upper
                          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(2 : ℕ),
    by
                         first
                         | omega
                         | (
                           have := GoldbergSeymour.TreeSequence.positive T
                           have := GoldbergSeymour.TreeSequence.positive T
                           have := N.height_upper
                           all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(3 : ℕ),
    by
                          first
                          | omega
                          | (
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := N.height_upper
                            all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(4 : ℕ),
    by
                          first
                          | omega
                          | (
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := N.height_upper
                            all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))

private abbrev helperContinuation3161Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (g : E) (v : V) (hgcolor : phi g = some gamma) (hgends : G.ends g = s(T.vertex
        (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(1 : ℕ),
    by
           first
           | omega
           | (
             have := GoldbergSeymour.TreeSequence.positive T
             have := NormalGlobalMaximumTriple.height_upper N
             have := GoldbergSeymour.TreeSequence.positive T
             all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(2 : ℕ),
    by
            first
            | omega
            | (
              have := GoldbergSeymour.TreeSequence.positive T
              have := NormalGlobalMaximumTriple.height_upper N
              have := GoldbergSeymour.TreeSequence.positive T
              all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(3 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(4 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v)) (x : v ∈ TreeSequenceVertexSet T) (hv1 : v ≠ T.vertex (⟨(1
        : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv2 : v ≠ T.vertex (⟨(2 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv3 : v ≠ T.vertex (⟨(3 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv4 : v ≠ T.vertex (⟨(4 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T)) (hy0T : y0 ∈
        TreeSequenceVertexSet T) (hy1T : y1 ∈ TreeSequenceVertexSet T) (hy4T : y4 ∈
        TreeSequenceVertexSet T) (hgamma0 : gamma ∈ MissingColors G phi y0) (f1 : E) (hf1inc :
        Incident G y1 f1) (hf1color : phi f1 = some gamma) (f2 : E) (hf2inc : Incident G y2 f2)
        (hf2color : phi f2 = some gamma) (f3 : E) (hf3inc : Incident G y3 f3) (hf3color : phi f3 =
        some gamma) (f4 : E) (hf4inc : Incident G y4 f4) (hf4color : phi f4 = some gamma) (z1 : V)
        (hf1ends : G.ends f1 = s(y1, z1)) (z2 : V) (hf2ends : G.ends f2 = s(y2, z2)) (z3 : V)
        (hf3ends : G.ends f3 = s(y3, z3)) (z4 : V) (hf4ends : G.ends f4 = s(y4, z4))
        (middle_no_escape :
    ∀ (r : E) (w : V) (hrcolor : phi r = some gamma) (hrends : G.ends r = s(T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w) ∨ G.ends r = s(T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w)), w = T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))),
    ∃ (f1 : E) (f2 : E) (f3 : E) (v1 : V) (v2 : V), G.ends f1 = s(T.vertex (⟨(1 : ℕ),
    by
           first
           | omega
           | (
             have := GoldbergSeymour.TreeSequence.positive T
             have := NormalGlobalMaximumTriple.height_upper N
             have := GoldbergSeymour.TreeSequence.positive T
             all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v1) ∧ G.ends f2 = s(T.vertex (⟨(4 : ℕ),
    by
            first
            | omega
            | (
              have := GoldbergSeymour.TreeSequence.positive T
              have := NormalGlobalMaximumTriple.height_upper N
              have := GoldbergSeymour.TreeSequence.positive T
              all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v2) ∧ G.ends f3 = s(T.vertex (⟨(2 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), T.vertex (⟨(3 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) ∧ phi f1 = some gamma ∧ phi f2 = some gamma ∧ phi f3 = some
        gamma ∧ v1 ∈ TreeSequenceVertexSet T ∧ v2 ∈ TreeSequenceVertexSet T ∧ v1 ≠ T.vertex (⟨(0 :
        ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(1 : ℕ),
    by
                   first
                   | omega
                   | (
                     have := GoldbergSeymour.TreeSequence.positive T
                     have := NormalGlobalMaximumTriple.height_upper N
                     have := GoldbergSeymour.TreeSequence.positive T
                     all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(2 : ℕ),
    by
                    first
                    | omega
                    | (
                      have := GoldbergSeymour.TreeSequence.positive T
                      have := NormalGlobalMaximumTriple.height_upper N
                      have := GoldbergSeymour.TreeSequence.positive T
                      all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(3 : ℕ),
    by
                     first
                     | omega
                     | (
                       have := GoldbergSeymour.TreeSequence.positive T
                       have := NormalGlobalMaximumTriple.height_upper N
                       have := GoldbergSeymour.TreeSequence.positive T
                       all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v1 ≠ T.vertex (⟨(4 : ℕ),
    by
                      first
                      | omega
                      | (
                        have := GoldbergSeymour.TreeSequence.positive T
                        have := NormalGlobalMaximumTriple.height_upper N
                        have := GoldbergSeymour.TreeSequence.positive T
                        all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(1 : ℕ),
    by
                        first
                        | omega
                        | (
                          have := GoldbergSeymour.TreeSequence.positive T
                          have := NormalGlobalMaximumTriple.height_upper N
                          have := GoldbergSeymour.TreeSequence.positive T
                          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(2 : ℕ),
    by
                         first
                         | omega
                         | (
                           have := GoldbergSeymour.TreeSequence.positive T
                           have := NormalGlobalMaximumTriple.height_upper N
                           have := GoldbergSeymour.TreeSequence.positive T
                           all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(3 : ℕ),
    by
                          first
                          | omega
                          | (
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := NormalGlobalMaximumTriple.height_upper N
                            have := GoldbergSeymour.TreeSequence.positive T
                            all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))) ∧ v2 ≠ T.vertex (⟨(4 : ℕ),
    by
                          first
                          | omega
                          | (
                            have := GoldbergSeymour.TreeSequence.positive T
                            have := NormalGlobalMaximumTriple.height_upper N
                            have := GoldbergSeymour.TreeSequence.positive T
                            all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))

private abbrev helperCaseContinuation3625Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ))
        (hGheight : ScheideGraphHeight G = (5 : ℕ)) (gamma : Fin k) (v : V) (x : v ∈
        TreeSequenceVertexSet T) (r : E) (w : V) (hrcolor : phi r = some gamma),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge;
    ∀ (hy01 : y0 ≠ y1) (hy02 : y0 ≠ y2) (hy03 : y0 ≠ y3) (hy04 : y0 ≠ y4) (hy12 : y1 ≠ y2) (hy13 :
        y1 ≠ y3) (hy14 : y1 ≠ y4) (hy23 : y2 ≠ y3) (hy24 : y2 ≠ y4) (hy34 : y3 ≠ y4) (ha1ends :
        G.ends a1 = s(y1, y2)) (ha3ends : G.ends a3 = s(y3, y4)) (hproper : IsProperEdgeColoring G
        phi) (ha1color : phi a1 = some N.alpha) (ha3color : phi a3 = some N.alpha) (hqcolor : phi
        q = some N.beta) (halpha_beta : N.alpha ≠ N.beta) (p1 : (TwoColorIncidenceGraph G phi
        gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin
        (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin
        (T.length + (1 : ℕ)))))),
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0);
    ∀ (hqinc0 : Incident G y0 q) (hqinc4 : Incident G y4 q) (hqC1 : Sum.inr q ∈ C1) (hy1C1 :
        Sum.inl y1 ∈ C1) (hqa1 : q ≠ a1) (hqa3 : q ≠ a3) (ha13ne : a1 ≠ a3) (hgamma_alpha : gamma
        ≠ N.alpha) (hgamma_beta : gamma ≠ N.beta) (hw0 : w ≠ y0) (hw1 : w ≠ y1) (hw2 : w ≠ y2)
        (hw3 : w ≠ y3) (hw4 : w ≠ y4) (hrincw : Incident G w r) (hrmiddle : Incident G y2 r ∨
        Incident G y3 r) (hrq : r ≠ q) (hrnotC1 : Sum.inr r ∉ C1),
    let i0 : Fin (T.length + (1 : ℕ)) := (⟨(0 : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let i1 : Fin (T.length + (1 : ℕ)) := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (pmax : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex i0)) (Sum.inl
        (T.vertex i1))) (hchangedata : IsProperEdgeColoring G (TwoColorComponentSwap G phi gamma
        N.beta (Sum.inl (T.vertex i0))) ∧ IsOneEdgeUncolored (TwoColorComponentSwap G phi gamma
        N.beta (Sum.inl (T.vertex i0))) e0 ∧ TashkinovTree G e0 (TwoColorComponentSwap G phi gamma
        N.beta (Sum.inl (T.vertex i0))) T),
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma N.beta (Sum.inl y0);
    ∀ (hproper' : IsProperEdgeColoring G phi') (hone' : IsOneEdgeUncolored phi' e0), False

private abbrev helperCaseContinuation3777Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ))
        (hGheight : ScheideGraphHeight G = (5 : ℕ)) (gamma : Fin k) (hgamma : gamma ∈
        MissingColors G phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 :
        ℕ))))) (g : E) (v : V) (hgcolor : phi g = some gamma) (x : v ∈ TreeSequenceVertexSet T) (r
        : E) (w : V) (hrcolor : phi r = some gamma) (hrends : G.ends r = s(T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w) ∨ G.ends r = s(T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge;
    ∀ (hy01 : y0 ≠ y1) (hy02 : y0 ≠ y2) (hy03 : y0 ≠ y3) (hy04 : y0 ≠ y4) (hy12 : y1 ≠ y2) (hy13 :
        y1 ≠ y3) (hy14 : y1 ≠ y4) (hy23 : y2 ≠ y3) (hy24 : y2 ≠ y4) (hy34 : y3 ≠ y4) (ha1ends :
        G.ends a1 = s(y1, y2)) (ha2ends : G.ends a2 = s(y2, y3)) (ha3ends : G.ends a3 = s(y3, y4))
        (hqends : G.ends q = s(y4, y0)) (hproper : IsProperEdgeColoring G phi) (missing_excludes :
    ∀ {c : Fin k} {x : V} {f : E} (hc : c ∈ MissingColors G phi x) (hinc : Incident G x f), phi f
        ≠ some c) (ha1color : phi a1 = some N.alpha) (ha12ne : a1 ≠ a2) (ha2color : phi a2 = some
        N.beta) (ha23ne : a2 ≠ a3) (ha3color : phi a3 = some N.alpha) (ha3qne : a3 ≠ q) (hqcolor :
        phi q = some N.beta) (halpha_beta : N.alpha ≠ N.beta) (hv0' : v ≠ y0) (hv1' : v ≠ y1)
        (hv2' : v ≠ y2) (hv3' : v ≠ y3) (hv4' : v ≠ y4) (hgends' : G.ends g = s(y0, v) ∨ G.ends g
        = s(y1, v) ∨ G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨ G.ends g = s(y4, v)) (p1 :
        (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (hp1 : p1.IsPath) (hp1div : (4
        : ℕ) ∣ p1.length) (hp1bound : p1.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G),
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0);
    ∀ (hC1root : Sum.inl y0 ∈ C1) (support_of_C1 :
    ∀ {z : V ⊕ E} (hz : z ∈ C1), z ∈ p1.support) (edge_step_C1 :
    ∀ {x : V} {f : E} (hx : Sum.inl x ∈ C1) (hxf : Incident G x f) (hfc : phi f = some gamma ∨ phi
        f = some N.beta), Sum.inr f ∈ C1) (vertex_step_C1 :
    ∀ {f : E} {x : V} (hf : Sum.inr f ∈ C1) (hxf : Incident G x f) (hfc : phi f = some gamma ∨ phi
        f = some N.beta), Sum.inl x ∈ C1) (hqinc0 : Incident G y0 q) (hqinc4 : Incident G y4 q)
        (hqC1 : Sum.inr q ∈ C1) (hy4C1 : Sum.inl y4 ∈ C1) (hy1C1 : Sum.inl y1 ∈ C1) (helem :
        ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) (hy0T : y0 ∈
        TreeSequenceVertexSet T) (hy1T : y1 ∈ TreeSequenceVertexSet T), w = T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))

private abbrev helperCaseContinuation4022Conditions.{u_1, u_2} : Prop :=
 open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ))
        (hGheight : ScheideGraphHeight G = (5 : ℕ)) (gamma : Fin k) (hgamma : gamma ∈
        MissingColors G phi (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 :
        ℕ))))) (g : E) (v : V) (hgcolor : phi g = some gamma) (hgends : G.ends g = s(T.vertex (⟨(0
        : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(1 : ℕ),
    by
           first
           | omega
           | (
             have := GoldbergSeymour.TreeSequence.positive T
             have := NormalGlobalMaximumTriple.height_upper N
             have := GoldbergSeymour.TreeSequence.positive T
             all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(2 : ℕ),
    by
            first
            | omega
            | (
              have := GoldbergSeymour.TreeSequence.positive T
              have := NormalGlobalMaximumTriple.height_upper N
              have := GoldbergSeymour.TreeSequence.positive T
              all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(3 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v) ∨ G.ends g = s(T.vertex (⟨(4 : ℕ),
    by
             first
             | omega
             | (
               have := GoldbergSeymour.TreeSequence.positive T
               have := NormalGlobalMaximumTriple.height_upper N
               have := GoldbergSeymour.TreeSequence.positive T
               all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ))), v)) (x : v ∈ TreeSequenceVertexSet T) (hv0 : v ≠ T.vertex (⟨(0
        : ℕ),
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv1 : v ≠ T.vertex (⟨(1 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv2 : v ≠ T.vertex (⟨(2 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv3 : v ≠ T.vertex (⟨(3 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))) (hv4 : v ≠ T.vertex (⟨(4 : ℕ),
    by
        first
        | omega
        | (
          have := GoldbergSeymour.TreeSequence.positive T
          have := NormalGlobalMaximumTriple.height_upper N
          have := GoldbergSeymour.TreeSequence.positive T
          all_goals omega)
    ⟩ : Fin (T.length + (1 : ℕ)))),
    let y0_1 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1_1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T)) (hy0T : y0_1 ∈
        TreeSequenceVertexSet T) (hy1T : y1_1 ∈ TreeSequenceVertexSet T) (r : E) (w : V) (hrcolor
        : phi r = some gamma) (hrends : G.ends r = s(T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w) ∨ G.ends r = s(T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))), w)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge;
    ∀ (hy01 : y0 ≠ y1) (hy02 : y0 ≠ y2) (hy03 : y0 ≠ y3) (hy04 : y0 ≠ y4) (hy12 : y1 ≠ y2) (hy13 :
        y1 ≠ y3) (hy14 : y1 ≠ y4) (hy23 : y2 ≠ y3) (hy24 : y2 ≠ y4) (hy34 : y3 ≠ y4) (ha1ends :
        G.ends a1 = s(y1, y2)) (ha2ends : G.ends a2 = s(y2, y3)) (ha3ends : G.ends a3 = s(y3, y4))
        (hqends : G.ends q = s(y4, y0)) (hproper : IsProperEdgeColoring G phi) (missing_excludes :
    ∀ {c : Fin k} {x : V} {f : E} (hc : c ∈ MissingColors G phi x) (hinc : Incident G x f), phi f
        ≠ some c) (edge_color_of_closing_support :
    ∀ (f : E) (hf : Sum.inr f ∈ N.closingPath.support), phi f = some N.alpha ∨ phi f = some
        N.beta) (ha1support : Sum.inr a1 ∈ N.closingPath.support) (ha2support : Sum.inr a2 ∈
        N.closingPath.support) (ha3support : Sum.inr a3 ∈ N.closingPath.support), w = T.vertex
        (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))) ∨ w = T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)))

private theorem helper_gamma_present_127.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) → y0
        ∈ TreeSequenceVertexSet T → gamma ∈ MissingColors G phi y0 →
    ∀ {x : V}, x ∈ TreeSequenceVertexSet T → x ≠ y0 → gamma ∈ PresentColors G phi x := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y0 helem hy0T hgamma0 x hxT hx0
  have hnot : gamma ∉ MissingColors G phi x := by
    intro hxmiss
    have hd := helem hxT hy0T hx0
    exact (Finset.disjoint_left.mp hd) hxmiss hgamma0
  simpa [MissingColors] using hnot

private theorem helper_missing_excludes_231.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) {c : Fin k} {x : V} {f : E}, c ∈ MissingColors G phi x →
        Incident G x f → phi f ≠ some c := by
  classical
  intro V E _ _ G k phi c x f hc hinc hfc
  let _ := Fintype.ofFinite V
  have hp : c ∈ PresentColors G phi x := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hinc, hfc⟩
  have hn : c ∉ PresentColors G phi x := by
    simpa [MissingColors] using hc
  exact hn hp

private theorem helper_edge_color_of_closing_support_241.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T),
    ∀ v ∈ TreeSequenceVertexSet T,
    ∀ (f : E), Sum.inr f ∈ N.closingPath.support → phi f = some N.alpha ∨ phi f = some N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N v _ f hf
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hf
  have hilt : i < N.closingPath.length := by
    by_contra hn
    have hil : N.closingPath.length ≤ i := by omega
    have hend := N.closingPath.getVert_of_length_le (i := i) hil
    rw [hi] at hend
    simp at hend
  have hadj := N.closingPath.adj_getVert_succ hilt
  rw [hi] at hadj
  cases hz : N.closingPath.getVert (i + 1) with
  | inl x =>
      rw [hz] at hadj
      have hdata : Incident G x f ∧
          (phi f = some N.alpha ∨ phi f = some N.beta) := by
        simpa [TwoColorIncidenceGraph] using hadj
      exact hdata.2
  | inr e =>
      rw [hz] at hadj
      simp [TwoColorIncidenceGraph] at hadj

private theorem helper_ha1color_275.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1; G.ends a1 = s(y1, y2) → (
    ∀ {c : Fin k} {x : V} {f : E}, c ∈ MissingColors G phi x → Incident G x f → phi f ≠ some c) →
        (
    ∀ (f : E), Sum.inr f ∈ N.closingPath.support → phi f = some N.alpha ∨ phi f = some N.beta) →
        Sum.inr a1 ∈ N.closingPath.support → phi a1 = some N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 r1 a1 ha1ends missing_excludes
      edge_color_of_closing_support ha1support
  rcases edge_color_of_closing_support a1 ha1support with h | h
  · exact h
  · have hbmiss : N.beta ∈ MissingColors G phi y1 := by
      simpa [y1] using N.beta_missing
    have hinc : Incident G y1 a1 := by
      unfold Incident
      rw [ha1ends]
      simp
    exact False.elim ((missing_excludes hbmiss hinc) h)

private theorem helper_ha1a2_285.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2; G.ends a1 = s(y1, y2) → G.ends a2 = s(y2, y3) → AdjacentEdges G a1 a2
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 y3 r1 r2 a1 a2 ha1ends ha2ends
  refine ⟨y2, ?_, ?_⟩ <;> unfold Incident
  · rw [ha1ends]
    simp
  · rw [ha2ends]
    simp

private theorem helper_ha2a3_299.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3; G.ends a2 = s(y2, y3) → G.ends a3 = s(y3, y4) → AdjacentEdges G a2 a3
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y2 y3 y4 r2 r3 a2 a3 ha2ends ha3ends
  refine ⟨y3, ?_, ?_⟩ <;> unfold Incident
  · rw [ha2ends]
    simp
  · rw [ha3ends]
    simp

private theorem helper_ha3q_313.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; G.ends a3 = s(y3, y4) → G.ends q = s(y4, y0) → AdjacentEdges G a3
        q := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y3 y4 r3 a3 q ha3ends hqends
  refine ⟨y4, ?_, ?_⟩ <;> unfold Incident
  · rw [ha3ends]
    simp
  · rw [hqends]
    simp

private theorem helper_halpha_beta_330.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1; G.ends a1 = s(y1, y2) → (
    ∀ {c : Fin k} {x : V} {f : E}, c ∈ MissingColors G phi x → Incident G x f → phi f ≠ some c) →
        phi a1 = some N.alpha → N.alpha ≠ N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 r1 a1 ha1ends missing_excludes ha1color h
  have hinc : Incident G y1 a1 := by
    unfold Incident
    rw [ha1ends]
    simp
  exact (missing_excludes (by simpa [y1] using N.beta_missing) hinc)
    (by simpa [h] using ha1color)

private theorem helper_hqa1_406.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let q : E := N.closingEdge; y1 ≠ y4 → y2 ≠ y4 → G.ends a1 = s(y1, y2) → G.ends q = s(y4, y0) →
        q ≠ a1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y1 y2 y4 r1 a1 q hy14 hy24 ha1ends hqends h
  have hpairs : s(y4, y0) = s(y1, y2) := by
    rw [← hqends, h, ha1ends]
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hy14 hd.1.symm
  · exact hy24 hs.1.symm

private theorem helper_hgamma_alpha_425.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
        ScheideGraphHeight G = (5 : ℕ) →
    ∀ (gamma : Fin k) (g : E) (v : V), phi g = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a2 : E := T.edge r2;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge; y0 ≠ y1 → y0 ≠ y2 → y0 ≠ y3 → y0 ≠ y4 → y1 ≠ y2 → y1 ≠ y3 → y1 ≠
        y4 → y2 ≠ y3 → y2 ≠ y4 → y3 ≠ y4 → G.ends a1 = s(y1, y2) → G.ends a2 = s(y2, y3) → G.ends
        a3 = s(y3, y4) → phi a1 = some N.alpha → a1 ≠ a2 → phi a2 = some N.beta → a2 ≠ a3 → phi a3
        = some N.alpha → v ≠ y0 → v ≠ y1 → v ≠ y2 → v ≠ y3 → v ≠ y4 → G.ends g = s(y0, v) ∨ G.ends
        g = s(y1, v) ∨ G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨ G.ends g = s(y4, v) →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p1.IsPath → (4 : ℕ) ∣
        p1.length → p1.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G →
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0); Sum.inl y0 ∈ C1 → (
    ∀ {z : V ⊕ E}, z ∈ C1 → z ∈ p1.support) → (
    ∀ {x : V} {f : E}, Sum.inl x ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inr f ∈ C1) → (
    ∀ {f : E} {x : V}, Sum.inr f ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inl x ∈ C1) → Sum.inr q ∈ C1 → Sum.inl y4 ∈ C1 → Sum.inl y1 ∈ C1 → q ≠ a1 → q ≠ a2 →
        q ≠ a3 → a1 ≠ a3 → gamma ≠ N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hGheight gamma g v hgcolor y0 y1 y2 y3 y4 r1 r2 r3 a1
      a2 a3 q hy01 hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34 ha1ends ha2ends ha3ends ha1color
      ha12ne ha2color ha23ne ha3color hv0' hv1' hv2' hv3' hv4' hgends' p1 hp1 hp1div hp1bound C1
      hC1root support_of_C1 edge_step_C1 vertex_step_C1 hqC1 hy4C1 hy1C1 hqa1 hqa2 hqa3 ha13ne hga
  have ha3C1 : Sum.inr a3 ∈ C1 := by
    apply edge_step_C1 hy4C1
    · unfold Incident
      rw [ha3ends]
      simp
    · left
      simpa [hga] using ha3color
  have hy3C1 : Sum.inl y3 ∈ C1 := by
    apply vertex_step_C1 ha3C1
    · unfold Incident
      rw [ha3ends]
      simp
    · left
      simpa [hga] using ha3color
  have ha2C1 : Sum.inr a2 ∈ C1 := by
    apply edge_step_C1 hy3C1
    · unfold Incident
      rw [ha2ends]
      simp
    · exact Or.inr ha2color
  have hy2C1 : Sum.inl y2 ∈ C1 := by
    apply vertex_step_C1 ha2C1
    · unfold Incident
      rw [ha2ends]
      simp
    · exact Or.inr ha2color
  have ha1C1 : Sum.inr a1 ∈ C1 := by
    apply edge_step_C1 hy2C1
    · unfold Incident
      rw [ha1ends]
      simp
    · left
      simpa [hga] using ha1color
  have hvC1 : Sum.inl v ∈ C1 := by
    rcases hgends' with hgv | hgv | hgv | hgv | hgv
    all_goals
      have hgi : Incident G v g := by unfold Incident; rw [hgv]; simp
    · have hgC := edge_step_C1 hC1root (by unfold Incident; rw [hgv]; simp)
          (Or.inl hgcolor)
      exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
    · have hgC := edge_step_C1 hy1C1 (by unfold Incident; rw [hgv]; simp)
          (Or.inl hgcolor)
      exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
    · have hgC := edge_step_C1 hy2C1 (by unfold Incident; rw [hgv]; simp)
          (Or.inl hgcolor)
      exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
    · have hgC := edge_step_C1 hy3C1 (by unfold Incident; rw [hgv]; simp)
          (Or.inl hgcolor)
      exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
    · have hgC := edge_step_C1 hy4C1 (by unfold Incident; rw [hgv]; simp)
          (Or.inl hgcolor)
      exact vertex_step_C1 hgC hgi (Or.inl hgcolor)
  let K10 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
      Sum.inl v, Sum.inr q, Sum.inr a1, Sum.inr a2, Sum.inr a3}
  have hK10card : K10.card = 10 := by
    simp [K10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
      hy34, hqa1, hqa2, hqa3,
      ha12ne, ha13ne, ha23ne, Ne.symm hv0',
      Ne.symm hv1', Ne.symm hv2', Ne.symm hv3', Ne.symm hv4']
  have hK10sub : K10 ⊆ p1.support.toFinset := by
    intro z hz
    simp only [K10, Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [List.mem_toFinset]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact support_of_C1 hC1root
    · exact support_of_C1 hy1C1
    · exact support_of_C1 hy2C1
    · exact support_of_C1 hy3C1
    · exact support_of_C1 hy4C1
    · exact support_of_C1 hvC1
    · exact support_of_C1 hqC1
    · exact support_of_C1 ha1C1
    · exact support_of_C1 ha2C1
    · exact support_of_C1 ha3C1
  have hp1lower : 9 ≤ p1.length := by
    have hc := Finset.card_le_card hK10sub
    rw [hK10card, List.toFinset_card_of_nodup hp1.support_nodup,
      p1.length_support] at hc
    omega
  rcases hp1div with ⟨d, hd⟩
  omega

private theorem helper_hrmiddle_523.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (r : E)
        (w : V),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); G.ends r = s(y2, w) ∨ G.ends r = s(y3, w) → Incident G y2 r ∨
        Incident G y3 r := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight r w y2 y3 hrends'
  rcases hrends' with h | h
  · left
    unfold Incident
    rw [h]
    simp
  · right
    unfold Incident
    rw [h]
    simp

private theorem helper_hbr_549.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (r : E)
        (w : V),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); y1 ≠ y2 → y1 ≠ y3 →
    ∀ (b : E), Incident G y1 b → G.ends r = s(y2, w) ∨ G.ends r = s(y3, w) → w ≠ y1 → b ≠ r := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight r w y1 y2 y3 hy12 hy13 b hbinc hrends' hw1 h
  have hinc : Incident G y1 r := by simpa [h] using hbinc
  rcases hrends' with hr | hr
  · unfold Incident at hinc
    rw [hr] at hinc
    simp [hy12] at hinc
    exact hw1 hinc.symm
  · unfold Incident at hinc
    rw [hr] at hinc
    simp [hy13] at hinc
    exact hw1 hinc.symm

private theorem helper_middle_too_large_561.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
        ScheideGraphHeight G = (5 : ℕ) →
    ∀ (gamma : Fin k) (r : E) (w : V), phi r = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a2 : E := T.edge r2;
    let q : E := N.closingEdge; y0 ≠ y1 → y0 ≠ y2 → y0 ≠ y3 → y0 ≠ y4 → y1 ≠ y2 → y1 ≠ y3 → y1 ≠
        y4 → y2 ≠ y3 → y2 ≠ y4 → y3 ≠ y4 → phi a2 = some N.beta →
    ∀ (p1 : (TwoColorIncidenceGraph G phi gamma N.beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p1.IsPath → (4 : ℕ) ∣
        p1.length → p1.length / (2 : ℕ) + (1 : ℕ) ≤ ScheideGraphHeight G →
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0); Sum.inl y0 ∈ C1 → (
    ∀ {z : V ⊕ E}, z ∈ C1 → z ∈ p1.support) → (
    ∀ {x : V} {f : E}, Sum.inl x ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inr f ∈ C1) → Sum.inr q ∈ C1 → Sum.inl y4 ∈ C1 → Sum.inl y1 ∈ C1 →
    ∀ (b : E), Sum.inr b ∈ C1 → q ≠ a2 → w ≠ y0 → w ≠ y1 → w ≠ y2 → w ≠ y3 → w ≠ y4 → Incident G
        y2 a2 → Incident G y2 r ∨ Incident G y3 r → b ≠ q → b ≠ a2 → r ≠ q → r ≠ a2 → b ≠ r →
        Sum.inl y2 ∈ C1 → Sum.inl y3 ∈ C1 → Sum.inl w ∈ C1 → False := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hGheight gamma r w hrcolor y0 y1 y2 y3 y4 r2 a2 q hy01
      hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34 ha2color p1 hp1 hp1div hp1bound C1 hC1root
      support_of_C1 edge_step_C1 hqC1 hy4C1 hy1C1 b hbC1 hqa2 hw0 hw1 hw2 hw3 hw4 ha2inc2
      hrmiddle hbq hba2 hrq hra2 hbr hy2C hy3C hwC
  have ha2C : Sum.inr a2 ∈ C1 :=
    edge_step_C1 hy2C ha2inc2 (Or.inr ha2color)
  have hrC : Sum.inr r ∈ C1 := by
    rcases hrmiddle with h | h
    · exact edge_step_C1 hy2C h (Or.inl hrcolor)
    · exact edge_step_C1 hy3C h (Or.inl hrcolor)
  let L10 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
      Sum.inl w, Sum.inr q, Sum.inr a2, Sum.inr b, Sum.inr r}
  have hL10card : L10.card = 10 := by
    simp [L10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
      hy34, hqa2, hbr,
      Ne.symm hw0, Ne.symm hw1,
      Ne.symm hw2, Ne.symm hw3, Ne.symm hw4, Ne.symm hbq, Ne.symm hba2, Ne.symm hrq, Ne.symm hra2]
  have hL10sub : L10 ⊆ p1.support.toFinset := by
    intro z hz
    simp only [L10, Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [List.mem_toFinset]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact support_of_C1 hC1root
    · exact support_of_C1 hy1C1
    · exact support_of_C1 hy2C
    · exact support_of_C1 hy3C
    · exact support_of_C1 hy4C1
    · exact support_of_C1 hwC
    · exact support_of_C1 hqC1
    · exact support_of_C1 ha2C
    · exact support_of_C1 hbC1
    · exact support_of_C1 hrC
  have hp1lower : 9 ≤ p1.length := by
    have hc := Finset.card_le_card hL10sub
    rw [hL10card, List.toFinset_card_of_nodup hp1.support_nodup,
      p1.length_support] at hc
    omega
  rcases hp1div with ⟨d, hd⟩
  omega

private theorem helper_hy2notC1_600.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (r : E) (w : V), phi r = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r2 : Fin T.length := (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a2 : E := T.edge r2; phi a2 = some N.beta →
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0); (
    ∀ {x : V} {f : E}, Sum.inl x ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inr f ∈ C1) → (
    ∀ {f : E} {x : V}, Sum.inr f ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inl x ∈ C1) → Incident G y2 a2 → Incident G y3 a2 → Incident G w r → Incident G y2 r
        ∨ Incident G y3 r → (Sum.inl y2 ∈ C1 → Sum.inl y3 ∈ C1 → Sum.inl w ∈ C1 → False) → Sum.inl
        y2 ∉ C1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma r w hrcolor y0 y2 y3 r2 a2 ha2color C1
      edge_step_C1 vertex_step_C1 ha2inc2 ha2inc3 hrincw hrmiddle middle_too_large hy2C
  have ha2C := edge_step_C1 hy2C ha2inc2 (Or.inr ha2color)
  have hy3C := vertex_step_C1 ha2C ha2inc3 (Or.inr ha2color)
  have hrC : Sum.inr r ∈ C1 := by
    rcases hrmiddle with h | h
    · exact edge_step_C1 hy2C h (Or.inl hrcolor)
    · exact edge_step_C1 hy3C h (Or.inl hrcolor)
  have hwC := vertex_step_C1 hrC hrincw (Or.inl hrcolor)
  exact middle_too_large hy2C hy3C hwC

private theorem helper_hwnotC1_614.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (r : E) (w : V), phi r = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let C1 : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0); (
    ∀ {x : V} {f : E}, Sum.inl x ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inr f ∈ C1) → (
    ∀ {f : E} {x : V}, Sum.inr f ∈ C1 → Incident G x f → phi f = some gamma ∨ phi f = some N.beta
        → Sum.inl x ∈ C1) → Incident G w r → Incident G y2 r ∨ Incident G y3 r → Sum.inl y2 ∉ C1 →
        Sum.inl y3 ∉ C1 → Sum.inl w ∉ C1 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma r w hrcolor y0 y2 y3 C1 edge_step_C1
      vertex_step_C1 hrincw hrmiddle hy2notC1 hy3notC1 hwC
  have hrC := edge_step_C1 hwC hrincw (Or.inl hrcolor)
  rcases hrmiddle with h | h
  · exact hy2notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
  · exact hy3notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))

private theorem helper_alpha_fixed_657.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); N.alpha ≠ N.beta →
    let _ : Set (V ⊕ E) := TwoColorComponent G phi gamma N.beta (Sum.inl y0); gamma ≠ N.alpha →
        gamma ≠ N.beta →
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma N.beta (Sum.inl y0);
    ∀ (f : E), phi' f = some N.alpha ↔ phi f = some N.alpha := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y0 halpha_beta C1 hgamma_alpha hgamma_beta phi' f
  by_cases hfC : Sum.inr f ∈ C1
  · by_cases hfg : phi f = some gamma
    · simp [phi', TwoColorComponentSwap, C1, hfC, hfg, hgamma_alpha,
        Ne.symm halpha_beta]
    · by_cases hfb : phi f = some N.beta
      · simp [phi', TwoColorComponentSwap, C1, hfC, hfb,
          hgamma_alpha, Ne.symm halpha_beta, Ne.symm hgamma_beta]
      · simp [phi', TwoColorComponentSwap, C1, hfC, hfg, hfb]
  · simp [phi', TwoColorComponentSwap, C1, hfC]

private theorem helper_hM10sub_738.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V] [ DecidableEq E] (G
        : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T :
        TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5
        : ℕ)) (gamma : Fin k) (r : E) (w : V),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let r1 : Fin T.length := (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let r3 : Fin T.length := (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length) ↦
    by omega
    ⟩ : Fin T.length);
    let a1 : E := T.edge r1;
    let a3 : E := T.edge r3;
    let q : E := N.closingEdge;
    let phi' : PartialEdgeColoring E k := TwoColorComponentSwap G phi gamma N.beta (Sum.inl y0);
    ∀ (p2 : (TwoColorIncidenceGraph G phi' N.alpha gamma).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))),
    let C2 : Set (V ⊕ E) := TwoColorComponent G phi' N.alpha gamma (Sum.inl y0); Sum.inl y0 ∈ C2 →
        (
    ∀ {z : V ⊕ E}, z ∈ C2 → z ∈ p2.support) → Sum.inr q ∈ C2 → Sum.inl y4 ∈ C2 → Sum.inr a3 ∈ C2 →
        Sum.inl y3 ∈ C2 → Sum.inl y1 ∈ C2 → Sum.inr a1 ∈ C2 → Sum.inl y2 ∈ C2 → Sum.inr r ∈ C2 →
        Sum.inl w ∈ C2 →
    let M10 : Finset (V ⊕ E) := (insert (Sum.inl y0) (insert (Sum.inl y1) (insert (Sum.inl y2)
        (insert (Sum.inl y3) (insert (Sum.inl y4) (insert (Sum.inl w) (insert (Sum.inr q) (insert
        (Sum.inr a1) (insert (Sum.inr a3) ({Sum.inr r} : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)) :
        Finset (V ⊕ E)) : Finset (V ⊕ E)) : Finset (V ⊕ E)); M10 ⊆ p2.support.toFinset := by
  classical
  intro V E _ _ _ _ G k e0 phi T N hNheight gamma r w y0 y1 y2 y3 y4 r1 r3 a1 a3 q phi' p2 C2
      hC2root support_of_C2 hqC2 hy4C2 ha3C2 hy3C2 hy1C2 ha1C2 hy2C2 hrC2 hwC2 M10 z hz
  simp only [M10, Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [List.mem_toFinset]
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact support_of_C2 hC2root
  · exact support_of_C2 hy1C2
  · exact support_of_C2 hy2C2
  · exact support_of_C2 hy3C2
  · exact support_of_C2 hy4C2
  · exact support_of_C2 hwC2
  · exact support_of_C2 hqC2
  · exact support_of_C2 ha1C2
  · exact support_of_C2 ha3C2
  · exact support_of_C2 hrC2

private theorem helper_endpoint_in_tree_768.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) → y0 ∈
        TreeSequenceVertexSet T → gamma ∈ MissingColors G phi y0 →
    ∀ {x z : V} {f : E}, x ∈ TreeSequenceVertexSet T → G.ends f = s(x, z) → phi f = some gamma → z
        ∈ TreeSequenceVertexSet T := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y0 hclosed hy0T hgamma0 x z f hxT hfends hfcolor
  by_contra hzT
  have hboundary : f ∈ BoundaryEdges G (TreeSequenceVertexSet T) := by
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, hxT, z, hzT, hfends⟩
  exact (hclosed hboundary hy0T hfcolor) hgamma0

private theorem helper_missing_excludes_806.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ)
        (phi : PartialEdgeColoring E k) (gamma : Fin k) {x : V} {f : E}, gamma ∈ MissingColors G
        phi x → Incident G x f → phi f ≠ some gamma := by
  classical
  intro V E _ _ G k phi gamma x f hm hinc hfc
  let _ := Fintype.ofFinite V
  have hp : gamma ∈ PresentColors G phi x := by
    simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨f, hinc, hfc⟩
  have hn : gamma ∉ PresentColors G phi x := by
    simpa [MissingColors] using hm
  exact hn hp

private theorem helper_hz20_822.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); gamma ∈ MissingColors G phi y0 →
    ∀ (f2 : E), phi f2 = some gamma →
    ∀ (z2 : V), G.ends f2 = s(y2, z2) → (
    ∀ {x : V} {f : E}, gamma ∈ MissingColors G phi x → Incident G x f → phi f ≠ some gamma) → z2 ≠
        y0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y0 y2 hgamma0 f2 hf2color z2 hf2ends
      missing_excludes h
  have hinc : Incident G y0 f2 := by
    unfold Incident
    rw [hf2ends, h]
    simp
  exact (missing_excludes hgamma0 hinc) hf2color

private theorem helper_hz30_829.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); gamma ∈ MissingColors G phi y0 →
    ∀ (f3 : E), phi f3 = some gamma →
    ∀ (z3 : V), G.ends f3 = s(y3, z3) → (
    ∀ {x : V} {f : E}, gamma ∈ MissingColors G phi x → Incident G x f → phi f ≠ some gamma) → z3 ≠
        y0 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y0 y3 hgamma0 f3 hf3color z3 hf3ends
      missing_excludes h
  have hinc : Incident G y0 f3 := by
    unfold Incident
    rw [hf3ends, h]
    simp
  exact (missing_excludes hgamma0 hinc) hf3color

private theorem helper_hz23_849.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f2 : E), phi f2 = some gamma →
    ∀ (f3 : E), Incident G y3 f3 → phi f3 = some gamma →
    ∀ (z2 : V), G.ends f2 = s(y2, z2) → IsProperEdgeColoring G phi → ¬f2 = f3 → z2 ≠ y3 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y2 y3 f2 hf2color f3 hf3inc hf3color z2 hf2ends
      hproper hne h
  have hinc : Incident G y3 f2 := by
    unfold Incident
    rw [hf2ends, h]
    simp
  exact (hproper hne ⟨y3, hinc, hf3inc⟩ hf2color) hf3color

private theorem helper_hz32_856.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f2 : E), Incident G y2 f2 → phi f2 = some gamma →
    ∀ (f3 : E), phi f3 = some gamma →
    ∀ (z3 : V), G.ends f3 = s(y3, z3) → IsProperEdgeColoring G phi → ¬f2 = f3 → z3 ≠ y2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y2 y3 f2 hf2inc hf2color f3 hf3color z3 hf3ends
      hproper hne h
  have hinc : Incident G y2 f3 := by
    unfold Incident
    rw [hf3ends, h]
    simp
  exact (hproper (Ne.symm hne) ⟨y2, hinc, hf2inc⟩ hf3color) hf2color

private theorem helper_hz2cases_863.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (z2 : V), z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 = y3 ∨ z2 = y4 → z2 ≠ y2 → z2 ≠ y0 → z2 ≠ y3 → z2
        = y1 ∨ z2 = y4 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y1 y2 y3 y4 z2 hz2trunk hz22 hz20 hz23
  rcases hz2trunk with h | h | h | h | h
  · exact False.elim (hz20 h)
  · exact Or.inl h
  · exact False.elim (hz22 h)
  · exact False.elim (hz23 h)
  · exact Or.inr h

private theorem helper_hz3cases_870.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (z3 : V), z3 = y0 ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4 → z3 ≠ y3 → z3 ≠ y0 → z3 ≠ y2 → z3
        = y1 ∨ z3 = y4 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y1 y2 y3 y4 z3 hz3trunk hz33 hz30 hz32
  rcases hz3trunk with h | h | h | h | h
  · exact False.elim (hz30 h)
  · exact Or.inl h
  · exact False.elim (hz32 h)
  · exact False.elim (hz33 h)
  · exact Or.inr h

private theorem helper_crossing_contra_877.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (g : E) (v : V), phi g = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); gamma ∈ MissingColors G phi y0 →
    ∀ (f2 : E), Incident G y2 f2 → phi f2 = some gamma →
    ∀ (f3 : E), Incident G y3 f3 → phi f3 = some gamma →
    ∀ (z2 : V), G.ends f2 = s(y2, z2) →
    ∀ (z3 : V), G.ends f3 = s(y3, z3) → IsProperEdgeColoring G phi → (
    ∀ {x : V} {f : E}, gamma ∈ MissingColors G phi x → Incident G x f → phi f ≠ some gamma) →
        G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨ G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
        G.ends g = s(y4, v) → v ≠ y1 → v ≠ y2 → v ≠ y3 → v ≠ y4 → Incident G v g → ¬f2 = f3 → z2 =
        y1 ∨ z2 = y4 → z3 = y1 ∨ z3 = y4 → False := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma g v hgcolor y0 y1 y2 y3 y4 hgamma0 f2 hf2inc
      hf2color f3 hf3inc hf3color z2 hf2ends z3 hf3ends hproper missing_excludes hgends' hv1'
      hv2' hv3' hv4' hgvinc hne hz2 hz3
  have hgf2 : g ≠ f2 := by
    intro h
    have hinc : Incident G v f2 := by simpa [h] using hgvinc
    unfold Incident at hinc
    rw [hf2ends] at hinc
    rcases hz2 with h2 | h2
    · rw [h2] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv2' hv1'
    · rw [h2] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv2' hv4'
  have hgf3 : g ≠ f3 := by
    intro h
    have hinc : Incident G v f3 := by simpa [h] using hgvinc
    unfold Incident at hinc
    rw [hf3ends] at hinc
    rcases hz3 with h3 | h3
    · rw [h3] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv3' hv1'
    · rw [h3] at hinc
      simp only [Sym2.mem_iff] at hinc
      exact hinc.elim hv3' hv4'
  rcases hz2 with h2 | h2 <;> rcases hz3 with h3 | h3
  · have hi2 : Incident G y1 f2 := by
      unfold Incident
      rw [hf2ends, h2]
      simp
    have hi3 : Incident G y1 f3 := by
      unfold Incident
      rw [hf3ends, h3]
      simp
    exact (hproper hne ⟨y1, hi2, hi3⟩ hf2color) hf3color
  · rcases hgends' with h | h | h | h | h
    · have hinc : Incident G y0 g := by unfold Incident; rw [h]; simp
      exact (missing_excludes hgamma0 hinc) hgcolor
    · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
      have hfinc : Incident G y1 f2 := by
        unfold Incident
        rw [hf2ends, h2]
        simp
      exact (hproper hgf2 ⟨y1, hginc, hfinc⟩ hgcolor) hf2color
    · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
    · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf3 ⟨y3, hginc, hf3inc⟩ hgcolor) hf3color
    · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
      have hfinc : Incident G y4 f3 := by
        unfold Incident
        rw [hf3ends, h3]
        simp
      exact (hproper hgf3 ⟨y4, hginc, hfinc⟩ hgcolor) hf3color
  · rcases hgends' with h | h | h | h | h
    · have hinc : Incident G y0 g := by unfold Incident; rw [h]; simp
      exact (missing_excludes hgamma0 hinc) hgcolor
    · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
      have hfinc : Incident G y1 f3 := by
        unfold Incident
        rw [hf3ends, h3]
        simp
      exact (hproper hgf3 ⟨y1, hginc, hfinc⟩ hgcolor) hf3color
    · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
    · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
      exact (hproper hgf3 ⟨y3, hginc, hf3inc⟩ hgcolor) hf3color
    · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
      have hfinc : Incident G y4 f2 := by
        unfold Incident
        rw [hf2ends, h2]
        simp
      exact (hproper hgf2 ⟨y4, hginc, hfinc⟩ hgcolor) hf2color
  · have hi2 : Incident G y4 f2 := by
      unfold Incident
      rw [hf2ends, h2]
      simp
    have hi3 : Incident G y4 f3 := by
      unfold Incident
      rw [hf3ends, h3]
      simp
    exact (hproper hne ⟨y4, hi2, hi3⟩ hf2color) hf3color

private theorem helper_hz2eq_964.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f2 : E) (z2 : V), G.ends f2 = s(y2, z2) → y2 ≠ y3 → Incident G y3 f2 → z2 = y3 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y2 y3 f2 z2 hf2ends hy23 hf23inc3
  have hm : y3 ∈ s(y2, z2) := by
    rw [← hf2ends]
    exact hf23inc3
  simp only [Sym2.mem_iff] at hm
  rcases hm with h | h
  · exact False.elim (hy23 h.symm)
  · exact h.symm

private theorem helper_hf1ne2_973.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f1 : E), Incident G y1 f1 →
    ∀ (f2 : E), y1 ≠ y2 → y1 ≠ y3 → G.ends f2 = s(y2, y3) → f1 ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y1 y2 y3 f1 hf1inc f2 hy12 hy13 hf23ends heq
  have hinc : Incident G y1 f2 := by
    rw [← heq]
    exact hf1inc
  unfold Incident at hinc
  rw [hf23ends] at hinc
  simp only [Sym2.mem_iff] at hinc
  exact hinc.elim hy12 hy13

private theorem helper_hz14_997.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (g : E) (v : V), phi g = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); gamma ∈ MissingColors G phi y0 →
    ∀ (f1 : E), Incident G y1 f1 → phi f1 = some gamma →
    ∀ (f2 : E), Incident G y2 f2 → phi f2 = some gamma →
    ∀ (z1 : V), G.ends f1 = s(y1, z1) → IsProperEdgeColoring G phi → (
    ∀ {x : V} {f : E}, gamma ∈ MissingColors G phi x → Incident G x f → phi f ≠ some gamma) →
        G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨ G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
        G.ends g = s(y4, v) → v ≠ y1 → v ≠ y2 → v ≠ y3 → v ≠ y4 → Incident G v g → Incident G y3
        f2 → G.ends f2 = s(y2, y3) → z1 ≠ y4 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma g v hgcolor y0 y1 y2 y3 y4 hgamma0 f1 hf1inc
      hf1color f2 hf2inc hf2color z1 hf1ends hproper missing_excludes hgends' hv1' hv2' hv3' hv4'
      hgvinc hf23inc3 hf23ends h14
  have hgf1 : g ≠ f1 := by
    intro h
    have hinc : Incident G v f1 := by simpa [h] using hgvinc
    unfold Incident at hinc
    rw [hf1ends, h14] at hinc
    simp only [Sym2.mem_iff] at hinc
    exact hinc.elim hv1' hv4'
  have hgf2 : g ≠ f2 := by
    intro h
    have hinc : Incident G v f2 := by simpa [h] using hgvinc
    unfold Incident at hinc
    rw [hf23ends] at hinc
    simp only [Sym2.mem_iff] at hinc
    exact hinc.elim hv2' hv3'
  rcases hgends' with h | h | h | h | h
  · have hginc : Incident G y0 g := by unfold Incident; rw [h]; simp
    exact (missing_excludes hgamma0 hginc) hgcolor
  · have hginc : Incident G y1 g := by unfold Incident; rw [h]; simp
    exact (hproper hgf1 ⟨y1, hginc, hf1inc⟩ hgcolor) hf1color
  · have hginc : Incident G y2 g := by unfold Incident; rw [h]; simp
    exact (hproper hgf2 ⟨y2, hginc, hf2inc⟩ hgcolor) hf2color
  · have hginc : Incident G y3 g := by unfold Incident; rw [h]; simp
    exact (hproper hgf2 ⟨y3, hginc, hf23inc3⟩ hgcolor) hf2color
  · have hginc : Incident G y4 g := by unfold Incident; rw [h]; simp
    have hfinc : Incident G y4 f1 := by
      unfold Incident
      rw [hf1ends, h14]
      simp
    exact (hproper hgf1 ⟨y4, hginc, hfinc⟩ hgcolor) hf1color

private theorem helper_hf4ne2_1035.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f2 f4 : E), Incident G y4 f4 → y2 ≠ y4 → y3 ≠ y4 → G.ends f2 = s(y2, y3) → f4 ≠ f2 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y2 y3 y4 f2 f4 hf4inc hy24 hy34 hf23ends heq
  have hinc : Incident G y4 f2 := by
    rw [← heq]
    exact hf4inc
  unfold Incident at hinc
  rw [hf23ends] at hinc
  simp only [Sym2.mem_iff] at hinc
  exact hinc.elim (Ne.symm hy24) (Ne.symm hy34)

private theorem helper_hz41_1052.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k),
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    ∀ (f1 : E), Incident G y1 f1 → phi f1 = some gamma →
    ∀ (f4 : E), phi f4 = some gamma →
    ∀ (z1 : V), G.ends f1 = s(y1, z1) →
    ∀ (z4 : V), G.ends f4 = s(y4, z4) → y1 ≠ y4 → IsProperEdgeColoring G phi → z1 ≠ y4 → z4 ≠ y1
  := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma y1 y4 f1 hf1inc hf1color f4 hf4color z1 hf1ends
      z4 hf4ends hy14 hproper hz14 h41
  have hf4inc1 : Incident G y1 f4 := by
    unfold Incident
    rw [hf4ends, h41]
    simp
  have heq : f4 = f1 := by
    by_contra hne
    exact (hproper hne ⟨y1, hf4inc1, hf1inc⟩ hf4color) hf1color
  have hpairs : s(y4, y1) = s(y1, z1) := by
    calc
      s(y4, y1) = G.ends f4 := by rw [hf4ends, h41]
      _ = G.ends f1 := congrArg G.ends heq
      _ = s(y1, z1) := hf1ends
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hy14 hd.1.symm
  · exact hz14 hs.1.symm

private theorem helper_f2_eq_f3_2262.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)) (gamma
        : Fin k) (g : E) (v : V), phi g = some gamma →
    let y0 : V := T.vertex (⟨(0 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y1 : V := T.vertex (⟨(1 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(1 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y2 : V := T.vertex (⟨(2 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(2 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y3 : V := T.vertex (⟨(3 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(3 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ)));
    let y4 : V := T.vertex (⟨(4 : ℕ),
    have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
        : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
    by omega
    ⟩ : Fin (T.length + (1 : ℕ))); gamma ∈ MissingColors G phi y0 →
    ∀ (f2 : E), Incident G y2 f2 → phi f2 = some gamma →
    ∀ (f3 : E), Incident G y3 f3 → phi f3 = some gamma →
    ∀ (z2 : V), G.ends f2 = s(y2, z2) →
    ∀ (z3 : V), G.ends f3 = s(y3, z3) → z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 = y3 ∨ z2 = y4 → z3 = y0
        ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4 → IsProperEdgeColoring G phi → (
    ∀ {x : V} {f : E}, gamma ∈ MissingColors G phi x → Incident G x f → phi f ≠ some gamma) → z2 ≠
        y2 → z3 ≠ y3 → z2 ≠ y0 → z3 ≠ y0 → G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨ G.ends g =
        s(y2, v) ∨ G.ends g = s(y3, v) ∨ G.ends g = s(y4, v) → v ≠ y1 → v ≠ y2 → v ≠ y3 → v ≠ y4 →
        Incident G v g → f2 = f3 := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma g v hgcolor y0 y1 y2 y3 y4 hgamma0 f2 hf2inc
      hf2color f3 hf3inc hf3color z2 hf2ends z3 hf3ends hz2trunk hz3trunk hproper
      missing_excludes hz22 hz33 hz20 hz30 hgends' hv1' hv2' hv3' hv4' hgvinc
  by_contra hne
  have hz23 := @helper_hz23_849 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@f2) (@hf2color) (@f3) (@hf3inc) (@hf3color) (@z2)
      (@hf2ends) (@hproper) (@hne)
  have hz32 := @helper_hz32_856 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@f2) (@hf2inc) (@hf2color) (@f3) (@hf3color) (@z3)
      (@hf3ends) (@hproper) (@hne)
  have hz2cases := @helper_hz2cases_863 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@z2) (@hz2trunk) (@hz22) (@hz20) (@hz23)
  have hz3cases := @helper_hz3cases_870 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@z3) (@hz3trunk) (@hz33) (@hz30) (@hz32)
  have crossing_contra := @helper_crossing_contra_877 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@g) (@v) (@hgcolor)
      (@hgamma0) (@f2) (@hf2inc) (@hf2color) (@f3) (@hf3inc) (@hf3color) (@z2) (@hf2ends) (@z3)
      (@hf3ends) (@hproper) (@missing_excludes) (@hgends') (@hv1') (@hv2') (@hv3') (@hv4') (@hgvinc)
      (@hne)
  exact crossing_contra hz2cases hz3cases

private theorem helper_continuation_2789.{u_1, u_2} :
    helperContinuation2789Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma g v hgcolor hgends _ hv1 hv2 hv3 hv4 y0 y1 y2 y3
      y4 hgamma0 f1 hf1inc hf1color f2 hf2inc hf2color f3 hf3inc hf3color f4 hf4inc hf4color z1
      hf1ends z2 hf2ends z3 hf3ends z4 hf4ends hz2trunk hz3trunk hz1T hz4T hy12 hy13 hy14 hy23
      hy24 hy34
  have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
  have missing_excludes := @helper_missing_excludes_806 (@V) (@E) inferInstance inferInstance (@G)
      (@k) (@phi) (@gamma)
  have hz22 : z2 ≠ y2 := by
    intro h
    exact G.loopless f2 y2 (by simpa [h] using hf2ends)
  have hz33 : z3 ≠ y3 := by
    intro h
    exact G.loopless f3 y3 (by simpa [h] using hf3ends)
  have hz20 := @helper_hz20_822 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@hgamma0) (@f2) (@hf2color) (@z2) (@hf2ends)
      (@missing_excludes)
  have hz30 := @helper_hz30_829 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@hgamma0) (@f3) (@hf3color) (@z3) (@hf3ends)
      (@missing_excludes)
  have hgends' : G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨
      G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
      G.ends g = s(y4, v) := by
    simpa [y0, y1, y2, y3, y4] using hgends
  have hv1' : v ≠ y1 := by simpa [y1] using hv1
  have hv2' : v ≠ y2 := by simpa [y2] using hv2
  have hv3' : v ≠ y3 := by simpa [y3] using hv3
  have hv4' : v ≠ y4 := by simpa [y4] using hv4
  have hgvinc : Incident G v g := by
    rcases hgends' with h | h | h | h | h <;>
      unfold Incident <;> rw [h] <;> simp
  have f2_eq_f3 := @helper_f2_eq_f3_2262 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@g) (@v) (@hgcolor) (@hgamma0) (@f2)
      (@hf2inc) (@hf2color) (@f3) (@hf3inc) (@hf3color) (@z2) (@hf2ends) (@z3) (@hf3ends)
      (@hz2trunk) (@hz3trunk) (@hproper) (@missing_excludes) (@hz22) (@hz33) (@hz20) (@hz30)
      (@hgends') (@hv1') (@hv2') (@hv3') (@hv4') (@hgvinc)
  have hf23inc3 : Incident G y3 f2 := by
    rw [f2_eq_f3]
    exact hf3inc
  have hz2eq := @helper_hz2eq_964 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@f2) (@z2) (@hf2ends) (@hy23) (@hf23inc3)
  have hf23ends : G.ends f2 = s(y2, y3) := by simpa [hz2eq] using hf2ends
  have hf1ne2 := @helper_hf1ne2_973 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@f1) (@hf1inc) (@f2) (@hy12) (@hy13) (@hf23ends)
  have hz11 : z1 ≠ y1 := by
    intro h
    exact G.loopless f1 y1 (by simpa [h] using hf1ends)
  have hz10 : z1 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (missing_excludes hgamma0 hinc) hf1color
  have hz12 : z1 ≠ y2 := by
    intro h
    have hinc : Incident G y2 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (hproper hf1ne2 ⟨y2, hinc, hf2inc⟩ hf1color) hf2color
  have hz13 : z1 ≠ y3 := by
    intro h
    have hinc : Incident G y3 f1 := by unfold Incident; rw [hf1ends, h]; simp
    exact (hproper hf1ne2 ⟨y3, hinc, hf23inc3⟩ hf1color) hf2color
  have hz14 := @helper_hz14_997 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@g) (@v) (@hgcolor) (@hgamma0) (@f1) (@hf1inc)
      (@hf1color) (@f2) (@hf2inc) (@hf2color) (@z1) (@hf1ends) (@hproper) (@missing_excludes)
      (@hgends') (@hv1') (@hv2') (@hv3') (@hv4') (@hgvinc) (@hf23inc3) (@hf23ends)
  have hz44 : z4 ≠ y4 := by
    intro h
    exact G.loopless f4 y4 (by simpa [h] using hf4ends)
  have hz40 : z4 ≠ y0 := by
    intro h
    have hinc : Incident G y0 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (missing_excludes hgamma0 hinc) hf4color
  have hf4ne2 := @helper_hf4ne2_1035 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@f2) (@f4) (@hf4inc) (@hy24) (@hy34) (@hf23ends)
  have hz42 : z4 ≠ y2 := by
    intro h
    have hinc : Incident G y2 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (hproper hf4ne2 ⟨y2, hinc, hf2inc⟩ hf4color) hf2color
  have hz43 : z4 ≠ y3 := by
    intro h
    have hinc : Incident G y3 f4 := by unfold Incident; rw [hf4ends, h]; simp
    exact (hproper hf4ne2 ⟨y3, hinc, hf23inc3⟩ hf4color) hf2color
  have hz41 := @helper_hz41_1052 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@gamma) (@f1) (@hf1inc) (@hf1color) (@f4) (@hf4color) (@z1)
      (@hf1ends) (@z4) (@hf4ends) (@hy14) (@hproper) (@hz14)
  refine ⟨f1, f4, f2, z1, z4, ?_, ?_, ?_, hf1color, hf4color,
    hf2color, hz1T, hz4T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [y1] using hf1ends
  · simpa [y4] using hf4ends
  · simpa [y2, y3] using hf23ends
  · simpa [y0] using hz10
  · simpa [y1] using hz11
  · simpa [y2] using hz12
  · simpa [y3] using hz13
  · simpa [y4] using hz14
  · simpa [y0] using hz40
  · simpa [y1] using hz41
  · simpa [y2] using hz42
  · simpa [y3] using hz43
  · simpa [y4] using hz44

private theorem helper_continuation_3161.{u_1, u_2} :
    helperContinuation3161Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight gamma g v hgcolor hgends _ hv1 hv2 hv3 hv4 y0 y1 y2 y3
      y4 hclosed hy0T hy1T hy4T hgamma0 f1 hf1inc hf1color f2 hf2inc hf2color f3 hf3inc hf3color
      f4 hf4inc hf4color z1 hf1ends z2 hf2ends z3 hf3ends z4 hf4ends middle_no_escape
  have hz2trunk : z2 = y0 ∨ z2 = y1 ∨ z2 = y2 ∨ z2 = y3 ∨ z2 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (middle_no_escape f2 z2 hf2color
        (Or.inl (by simpa [y2] using hf2ends)))
  have hz3trunk : z3 = y0 ∨ z3 = y1 ∨ z3 = y2 ∨ z3 = y3 ∨ z3 = y4 := by
    simpa [y0, y1, y2, y3, y4] using
      (middle_no_escape f3 z3 hf3color
        (Or.inr (by simpa [y3] using hf3ends)))
  have endpoint_in_tree := @helper_endpoint_in_tree_768 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@hclosed) (@hy0T)
      (@hgamma0)
  have hz1T : z1 ∈ TreeSequenceVertexSet T :=
    endpoint_in_tree hy1T (by simpa [y1] using hf1ends) hf1color
  have hz4T : z4 ∈ TreeSequenceVertexSet T :=
    endpoint_in_tree hy4T (by simpa [y4] using hf4ends) hf4color
  have hy12 : y1 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy13 : y1 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy14 : y1 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy23 : y2 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy24 : y2 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy34 : y3 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  exact @helper_continuation_2789 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@g) (@v) (@hgcolor) (@hgends) (by
    assumption) (@hv1) (@hv2) (@hv3) (@hv4) (@hgamma0) (@f1) (@hf1inc) (@hf1color) (@f2)
        (@hf2inc) (@hf2color) (@f3) (@hf3inc) (@hf3color) (@f4) (@hf4inc) (@hf4color) (@z1)
        (@hf1ends) (@z2) (@hf2ends) (@z3) (@hf3ends) (@z4) (@hf4ends) (@hz2trunk) (@hz3trunk)
        (@hz1T) (@hz4T) (@hy12) (@hy13) (@hy14) (@hy23) (@hy24) (@hy34)

private theorem helper_caseContinuation_3625.{u_1, u_2} :
    helperCaseContinuation3625Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hGheight gamma v _ r w hrcolor y0 y1 y2 y3 y4 r1 r3 a1
      a3 q hy01 hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34 ha1ends ha3ends hproper ha1color
      ha3color hqcolor halpha_beta p1 C1 hqinc0 hqinc4 hqC1 hy1C1 hqa1 hqa3 ha13ne hgamma_alpha
      hgamma_beta hw0 hw1 hw2 hw3 hw4 hrincw hrmiddle hrq hrnotC1 i0 i1 pmax hchangedata phi'
      hproper' hone'
  have hTash' : TashkinovTree G e0 phi' T := by
    simpa [phi', y0, i0] using hchangedata.2.2
  have hglobal' : GlobalMaximumTriple G k e0 phi' T := by
    exact ⟨⟨N.global.1.1, N.global.1.2.1, N.global.1.2.2.1,
      hproper', hone'⟩, hTash', N.global.2.2⟩
  have hbehavior := TwoColorComponentSwapMissingBehavior G phi gamma N.beta
    hgamma_beta hproper (Sum.inl y0)
  have hgamma' : gamma ∈ MissingColors G phi' y1 := by
    exact hbehavior.2.2.1 y1 hy1C1 (by simpa [y1] using N.beta_missing)
  have halpha' : N.alpha ∈ MissingColors G phi' y0 := by
    apply (hbehavior.2.2.2 y0 N.alpha hgamma_alpha.symm halpha_beta).2
    simpa [y0] using N.alpha_missing
  have hqcolor' : phi' q = some gamma := by
    simp [phi', TwoColorComponentSwap, C1, hqC1, hqcolor]
  have alpha_fixed := @helper_alpha_fixed_657 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@halpha_beta) (@hgamma_alpha)
      (@hgamma_beta)
  have ha1color' : phi' a1 = some N.alpha := (alpha_fixed a1).2 ha1color
  have ha3color' : phi' a3 = some N.alpha := (alpha_fixed a3).2 ha3color
  have hrcolor' : phi' r = some gamma := by
    simp [phi', TwoColorComponentSwap, C1, hrnotC1, hrcolor]
  obtain ⟨p2, hp2, hp2support, hp2div, hp2vertices, hp2bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi' T hglobal' N.alpha gamma
      (by simpa [y0] using halpha') (by simpa [y1] using hgamma')
  have hp2bound' : p2.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp2bound
  let H2 := TwoColorIncidenceGraph G phi' N.alpha gamma
  let C2 := TwoColorComponent G phi' N.alpha gamma (Sum.inl y0)
  have hp2support' : {z | z ∈ p2.support} = C2 := by
    simpa [C2, y0] using hp2support
  have hC2root : Sum.inl y0 ∈ C2 := by
    change H2.connectedComponentMk (Sum.inl y0) =
      H2.connectedComponentMk (Sum.inl y0)
    rfl
  have C2_of_adj {x z : Sum V E} (hx : x ∈ C2) (hxz : H2.Adj x z) : z ∈ C2 := by
    change H2.connectedComponentMk x = H2.connectedComponentMk (Sum.inl y0) at hx
    change H2.connectedComponentMk z = H2.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C2 {z : Sum V E} (hz : z ∈ C2) : z ∈ p2.support := by
    exact (Set.ext_iff.mp hp2support' z).mpr hz
  have edge_step_C2 {x : V} {f : E} (hx : Sum.inl x ∈ C2)
      (hxf : Incident G x f)
      (hfc : phi' f = some N.alpha ∨ phi' f = some gamma) :
      Sum.inr f ∈ C2 := by
    apply C2_of_adj hx
    simpa [H2, TwoColorIncidenceGraph] using And.intro hxf hfc
  have vertex_step_C2 {f : E} {x : V} (hf : Sum.inr f ∈ C2)
      (hxf : Incident G x f)
      (hfc : phi' f = some N.alpha ∨ phi' f = some gamma) :
      Sum.inl x ∈ C2 := by
    apply C2_of_adj hf
    simpa [H2, TwoColorIncidenceGraph] using And.intro hxf hfc
  have hqC2 := edge_step_C2 hC2root hqinc0 (Or.inr hqcolor')
  have hy4C2 := vertex_step_C2 hqC2 hqinc4 (Or.inr hqcolor')
  have ha3inc4 : Incident G y4 a3 := by unfold Incident; rw [ha3ends]; simp
  have ha3inc3 : Incident G y3 a3 := by unfold Incident; rw [ha3ends]; simp
  have ha3C2 := edge_step_C2 hy4C2 ha3inc4 (Or.inl ha3color')
  have hy3C2 := vertex_step_C2 ha3C2 ha3inc3 (Or.inl ha3color')
  have hy1C2 : Sum.inl y1 ∈ C2 := by
    have hm := p2.getVert_mem_support p2.length
    rw [p2.getVert_length] at hm
    apply (Set.ext_iff.mp hp2support' _).mp
    simpa [y1] using hm
  have ha1inc1 : Incident G y1 a1 := by unfold Incident; rw [ha1ends]; simp
  have ha1inc2 : Incident G y2 a1 := by unfold Incident; rw [ha1ends]; simp
  have ha1C2 := edge_step_C2 hy1C2 ha1inc1 (Or.inl ha1color')
  have hy2C2 := vertex_step_C2 ha1C2 ha1inc2 (Or.inl ha1color')
  have hrC2 : Sum.inr r ∈ C2 := by
    rcases hrmiddle with h | h
    · exact edge_step_C2 hy2C2 h (Or.inr hrcolor')
    · exact edge_step_C2 hy3C2 h (Or.inr hrcolor')
  have hwC2 := vertex_step_C2 hrC2 hrincw (Or.inr hrcolor')
  have hra1 : r ≠ a1 := by
    intro h
    rw [h, ha1color] at hrcolor
    exact hgamma_alpha (Option.some.inj hrcolor.symm)
  have hra3 : r ≠ a3 := by
    intro h
    rw [h, ha3color] at hrcolor
    exact hgamma_alpha (Option.some.inj hrcolor.symm)
  let M10 : Finset (Sum V E) :=
    {Sum.inl y0, Sum.inl y1, Sum.inl y2, Sum.inl y3, Sum.inl y4,
      Sum.inl w, Sum.inr q, Sum.inr a1, Sum.inr a3, Sum.inr r}
  have hM10card : M10.card = 10 := by
    simp [M10, hy01, hy02, hy03, hy04, hy12, hy13, hy14, hy23, hy24,
      hy34, hqa1, hqa3, ha13ne, Ne.symm hw0, Ne.symm hw1,
      Ne.symm hw2, Ne.symm hw3, Ne.symm hw4, Ne.symm hrq, Ne.symm hra1,
      Ne.symm hra3]
  have hM10sub := @helper_hM10sub_738 (@V) (@E) inferInstance inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@r) (@w) (@p2) (@hC2root)
      (@support_of_C2) (@hqC2) (@hy4C2) (@ha3C2) (@hy3C2) (@hy1C2) (@ha1C2) (@hy2C2) (@hrC2) (@hwC2)
  have hp2lower : 9 ≤ p2.length := by
    have hc := Finset.card_le_card hM10sub
    rw [hM10card, List.toFinset_card_of_nodup hp2.support_nodup,
      p2.length_support] at hc
    omega
  rcases hp2div with ⟨d, hd⟩
  omega

private theorem helper_caseContinuation_3777.{u_1, u_2} :
    helperCaseContinuation3777Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hGheight gamma hgamma g v hgcolor _ r w hrcolor hrends
      y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q hy01 hy02 hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34
      ha1ends ha2ends ha3ends hqends hproper missing_excludes ha1color ha12ne ha2color ha23ne
      ha3color ha3qne hqcolor halpha_beta hv0' hv1' hv2' hv3' hv4' hgends' p1 hp1 hp1div hp1bound
      C1 hC1root support_of_C1 edge_step_C1 vertex_step_C1 hqinc0 hqinc4 hqC1 hy4C1 hy1C1 helem
      hy0T hy1T
  have hgamma_not_missing_y1 : gamma ∉ MissingColors G phi y1 := by
    intro hm
    have hd := helem hy0T hy1T hy01
    exact (Finset.disjoint_left.mp hd) (by simpa [y0] using hgamma) hm
  have hgamma_present_y1 : gamma ∈ PresentColors G phi y1 := by
    simpa [MissingColors] using hgamma_not_missing_y1
  obtain ⟨b, hbinc, hbcolor⟩ : ∃ b : E,
      Incident G y1 b ∧ phi b = some gamma := by
    simpa [PresentColors] using hgamma_present_y1
  have hbC1 : Sum.inr b ∈ C1 :=
    edge_step_C1 hy1C1 hbinc (Or.inl hbcolor)
  have hqa1 := @helper_hqa1_406 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@hy14) (@hy24) (@ha1ends) (@hqends)
  have hqa2 := @SharedFacts.ScheideHeightFiveGammaEdges.hqa2 (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@hy24) (@hy34) (@ha2ends) (@hqends)
  have hqa3 : q ≠ a3 := ha3qne.symm
  have ha13ne : a1 ≠ a3 := by
    intro h
    exact (show r1 ≠ r3 by simp [r1, r3])
      (T.edge_injective (by simpa [a1, a3] using h))
  have hgamma_alpha := @helper_hgamma_alpha_425 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@g) (@v) (@hgcolor) (@hy01)
      (@hy02) (@hy03) (@hy04) (@hy12) (@hy13) (@hy14) (@hy23) (@hy24) (@hy34) (@ha1ends) (@ha2ends)
      (@ha3ends) (@ha1color) (@ha12ne) (@ha2color) (@ha23ne) (@ha3color) (@hv0') (@hv1') (@hv2')
      (@hv3') (@hv4') (@hgends') (@p1) (@hp1) (@hp1div) (@hp1bound) (@hC1root) (@support_of_C1)
      (@edge_step_C1) (@vertex_step_C1) (@hqC1) (@hy4C1) (@hy1C1) (@hqa1) (@hqa2) (@hqa3) (@ha13ne)
  have hgamma_beta : gamma ≠ N.beta := by
    intro h
    exact (missing_excludes (by simpa [y1] using N.beta_missing) hbinc)
      (by simpa [h] using hbcolor)
  have hrends' : G.ends r = s(y2, w) ∨ G.ends r = s(y3, w) := by
    simpa [y2, y3] using hrends
  change w = y0 ∨ w = y1 ∨ w = y2 ∨ w = y3 ∨ w = y4
  by_contra hwtrunk
  push Not at hwtrunk
  rcases hwtrunk with ⟨hw0, hw1, hw2, hw3, hw4⟩
  have ha2inc2 : Incident G y2 a2 := by unfold Incident; rw [ha2ends]; simp
  have ha2inc3 : Incident G y3 a2 := by unfold Incident; rw [ha2ends]; simp
  have hrincw : Incident G w r := by
    rcases hrends' with h | h <;> unfold Incident <;> rw [h] <;> simp
  have hrmiddle := @helper_hrmiddle_523 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@r) (@w) (@hrends')
  have hbq : b ≠ q := by
    intro h
    rw [h, hqcolor] at hbcolor
    exact hgamma_beta (Option.some.inj hbcolor.symm)
  have hba2 : b ≠ a2 := by
    intro h
    rw [h, ha2color] at hbcolor
    exact hgamma_beta (Option.some.inj hbcolor.symm)
  have hrq : r ≠ q := by
    intro h
    rw [h, hqcolor] at hrcolor
    exact hgamma_beta (Option.some.inj hrcolor.symm)
  have hra2 : r ≠ a2 := by
    intro h
    rw [h, ha2color] at hrcolor
    exact hgamma_beta (Option.some.inj hrcolor.symm)
  have hbr := @helper_hbr_549 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@r) (@w) (@hy12) (@hy13) (@b) (@hbinc) (@hrends') (@hw1)
  have middle_too_large := @helper_middle_too_large_561 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@r) (@w)
      (@hrcolor) (@hy01) (@hy02) (@hy03) (@hy04) (@hy12) (@hy13) (@hy14) (@hy23) (@hy24) (@hy34)
      (@ha2color) (@p1) (@hp1) (@hp1div) (@hp1bound) (@hC1root) (@support_of_C1) (@edge_step_C1)
      (@hqC1) (@hy4C1) (@hy1C1) (@b) (@hbC1) (@hqa2) (@hw0) (@hw1) (@hw2) (@hw3) (@hw4) (@ha2inc2)
      (@hrmiddle) (@hbq) (@hba2) (@hrq) (@hra2) (@hbr)
  have hy2notC1 := @helper_hy2notC1_600 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@r) (@w) (@hrcolor) (@ha2color)
      (@edge_step_C1) (@vertex_step_C1) (@ha2inc2) (@ha2inc3) (@hrincw) (@hrmiddle)
      (@middle_too_large)
  have hy3notC1 : Sum.inl y3 ∉ C1 := by
    intro hy3C
    have ha2C := edge_step_C1 hy3C ha2inc3 (Or.inr ha2color)
    exact hy2notC1 (vertex_step_C1 ha2C ha2inc2 (Or.inr ha2color))
  have hwnotC1 := @helper_hwnotC1_614 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@r) (@w) (@hrcolor) (@edge_step_C1)
      (@vertex_step_C1) (@hrincw) (@hrmiddle) (@hy2notC1) (@hy3notC1)
  have hrnotC1 : Sum.inr r ∉ C1 := by
    intro hrC
    rcases hrmiddle with h | h
    · exact hy2notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
    · exact hy3notC1 (vertex_step_C1 hrC h (Or.inl hrcolor))
  have hfixed : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T N.global
  let i0 : Fin (T.length + 1) := ⟨0, by omega⟩
  let i1 : Fin (T.length + 1) := ⟨1, by have := N.height_upper; omega⟩
  obtain ⟨_, pmax, hpmax, hpmaxsupport, hpmaxdiv, hpmaxvertices, hchange⟩ :=
    ScheideMaximalKempePath G k e0 phi T T N.global.1 hfixed N.global.2.1
      i0 i1 (by simp [i0, i1]) gamma N.beta
      (by simpa [i0] using hgamma) (by simpa [i1] using N.beta_missing)
  have hunused : TreeColorUnusedThrough phi T gamma i1 := by
    intro j hjpos hjlt
    simp [i1] at hjlt
    omega
  have hchangedata := hchange hunused
  let phi' := TwoColorComponentSwap G phi gamma N.beta (Sum.inl y0)
  have hproper' : IsProperEdgeColoring G phi' := by
    simpa [phi', y0, i0] using hchangedata.1
  have hone' : IsOneEdgeUncolored phi' e0 := by
    simpa [phi', y0, i0] using hchangedata.2.1
  exact @helper_caseContinuation_3625 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@v) (by
    assumption) (@r) (@w) (@hrcolor) (@hy01) (@hy02) (@hy03) (@hy04) (@hy12) (@hy13) (@hy14)
        (@hy23) (@hy24) (@hy34) (@ha1ends) (@ha3ends) (@hproper) (@ha1color) (@ha3color)
        (@hqcolor) (@halpha_beta) (@p1) (@hqinc0) (@hqinc4) (@hqC1) (@hy1C1) (@hqa1) (@hqa3)
        (@ha13ne) (@hgamma_alpha) (@hgamma_beta) (@hw0) (@hw1) (@hw2) (@hw3) (@hw4) (@hrincw)
        (@hrmiddle) (@hrq) (@hrnotC1) (@pmax) (@hchangedata) (@hproper') (@hone')

private theorem helper_caseContinuation_4022.{u_1, u_2} :
    helperCaseContinuation4022Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight hGheight gamma hgamma g v hgcolor hgends _ hv0 hv1 hv2
      hv3 hv4 _ _ helem hy0T hy1T r w hrcolor hrends y0 y1 y2 y3 y4 r1 r2 r3 a1 a2 a3 q hy01 hy02
      hy03 hy04 hy12 hy13 hy14 hy23 hy24 hy34 ha1ends ha2ends ha3ends hqends hproper
      missing_excludes edge_color_of_closing_support ha1support ha2support ha3support
  have hqsupport : Sum.inr q ∈ N.closingPath.support := by
    exact (N.closingPath_edges q).2 (Or.inl rfl)
  have ha1color := @helper_ha1color_275 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@ha1ends) (@missing_excludes)
      (@edge_color_of_closing_support) (@ha1support)
  have ha1a2 := @helper_ha1a2_285 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@ha1ends) (@ha2ends)
  have ha12ne : a1 ≠ a2 := by
    intro h
    exact (show r1 ≠ r2 by simp [r1, r2])
      (T.edge_injective (by simpa [a1, a2] using h))
  have ha2color : phi a2 = some N.beta := by
    rcases edge_color_of_closing_support a2 ha2support with h | h
    · exact False.elim ((hproper ha12ne ha1a2 ha1color) h)
    · exact h
  have ha2a3 := @helper_ha2a3_299 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@ha2ends) (@ha3ends)
  have ha23ne : a2 ≠ a3 := by
    intro h
    exact (show r2 ≠ r3 by simp [r2, r3])
      (T.edge_injective (by simpa [a2, a3] using h))
  have ha3color : phi a3 = some N.alpha := by
    rcases edge_color_of_closing_support a3 ha3support with h | h
    · exact h
    · exact False.elim ((hproper ha23ne ha2a3 ha2color) h)
  have ha3q := @helper_ha3q_313 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k) (@e0)
      (@phi) (@T) (@N) (@hNheight) (@ha3ends) (@hqends)
  have ha3qne := @SharedFacts.ScheideHeightFiveGammaEdges.ha3qne (@V) (@E) inferInstance
      inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@hy03) (@hy34) (@ha3ends) (@hqends)
  have hqcolor : phi q = some N.beta := by
    rcases edge_color_of_closing_support q hqsupport with h | h
    · exact False.elim ((hproper ha3qne ha3q ha3color) h)
    · exact h
  have halpha_beta := @helper_halpha_beta_330 (@V) (@E) inferInstance inferInstance inferInstance
      (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@ha1ends) (@missing_excludes) (@ha1color)
  have hv0' : v ≠ y0 := by simpa [y0] using hv0
  have hv1' : v ≠ y1 := by simpa [y1] using hv1
  have hv2' : v ≠ y2 := by simpa [y2] using hv2
  have hv3' : v ≠ y3 := by simpa [y3] using hv3
  have hv4' : v ≠ y4 := by simpa [y4] using hv4
  have hgends' : G.ends g = s(y0, v) ∨ G.ends g = s(y1, v) ∨
      G.ends g = s(y2, v) ∨ G.ends g = s(y3, v) ∨
      G.ends g = s(y4, v) := by
    simpa [y0, y1, y2, y3, y4] using hgends
  obtain ⟨p1, hp1, hp1support, hp1div, hp1vertices, hp1bound⟩ :=
    ScheideKempePathHeightBound G k e0 phi T N.global gamma N.beta
      hgamma N.beta_missing
  have hp1bound' : p1.length / 2 + 1 ≤ 5 := by
    simpa [hGheight] using hp1bound
  let H1 := TwoColorIncidenceGraph G phi gamma N.beta
  let C1 := TwoColorComponent G phi gamma N.beta (Sum.inl y0)
  have hp1support' : {z | z ∈ p1.support} = C1 := by
    simpa [C1, y0] using hp1support
  have hC1root : Sum.inl y0 ∈ C1 := by
    change H1.connectedComponentMk (Sum.inl y0) =
      H1.connectedComponentMk (Sum.inl y0)
    rfl
  have C1_of_adj {x z : Sum V E} (hx : x ∈ C1) (hxz : H1.Adj x z) : z ∈ C1 := by
    change H1.connectedComponentMk x = H1.connectedComponentMk (Sum.inl y0) at hx
    change H1.connectedComponentMk z = H1.connectedComponentMk (Sum.inl y0)
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
  have support_of_C1 {z : Sum V E} (hz : z ∈ C1) : z ∈ p1.support := by
    exact (Set.ext_iff.mp hp1support' z).mpr hz
  have edge_step_C1 {x : V} {f : E} (hx : Sum.inl x ∈ C1)
      (hxf : Incident G x f)
      (hfc : phi f = some gamma ∨ phi f = some N.beta) :
      Sum.inr f ∈ C1 := by
    apply C1_of_adj hx
    simpa [H1, TwoColorIncidenceGraph] using And.intro hxf hfc
  have vertex_step_C1 {f : E} {x : V} (hf : Sum.inr f ∈ C1)
      (hxf : Incident G x f)
      (hfc : phi f = some gamma ∨ phi f = some N.beta) :
      Sum.inl x ∈ C1 := by
    apply C1_of_adj hf
    simpa [H1, TwoColorIncidenceGraph] using And.intro hxf hfc
  have hqinc0 : Incident G y0 q := by unfold Incident; rw [hqends]; simp
  have hqinc4 : Incident G y4 q := by unfold Incident; rw [hqends]; simp
  have hqC1 : Sum.inr q ∈ C1 :=
    edge_step_C1 hC1root hqinc0 (Or.inr hqcolor)
  have hy4C1 : Sum.inl y4 ∈ C1 :=
    vertex_step_C1 hqC1 hqinc4 (Or.inr hqcolor)
  have hy1C1 : Sum.inl y1 ∈ C1 := by
    have hm := p1.getVert_mem_support p1.length
    rw [p1.getVert_length] at hm
    apply (Set.ext_iff.mp hp1support' _).mp
    simpa [y1] using hm
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    (ScheideGlobalMaximumOrder G k e0 phi T N.global).2.2.2.1
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    simp [y0, TreeSequenceVertexSet]
  have hy1T : y1 ∈ TreeSequenceVertexSet T := by
    simp [y1, TreeSequenceVertexSet]
  exact @helper_caseContinuation_3777 (@V) (@E) inferInstance inferInstance inferInstance (@G)
      (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@hgamma) (@g) (@v) (@hgcolor)
      (by
    assumption) (@r) (@w) (@hrcolor) (@hrends) (@hy01) (@hy02) (@hy03) (@hy04) (@hy12) (@hy13)
        (@hy14) (@hy23) (@hy24) (@hy34) (@ha1ends) (@ha2ends) (@ha3ends) (@hqends) (@hproper)
        (@missing_excludes) (@ha1color) (@ha12ne) (@ha2color) (@ha23ne) (@ha3color) (@ha3qne)
        (@hqcolor) (@halpha_beta) (@hv0') (@hv1') (@hv2') (@hv3') (@hv4') (@hgends') (@p1) (@hp1)
        (@hp1div) (@hp1bound) (@hC1root) (@support_of_C1) (@edge_step_C1) (@vertex_step_C1)
        (@hqinc0) (@hqinc4) (@hqC1) (@hy4C1) (@hy1C1) (@helem) (@hy0T) (@hy1T)

theorem ScheideHeightFiveGammaEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hNheight : N.height = 5) (hGheight : ScheideGraphHeight G = 5)
    (gamma : Fin k)
    (hgamma : gamma ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (g : E) (v : V) (hgcolor : phi g = some gamma)
    (hgends :
      G.ends g = s(T.vertex ⟨0, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨2, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨3, by have := N.height_upper; omega⟩, v) ∨
      G.ends g = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v))
    (_ : v ∈ TreeSequenceVertexSet T)
    (hv0 : v ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩)
    (hv1 : v ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩)
    (hv2 : v ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩)
    (hv3 : v ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩)
    (hv4 : v ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩) :
    ∃ (f1 f2 f3 : E) (v1 v2 : V),
      G.ends f1 = s(T.vertex ⟨1, by have := N.height_upper; omega⟩, v1) ∧
      G.ends f2 = s(T.vertex ⟨4, by have := N.height_upper; omega⟩, v2) ∧
      G.ends f3 = s(T.vertex ⟨2, by have := N.height_upper; omega⟩,
        T.vertex ⟨3, by have := N.height_upper; omega⟩) ∧
      phi f1 = some gamma ∧ phi f2 = some gamma ∧
      phi f3 = some gamma ∧
      v1 ∈ TreeSequenceVertexSet T ∧ v2 ∈ TreeSequenceVertexSet T ∧
      v1 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v1 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨0, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨1, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨2, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨3, by have := N.height_upper; omega⟩ ∧
      v2 ≠ T.vertex ⟨4, by have := N.height_upper; omega⟩ := by
  classical
  let y0 : V := T.vertex ⟨0, by have := N.height_upper; omega⟩
  let y1 : V := T.vertex ⟨1, by have := N.height_upper; omega⟩
  let y2 : V := T.vertex ⟨2, by have := N.height_upper; omega⟩
  let y3 : V := T.vertex ⟨3, by have := N.height_upper; omega⟩
  let y4 : V := T.vertex ⟨4, by have := N.height_upper; omega⟩
  have hy01 : y0 ≠ y1 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy02 : y0 ≠ y2 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy03 : y0 ≠ y3 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have hy04 : y0 ≠ y4 := by
    intro h
    have := T.vertex_injective h
    simp [] at this
  have horder := ScheideGlobalMaximumOrder G k e0 phi T N.global
  have helem : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.1
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T) :=
    horder.2.2.2.2
  have hy0T : y0 ∈ TreeSequenceVertexSet T := by
    simp [y0, TreeSequenceVertexSet]
  have hy1T : y1 ∈ TreeSequenceVertexSet T := by
    simp [y1, TreeSequenceVertexSet]
  have hy2T : y2 ∈ TreeSequenceVertexSet T := by
    simp [y2, TreeSequenceVertexSet]
  have hy3T : y3 ∈ TreeSequenceVertexSet T := by
    simp [y3, TreeSequenceVertexSet]
  have hy4T : y4 ∈ TreeSequenceVertexSet T := by
    simp [y4, TreeSequenceVertexSet]
  have hgamma0 : gamma ∈ MissingColors G phi y0 := by
    simpa [y0] using hgamma
  have gamma_present := @helper_gamma_present_127 (@V) (@E) inferInstance inferInstance
      inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@helem) (@hy0T)
      (@hgamma0)
  obtain ⟨f1, hf1inc, hf1color⟩ : ∃ f1 : E,
      Incident G y1 f1 ∧ phi f1 = some gamma := by
    simpa [PresentColors] using gamma_present hy1T hy01.symm
  obtain ⟨f2, hf2inc, hf2color⟩ : ∃ f2 : E,
      Incident G y2 f2 ∧ phi f2 = some gamma := by
    simpa [PresentColors] using gamma_present hy2T hy02.symm
  obtain ⟨f3, hf3inc, hf3color⟩ : ∃ f3 : E,
      Incident G y3 f3 ∧ phi f3 = some gamma := by
    simpa [PresentColors] using gamma_present hy3T hy03.symm
  obtain ⟨f4, hf4inc, hf4color⟩ : ∃ f4 : E,
      Incident G y4 f4 ∧ phi f4 = some gamma := by
    simpa [PresentColors] using gamma_present hy4T hy04.symm
  obtain ⟨z1, hf1ends⟩ := Sym2.mem_iff_exists.mp hf1inc
  obtain ⟨z2, hf2ends⟩ := Sym2.mem_iff_exists.mp hf2inc
  obtain ⟨z3, hf3ends⟩ := Sym2.mem_iff_exists.mp hf3inc
  obtain ⟨z4, hf4ends⟩ := Sym2.mem_iff_exists.mp hf4inc
  have middle_no_escape (r : E) (w : V)
      (hrcolor : phi r = some gamma)
      (hrends :
        G.ends r = s(T.vertex ⟨2, by have := N.height_upper; omega⟩, w) ∨
        G.ends r = s(T.vertex ⟨3, by have := N.height_upper; omega⟩, w)) :
      w = T.vertex ⟨0, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨1, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨2, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨3, by have := N.height_upper; omega⟩ ∨
      w = T.vertex ⟨4, by have := N.height_upper; omega⟩ := by
    classical
    let y0 : V := T.vertex ⟨0, by have := N.height_upper; omega⟩
    let y1 : V := T.vertex ⟨1, by have := N.height_upper; omega⟩
    let y2 : V := T.vertex ⟨2, by have := N.height_upper; omega⟩
    let y3 : V := T.vertex ⟨3, by have := N.height_upper; omega⟩
    let y4 : V := T.vertex ⟨4, by have := N.height_upper; omega⟩
    let r1 : Fin T.length := ⟨1, by have := N.height_upper; omega⟩
    let r2 : Fin T.length := ⟨2, by have := N.height_upper; omega⟩
    let r3 : Fin T.length := ⟨3, by have := N.height_upper; omega⟩
    let a1 : E := T.edge r1
    let a2 : E := T.edge r2
    let a3 : E := T.edge r3
    let q : E := N.closingEdge
    have hy01 : y0 ≠ y1 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy02 : y0 ≠ y2 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy03 : y0 ≠ y3 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy04 : y0 ≠ y4 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy12 : y1 ≠ y2 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy13 : y1 ≠ y3 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy14 : y1 ≠ y4 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy23 : y2 ≠ y3 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy24 : y2 ≠ y4 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have hy34 : y3 ≠ y4 := by
      intro h
      have := T.vertex_injective h
      simp [] at this
    have ha1ends : G.ends a1 = s(y1, y2) := by
      simpa [a1, r1, y1, y2, hNheight] using N.trunk_edge_ends r1 (by simp [r1])
        (by simp [r1, hNheight])
    have ha2ends : G.ends a2 = s(y2, y3) := by
      simpa [a2, r2, y2, y3, hNheight] using N.trunk_edge_ends r2 (by simp [r2])
        (by simp [r2, hNheight])
    have ha3ends : G.ends a3 = s(y3, y4) := by
      simpa [a3, r3, y3, y4, hNheight] using N.trunk_edge_ends r3 (by simp [r3])
        (by simp [r3, hNheight])
    have hqends := @SharedFacts.ScheideHeightFiveGammaEdges.hqends (@V) (@E) inferInstance
        inferInstance inferInstance (@G) (@k)
        (@e0) (@phi) (@T) (@N) (@hNheight)
    have hproper : IsProperEdgeColoring G phi := N.global.1.2.2.2.1
    have missing_excludes := @helper_missing_excludes_231 (@V) (@E) inferInstance inferInstance (@G)
        (@k) (@phi)
    have edge_color_of_closing_support (f : E)
        (hf : Sum.inr f ∈ N.closingPath.support) :
        phi f = some N.alpha ∨ phi f = some N.beta := by
      exact @helper_edge_color_of_closing_support_241 (@V) (@E) inferInstance inferInstance
          inferInstance (@G) (@k) (@e0) (@phi) (@T) (@N) (@v) (by
        assumption) (@f) (@hf)
    have ha1support : Sum.inr a1 ∈ N.closingPath.support := by
      apply (N.closingPath_edges a1).2
      exact Or.inr ⟨r1, by simp [r1], by simp [r1, hNheight], rfl⟩
    have ha2support : Sum.inr a2 ∈ N.closingPath.support := by
      apply (N.closingPath_edges a2).2
      exact Or.inr ⟨r2, by simp [r2], by simp [r2, hNheight], rfl⟩
    have ha3support : Sum.inr a3 ∈ N.closingPath.support := by
      apply (N.closingPath_edges a3).2
      exact Or.inr ⟨r3, by simp [r3], by simp [r3, hNheight], rfl⟩
    exact @helper_caseContinuation_4022 (@V) (@E) inferInstance inferInstance inferInstance (@G)
        (@k) (@e0) (@phi) (@T) (@N) (@hNheight) (@hGheight) (@gamma) (@hgamma) (@g) (@v)
        (@hgcolor) (@hgends) (by
      assumption) (@hv0) (@hv1) (@hv2) (@hv3) (@hv4) (@helem) (@hy0T) (@hy1T) (@r) (@w)
          (@hrcolor) (@hrends) (@hy01) (@hy02) (@hy03) (@hy04) (@hy12) (@hy13) (@hy14) (@hy23)
          (@hy24) (@hy34) (@ha1ends) (@ha2ends) (@ha3ends) (@hqends) (@hproper)
          (@missing_excludes) (@edge_color_of_closing_support) (@ha1support) (@ha2support)
          (@ha3support)
  exact @helper_continuation_3161 (@V) (@E) inferInstance inferInstance inferInstance (@G) (@k)
      (@e0) (@phi) (@T) (@N) (@hNheight) (@gamma) (@g) (@v) (@hgcolor) (@hgends) (by
    assumption) (@hv1) (@hv2) (@hv3) (@hv4) (@hclosed) (@hy0T) (@hy1T) (@hy4T) (@hgamma0) (@f1)
        (@hf1inc) (@hf1color) (@f2) (@hf2inc) (@hf2color) (@f3) (@hf3inc) (@hf3color) (@f4)
        (@hf4inc) (@hf4color) (@z1) (@hf1ends) (@z2) (@hf2ends) (@z3) (@hf3ends) (@z4) (@hf4ends)
        (@middle_no_escape)
end GoldbergSeymour

end
