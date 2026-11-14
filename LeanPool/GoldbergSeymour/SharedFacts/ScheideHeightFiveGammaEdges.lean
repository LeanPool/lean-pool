/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

/-!
# Shared facts for ScheideHeightFiveGammaEdges

These interfaces and proofs are shared across the imported proof branches.
Extracted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12 during the Lean Pool port.
-/

@[expose] public section

namespace GoldbergSeymour.SharedFacts.ScheideHeightFiveGammaEdges

open scoped Sym2

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hqendsStatement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
          G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
      let y0 : V := T.vertex (⟨(0 : ℕ),
      have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
          : ¬(0 : ℕ) < T.length + (1 : ℕ)) ↦
      by omega
      ⟩ : Fin (T.length + (1 : ℕ)));
      let y4 : V := T.vertex (⟨(4 : ℕ),
      have this : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a
          : ¬(4 : ℕ) < T.length + (1 : ℕ)) ↦
      by omega
      ⟩ : Fin (T.length + (1 : ℕ)));
      let q : E := N.closingEdge; G.ends q = s(y4, y0)

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev ha3qneStatement.{u_1, u_2} : Prop :=
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
      let q : E := N.closingEdge; y0 ≠ y3 → y3 ≠ y4 → G.ends a3 = s(y3, y4) → G.ends q = s(y4, y0) →
          a3 ≠ q

/-- Dependent interface shared by the proof branches, so its assumptions stay synchronized. -/
abbrev hqa2Statement.{u_1, u_2} : Prop :=
  open scoped Classical in
      ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
          LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
          G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hNheight : N.height = (5 : ℕ)),
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
      let q : E := N.closingEdge; y2 ≠ y4 → y3 ≠ y4 → G.ends a2 = s(y2, y3) → G.ends q = s(y4, y0) →
          q ≠ a2

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hqends.{u_1, u_2} : hqendsStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y4 q
  have hlast : N.lastIndex = ⟨4, by have := N.height_upper; omega⟩ := by
    apply Fin.ext
    have := N.lastIndex_height
    simp
    rw [hNheight] at this
    omega
  simpa [q, y0, y4, hlast] using N.closing_ends

/-- A common proof used by the branches of this transport or construction argument. -/
theorem ha3qne.{u_1, u_2} : ha3qneStatement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y3 y4 r3 a3 q hy03 hy34 ha3ends hqends h
  have hpairs : s(y3, y4) = s(y4, y0) := by
    rw [← ha3ends, h, hqends]
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hy34 hd.1
  · exact hy03 hs.1.symm

/-- A common proof used by the branches of this transport or construction argument. -/
theorem hqa2.{u_1, u_2} : hqa2Statement.{u_1, u_2} := by
  classical
  intro V E _ _ _ G k e0 phi T N hNheight y0 y2 y3 y4 r2 a2 q hy24 hy34 ha2ends hqends h
  have hpairs : s(y4, y0) = s(y2, y3) := by
    rw [← hqends, h, ha2ends]
  rcases Sym2.eq_iff.mp hpairs with hd | hs
  · exact hy24 hd.1.symm
  · exact hy34 hs.1.symm

end GoldbergSeymour.SharedFacts.ScheideHeightFiveGammaEdges

end
