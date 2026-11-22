/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.FlagSystem

/-!
# The orientation double cover of a flag system

The orientation double cover of a flag system `G` on `D` has darts `D × Bool`, with
`adj i (d, b) = (adj i d, !b)`. It is always orientable
(`GMap.isOrientable_orientationDoubleCover`), and, for a nonempty flag system with no dart fixed
by any `adj i`, it is connected exactly when `G` is connected and not orientable
(`GMap.isConnected_orientationDoubleCover_iff`), which is the connectedness criterion of
Weichsel for the bipartite double cover of the flag graph.

## References

* S. Wilson, *Maniplexes: Part 1: maps, polytopes, symmetry and operators*, Symmetry 4 (2012),
  265–275, §5, p. 270.
* P. M. Weichsel, *The Kronecker product of graphs*, Proc. Amer. Math. Soc. 13 (1962), 47–52,
  Theorem 1.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

namespace GMap

variable {n : ℕ} {D : Type*} (G : GMap n D)

/-- The orientation double cover: darts `D × Bool`, with `adj i (d, b) = (adj i d, !b)`. -/
def orientationDoubleCover : GMap n (D × Bool) where
  adj i := (G.adj i).prodCongr (Function.Involutive.toPerm not Bool.not_not)
  involutive i p := Prod.ext (G.involutive i p.1) (Bool.not_not p.2)
  commute_of_far i j h := by
    unfold Commute SemiconjBy
    refine Equiv.ext fun p => Prod.ext ?_ rfl
    exact congrArg (fun σ : Perm D => σ p.1) (G.commute_of_far i j h).eq

@[simp]
theorem orientationDoubleCover_adj (i : Fin (n + 1)) (p : D × Bool) :
    G.orientationDoubleCover.adj i p = (G.adj i p.1, !p.2) := rfl

theorem orientationDoubleCover_flagGraph_adj {p q : D × Bool} :
    G.orientationDoubleCover.flagGraph.Adj p q ↔ ∃ i, G.adj i p.1 = q.1 ∧ q.2 = !p.2 := by
  change (p ≠ q ∧ ∃ i, (G.adj i p.1, !p.2) = q) ↔ _
  constructor
  · rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl, rfl⟩
  · rintro ⟨i, h1, h2⟩
    refine ⟨fun h => ?_, i, Prod.ext h1 h2.symm⟩
    rw [h] at h2
    simp at h2

/-- The orientation double cover is orientable, coloured by the second coordinate. -/
theorem isOrientable_orientationDoubleCover : G.orientationDoubleCover.IsOrientable := by
  refine ⟨SimpleGraph.Coloring.mk (fun p => if p.2 then 1 else 0) fun {p q} h => ?_⟩
  obtain ⟨_, h2⟩ := (G.orientationDoubleCover_flagGraph_adj).1 h |>.choose_spec
  rcases p with ⟨d, b⟩
  rcases q with ⟨e, c⟩
  simp only at h2
  subst h2
  cases b <;> simp

/-- The exchange of the two sheets of the double cover. -/
def sheetSwap : G.orientationDoubleCover.flagGraph ≃g G.orientationDoubleCover.flagGraph where
  toEquiv := (Equiv.refl D).prodCongr (Function.Involutive.toPerm not Bool.not_not)
  map_rel_iff' {p q} := by
    simp only [orientationDoubleCover_flagGraph_adj]
    simp [Function.Involutive.toPerm]

theorem reachable_sheetSwap {p q : D × Bool}
    (h : G.orientationDoubleCover.flagGraph.Reachable p q) :
    G.orientationDoubleCover.flagGraph.Reachable (p.1, !p.2) (q.1, !q.2) :=
  h.map G.sheetSwap.toHom

/-- A path of the flag graph of `G` lifts to the double cover from either sheet. -/
theorem exists_reachable_lift {d e : D} (h : G.flagGraph.Reachable d e) (b : Bool) :
    ∃ c, G.orientationDoubleCover.flagGraph.Reachable (d, b) (e, c) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ⟨b, SimpleGraph.Reachable.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨_, i, rfl⟩ := hbc
    refine ⟨!c, hc.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact (G.orientationDoubleCover_flagGraph_adj).2 ⟨i, rfl, rfl⟩

/-- Without fixed darts, the projection of the double cover is a map of flag graphs. -/
def coverProj (hfix : ∀ i d, G.adj i d ≠ d) :
    G.orientationDoubleCover.flagGraph →g G.flagGraph where
  toFun := Prod.fst
  map_rel' {p q} h := by
    obtain ⟨i, h1, _⟩ := (G.orientationDoubleCover_flagGraph_adj).1 h
    exact ⟨fun h' => hfix i p.1 (h1.trans h'.symm), i, h1⟩

private theorem decide_eq_not_of_ne {a b : Fin 2} (h : a ≠ b) :
    decide (b = 0) = !decide (a = 0) := by
  revert a b; decide

/-- A two-colouring of `G` is an invariant of the components of the double cover. -/
private theorem reachable_invariant (hfix : ∀ i d, G.adj i d ≠ d)
    (C : G.flagGraph.Coloring (Fin 2)) {p q : D × Bool}
    (h : G.orientationDoubleCover.flagGraph.Reachable p q) :
    xor (decide (C p.1 = 0)) p.2 = xor (decide (C q.1 = 0)) q.2 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail x y _ hbc ih =>
    rw [ih]
    have hval := C.valid ((G.coverProj hfix).map_rel hbc)
    obtain ⟨_, _, h2⟩ := (G.orientationDoubleCover_flagGraph_adj).1 hbc
    change C x.1 ≠ C y.1 at hval
    rw [h2, decide_eq_not_of_ne hval]
    cases decide (C _ = 0) <;> cases Prod.snd _ <;> rfl

/-- A nonempty flag system with no fixed dart has a connected orientation double cover exactly
when it is connected and not orientable. -/
theorem isConnected_orientationDoubleCover_iff [Nonempty D] (hfix : ∀ i d, G.adj i d ≠ d) :
    G.orientationDoubleCover.IsConnected ↔ G.IsConnected ∧ ¬ G.IsOrientable := by
  classical
  simp only [isConnected_iff_preconnected_flagGraph]
  obtain ⟨d₀⟩ := ‹Nonempty D›
  set H := G.orientationDoubleCover.flagGraph
  constructor
  · intro hH
    refine ⟨fun d e => (hH (d, false) (e, false)).map (G.coverProj hfix), ?_⟩
    rintro ⟨C⟩
    have := G.reachable_invariant hfix C (hH (d₀, false) (d₀, true))
    cases decide (C d₀ = 0) <;> simp at this
  · rintro ⟨hG, hno⟩
    -- the two lifts of `d₀` are joined, otherwise reachability from `(d₀, false)` colours `G`
    have hsw : H.Reachable (d₀, false) (d₀, true) := by
      by_contra hne
      have key : ∀ d, (H.Reachable (d₀, false) (d, false) ↔
          ¬ H.Reachable (d₀, false) (d, true)) := by
        intro d
        constructor
        · intro hf ht
          have h1 := G.reachable_sheetSwap hf
          exact hne (ht.trans h1.symm)
        · intro ht
          obtain ⟨c, hc⟩ := G.exists_reachable_lift (hG d₀ d) false
          cases c
          · exact hc
          · exact absurd hc ht
      apply hno
      refine ⟨SimpleGraph.Coloring.mk
        (fun d => if H.Reachable (d₀, false) (d, false) then 0 else 1) fun {d e} hde => ?_⟩
      obtain ⟨_, i, rfl⟩ := hde
      have hl : ∀ b, H.Reachable (d, b) (G.adj i d, !b) := fun b =>
        SimpleGraph.Adj.reachable ((G.orientationDoubleCover_flagGraph_adj).2 ⟨i, rfl, rfl⟩)
      by_cases hd : H.Reachable (d₀, false) (d, false)
      · have : H.Reachable (d₀, false) (G.adj i d, true) := hd.trans (hl false)
        simpa [hd] using fun h => (key _).1 h this
      · have hdt := (not_congr (key d)).1 hd
        rw [not_not] at hdt
        have : H.Reachable (d₀, false) (G.adj i d, false) := hdt.trans (hl true)
        simp [hd, this]
    have hall : ∀ p : D × Bool, H.Reachable (d₀, false) p := by
      rintro ⟨d, b⟩
      obtain ⟨c, hc⟩ := G.exists_reachable_lift (hG d₀ d) false
      have hc' := hsw.trans (G.reachable_sheetSwap hc)
      cases b <;> cases c
      · exact hc
      · exact hc'
      · exact hc'
      · exact hc
    exact fun p q => (hall p).symm.trans (hall q)

end GMap

end LeanPool.PseudolineArrangements
