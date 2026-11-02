/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Tutte
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
/-!

Imported from [jtraverso/tutte-f-factor](https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorGadget.lean), registered as PALOMAR-2026-10-18-000005. The original proof is retained; module paths and imports are adapted for this collection.

# Tutte's gadget for the f-factor theorem

For a graph `G` and `f : V → ℕ` we build the graph `FFactor.gadget G f` whose vertices are the
darts of `G` ("outer" vertices) together with `deg v − f v` "inner" vertices for every `v`.
A perfect matching of the gadget yields an f-factor of `G` (`FFactor.exists_factor_of_matching`).
-/

@[expose] public section

open Finset SimpleGraph

namespace FFactor

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (f : V → ℕ)

open Classical in
/-- Vertices of the gadget: darts of `G` and `deg v − f v` inner vertices for each `v`. -/
abbrev GV := G.Dart ⊕ (Σ v : V, Fin (G.degree v - f v))

/-- Adjacency in the gadget. -/
def gadgetAdj : GV G f → GV G f → Prop
  | .inl d, .inl d' => d' = d.symm
  | .inl d, .inr p => d.fst = p.1
  | .inr p, .inl d => d.fst = p.1
  | .inr _, .inr _ => False

/-- Tutte's gadget. -/
noncomputable def gadget : SimpleGraph (GV G f) where
  Adj := gadgetAdj G f
  symm := ⟨by
    intro x y h
    rcases x with d | p <;> rcases y with d' | p' <;> simp only [gadgetAdj] at h ⊢
    · rw [h, Dart.symm_symm]
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro x h
    rcases x with d | p <;> simp only [gadgetAdj] at h
    exact Dart.symm_ne _ h.symm⟩

@[simp] theorem gadget_adj_inl_inl {d d' : G.Dart} :
    (gadget G f).Adj (.inl d) (.inl d') ↔ d' = d.symm := Iff.rfl
open Classical in
@[simp] theorem gadget_adj_inl_inr {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)} :
    (gadget G f).Adj (.inl d) (.inr p) ↔ d.fst = p.1 := Iff.rfl
open Classical in
@[simp] theorem gadget_adj_inr_inl {d : G.Dart} {p : Σ v : V, Fin (G.degree v - f v)} :
    (gadget G f).Adj (.inr p) (.inl d) ↔ d.fst = p.1 := Iff.rfl
open Classical in
@[simp] theorem gadget_adj_inr_inr {p q : Σ v : V, Fin (G.degree v - f v)} :
    ¬ (gadget G f).Adj (.inr p) (.inr q) := id

variable {G f}

open Classical in
/-- A perfect matching of the gadget gives an f-factor of `G`. -/
theorem exists_factor_of_matching (hf : ∀ v, f v ≤ G.degree v) (M : (gadget G f).Subgraph)
    (hM : M.IsPerfectMatching) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ v, #{u | H.Adj v u} = f v := by
  classical
  rw [Subgraph.isPerfectMatching_iff] at hM
  obtain ⟨H, hH⟩ : ∃ H : SimpleGraph V, ∀ u w, H.Adj u w ↔
      ∃ h : G.Adj u w, M.Adj (.inl ⟨(u, w), h⟩) (.inl ⟨(w, u), h.symm⟩) :=
    ⟨{ Adj := fun u w => ∃ h : G.Adj u w, M.Adj (.inl ⟨(u, w), h⟩) (.inl ⟨(w, u), h.symm⟩)
       symm := ⟨fun u w ⟨h, h'⟩ => ⟨h.symm, h'.symm⟩⟩
       loopless := ⟨fun u ⟨h, _⟩ => G.loopless.irrefl u h⟩ }, fun _ _ => Iff.rfl⟩
  refine ⟨H, fun u w h => ((hH u w).mp h).1, fun v => ?_⟩
  have huniq : ∀ x y z, M.Adj x y → M.Adj x z → y = z := fun x y z h1 h2 =>
    (hM x).unique h1 h2
  set D : Finset G.Dart := {d | d.fst = v}
  have hD : #D = G.degree v := G.dart_fst_fiber_card_eq_degree v
  have hsplit := card_filter_add_card_filter_not
    (s := D) (fun d => M.Adj (.inl d) (.inl d.symm))
  -- darts matched to their reverse correspond to the `H`-neighbours of `v`
  have h1 : #{d ∈ D | M.Adj (.inl d) (.inl d.symm)} = #{u | H.Adj v u} := by
    apply card_bij (fun d _ => d.snd)
    · rintro ⟨⟨a, b⟩, hab⟩ hd
      simp only [D, mem_filter, mem_univ, true_and] at hd ⊢
      obtain ⟨rfl, hd2⟩ := hd
      exact (hH _ _).mpr ⟨hab, hd2⟩
    · intro d1 hd1 d2 hd2 h
      simp only [D, mem_filter, mem_univ, true_and] at hd1 hd2
      exact Dart.ext _ _ (Prod.ext (hd1.1.trans hd2.1.symm) h)
    · intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu
      obtain ⟨h, hM'⟩ := (hH _ _).mp hu
      exact ⟨⟨(v, u), h⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, rfl⟩, hM'⟩, rfl⟩
  -- the other darts correspond to the inner vertices of `v`
  have hex : ∀ i : Fin (G.degree v - f v), ∃ d : G.Dart, M.Adj (.inr ⟨v, i⟩) (.inl d) := by
    intro i
    obtain ⟨y, hy, -⟩ := hM (.inr ⟨v, i⟩)
    rcases y with d | q
    · exact ⟨d, hy⟩
    · exact absurd (M.adj_sub hy) (gadget_adj_inr_inr G f)
  have h2 : #(univ : Finset (Fin (G.degree v - f v))) =
      #{d ∈ D | ¬ M.Adj (.inl d) (.inl d.symm)} := by
    apply card_bij (fun i _ => Classical.choose (hex i))
    · intro i _
      have hi := Classical.choose_spec (hex i)
      have hfst : (Classical.choose (hex i)).fst = v := M.adj_sub hi
      simp only [D, mem_filter, mem_univ, true_and]
      refine ⟨hfst, fun h => ?_⟩
      have := huniq _ _ _ hi.symm h
      cases this
    · intro i _ j _ hij
      have hi := Classical.choose_spec (hex i)
      have hj := Classical.choose_spec (hex j)
      rw [hij] at hi
      have := huniq _ _ _ hi.symm hj.symm
      simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
      exact this
    · intro d hd
      simp only [D, mem_filter, mem_univ, true_and] at hd
      obtain ⟨y, hy, -⟩ := hM (.inl d)
      rcases y with d' | ⟨w, i⟩
      · have : d' = d.symm := M.adj_sub hy
        subst this
        exact absurd hy hd.2
      · have hw : d.fst = w := M.adj_sub hy
        have hvw : v = w := hd.1.symm.trans hw
        subst hvw
        refine ⟨i, mem_univ _, ?_⟩
        have hi := Classical.choose_spec (hex i)
        have := huniq _ _ _ hi hy.symm
        simpa using this
  rw [card_univ, Fintype.card_fin] at h2
  have := hf v
  have hs : #{d ∈ D | M.Adj (.inl d) (.inl d.symm)} + #{d ∈ D | ¬ M.Adj (.inl d) (.inl d.symm)} =
      #D := hsplit
  rw [h1, ← h2, hD] at hs
  omega

end FFactor
