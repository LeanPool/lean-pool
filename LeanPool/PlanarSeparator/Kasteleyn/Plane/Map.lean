/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.Kasteleyn.Spec

/-!
# Rotation systems and plane graphs

A *rotation system* on a simple graph `G` is a permutation `rot` of the darts (oriented edges)
of `G` which, for every vertex `v`, permutes the darts leaving `v` cyclically: `rot d` leaves the
same vertex as `d`, and any two darts leaving the same vertex lie in the same cycle of `rot`.
Together with the reversal of darts `d ↦ d.symm` this is a *combinatorial map*: its vertices are
the cycles of `rot` (the vertices of `G`), its edges are the pairs `{d, d.symm}` (the edges of `G`),
and its *faces* are the cycles of the face permutation
`faceNext d = rot d.symm`.
Thus the boundary walk of a face follows a dart `d` to its head `v` and continues with the
successor of `d.symm` in the rotation at `v`. If `rot` lists the darts at each vertex
counterclockwise, the face lies on the right of each of its darts, so that the boundary of every
bounded face is traversed clockwise.

Every embedding of a connected graph in an oriented closed surface determines a rotation system
(the counterclockwise order of the edges at each vertex), and conversely every rotation system of
a connected graph is induced by an embedding in an oriented surface, unique up to homeomorphism,
whose faces are the cycles of `faceNext`. The surface is the sphere exactly when Euler's formula
`V - E + F = 2` holds. A rotation system of a connected graph satisfying Euler's formula is
therefore the combinatorial form of an embedding of the graph in the plane; this is the
definition of a plane graph used here (`Kasteleyn.RotationSystem.IsPlane`).

## Main definitions (in `Kasteleyn/Spec.lean`)

* `Kasteleyn.RotationSystem G`: a rotation system on `G`.
* `Kasteleyn.RotationSystem.faceNext`, `Kasteleyn.RotationSystem.Face`,
  `Kasteleyn.RotationSystem.face`: the face permutation, the type of faces, the face of a dart.
* `Kasteleyn.RotationSystem.IsPlane`: `G` is connected and `V - E + F = 2`.

## Main results

* `Kasteleyn.RotationSystem.dart_induction`: in a connected graph, a property of darts which is
  preserved by `rot` and by reversal holds for all darts if it holds for one.
* `Kasteleyn.RotationSystem.IsPlane.exists_dart`: in a plane graph every vertex has a dart.

## References

* J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices Amer. Math. Soc.
  7 (1960), 646.
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001),
  §3.2 and §4.1.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

@[simp] lemma dartRev_apply (d : G.Dart) : dartRev G d = d.symm := rfl

namespace RotationSystem

variable (M : RotationSystem G)

attribute [simp] RotationSystem.fst_rot

@[simp] lemma fst_rot_pow (n : ℕ) (d : G.Dart) : ((M.rot ^ n) d).fst = d.fst := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, M.fst_rot, ih]

@[simp] lemma fst_rot_symm (d : G.Dart) : (M.rot.symm d).fst = d.fst := by
  conv_rhs => rw [← M.rot.apply_symm_apply d]
  rw [M.fst_rot]

@[simp] lemma faceNext_apply (d : G.Dart) : M.faceNext d = M.rot d.symm := rfl

lemma fst_faceNext (d : G.Dart) : (M.faceNext d).fst = d.snd := by
  simp

lemma face_surjective : Function.Surjective M.face := Quotient.mk_surjective

lemma face_eq_face_iff {d d' : G.Dart} : M.face d = M.face d' ↔ M.faceNext.SameCycle d d' :=
  Quotient.eq

lemma face_faceNext (d : G.Dart) : M.face (M.faceNext d) = M.face d :=
  M.face_eq_face_iff.2 (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))

/-- The face following the dart `rot d` is the face of `d.symm`: the corner between `d` and
`rot d` at their common vertex. -/
@[simp] lemma face_rot (d : G.Dart) : M.face (M.rot d) = M.face d.symm := by
  rw [← M.face_faceNext d.symm, faceNext_apply, Dart.symm_symm]

section Finite

variable [Finite V]

/-- Two darts leaving the same vertex are related by a power of `rot`. -/
lemma exists_rot_pow_eq {d d' : G.Dart} (h : d.fst = d'.fst) : ∃ n : ℕ, (M.rot ^ n) d = d' := by
  classical
  let := Fintype.ofFinite V
  exact (M.sameCycle_of_fst_eq d d' h).exists_nat_pow_eq

/-- **Induction over darts.** In a connected graph, a property of darts which is preserved by the
rotation and by reversal holds for every dart if it holds for one. -/
theorem dart_induction (hG : G.Connected) {P : G.Dart → Prop}
    (hrot : ∀ d, P d → P (M.rot d)) (hsymm : ∀ d, P d → P d.symm) {d₀ : G.Dart} (h₀ : P d₀)
    (d : G.Dart) : P d := by
  have hvert : ∀ d d' : G.Dart, d.fst = d'.fst → P d → P d' := by
    intro d d' h hd
    obtain ⟨n, rfl⟩ := M.exists_rot_pow_eq h
    clear h
    induction n with
    | zero => exact hd
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hrot _ ih
  have hreach : Relation.ReflTransGen G.Adj d₀.fst d.fst :=
    (reachable_iff_reflTransGen _ _).1 (hG.preconnected _ _)
  have key : ∀ v, Relation.ReflTransGen G.Adj d₀.fst v → ∃ d : G.Dart, d.fst = v ∧ P d := by
    intro v hv
    induction hv with
    | refl => exact ⟨d₀, rfl, h₀⟩
    | @tail a b _ hab ih =>
      obtain ⟨d', hd', hP⟩ := ih
      refine ⟨(⟨(a, b), hab⟩ : G.Dart).symm, rfl, hsymm _ (hvert _ _ hd' hP)⟩
  obtain ⟨d', hd', hP⟩ := key _ hreach
  exact hvert _ _ hd' hP

/-- In a connected graph, a function on faces which takes the same value on the two sides of
every edge is constant. -/
theorem face_const (hG : G.Connected) {α : Type*} {g : M.Face → α}
    (hg : ∀ d, g (M.face d.symm) = g (M.face d)) (f f' : M.Face) : g f = g f' := by
  obtain ⟨d, rfl⟩ := M.face_surjective f
  obtain ⟨d', rfl⟩ := M.face_surjective f'
  refine M.dart_induction hG (P := fun x => g (M.face d) = g (M.face x)) (fun x hx => ?_)
    (fun x hx => ?_) rfl d'
  · rw [face_rot, hg, hx]
  · rw [hg, hx]

end Finite

section Fintype

variable [Fintype V] [DecidableRel G.Adj] [DecidableEq V]

/-- In a plane graph every vertex has a dart; in particular there are at least two vertices. -/
theorem IsPlane.exists_dart {M : RotationSystem G} (hM : M.IsPlane) (v : V) :
    ∃ d : G.Dart, d.fst = v := by
  by_contra hv
  push Not at hv
  have hsub : ∀ u, u = v := by
    intro u
    have h : Relation.ReflTransGen G.Adj v u :=
      (reachable_iff_reflTransGen _ _).1 (hM.connected.preconnected _ _)
    rcases h.cases_head with h | ⟨c, hvc, -⟩
    · exact h.symm
    · exact absurd rfl (hv ⟨(v, c), hvc⟩)
  have hD : IsEmpty G.Dart := ⟨fun d => d.adj.ne ((hsub _).trans (hsub _).symm)⟩
  have hF : IsEmpty M.Face := ⟨fun f => by
    obtain ⟨d, -⟩ := M.face_surjective f
    exact hD.false d⟩
  have hE : #G.edgeFinset = 0 := by
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro e he
    rw [mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h a b => exact hD.false ⟨(a, b), he⟩
  have hV : Fintype.card V = 1 := Fintype.card_eq_one_iff.2 ⟨v, hsub⟩
  have := hM.euler
  rw [hV, hE, Fintype.card_eq_zero] at this
  omega

end Fintype

end RotationSystem

end Kasteleyn
