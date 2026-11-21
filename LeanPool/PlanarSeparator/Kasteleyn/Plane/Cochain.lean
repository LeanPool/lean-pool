/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Cochain

/-!
# Cochains modulo 2 on a rotation system

A *cochain* (modulo 2) on a graph `G` is a function `c : G.edgeSet → ZMod 2`, that is, a set of
edges. For a rotation system `M` on `G` we consider

* the sums of `c` over the darts leaving each vertex: `c` is *closed* (a cycle of the graph, in
  the sense of the cycle space) when they all vanish, i.e. when every vertex has even degree in
  the set of edges of `c`;
* the sums of `c` over the boundary walk of each face;
* the *coboundary* of a function `h` on the faces, which takes on each edge the sum of the values
  of `h` on the two sides of the edge.

Every coboundary is closed. The main result, `Kasteleyn.RotationSystem.exists_face_cochain`, is
the converse for plane graphs: on a connected rotation system satisfying Euler's formula every
closed cochain is a coboundary. This is the combinatorial form of the fact that the first
homology of the sphere vanishes; it is the separation property of plane graphs used below (a
cycle of the graph splits the faces into two classes, its *inside* and its *outside*). The proof
is a dimension count: the coboundaries form a space of dimension `F - 1`, the closed cochains a
space of dimension at most `E - V + 1`, and Euler's formula says these agree.

We also prove (`Kasteleyn.RotationSystem.exists_cochain_faceSum`) that on any connected
rotation system the face sums of the cochains can be prescribed arbitrarily on all faces but one.

## References

* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §4.1.
-/

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The edge of a dart, as an element of the edge set. -/
def dartEdge (d : G.Dart) : G.edgeSet := ⟨d.edge, d.edge_mem⟩

@[simp] lemma dartEdge_symm (d : G.Dart) : dartEdge d.symm = dartEdge d :=
  Subtype.ext d.edge_symm

lemma dartEdge_eq_iff {d d' : G.Dart} : dartEdge d = dartEdge d' ↔ d = d' ∨ d = d'.symm := by
  rw [dartEdge, dartEdge, Subtype.mk.injEq]
  exact dart_edge_eq_iff d d'

lemma dartEdge_surjective : Function.Surjective (dartEdge : G.Dart → G.edgeSet) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b => exact ⟨⟨(a, b), he⟩, rfl⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma filter_dartEdge_eq (d : G.Dart) :
    ({d' | dartEdge d' = dartEdge d} : Finset G.Dart) = {d, d.symm} := by
  ext d'
  simp [dartEdge_eq_iff]

/-- The sums of a cochain over the fibres of a function `g` on the darts. For `g = Dart.fst`
these are the sums over the darts leaving the vertices; for `g = face`, the sums over the
boundary walks of the faces. -/
def fibreSum {X : Type*} [DecidableEq X] (g : G.Dart → X) :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) :=
  dartFibreSum dartEdge g

omit [DecidableEq V] in
lemma fibreSum_apply {X : Type*} [DecidableEq X] (g : G.Dart → X) (c : G.edgeSet → ZMod 2)
    (x : X) : fibreSum g c x = ∑ d with g d = x, c (dartEdge d) := rfl

/-- The fibre sums of the indicator of a single edge. -/
lemma fibreSum_single {X : Type*} [DecidableEq X] (g : G.Dart → X) (d : G.Dart) :
    fibreSum g (Pi.single (dartEdge d) 1) = Pi.single (g d) 1 + Pi.single (g d.symm) 1 :=
  dartFibreSum_single dartEdge g (Dart.symm_ne d).symm (filter_dartEdge_eq d)

omit [DecidableEq V] in
/-- If the fibres of `g` are connected by the edges, the fibre sums of the cochains are all the
functions with total sum zero. -/
lemma sumZero_le_range_fibreSum {X : Type*} [Fintype X] [DecidableEq X] (g : G.Dart → X)
    (x₀ : X) (hconn : ∀ y, Relation.ReflTransGen (fun a b => ∃ d : G.Dart, g d = a ∧ g d.symm = b)
      x₀ y) :
    sumZero X ≤ LinearMap.range (fibreSum g) := by
  classical
  refine sumZero_le_range_of_reachable (fibreSum g) x₀ hconn ?_
  rintro _ _ ⟨d, rfl, rfl⟩
  exact ⟨_, fibreSum_single g d⟩

/-! ### Coboundaries -/

namespace RotationSystem

variable (M : RotationSystem G)

/-- The coboundary of a function on the faces: on each edge, the sum of its values on the two
sides of the edge. -/
def cob : (M.Face → ZMod 2) →ₗ[ZMod 2] (G.edgeSet → ZMod 2) where
  toFun h e := ∑ d with dartEdge d = e, h (M.face d)
  map_add' a b := by
    funext e
    simp [sum_add_distrib]
  map_smul' r a := by
    funext e
    simp [mul_sum]

lemma cob_dartEdge (h : M.Face → ZMod 2) (d : G.Dart) :
    M.cob h (dartEdge d) = h (M.face d) + h (M.face d.symm) := by
  change ∑ d' with dartEdge d' = dartEdge d, h (M.face d') = _
  rw [filter_dartEdge_eq, sum_pair (Dart.symm_ne d).symm]

/-- A sum over the darts leaving a vertex is invariant under the rotation. -/
lemma sum_fst_rot {β : Type*} [AddCommMonoid β] (v : V) (φ : G.Dart → β) :
    ∑ d with d.fst = v, φ (M.rot d) = ∑ d with d.fst = v, φ d :=
  sum_equiv M.rot (fun d => by simp [M.fst_rot]) (fun _ _ => rfl)

/-- Coboundaries are closed. -/
lemma fibreSum_fst_cob (h : M.Face → ZMod 2) :
    fibreSum (fun d : G.Dart => d.fst) (M.cob h) = 0 := by
  funext v
  rw [fibreSum_apply, Pi.zero_apply]
  simp only [cob_dartEdge, sum_add_distrib]
  rw [← sum_congr rfl fun d _ => congrArg h (M.face_rot d), M.sum_fst_rot v (fun d => h (M.face d)),
    ZMod.two_add_self]

/-- A function on faces with zero coboundary is constant. -/
lemma cob_eq_zero_iff (hG : G.Connected) {h : M.Face → ZMod 2} (h0 : M.cob h = 0)
    (f f' : M.Face) : h f = h f' :=
  M.face_const hG (fun d => (ZMod.two_eq_of_add_eq_zero
    (by rw [← cob_dartEdge, h0, Pi.zero_apply])).symm) f f'

/-- **Closed cochains on a plane graph are coboundaries.** If every vertex has even degree in the
set of edges `c`, then the faces can be split into two classes (the zeros and the ones of `h`)
such that the edges of `c` are exactly the edges separating the two classes. -/
theorem exists_face_cochain {M : RotationSystem G} (hM : M.IsPlane) (c : G.edgeSet → ZMod 2)
    (hc : ∀ v, ∑ d with d.fst = v, c (dartEdge d) = 0) :
    ∃ h : M.Face → ZMod 2, ∀ d, h (M.face d) + h (M.face d.symm) = c (dartEdge d) := by
  let R := PlanarSeparator.Map.ofRotation M
  have hR : R.IsPlane := PlanarSeparator.Map.isPlane_ofRotation hM
  obtain ⟨h, hh⟩ := hR.exists_face_cochain (fun d => c (dartEdge d))
    (fun d => by
      change c (dartEdge d.symm) = c (dartEdge d)
      rw [dartEdge_symm]) hc
  exact ⟨h, hh⟩

/-- **Prescribing face sums.** On a connected rotation system, for every function `b` on the
faces and every face `f₀` there is a set of edges `x` whose number of darts on the boundary walk
of every face `f ≠ f₀` has the parity `b f`. -/
theorem exists_cochain_faceSum (hG : G.Connected) (b : M.Face → ZMod 2) (f₀ : M.Face) :
    ∃ x : G.edgeSet → ZMod 2, ∀ f ≠ f₀, ∑ d with M.face d = f, x (dartEdge d) = b f := by
  classical
  obtain ⟨d₀, hd₀⟩ := M.face_surjective f₀
  have hconn : ∀ f, Relation.ReflTransGen
      (fun a b => ∃ d : G.Dart, M.face d = a ∧ M.face d.symm = b) f₀ f := by
    intro f
    obtain ⟨d, rfl⟩ := M.face_surjective f
    refine M.dart_induction hG (P := fun d => Relation.ReflTransGen _ f₀ (M.face d))
      (fun d hd => ?_) (fun d hd => hd.tail ⟨d, rfl, rfl⟩) (by rw [hd₀]) d
    rw [face_rot]
    exact hd.tail ⟨d, rfl, rfl⟩
  have hR := sumZero_le_range_fibreSum M.face f₀ hconn
  set b' := Function.update b f₀ (∑ f ∈ univ.erase f₀, b f)
  have hb' : b' ∈ sumZero M.Face := by
    rw [mem_sumZero, ← add_sum_erase _ _ (mem_univ f₀)]
    simp only [b', Function.update_self]
    rw [sum_congr rfl fun f hf => Function.update_of_ne (ne_of_mem_erase hf) _ _,
      ZMod.two_add_self]
  obtain ⟨x, hx⟩ := hR hb'
  refine ⟨x, fun f hf => ?_⟩
  have := congrFun hx f
  rw [fibreSum_apply] at this
  rw [this]
  exact Function.update_of_ne hf _ _

end RotationSystem

end Kasteleyn
