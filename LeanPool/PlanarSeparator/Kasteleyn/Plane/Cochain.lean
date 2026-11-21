/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.Kasteleyn.Plane.Map
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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

open Finset SimpleGraph Module

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

lemma ZMod.two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

lemma ZMod.two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

lemma filter_dartEdge_eq (d : G.Dart) :
    ({d' | dartEdge d' = dartEdge d} : Finset G.Dart) = {d, d.symm} := by
  ext d'
  simp [dartEdge_eq_iff]

/-- The sums of a cochain over the fibres of a function `g` on the darts. For `g = Dart.fst`
these are the sums over the darts leaving the vertices; for `g = face`, the sums over the
boundary walks of the faces. -/
def fibreSum {X : Type*} [DecidableEq X] (g : G.Dart → X) :
    (G.edgeSet → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun c x := ∑ d with g d = x, c (dartEdge d)
  map_add' a b := by
    funext x
    simp [sum_add_distrib]
  map_smul' r a := by
    funext x
    simp [mul_sum]

omit [DecidableEq V] in
lemma fibreSum_apply {X : Type*} [DecidableEq X] (g : G.Dart → X) (c : G.edgeSet → ZMod 2)
    (x : X) : fibreSum g c x = ∑ d with g d = x, c (dartEdge d) := rfl

/-- The fibre sums of the indicator of a single edge. -/
lemma fibreSum_single {X : Type*} [DecidableEq X] (g : G.Dart → X) (d : G.Dart) :
    fibreSum g (Pi.single (dartEdge d) 1) = Pi.single (g d) 1 + Pi.single (g d.symm) 1 := by
  funext x
  rw [fibreSum_apply, sum_filter]
  have : ∀ d' : G.Dart, (if g d' = x then (Pi.single (dartEdge d) (1 : ZMod 2) : _ → ZMod 2)
      (dartEdge d') else 0) =
      if dartEdge d' = dartEdge d then (if g d' = x then 1 else 0) else 0 := by
    intro d'
    by_cases h1 : g d' = x <;> by_cases h2 : dartEdge d' = dartEdge d <;> simp [h1, h2]
  rw [sum_congr rfl fun d' _ => this d', ← sum_filter, filter_dartEdge_eq,
    sum_pair (Dart.symm_ne d).symm]
  simp [Pi.single_apply, eq_comm]

/-! ### Functions with total sum zero -/

/-- The sum of the values of a function on a finite type. -/
def sumLin (X : Type*) [Fintype X] : (X → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun p := ∑ x, p x
  map_add' a b := by simp [sum_add_distrib]
  map_smul' r a := by simp [mul_sum]

/-- The functions on a finite type with total sum zero. -/
def sumZero (X : Type*) [Fintype X] : Submodule (ZMod 2) (X → ZMod 2) :=
  LinearMap.ker (sumLin X)

lemma mem_sumZero {X : Type*} [Fintype X] {p : X → ZMod 2} : p ∈ sumZero X ↔ ∑ x, p x = 0 :=
  Iff.rfl

lemma finrank_sumZero {X : Type*} [Fintype X] [Nonempty X] :
    finrank (ZMod 2) (sumZero X) + 1 = Fintype.card X := by
  classical
  have hφ : LinearMap.range (sumLin X) = ⊤ := by
    obtain ⟨x₀⟩ := ‹Nonempty X›
    rw [LinearMap.range_eq_top]
    intro r
    exact ⟨Pi.single x₀ r, by simp [sumLin]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (sumLin X)
  rw [hφ, finrank_top, finrank_self, Module.finrank_fintype_fun_eq_card] at h
  change 1 + finrank (ZMod 2) (sumZero X) = _ at h
  omega

omit [DecidableEq V] in
/-- If the fibres of `g` are connected by the edges, the fibre sums of the cochains are all the
functions with total sum zero. -/
lemma sumZero_le_range_fibreSum {X : Type*} [Fintype X] [DecidableEq X] (g : G.Dart → X)
    (x₀ : X) (hconn : ∀ y, Relation.ReflTransGen (fun a b => ∃ d : G.Dart, g d = a ∧ g d.symm = b)
      x₀ y) :
    sumZero X ≤ LinearMap.range (fibreSum g) := by
  classical
  set R := LinearMap.range (fibreSum g)
  have hpair : ∀ y, Pi.single x₀ (1 : ZMod 2) + Pi.single y 1 ∈ R := by
    intro y
    induction hconn y with
    | refl =>
      convert R.zero_mem
      funext z
      exact ZMod.two_add_self _
    | @tail a b _ hab ih =>
      obtain ⟨d, rfl, rfl⟩ := hab
      have h := R.add_mem ih ⟨_, fibreSum_single g d⟩
      convert h using 1
      funext z
      simp only [Pi.add_apply]
      rw [add_assoc, ← add_assoc (Pi.single (g d) 1 z), ZMod.two_add_self, zero_add]
  intro p hp
  rw [mem_sumZero] at hp
  have hp' : p = ∑ y, p y • (Pi.single x₀ (1 : ZMod 2) + Pi.single y 1) := by
    funext z
    by_cases hz : z = x₀
    · subst hz
      simp [Finset.sum_apply, Pi.single_apply, sum_add_distrib, hp]
    · simp [Finset.sum_apply, Pi.single_apply, hz]
  rw [hp']
  exact R.sum_mem fun y _ => R.smul_mem _ (hpair y)

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
  classical
  have hG := hM.connected
  have hne : Nonempty V := hG.nonempty
  obtain ⟨v₀⟩ := hG.nonempty
  obtain ⟨d₀, -⟩ := hM.exists_dart v₀
  set A := fibreSum (fun d : G.Dart => d.fst)
  -- the closed cochains: dimension at most `E - V + 1`
  have hA : sumZero V ≤ LinearMap.range A := by
    refine sumZero_le_range_fibreSum _ v₀ fun y => ?_
    exact Relation.ReflTransGen.mono (fun a b hab => ⟨⟨(a, b), hab⟩, rfl, rfl⟩) _ _
      ((reachable_iff_reflTransGen _ _).1 (hG.preconnected v₀ y))
  have h1 := LinearMap.finrank_range_add_finrank_ker A
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_mono hA
  have h3 : finrank (ZMod 2) (sumZero V) + 1 = Fintype.card V := finrank_sumZero
  -- the coboundaries: dimension at least `F - 1`
  have h4 := LinearMap.finrank_range_add_finrank_ker M.cob
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have hker : LinearMap.ker M.cob ≤ Submodule.span (ZMod 2) {fun _ => 1} := by
    intro h hh
    rw [Submodule.mem_span_singleton]
    refine ⟨h (M.face d₀), funext fun f => ?_⟩
    simp [M.cob_eq_zero_iff hG (LinearMap.mem_ker.1 hh) (M.face d₀) f]
  have h5 := (Submodule.finrank_mono hker).trans (finrank_span_le_card _)
  rw [Set.toFinset_singleton, card_singleton] at h5
  -- coboundaries are closed
  have hle : LinearMap.range M.cob ≤ LinearMap.ker A := by
    rintro _ ⟨h, rfl⟩
    exact M.fibreSum_fst_cob h
  have heq : LinearMap.range M.cob = LinearMap.ker A := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have := hM.euler
    rw [edgeFinset_card] at this
    omega
  have hcZ : c ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker]
    funext v
    exact hc v
  rw [← heq] at hcZ
  obtain ⟨h, hh⟩ := hcZ
  exact ⟨h, fun d => by rw [← hh, cob_dartEdge]⟩

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
