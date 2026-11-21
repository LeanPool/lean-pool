/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Map
public import LeanPool.PlanarSeparator.Kasteleyn.Plane.Cochain

/-!
# Closed cochains on a plane map are face coboundaries

A *cochain* (modulo 2) on a map is a function on its edges, that is, a set of edges. It is
*closed* when every vertex has even degree in it (a loop counting twice). The *coboundary* of a
function `h` on the faces takes on each edge the sum of the values of `h` on its two sides.

For a plane map every closed cochain is a coboundary
(`PlanarSeparator.Map.IsPlane.exists_face_cochain`): a set of edges of even degree at every
vertex splits the faces into two classes, such that the edges of the set are exactly the edges
between the two classes. This is the combinatorial form of the Jordan curve theorem. The proof
is a dimension count: the coboundaries form a space of dimension at least `F - 1`, the closed
cochains a space of dimension at most `E - V + 1`, and Euler's formula says these agree. (For
rotation systems of simple graphs this is `Kasteleyn.RotationSystem.exists_face_cochain`.)

## References

* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §4.1.
-/

@[expose] public section

namespace PlanarSeparator

open Finset Module

namespace Map

variable {D P : Type*} (M : Map D P) [Fintype D] [DecidableEq D]

/-- The sums of a cochain over the fibres of a function `g` on the darts. -/
def fibreSum {X : Type*} [DecidableEq X] (g : D → X) :
    (M.Edge → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun c x := ∑ d with g d = x, c (M.edge d)
  map_add' a b := by
    funext x
    simp [sum_add_distrib]
  map_smul' r a := by
    funext x
    simp [mul_sum]

omit [DecidableEq D] in
lemma fibreSum_apply {X : Type*} [DecidableEq X] (g : D → X) (c : M.Edge → ZMod 2) (x : X) :
    M.fibreSum g c x = ∑ d with g d = x, c (M.edge d) := rfl

/-- The fibre sums of the indicator of a single edge. -/
lemma fibreSum_single {X : Type*} [DecidableEq X] (g : D → X) (d : D) :
    M.fibreSum g (Pi.single (M.edge d) 1) = Pi.single (g d) 1 + Pi.single (g (M.α d)) 1 := by
  funext x
  rw [fibreSum_apply, sum_filter]
  have : ∀ d' : D, (if g d' = x then (Pi.single (M.edge d) (1 : ZMod 2) : _ → ZMod 2)
      (M.edge d') else 0) =
      if M.edge d' = M.edge d then (if g d' = x then 1 else 0) else 0 := by
    intro d'
    by_cases h1 : g d' = x <;> by_cases h2 : M.edge d' = M.edge d <;> simp [h1, h2]
  rw [sum_congr rfl fun d' _ => this d', ← sum_filter, filter_edge_eq,
    sum_pair (M.α_ne d).symm]
  simp [Pi.single_apply, eq_comm]

omit [DecidableEq D] in
/-- If the fibres of `g` are connected by the edges, the fibre sums of the cochains are all the
functions with total sum zero. -/
lemma sumZero_le_range_fibreSum {X : Type*} [Fintype X] [DecidableEq X] (g : D → X)
    (x₀ : X) (hconn : ∀ y, Relation.ReflTransGen (fun a b => ∃ d : D, g d = a ∧ g (M.α d) = b)
      x₀ y) :
    Kasteleyn.sumZero X ≤ LinearMap.range (M.fibreSum g) := by
  classical
  set R := LinearMap.range (M.fibreSum g)
  have hpair : ∀ y, Pi.single x₀ (1 : ZMod 2) + Pi.single y 1 ∈ R := by
    intro y
    induction hconn y with
    | refl =>
      convert R.zero_mem
      funext z
      exact Kasteleyn.ZMod.two_add_self _
    | @tail a b _ hab ih =>
      obtain ⟨d, rfl, rfl⟩ := hab
      have h := R.add_mem ih ⟨_, M.fibreSum_single g d⟩
      convert h using 1
      funext z
      simp only [Pi.add_apply]
      rw [add_assoc, ← add_assoc (Pi.single (g d) 1 z), Kasteleyn.ZMod.two_add_self, zero_add]
  intro p hp
  rw [Kasteleyn.mem_sumZero] at hp
  have hp' : p = ∑ y, p y • (Pi.single x₀ (1 : ZMod 2) + Pi.single y 1) := by
    funext z
    by_cases hz : z = x₀
    · subst hz
      simp [Finset.sum_apply, Pi.single_apply, sum_add_distrib, hp]
    · simp [Finset.sum_apply, Pi.single_apply, hz]
  rw [hp']
  exact R.sum_mem fun y _ => R.smul_mem _ (hpair y)

/-- The coboundary of a function on the faces: on each edge, the sum of its values on the two
sides of the edge. -/
def cob : (M.Face → ZMod 2) →ₗ[ZMod 2] (M.Edge → ZMod 2) where
  toFun h e := ∑ d with M.edge d = e, h (M.face d)
  map_add' a b := by
    funext e
    simp [sum_add_distrib]
  map_smul' r a := by
    funext e
    simp [mul_sum]

lemma cob_edge (h : M.Face → ZMod 2) (d : D) :
    M.cob h (M.edge d) = h (M.face d) + h (M.face (M.α d)) := by
  change ∑ d' with M.edge d' = M.edge d, h (M.face d') = _
  rw [filter_edge_eq, sum_pair (M.α_ne d).symm]

omit [DecidableEq D] in
/-- A sum over the darts at a vertex is invariant under the rotation. -/
lemma sum_vert_σ {β : Type*} [AddCommMonoid β] [DecidableEq P] (v : P) (g : D → β) :
    ∑ d with M.vert d = v, g (M.σ d) = ∑ d with M.vert d = v, g d :=
  sum_equiv M.σ (fun d => by simp [M.vert_σ]) (fun _ _ => rfl)

/-- Coboundaries are closed. -/
lemma fibreSum_vert_cob [DecidableEq P] (h : M.Face → ZMod 2) :
    M.fibreSum M.vert (M.cob h) = 0 := by
  funext v
  rw [fibreSum_apply, Pi.zero_apply]
  simp only [cob_edge, sum_add_distrib]
  rw [← sum_congr rfl fun d _ => congrArg h (M.face_σ d), M.sum_vert_σ v (fun d => h (M.face d)),
    Kasteleyn.ZMod.two_add_self]

omit [Fintype D] [DecidableEq D] in
/-- The vertices of a connected map are connected through the edges. -/
lemma Connected.reach_vert {M : Map D P} (hM : M.Connected) (d₀ d : D) :
    Relation.ReflTransGen (fun a b => ∃ d' : D, M.vert d' = a ∧ M.vert (M.α d') = b)
      (M.vert d₀) (M.vert d) := by
  induction hM d₀ d with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hab ih =>
    rcases hab with rfl | rfl
    · rwa [M.vert_σ]
    · exact ih.tail ⟨a, rfl, rfl⟩

variable [Fintype P] [DecidableEq P]

variable {M}

/-- **Closed cochains on a plane map are coboundaries.** If every vertex has even degree in the
set of edges `c`, then the faces can be split into two classes (the zeros and the ones of `h`)
such that the edges of `c` are exactly the edges separating the two classes. -/
theorem IsPlane.exists_face_cochain_edge (hM : M.IsPlane) (c : M.Edge → ZMod 2)
    (hc : ∀ v, ∑ d with M.vert d = v, c (M.edge d) = 0) :
    ∃ h : M.Face → ZMod 2, ∀ d, h (M.face d) + h (M.face (M.α d)) = c (M.edge d) := by
  classical
  have hG := hM.connected
  by_cases hD : IsEmpty D
  · exact ⟨0, fun d => hD.elim d⟩
  rw [not_isEmpty_iff] at hD
  obtain ⟨d₀⟩ := hD
  set A := M.fibreSum M.vert
  have hA : Kasteleyn.sumZero P ≤ LinearMap.range A := by
    refine M.sumZero_le_range_fibreSum _ (M.vert d₀) fun y => ?_
    obtain ⟨d, rfl⟩ := hM.exists_dart y
    exact hG.reach_vert d₀ d
  have hne : Nonempty P := ⟨M.vert d₀⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker A
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := Submodule.finrank_mono hA
  have h3 : finrank (ZMod 2) (Kasteleyn.sumZero P) + 1 = Fintype.card P :=
    Kasteleyn.finrank_sumZero
  have h4 := LinearMap.finrank_range_add_finrank_ker M.cob
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have hker : LinearMap.ker M.cob ≤ Submodule.span (ZMod 2) {fun _ => 1} := by
    intro h hh
    rw [Submodule.mem_span_singleton]
    refine ⟨h (M.face d₀), funext fun f => ?_⟩
    have hconst : ∀ f f', h f = h f' := hG.face_const fun d => by
      have := congrFun (LinearMap.mem_ker.1 hh) (M.edge d)
      rw [cob_edge, Pi.zero_apply] at this
      exact (Kasteleyn.ZMod.two_eq_of_add_eq_zero this).symm
    simp [hconst (M.face d₀) f]
  have h5 := (Submodule.finrank_mono hker).trans (finrank_span_le_card _)
  rw [Set.toFinset_singleton, card_singleton] at h5
  have hle : LinearMap.range M.cob ≤ LinearMap.ker A := by
    rintro _ ⟨h, rfl⟩
    exact M.fibreSum_vert_cob h
  have heq : LinearMap.range M.cob = LinearMap.ker A := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have := hM.euler
    omega
  have hcZ : c ∈ LinearMap.ker A := by
    rw [LinearMap.mem_ker]
    funext v
    exact hc v
  rw [← heq] at hcZ
  obtain ⟨h, hh⟩ := hcZ
  exact ⟨h, fun d => by rw [← hh, cob_edge]⟩

/-- **Closed cochains on a plane map are coboundaries**, for cochains given as functions on the
darts which take the same value on the two darts of each edge. -/
theorem IsPlane.exists_face_cochain (hM : M.IsPlane) (c : D → ZMod 2)
    (hcα : ∀ d, c (M.α d) = c d) (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) :
    ∃ h : M.Face → ZMod 2, ∀ d, h (M.face d) + h (M.face (M.α d)) = c d := by
  let c' : M.Edge → ZMod 2 := Quotient.lift c fun a b hab => by
    rcases M.sameCycle_α_iff.1 hab with rfl | rfl
    · rfl
    · exact (hcα a).symm
  have hc' : ∀ d, c' (M.edge d) = c d := fun _ => rfl
  obtain ⟨h, hh⟩ := hM.exists_face_cochain_edge c' (fun v => by simp only [hc']; exact hc v)
  exact ⟨h, fun d => (hh d).trans (hc' d)⟩

end Map

end PlanarSeparator
