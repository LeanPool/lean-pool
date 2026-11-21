/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.Kasteleyn.Plane.Map

/-!
# Combinatorial maps

A *combinatorial map* is given by a finite set of darts `D` with a fixed-point-free involution
`α` (reversal of darts) and a permutation `σ` (the rotation at the vertices), together with a
labelling `vert : D → P` of the darts by vertices such that the darts with a given label form a
single cycle of `σ`. Its edges are the orbits `{d, α d}` of `α`, and its faces are the cycles of
the face permutation `φ d = σ (α d)`. Unlike rotation systems of simple graphs
(`Kasteleyn.RotationSystem`), maps may have loops and multiple edges; this is needed for the
constructions on maps used below (the stellar subdivision of a map adds an edge from the centre
of a face to each corner of the face).

A map is *plane* if every vertex carries a dart, the darts are connected through `σ` and `α`, and
Euler's formula `V + F = E + 2` holds. Every plane rotation system of a simple graph defines a
plane map (`PlanarSeparator.Map.ofRotation`).

## Main definitions

* `PlanarSeparator.Map D P`: a combinatorial map with darts `D` and vertices `P`.
* `PlanarSeparator.Map.φ`, `PlanarSeparator.Map.Face`, `PlanarSeparator.Map.face`: the face
  permutation, the faces, the face of a dart.
* `PlanarSeparator.Map.Edge`, `PlanarSeparator.Map.edge`: the edges.
* `PlanarSeparator.Map.IsPlane`: plane maps.
* `PlanarSeparator.Map.ofRotation`: the map of a rotation system of a simple graph.

## References

* J. Edmonds, *A combinatorial representation for polyhedral surfaces*, Notices Amer. Math. Soc.
  7 (1960), 646.
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press (2001), §3.2.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

/-- A combinatorial map with darts `D` and vertices `P`. -/
structure Map (D : Type*) (P : Type*) where
  /-- The reversal of darts. -/
  α : Equiv.Perm D
  /-- The rotation of the darts around their vertex. -/
  σ : Equiv.Perm D
  /-- The vertex at which a dart starts. -/
  vert : D → P
  α_α : ∀ d, α (α d) = d
  α_ne : ∀ d, α d ≠ d
  vert_σ : ∀ d, vert (σ d) = vert d
  sameCycle : ∀ d d', vert d = vert d' → σ.SameCycle d d'

namespace Map

variable {D P : Type*} (M : Map D P)

attribute [simp] Map.vert_σ

/-- The face permutation: after a dart `d`, the boundary walk of its face continues with the
successor of `α d` in the rotation at the head of `d`. -/
def φ : Equiv.Perm D := M.α.trans M.σ

@[simp] lemma φ_apply (d : D) : M.φ d = M.σ (M.α d) := rfl

@[simp] lemma φ_symm_σ_α (d : D) : M.φ.symm (M.σ (M.α d)) = d := M.φ.symm_apply_apply d

@[simp] lemma σ_α_φ_symm (d : D) : M.σ (M.α (M.φ.symm d)) = d := M.φ.apply_symm_apply d

lemma vert_φ (d : D) : M.vert (M.φ d) = M.vert (M.α d) := M.vert_σ _

@[simp] lemma vert_σ_pow (n : ℕ) (d : D) : M.vert ((M.σ ^ n) d) = M.vert d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, M.vert_σ, ih]

@[simp] lemma vert_σ_symm (d : D) : M.vert (M.σ.symm d) = M.vert d := by
  conv_rhs => rw [← M.σ.apply_symm_apply d]
  rw [M.vert_σ]

lemma α_injective : Function.Injective M.α := M.α.injective

/-- The faces: the cycles of the face permutation. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.φ)

/-- The face of a dart. -/
def face (d : D) : M.Face := Quotient.mk _ d

lemma face_surjective : Function.Surjective M.face := Quotient.mk_surjective

lemma face_eq_face_iff {d d' : D} : M.face d = M.face d' ↔ M.φ.SameCycle d d' :=
  Quotient.eq

lemma face_φ (d : D) : M.face (M.φ d) = M.face d :=
  M.face_eq_face_iff.2 (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))

@[simp] lemma face_φ_symm (d : D) : M.face (M.φ.symm d) = M.face d := by
  conv_rhs => rw [← M.φ.apply_symm_apply d]
  rw [face_φ]

/-- The face following the dart `σ d` is the face of `α d`. -/
@[simp] lemma face_σ (d : D) : M.face (M.σ d) = M.face (M.α d) := by
  rw [← M.face_φ (M.α d), φ_apply, M.α_α]

/-- The edges: the orbits `{d, α d}` of the reversal. -/
def Edge : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.α)

/-- The edge of a dart. -/
def edge (d : D) : M.Edge := Quotient.mk _ d

lemma edge_surjective : Function.Surjective M.edge := Quotient.mk_surjective

lemma sameCycle_α_iff {d d' : D} : M.α.SameCycle d d' ↔ d' = d ∨ d' = M.α d := by
  constructor
  · rintro ⟨k, hk⟩
    have h2 : M.α ^ (2 : ℤ) = 1 := by
      ext d
      simp [sq, M.α_α]
    have hk' : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hk, hk', h, add_zero, zpow_mul, h2, one_zpow, Equiv.Perm.one_apply]
    · right
      rw [← hk, hk', h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp⟩

lemma edge_eq_edge_iff {d d' : D} : M.edge d = M.edge d' ↔ d' = d ∨ d' = M.α d :=
  Quotient.eq.trans M.sameCycle_α_iff

@[simp] lemma edge_α (d : D) : M.edge (M.α d) = M.edge d :=
  (M.edge_eq_edge_iff.2 (Or.inr rfl)).symm

/-- The darts are connected through the rotation and the reversal. -/
def Connected : Prop :=
  ∀ d d' : D, Relation.ReflTransGen (fun a b => b = M.σ a ∨ b = M.α a) d d'

/-- **Induction over darts.** In a connected map, a property of darts which is preserved by the
rotation and by the reversal holds for every dart if it holds for one. -/
theorem Connected.induction {M : Map D P} (hM : M.Connected) {p : D → Prop}
    (hσ : ∀ d, p d → p (M.σ d)) (hα : ∀ d, p d → p (M.α d)) {d₀ : D} (h₀ : p d₀) (d : D) :
    p d := by
  induction hM d₀ d with
  | refl => exact h₀
  | tail _ hab ih =>
    rcases hab with rfl | rfl
    · exact hσ _ ih
    · exact hα _ ih

/-- In a connected map, a function on faces which takes the same value on the two sides of
every edge is constant. -/
theorem Connected.face_const {M : Map D P} (hM : M.Connected) {β : Type*} {g : M.Face → β}
    (hg : ∀ d, g (M.face (M.α d)) = g (M.face d)) (f f' : M.Face) : g f = g f' := by
  obtain ⟨d, rfl⟩ := M.face_surjective f
  obtain ⟨d', rfl⟩ := M.face_surjective f'
  refine hM.induction (p := fun x => g (M.face d) = g (M.face x)) (fun x hx => ?_)
    (fun x hx => ?_) rfl d'
  · rw [face_σ, hg, hx]
  · rw [hg, hx]

section Fintype

variable [Fintype D] [DecidableEq D]

instance : DecidableEq M.Face :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.φ)

instance : Fintype M.Face :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.φ)

instance : DecidableEq M.Edge :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.α)

instance : Fintype M.Edge :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.α)

lemma filter_edge_eq (d : D) : ({d' | M.edge d' = M.edge d} : Finset D) = {d, M.α d} := by
  ext d'
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  rw [eq_comm, M.edge_eq_edge_iff]

/-- Every edge has two darts. -/
theorem card_darts : Fintype.card D = 2 * Fintype.card M.Edge := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := M.edge) (t := univ) (fun _ _ => mem_univ _),
    mul_comm, ← smul_eq_mul, ← card_univ, ← sum_const]
  refine sum_congr rfl fun e _ => ?_
  obtain ⟨d, rfl⟩ := M.edge_surjective e
  rw [filter_edge_eq, card_pair (M.α_ne d).symm]

omit [DecidableEq D] [Fintype D] in
/-- Two darts at the same vertex are related by a power of the rotation. -/
lemma exists_σ_pow_eq [Finite D] {d d' : D} (h : M.vert d = M.vert d') :
    ∃ n : ℕ, (M.σ ^ n) d = d' :=
  (M.sameCycle d d' h).exists_nat_pow_eq

omit [DecidableEq D] [Fintype D] in
/-- If the face permutation has period three at `δ`, then the darts of the face of `δ` are
`δ`, `φ δ` and `φ (φ δ)`. -/
lemma eq_of_face_eq_of_φ_three [Finite D] {δ : D} (h3 : M.φ (M.φ (M.φ δ)) = δ) {d : D}
    (hd : M.face d = M.face δ) : d = δ ∨ d = M.φ δ ∨ d = M.φ (M.φ δ) := by
  classical
  obtain ⟨n, hn⟩ := (M.face_eq_face_iff.1 hd).symm.exists_nat_pow_eq
  subst hn
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases ih (M.face_eq_face_iff.2 (Equiv.Perm.SameCycle.symm ⟨n, by simp⟩)) with
      h | h | h <;> rw [h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl h3

/-- The face of `δ` is a triangle with three distinct edges. -/
structure IsTriangle (δ : D) : Prop where
  φ_three : M.φ (M.φ (M.φ δ)) = δ
  edge_ne₁ : M.edge (M.φ δ) ≠ M.edge δ
  edge_ne₂ : M.edge (M.φ (M.φ δ)) ≠ M.edge δ
  edge_ne₃ : M.edge (M.φ (M.φ δ)) ≠ M.edge (M.φ δ)

variable [Fintype P] [DecidableEq P]

/-- A map is *plane* if every vertex carries a dart, the darts are connected, and Euler's formula
`V + F = E + 2` holds. -/
structure IsPlane : Prop where
  exists_dart : ∀ v : P, ∃ d : D, M.vert d = v
  connected : M.Connected
  euler : Fintype.card P + Fintype.card M.Face = Fintype.card M.Edge + 2

end Fintype

/-! ### The map of a rotation system -/

section Rotation

variable {V : Type*} {G : SimpleGraph V}

/-- The map of a rotation system of a simple graph: the darts of the graph, with the reversal of
darts and the rotation of the rotation system. -/
def ofRotation (R : Kasteleyn.RotationSystem G) : Map G.Dart V where
  α := Kasteleyn.dartRev G
  σ := R.rot
  vert d := d.fst
  α_α d := SimpleGraph.Dart.symm_symm d
  α_ne d := SimpleGraph.Dart.symm_ne d
  vert_σ := R.fst_rot
  sameCycle := R.sameCycle_of_fst_eq

variable (R : Kasteleyn.RotationSystem G)

@[simp] lemma ofRotation_α (d : G.Dart) : (ofRotation R).α d = d.symm := rfl

@[simp] lemma ofRotation_σ (d : G.Dart) : (ofRotation R).σ d = R.rot d := rfl

@[simp] lemma ofRotation_vert (d : G.Dart) : (ofRotation R).vert d = d.fst := rfl

/-- The map of a rotation system has no loops. -/
lemma ofRotation_vert_α_ne (d : G.Dart) : (ofRotation R).vert ((ofRotation R).α d) ≠
    (ofRotation R).vert d :=
  d.adj.ne.symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The map of a plane rotation system is plane. -/
theorem isPlane_ofRotation {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) :
    (ofRotation R).IsPlane where
  exists_dart := hR.exists_dart
  connected d d' := R.dart_induction hR.connected
    (P := fun x => Relation.ReflTransGen (fun a b => b = (ofRotation R).σ a ∨
      b = (ofRotation R).α a) d x)
    (fun x hx => hx.tail (Or.inl rfl)) (fun x hx => hx.tail (Or.inr rfl))
    Relation.ReflTransGen.refl d'
  euler := by
    have h1 := (ofRotation R).card_darts
    have h2 := G.dart_card_eq_twice_card_edges
    have h3 : Fintype.card (ofRotation R).Face = Fintype.card R.Face :=
      Fintype.card_congr (Equiv.refl _)
    have := hR.euler
    omega

end Rotation

end Map

end PlanarSeparator
