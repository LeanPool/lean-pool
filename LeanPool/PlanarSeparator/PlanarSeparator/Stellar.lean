/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Map

/-!
# The stellar subdivision of a map

The *stellar subdivision* of a map `M` adds a new vertex, the *centre*, inside every face `f`
and joins it to every corner of `f`. Each dart `d` of `M` gives two new darts: the spoke `up d`
from the initial vertex of `d` to the centre of the face of `d`, inserted in the rotation just
before `d`, and its reversal `down d`. The rotation at the centre of a face lists the spokes in
the reverse order of the boundary walk of the face.

Every face of the subdivision is a triangle `old d → up (φ d) → down d` (`old d` being the dart
`d` of `M`), so the faces of the subdivision correspond to the darts of `M`. Counting gives
Euler's formula for the subdivision from that of `M`: the subdivision of a plane map is a plane
map all of whose faces are triangles (`PlanarSeparator.Map.isPlane_stellar`,
`PlanarSeparator.Map.isTriangle_stellar`). The subdivision may have multiple edges (when a vertex
appears several times on the boundary of a face), which is why it is a map and not a rotation
system of a simple graph.
-/

@[expose] public section

namespace PlanarSeparator

open Finset

/-- The darts of the stellar subdivision: the darts of the map and the two darts of each
spoke. -/
inductive StDart (D : Type*) where
  /-- A dart of the original map. -/
  | old (d : D)
  /-- The spoke from the initial vertex of `d` to the centre of the face of `d`. -/
  | up (d : D)
  /-- The spoke from the centre of the face of `d` to the initial vertex of `d`. -/
  | down (d : D)
  deriving DecidableEq

namespace StDart

variable {D : Type*}

/-- The darts of the subdivision as a sum type. -/
def equivSum : StDart D ≃ D ⊕ D ⊕ D where
  toFun
    | old d => .inl d
    | up d => .inr (.inl d)
    | down d => .inr (.inr d)
  invFun
    | .inl d => old d
    | .inr (.inl d) => up d
    | .inr (.inr d) => down d
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | x | x <;> rfl

instance [Fintype D] : Fintype (StDart D) := Fintype.ofEquiv _ equivSum.symm

lemma card [Fintype D] : Fintype.card (StDart D) = 3 * Fintype.card D := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, Fintype.card_sum]
  ring

end StDart

namespace Map

open StDart

variable {D P : Type*} (M : Map D P)

/-- The rotation of the stellar subdivision. -/
def stσ : Equiv.Perm (StDart D) where
  toFun
    | old d => up (M.σ d)
    | up d => old d
    | down d => down (M.φ.symm d)
  invFun
    | old d => up d
    | up d => old (M.σ.symm d)
    | down d => down (M.φ d)
  left_inv x := by cases x <;> simp
  right_inv x := by cases x <;> simp

/-- The reversal of darts of the stellar subdivision. -/
def stα : Equiv.Perm (StDart D) where
  toFun
    | old d => old (M.α d)
    | up d => down d
    | down d => up d
  invFun
    | old d => old (M.α d)
    | up d => down d
    | down d => up d
  left_inv x := by cases x <;> simp [M.α_α]
  right_inv x := by cases x <;> simp [M.α_α]

@[simp] lemma stσ_old (d : D) : M.stσ (old d) = up (M.σ d) := rfl
@[simp] lemma stσ_up (d : D) : M.stσ (up d) = old d := rfl
@[simp] lemma stσ_down (d : D) : M.stσ (down d) = down (M.φ.symm d) := rfl
@[simp] lemma stα_old (d : D) : M.stα (old d) = old (M.α d) := rfl
@[simp] lemma stα_up (d : D) : M.stα (up d) = down d := rfl
@[simp] lemma stα_down (d : D) : M.stα (down d) = up d := rfl

/-- The vertex of a dart of the stellar subdivision: an original vertex, or the centre of a
face. -/
def stVert : StDart D → P ⊕ M.Face
  | old d => .inl (M.vert d)
  | up d => .inl (M.vert d)
  | down d => .inr (M.face d)

lemma stσ_old_pow (n : ℕ) (d : D) : (M.stσ ^ (2 * n)) (old d) = old ((M.σ ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add, Equiv.Perm.mul_apply, ih, pow_two,
      Equiv.Perm.mul_apply]
    simp [pow_succ']

lemma stσ_down_pow (n : ℕ) (d : D) :
    (M.stσ ^ n) (down d) = down ((M.φ⁻¹ ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    rfl

variable [Finite D]

/-- The stellar subdivision of a map. -/
def stellar : Map (StDart D) (P ⊕ M.Face) where
  α := M.stα
  σ := M.stσ
  vert := M.stVert
  α_α x := by cases x <;> simp [M.α_α]
  α_ne x := by cases x <;> simp [M.α_ne]
  vert_σ x := by cases x <;> simp [stVert, M.vert_σ]
  sameCycle x y hxy := by
    classical
    -- old darts at the same vertex
    have hold : ∀ d e : D, M.vert d = M.vert e → M.stσ.SameCycle (old d) (old e) := by
      intro d e h
      obtain ⟨n, hn⟩ := (M.sameCycle d e h).exists_pow_eq'
      exact ⟨((2 * n : ℕ) : ℤ), by rw [zpow_natCast, M.stσ_old_pow, hn.2]⟩
    have hup : ∀ d : D, M.stσ.SameCycle (old (M.σ.symm d)) (up d) := fun d =>
      ⟨1, by simp⟩
    cases x with
    | old d =>
      cases y with
      | old e => exact hold d e (by simpa [stVert] using hxy)
      | up e =>
        exact (hold d _ (by simpa [stVert] using hxy)).trans (hup e)
      | down e => simp [stVert] at hxy
    | up d =>
      cases y with
      | old e => exact (hup d).symm.trans (hold _ e (by simpa [stVert] using hxy))
      | up e => exact (hup d).symm.trans ((hold _ _ (by simpa [stVert] using hxy)).trans (hup e))
      | down e => simp [stVert] at hxy
    | down d =>
      cases y with
      | old e => simp [stVert] at hxy
      | up e => simp [stVert] at hxy
      | down e =>
        have h : M.face d = M.face e := by simpa [stVert] using hxy
        obtain ⟨n, hn⟩ := (Equiv.Perm.sameCycle_inv.2 (M.face_eq_face_iff.1 h)).exists_pow_eq'
        exact ⟨(n : ℤ), by rw [zpow_natCast, M.stσ_down_pow, hn.2]⟩

@[simp] lemma stellar_α (x : StDart D) : M.stellar.α x = M.stα x := rfl
@[simp] lemma stellar_σ (x : StDart D) : M.stellar.σ x = M.stσ x := rfl
@[simp] lemma stellar_vert_old (d : D) : M.stellar.vert (old d) = .inl (M.vert d) := rfl
@[simp] lemma stellar_vert_up (d : D) : M.stellar.vert (up d) = .inl (M.vert d) := rfl
@[simp] lemma stellar_vert_down (d : D) : M.stellar.vert (down d) = .inr (M.face d) := rfl

@[simp] lemma stellar_φ_old (d : D) : M.stellar.φ (old d) = up (M.φ d) := rfl
@[simp] lemma stellar_φ_up (d : D) : M.stellar.φ (up d) = down (M.φ.symm d) := rfl
@[simp] lemma stellar_φ_down (d : D) : M.stellar.φ (down d) = old d := rfl

/-- Every face of the stellar subdivision is a triangle `old d → up (φ d) → down d`. -/
lemma stellar_φ_three (x : StDart D) : M.stellar.φ (M.stellar.φ (M.stellar.φ x)) = x := by
  cases x <;> simp

lemma stellar_face_up (e : D) : M.stellar.face (up e) = M.stellar.face (old (M.φ.symm e)) := by
  rw [← M.stellar.face_φ (old (M.φ.symm e)), stellar_φ_old, Equiv.apply_symm_apply]

lemma stellar_face_down (d : D) : M.stellar.face (down d) = M.stellar.face (old d) := by
  rw [← M.stellar.face_φ (down d), stellar_φ_down]

/-- The stellar subdivision of a map without loops has only triangular faces with three distinct
edges. -/
theorem isTriangle_stellar (hM : ∀ d, M.vert (M.α d) ≠ M.vert d) (x : StDart D) :
    M.stellar.IsTriangle x := by
  have hφ : ∀ d, M.φ d ≠ d := fun d h => hM d (by rw [← M.vert_φ, h])
  have hφ2 : ∀ d, M.σ (M.α d) ≠ d := hφ
  have hφ' : ∀ d, M.φ.symm d ≠ d := fun d h => hφ (M.φ.symm d) (by
    conv_rhs => rw [h]
    simp)
  refine ⟨M.stellar_φ_three x, ?_, ?_, ?_⟩ <;>
  · cases x <;> simp [edge_eq_edge_iff, hφ2, Ne.symm (hφ2 _), Ne.symm (hφ' _)]

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
/-- The faces of the stellar subdivision correspond to the darts of the map. -/
lemma card_stellar_face : Fintype.card M.stellar.Face = Fintype.card D := by
  classical
  symm
  refine Fintype.card_of_bijective (f := fun d => M.stellar.face (old d)) ⟨fun d e h => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (M.stellar.face_eq_face_iff.1 h).exists_nat_pow_eq
    have key : ∀ n : ℕ, (M.stellar.φ ^ n) (old d) = old d ∨
        (M.stellar.φ ^ n) (old d) = up (M.φ d) ∨ (M.stellar.φ ^ n) (old d) = down d := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h | h <;> rw [h] <;> simp
    rcases key n with h' | h' | h' <;> rw [h'] at hn
    · exact StDart.old.inj hn
    · exact absurd hn (by simp)
    · exact absurd hn (by simp)
  · intro F
    obtain ⟨x, rfl⟩ := M.stellar.face_surjective F
    cases x with
    | old d => exact ⟨d, rfl⟩
    | up e => exact ⟨M.φ.symm e, (M.stellar_face_up e).symm⟩
    | down d => exact ⟨d, (M.stellar_face_down d).symm⟩

omit [DecidableEq P] in
/-- The stellar subdivision of a plane map is plane. -/
theorem isPlane_stellar {M : Map D P} (hM : M.IsPlane) : M.stellar.IsPlane where
  exists_dart v := by
    rcases v with v | F
    · obtain ⟨d, hd⟩ := hM.exists_dart v
      exact ⟨old d, by simp [hd]⟩
    · obtain ⟨d, rfl⟩ := M.face_surjective F
      exact ⟨down d, rfl⟩
  connected := by
    set R := fun a b : StDart D => b = M.stellar.σ a ∨ b = M.stellar.α a
    have sσ : ∀ a, R a (M.stσ a) := fun a => Or.inl rfl
    have sα : ∀ a, R a (M.stα a) := fun a => Or.inr rfl
    have hlift : ∀ d e : D, Relation.ReflTransGen R (old d) (old e) := by
      intro d e
      induction hM.connected d e with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b _ hab ih =>
        rcases hab with rfl | rfl
        · exact (ih.tail (sσ (old a))).tail (sσ (up (M.σ a)))
        · exact ih.tail (sα (old a))
    have hto : ∀ x, ∃ d, Relation.ReflTransGen R x (old d) := by
      intro x
      cases x with
      | old d => exact ⟨d, Relation.ReflTransGen.refl⟩
      | up d => exact ⟨d, Relation.ReflTransGen.single (sσ (up d))⟩
      | down d => exact ⟨d, (Relation.ReflTransGen.single (sα (down d))).tail (sσ (up d))⟩
    have hfrom : ∀ x, ∃ d, Relation.ReflTransGen R (old d) x := by
      intro x
      cases x with
      | old d => exact ⟨d, Relation.ReflTransGen.refl⟩
      | up d =>
        refine ⟨M.σ.symm d, ?_⟩
        have := Relation.ReflTransGen.single (sσ (old (M.σ.symm d)))
        simpa using this
      | down d =>
        refine ⟨M.σ.symm d, ?_⟩
        have := (Relation.ReflTransGen.single (sσ (old (M.σ.symm d)))).tail (sα _)
        simpa using this
    intro x y
    obtain ⟨d, hd⟩ := hto x
    obtain ⟨e, he⟩ := hfrom y
    exact hd.trans ((hlift d e).trans he)
  euler := by
    have h1 := M.stellar.card_darts
    have h2 := M.card_darts
    have h3 := M.card_stellar_face
    have h4 : Fintype.card (StDart D) = 3 * Fintype.card D := StDart.card
    have h5 := hM.euler
    rw [Fintype.card_sum]
    omega

end Map

end PlanarSeparator
