/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1DualEdges
public import LeanPool.ApollonianSuperharmonic.P3776T1WalkMapProperties

-- [TABLET NODE: P3776T1DualEdgesExist]

/-!
# P3776T1DualEdgesExist

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DualEdgesProof

private theorem pair_spec :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b), first a b hab ≠ second a b hab ∧ (∃ (i
        : Fin (3 : ℕ)), P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i =
        b) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i :
        Fin (3 : ℕ)), P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab := by
  classical
  intro ι P first second a b hab
  rcases Classical.choose_spec (Classical.choose_spec
    (P.plane.every_edge_two_faces a b hab)) with
    ⟨hne, ⟨ha, hb⟩, ⟨hc, hd⟩, hu⟩
  exact ⟨hne, ha, hb, hc, hd, hu⟩

private theorem midpoint_reverse :
    ∀ (p : List GaussianInt), (p ≠ []) → (P3776T1WalkMap p ⟨1 / 2, by norm_num⟩ =
        P3776T1WalkMap p.reverse ⟨1 / 2, by norm_num⟩) := by
  classical
  intro p hp
  obtain ⟨_, _, _, hrev, _, _⟩ := P3776T1WalkMapProperties p hp
  let t : Set.Icc (0 : Real) 1 := ⟨1 / 2, by norm_num⟩
  have ht : t = ⟨1 - (t : Real), by constructor <;> norm_num⟩ := by
    apply Subtype.ext
    norm_num [t]
  have heq : P3776T1WalkMap p t =
      P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> norm_num⟩ :=
    congrArg (P3776T1WalkMap p) ht
  exact heq.trans (hrev t).symm

private theorem other_spec :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
        (second a b hab) (first a b hab)
    (∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b), first a b hab ≠ second a b hab ∧ (∃ i,
        P.plane.faceVertex (first a b hab) i = a) ∧ (∃ i, P.plane.faceVertex (first a b hab) i =
        b) ∧ (∃ i, P.plane.faceVertex (second a b hab) i = a) ∧ (∃ i, P.plane.faceVertex (second
        a b hab) i = b) ∧ ∀ h : P.plane.Face, ((∃ i, P.plane.faceVertex h i = a) ∧ (∃ i,
        P.plane.faceVertex h i = b)) → h = first a b hab ∨ h = second a b hab) → (∀ (f :
            P.plane.Face), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b), (∃ (i : Fin (3 :
        ℕ)), P.plane.faceVertex f i = a) → (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = b) →
        other f a b hab ≠ f ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = a) ∧
        ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = b) := by
  classical
  intro ι P first second other pair_spec f a b hab hfa hfb
  have hp := pair_spec a b hab
  have hf := hp.2.2.2.2.2 f ⟨hfa, hfb⟩
  rcases hf with hf | hf
  · change f = first a b hab at hf
    rw [hf]
    simp only [other, ite_eq_left rfl]
    exact ⟨hp.1.symm, hp.2.2.2.1, hp.2.2.2.2.1⟩
  · change f = second a b hab at hf
    rw [hf]
    simp only [other, ite_eq_right hp.1.symm]
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

private theorem hswap :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (hba : P.plane.adjacent b a), (first b a hba ≠ second b a hba ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first b a hba) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (first b a hba) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second b a hba) i = b)
        ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second b a hba) i = a) ∧ ∀ (h :
            P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = b) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = a) → h = first b a hba ∨ h = second b a hba) → ((first b a hba =
        first a b hab ∨ first b a hba = second a b hab) → ((second b a hba = first a b hab ∨
        second b a hba = second a b hab) → ((first b a hba = first a b hab ∧ second b a hba =
        second a b hab) ∨ (first b a hba = second a b hab ∧ second b a hba = first a b hab)))) := by
  classical
  intro ι P a b hab first second hba hq hfirst hsecond
  rcases hfirst with hf | hf <;> rcases hsecond with hg | hg
  · have heq : first b a hba = second b a hba := hf.trans hg.symm
    exact (hq.1 heq).elim
  · exact Or.inl ⟨hf, hg⟩
  · exact Or.inr ⟨hf, hg⟩
  · have heq : first b a hba = second b a hba := hf.trans hg.symm
    exact (hq.1 heq).elim

private theorem hfirstAt289 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    (∀ (u : P.lattice), ∀ (f : P.plane.Face), ∀ (a : ι), (∃ i, P.plane.faceVertex f i = P.shift u
        a) → (∃ i, P.plane.faceVertex (P.faceShift (-u) f) i = a)) → ((∀ (u : P.lattice), ∀ (f :
            P.plane.Face), P.faceShift u (P.faceShift (-u) f) = f) → (∀ (u : ↥P.lattice), ∀ (hab'
            : P.plane.adjacent (P.shift u a) (P.shift u b)), (first a b hab ≠ second a b hab ∧ (∃
            (i :
        Fin (3 : ℕ)), P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i =
        b) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i :
        Fin (3 : ℕ)), P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab) →
        ((first (P.shift u a) (P.shift u b) hab' ≠ second (P.shift u a) (P.shift u b) hab' ∧ (∃
        (i : Fin (3 : ℕ)), P.plane.faceVertex (first (P.shift u a) (P.shift u b) hab') i =
        P.shift u a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (first (P.shift u a) (P.shift u
        b) hab') i = P.shift u b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second (P.shift u
        a) (P.shift u b) hab') i = P.shift u a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second (P.shift u a) (P.shift u b) hab') i = P.shift u b) ∧ ∀ (h : P.plane.Face), ((∃ (i
        : Fin (3 : ℕ)), P.plane.faceVertex h i = P.shift u a) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = P.shift u b) → h = first (P.shift u a) (P.shift u b) hab' ∨ h =
        second (P.shift u a) (P.shift u b) hab') → (
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    first (P.shift u a) (P.shift u b) hab' = f' ∨ first (P.shift u a) (P.shift u b) hab' = g'))))
        := by
  classical
  intro ι P a b hab first second unshifted_incidence faceShift_cancel u hab' hp hq f g f' g'
  have hinc1 := unshifted_incidence u
    (first (P.shift u a) (P.shift u b) hab') a hq.2.1
  have hinc2 := unshifted_incidence u
    (first (P.shift u a) (P.shift u b) hab') b hq.2.2.1
  rcases hp.2.2.2.2.2 _ ⟨hinc1, hinc2⟩ with h | h
  · left
    calc
      first (P.shift u a) (P.shift u b) hab' =
          P.faceShift u (P.faceShift (-u)
            (first (P.shift u a) (P.shift u b) hab')) :=
        (faceShift_cancel u _).symm
      _ = P.faceShift u f := congrArg (P.faceShift u) h
      _ = f' := rfl
  · right
    calc
      first (P.shift u a) (P.shift u b) hab' =
          P.faceShift u (P.faceShift (-u)
            (first (P.shift u a) (P.shift u b) hab')) :=
        (faceShift_cancel u _).symm
      _ = P.faceShift u g := congrArg (P.faceShift u) h
      _ = g' := rfl

private theorem hsecondAt312 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    (∀ (u : P.lattice), ∀ (f : P.plane.Face), ∀ (a : ι), (∃ i, P.plane.faceVertex f i = P.shift u
        a) → (∃ i, P.plane.faceVertex (P.faceShift (-u) f) i = a)) → ((∀ (u : P.lattice), ∀ (f :
            P.plane.Face), P.faceShift u (P.faceShift (-u) f) = f) → (∀ (u : ↥P.lattice), ∀ (hab'
            : P.plane.adjacent (P.shift u a) (P.shift u b)), (first a b hab ≠ second a b hab ∧ (∃
            (i :
        Fin (3 : ℕ)), P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i =
        b) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i :
        Fin (3 : ℕ)), P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab) →
        ((first (P.shift u a) (P.shift u b) hab' ≠ second (P.shift u a) (P.shift u b) hab' ∧ (∃
        (i : Fin (3 : ℕ)), P.plane.faceVertex (first (P.shift u a) (P.shift u b) hab') i =
        P.shift u a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (first (P.shift u a) (P.shift u
        b) hab') i = P.shift u b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second (P.shift u
        a) (P.shift u b) hab') i = P.shift u a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second (P.shift u a) (P.shift u b) hab') i = P.shift u b) ∧ ∀ (h : P.plane.Face), ((∃ (i
        : Fin (3 : ℕ)), P.plane.faceVertex h i = P.shift u a) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = P.shift u b) → h = first (P.shift u a) (P.shift u b) hab' ∨ h =
        second (P.shift u a) (P.shift u b) hab') → (
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    second (P.shift u a) (P.shift u b) hab' = f' ∨ second (P.shift u a) (P.shift u b) hab' =
        g')))) := by
  classical
  intro ι P a b hab first second unshifted_incidence faceShift_cancel u hab' hp hq f g f' g'
  have hinc1 := unshifted_incidence u
    (second (P.shift u a) (P.shift u b) hab') a hq.2.2.2.1
  have hinc2 := unshifted_incidence u
    (second (P.shift u a) (P.shift u b) hab') b hq.2.2.2.2.1
  rcases hp.2.2.2.2.2 _ ⟨hinc1, hinc2⟩ with h | h
  · left
    calc
      second (P.shift u a) (P.shift u b) hab' =
          P.faceShift u (P.faceShift (-u)
            (second (P.shift u a) (P.shift u b) hab')) :=
        (faceShift_cancel u _).symm
      _ = P.faceShift u f := congrArg (P.faceShift u) h
      _ = f' := rfl
  · right
    calc
      second (P.shift u a) (P.shift u b) hab' =
          P.faceShift u (P.faceShift (-u)
            (second (P.shift u a) (P.shift u b) hab')) :=
        (faceShift_cancel u _).symm
      _ = P.faceShift u g := congrArg (P.faceShift u) h
      _ = g' := rfl

private theorem horder :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (u : ↥P.lattice), ∀ (hab' : P.plane.adjacent (P.shift u a) (P.shift u b)), (first (P.shift
        u a) (P.shift u b) hab' ≠ second (P.shift u a) (P.shift u b) hab' ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first (P.shift u a) (P.shift u b) hab') i = P.shift u a) ∧ (∃ (i :
        Fin (3 : ℕ)), P.plane.faceVertex (first (P.shift u a) (P.shift u b) hab') i = P.shift u
        b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second (P.shift u a) (P.shift u b) hab') i
        = P.shift u a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second (P.shift u a) (P.shift
        u b) hab') i = P.shift u b) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = P.shift u a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i =
        P.shift u b) → h = first (P.shift u a) (P.shift u b) hab' ∨ h = second (P.shift u a)
        (P.shift u b) hab') → (
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    (first (P.shift u a) (P.shift u b) hab' = f' ∨ first (P.shift u a) (P.shift u b) hab' = g') →
        ((second (P.shift u a) (P.shift u b) hab' = f' ∨ second (P.shift u a) (P.shift u b) hab'
        = g') → ((first (P.shift u a) (P.shift u b) hab' = f' ∧ second (P.shift u a) (P.shift u
        b) hab' = g') ∨ (first (P.shift u a) (P.shift u b) hab' = g' ∧ second (P.shift u a)
        (P.shift u b) hab' = f')))) := by
  classical
  intro ι P a b hab first second u hab' hq f g f' g' hfirst hsecond
  rcases hfirst with hf | hf <;> rcases hsecond with hg | hg
  · exact (hq.1 (hf.trans hg.symm)).elim
  · exact Or.inl ⟨hf, hg⟩
  · exact Or.inr ⟨hf, hg⟩
  · exact (hq.1 (hf.trans hg.symm)).elim

private theorem hotherEq :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
        (second a b hab) (first a b hab)
    ∀ (hba : P.plane.adjacent b a), (other f b a hba ≠ f ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (other f b a hba) i = b) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (other f b a hba) i = a) → ((first a b hab ≠ second a b hab ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = a)
        ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = b) ∧ ∀ (h :
            P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab) → ((f = first a b
        hab ∨ f = second a b hab) → ((other f b a hba = first a b hab ∨ other f b a hba = second
        a b hab) → (other f b a hba = other f a b hab)))) := by
  classical
  intro ι P a b hab first second f other hba hotherBA hp hf hcand
  rcases hf with hf | hf
  · change f = first a b hab at hf
    rcases hcand with hc | hc
    · exact (hotherBA.1 (hc.trans hf.symm)).elim
    · simpa only [other, ite_eq_left hf] using hc
  · change f = second a b hab at hf
    rcases hcand with hc | hc
    · have hnot : f ≠ first a b hab := fun h => hp.1 (h.symm.trans hf)
      simpa only [other, ite_eq_right hnot] using hc
    · exact (hotherBA.1 (hc.trans hf.symm)).elim

private theorem hother_shift :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
        (second a b hab) (first a b hab)
    (∀ (u : P.lattice), Function.Injective (P.faceShift u)) → (∀ (u : ↥P.lattice), ∀ (hab' :
        P.plane.adjacent (P.shift u a) (P.shift u b)),
    let g := other f a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    (other f a b hab ≠ f ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = a) ∧ ∃
        (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = b) → ((other f' (P.shift u a)
        (P.shift u b) hab' ≠ f' ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other f' (P.shift u
        a) (P.shift u b) hab') i = P.shift u a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other
        f' (P.shift u a) (P.shift u b) hab') i = P.shift u b) → ((f' = first (P.shift u a)
        (P.shift u b) hab' ∨ f' = second (P.shift u a) (P.shift u b) hab') → ((other f' (P.shift
        u a) (P.shift u b) hab' = first (P.shift u a) (P.shift u b) hab' ∨ other f' (P.shift u a)
        (P.shift u b) hab' = second (P.shift u a) (P.shift u b) hab') → ((g' = first (P.shift u
        a) (P.shift u b) hab' ∨ g' = second (P.shift u a) (P.shift u b) hab') → (other f'
        (P.shift u a) (P.shift u b) hab' = g')))))) := by
  classical
  intro ι P a b hab first second f other faceShift_injective u hab' g f' g' hother hlhs hfchoice
      hlchoice hgchoice
  rcases hfchoice with hf | hf
  · rcases hlchoice with hl | hl
    · exact (hlhs.1 (hl.trans hf.symm)).elim
    · rcases hgchoice with hg | hg
      · exact (hother.1 (faceShift_injective u (hg.trans hf.symm))).elim
      · exact hl.trans hg.symm
  · rcases hlchoice with hl | hl
    · rcases hgchoice with hg | hg
      · exact hl.trans hg.symm
      · exact (hother.1 (faceShift_injective u (hg.trans hf.symm))).elim
    · exact (hlhs.1 (hl.trans hf.symm)).elim

end DualEdgesProof

namespace DualEdgeDetails

private theorem faceShift_injective :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : ↥P.lattice), Function.Injective (P.faceShift
        u) := by
  classical
  intro ι P u f g h
  have h' := congrArg (P.faceShift (-u)) h
  simpa only [← P.faceShift_add, neg_add_cancel, P.faceShift_zero] using h'

private theorem shifted_incidence :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : ↥P.lattice), ∀ (f : P.plane.Face), ∀ (a :
        ι), (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = a) → ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (P.faceShift u f) i = P.shift u a := by
  classical
  intro ι P u f a ha
  rcases ha with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [P.face_vertices_periodic, hi]

private theorem unshifted_incidence :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : ↥P.lattice), ∀ (f : P.plane.Face), ∀ (a :
        ι), (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex f i = P.shift u a) → ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (P.faceShift (-u) f) i = a := by
  classical
  intro ι P u f a ha
  rcases ha with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [P.face_vertices_periodic, hi]
  rw [← P.shift_add, neg_add_cancel, P.shift_zero]

private theorem faceShift_cancel :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : ↥P.lattice), ∀ (f : P.plane.Face),
        P.faceShift u (P.faceShift (-u) f) = f := by
  classical
  intro ι P u f
  rw [← P.faceShift_add, add_neg_cancel, P.faceShift_zero]

private theorem faceShift_cancel' :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (u : ↥P.lattice), ∀ (f : P.plane.Face),
        P.faceShift (-u) (P.faceShift u f) = f := by
  classical
  intro ι P u f
  rw [← P.faceShift_add, neg_add_cancel, P.faceShift_zero]

private theorem walk_translate :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (p : List GaussianInt), p ≠ [] → ∀ (u :
        ↥P.lattice), ∀ (t : (↑(Set.Icc (0 : ℝ) (1 : ℝ)) : Type)), P3776T1WalkMap (List.map (fun
        (z : GaussianInt) => z + (↑u : GaussianInt)) p) t = P3776T1WalkMap p t +
        GaussianRealPoint (↑u : GaussianInt) := by
  classical
  intro ι P p hp u t
  obtain ⟨_, _, _, _, htranslate, _⟩ := P3776T1WalkMapProperties p hp
  exact htranslate (u : GaussianInt) t

private theorem hfirstAt497 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (hba : P.plane.adjacent b a), (first a b hab ≠ second a b hab ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = a)
        ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = b) ∧ ∀ (h :
            P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab) → ((first b a hba ≠
        second b a hba ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (first b a hba) i = b) ∧ (∃ (i
        : Fin (3 : ℕ)), P.plane.faceVertex (first b a hba) i = a) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (second b a hba) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second b a hba) i = a) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        h i = b) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) → h = first b a hba ∨ h =
        second b a hba) → (first b a hba = first a b hab ∨ first b a hba = second a b hab)) := by
  classical
  intro ι P a b hab first second hba hp hq
  apply hp.2.2.2.2.2
  exact ⟨hq.2.2.1, hq.2.1⟩

private theorem hsecondAt501 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (hba : P.plane.adjacent b a), (first a b hab ≠ second a b hab ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (first a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = a)
        ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (second a b hab) i = b) ∧ ∀ (h :
            P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) ∧ ∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex h i = b) → h = first a b hab ∨ h = second a b hab) → ((first b a hba ≠
        second b a hba ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (first b a hba) i = b) ∧ (∃ (i
        : Fin (3 : ℕ)), P.plane.faceVertex (first b a hba) i = a) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (second b a hba) i = b) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second b a hba) i = a) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        h i = b) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = a) → h = first b a hba ∨ h =
        second b a hba) → (second b a hba = first a b hab ∨ second b a hba = second a b hab)) := by
  classical
  intro ι P a b hab first second hba hp hq
  apply hp.2.2.2.2.2
  exact ⟨hq.2.2.2.2.1, hq.2.2.2.1⟩

private theorem hneAt517 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    let p := P.facePath (first a b hab) (second a b hab)
    ((P.facePath (first a b hab) (second a b hab)).head? = some (P.rho (first a b hab))) → (p ≠
        []) := by
  classical
  intro ι P a b hab first second p hhead he
  change P.facePath (first a b hab) (second a b hab) = [] at he
  rw [he] at hhead
  simp at hhead

private theorem ht :
    let t : Set.Icc (0 : Real) 1 := ⟨1 / 2, by norm_num⟩
    t = ⟨1 - (t : Real), by constructor <;> norm_num⟩ := by
  classical
  intro t
  apply Subtype.ext
  norm_num [t]

private theorem hneAt542 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ((P.facePath (first a b hab) (second a b hab)).head? = some (P.rho (first a b hab)) ∧
        (P.facePath (first a b hab) (second a b hab)).getLast? = some (P.rho (second a b hab)) ∧
        (∀ x ∈ P.facePath (first a b hab) (second a b hab), x ∈ FootprintVertices (P.tile a) ∩
        FootprintVertices (P.tile b)) ∧ ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List
        GaussianInt), ∀ (l₂ : List GaussianInt), P.facePath (first a b hab) (second a b hab) = l₁
        ++ x :: y :: l₂ → {x, y} ∈ FootprintEdges (P.tile a) ∩ FootprintEdges (P.tile b)) →
        (P.facePath (first a b hab) (second a b hab) ≠ []) := by
  classical
  intro ι P a b hab first second hhead he
  have hh := hhead.1
  rw [he] at hh
  simp at hh

private theorem hfgAt566 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    (∀ (u : P.lattice), Function.Injective (P.faceShift u)) → (∀ (u : ↥P.lattice), (first a b hab
        ≠ second a b hab ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (first a b hab) i = a) ∧ (∃
        (i : Fin (3 : ℕ)), P.plane.faceVertex (first a b hab) i = b) ∧ (∃ (i : Fin (3 : ℕ)),
        P.plane.faceVertex (second a b hab) i = a) ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        (second a b hab) i = b) ∧ ∀ (h : P.plane.Face), ((∃ (i : Fin (3 : ℕ)), P.plane.faceVertex
        h i = a) ∧ ∃ (i : Fin (3 : ℕ)), P.plane.faceVertex h i = b) → h = first a b hab ∨ h =
        second a b hab) → (
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    f' ≠ g')) := by
  classical
  intro ι P a b hab first second faceShift_injective u hp f g f' g' h
  exact hp.1 (faceShift_injective u h)

private theorem hpneAt583 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    let f := first a b hab
    let g := second a b hab
    ((P.facePath f g).head? = some (P.rho f) ∧ (P.facePath f g).getLast? = some (P.rho g) ∧ (∀ x
        ∈ P.facePath f g, x ∈ FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b)) ∧ ∀ (x
            : GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
        GaussianInt), P.facePath f g = l₁ ++ x :: y :: l₂ → {x, y} ∈ FootprintEdges (P.tile a) ∩
        FootprintEdges (P.tile b)) → (P.facePath f g ≠ []) := by
  classical
  intro ι P a b hab first second f g hspec he
  rw [he] at hspec
  simp at hspec

private theorem hpath :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (u : ↥P.lattice),
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    P.facePath f' g' = (P.facePath f g).map (fun z => z + (u : GaussianInt)) := by
  classical
  intro ι P a b hab first second u f g f' g'
  exact P.facePath_periodic u f g

private theorem hpathne :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (u : ↥P.lattice),
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    (P.facePath f g ≠ []) → ((P.facePath f' g' = (P.facePath f g).map (fun z => z + (u :
        GaussianInt))) → (P.facePath f' g' ≠ [])) := by
  classical
  intro ι P a b hab first second u f g f' g' hpne hpath
  rw [hpath]
  intro hm
  apply hpne
  cases hp : P.facePath f g with
  | nil => rfl
  | cons z zs => simp [hp] at hm

private theorem hnonempty :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
          (second a b hab) (first a b hab)
    ((P.facePath f (other f a b hab)).head? = some (P.rho f)) → (P.facePath f (other f a b hab) ≠
        []) := by
  classical
  intro ι P a b hab first second f other hhead h
  simp [h] at hhead

private theorem hfirstpoint :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
          (second a b hab) (first a b hab)
    ((P.facePath f (other f a b hab)).head? = some (P.rho f)) → ((P.facePath f (other f a b
        hab)).getD 0 0 = P.rho f) := by
  classical
  intro ι P a b hab first second f other hhead
  cases hp : P.facePath f (other f a b hab) with
  | nil => simp [hp] at hhead
  | cons z zs => simpa [hp] using hhead

private theorem hparameter :
    Continuous (fun t : Set.Icc (0 : Real) 1 =>
      (⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ :
        Set.Icc (0 : Real) 1)) := by
  classical
  fun_prop

private theorem hparam :
    (⟨(⟨1, by norm_num⟩ : Set.Icc (0 : Real) 1) / 2,
        by constructor <;> norm_num⟩ : Set.Icc (0 : Real) 1) =
      (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : Real) 1) := by
  classical
  apply Subtype.ext
  norm_num

private theorem hfgAt699 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
          (second a b hab) (first a b hab)
    (∀ (u : P.lattice), Function.Injective (P.faceShift u)) → (∀ (u : ↥P.lattice),
    let g := other f a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    (other f a b hab ≠ f ∧ (∃ (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = a) ∧ ∃
        (i : Fin (3 : ℕ)), P.plane.faceVertex (other f a b hab) i = b) → (f' ≠ g')) := by
  classical
  intro ι P a b hab first second f other faceShift_injective u g f' g' hother h
  exact hother.1 (faceShift_injective u h).symm

private theorem hpneAt718 :
    ∀ (ι : Type), ∀ (P : PeriodicTileCore ι), ∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b),
    let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (P.plane.every_edge_two_faces a b hab)
    let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
      Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
    ∀ (f : P.plane.Face),
    let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
      @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
          (second a b hab) (first a b hab)
    let g := other f a b hab
    ((P.facePath f g).head? = some (P.rho f) ∧ (P.facePath f g).getLast? = some (P.rho g) ∧ (∀ x
        ∈ P.facePath f g, x ∈ FootprintVertices (P.tile a) ∩ FootprintVertices (P.tile b)) ∧ ∀ (x
            : GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
        GaussianInt), P.facePath f g = l₁ ++ x :: y :: l₂ → {x, y} ∈ FootprintEdges (P.tile a) ∩
        FootprintEdges (P.tile b)) → (P.facePath f g ≠ []) := by
  classical
  intro ι P a b hab first second f other g hspec he
  rw [he] at hspec
  simp at hspec

end DualEdgeDetails

namespace DualHalfSpecification

private theorem halfSpecification :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (P : PeriodicTileCore ι),
        let first (a b : ι) (hab : P.plane.adjacent a
            b) : P.plane.Face :=
          Classical.choose (P.plane.every_edge_two_faces a b hab)
        let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
          Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
        let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
          @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
              (second a b hab) (first a b hab)
        let port (a b : ι) : Real × Real :=
          if hab : P.plane.adjacent a b then
            P3776T1WalkMap (P.facePath (first a b hab) (second a b hab))
              ⟨1 / 2, by norm_num⟩
          else 0
        let half (f : P.plane.Face) (a b : ι) (t : Set.Icc (0 : Real) 1) : Real × Real :=
          if hab : P.plane.adjacent a b then
            P3776T1WalkMap (P.facePath f (other f a b hab))
              ⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
          else 0
        (∀ (a : ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b), first a b hab ≠ second a b hab ∧
            (∃ i, P.plane.faceVertex (first a b hab) i = a) ∧ (∃ i, P.plane.faceVertex (first a b
            hab) i = b) ∧ (∃ i, P.plane.faceVertex (second a b hab) i = a) ∧ (∃ i,
            P.plane.faceVertex (second a b hab) i = b) ∧ ∀ h : P.plane.Face, ((∃ i,
            P.plane.faceVertex h i = a) ∧ (∃ i, P.plane.faceVertex h i = b)) → h = first a b hab
            ∨ h = second a b hab) → ((∀ (p : List GaussianInt), (p ≠ []) → (P3776T1WalkMap p ⟨1
            / 2, by norm_num⟩ =
            P3776T1WalkMap p.reverse ⟨1 / 2, by norm_num⟩)) → ((∀ (f : P.plane.Face), ∀ (a :
                ι), ∀ (b : ι), ∀ (hab : P.plane.adjacent a b), (∃ i, P.plane.faceVertex f i = a)
                → ((∃ i, P.plane.faceVertex f i = b) → (other f a b hab ≠ f ∧ (∃ i,
                P.plane.faceVertex (other f a b hab) i = a) ∧ (∃ i, P.plane.faceVertex (other f a
                b hab) i = b)))) → (∀ f, ∀ a, ∀ b, P.plane.adjacent a b →
          (∃ i, P.plane.faceVertex f i = a) →
          (∃ i, P.plane.faceVertex f i = b) →
          Continuous (half f a b) ∧
          half f a b ⟨0, by norm_num⟩ = GaussianRealPoint (P.rho f) ∧
          half f a b ⟨1, by norm_num⟩ = port a b ∧
          (∀ t, half f a b t ∈ TileRealization (P.tile a) ∩ TileRealization (P.tile b)) ∧
          (∀ t, half f a b t = half f b a t) ∧
          ∃ g, g ≠ f ∧ (∃ i, P.plane.faceVertex g i = a) ∧
            (∃ i, P.plane.faceVertex g i = b) ∧
            ∀ t, half f a b t = P3776T1WalkMap (P.facePath f g)
              ⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩)))) := by
  classical
  intro ι P first second other port half pair_spec midpoint_reverse other_spec f a b hab hfa hfb
  have hpairs := pair_spec a b hab
  have hother := other_spec f a b hab hfa hfb
  obtain ⟨hhead, hlast, hvertices, hedges⟩ :=
    P.facePath_spec a b hab f (other f a b hab) hother.1.symm hfa hfb
      hother.2.1 hother.2.2
  have hnonempty : P.facePath f (other f a b hab) ≠ [] := DualEdgeDetails.hnonempty ι P a b hab
      f hhead
  obtain ⟨hcontinuous, hzero, _, _, _, hsupport⟩ :=
    P3776T1WalkMapProperties _ hnonempty
  have hfirstpoint :
      (P.facePath f (other f a b hab)).getD 0 0 = P.rho f := DualEdgeDetails.hfirstpoint ι P a
          b hab f hhead
  refine ⟨?_, ?_, ?_, ?_, ?_, other f a b hab,
    hother.1, hother.2.1, hother.2.2, ?_⟩
  · have hparameter : Continuous (fun t : Set.Icc (0 : Real) 1 =>
        (⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ :
          Set.Icc (0 : Real) 1)) := DualEdgeDetails.hparameter
    simpa only [half, dite_eq_left hab, Function.comp_def] using hcontinuous.comp hparameter
  · rw [hfirstpoint] at hzero
    simpa only [half, dite_eq_left hab, zero_div] using hzero
  · have hparam :
        (⟨(⟨1, by norm_num⟩ : Set.Icc (0 : Real) 1) / 2,
          by constructor <;> norm_num⟩ : Set.Icc (0 : Real) 1) =
        (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : Real) 1) := DualEdgeDetails.hparam
    have hf := hpairs.2.2.2.2.2 f ⟨hfa, hfb⟩
    have hneq := hpairs.1
    simp only [half, port, dite_eq_left hab]
    rw [hparam]
    change f = first a b hab ∨ f = second a b hab at hf
    rcases hf with hf | hf
    · rw [hf]
      simp only [other, ite_eq_left rfl]
    · rw [hf]
      have hneq' : ¬ second a b hab = first a b hab := fun h => hneq h.symm
      simp only [other, ite_eq_right hneq']
      have hnon' : P.facePath (second a b hab) (first a b hab) ≠ [] := by
        simpa [hf, other, hneq'] using hnonempty
      have hmr := midpoint_reverse (P.facePath (second a b hab)
        (first a b hab)) hnon'
      have hpathrev : P.facePath (second a b hab) (first a b hab) =
          (P.facePath (first a b hab) (second a b hab)).reverse :=
        P.facePath_reverse _ _
      calc
        P3776T1WalkMap (P.facePath (second a b hab) (first a b hab))
            ⟨1 / 2, by norm_num⟩ =
          P3776T1WalkMap (P.facePath (second a b hab) (first a b hab)).reverse
            ⟨1 / 2, by norm_num⟩ := hmr
        _ = P3776T1WalkMap (P.facePath (first a b hab) (second a b hab))
            ⟨1 / 2, by norm_num⟩ := by rw [hpathrev, List.reverse_reverse]
  · intro t
    simp only [half, dite_eq_left hab]
    exact ⟨hsupport (P.tile a) (P.tiles_are_disks a)
      (fun z hz => (hvertices z hz).1)
      (fun x y l₁ l₂ h => (hedges x y l₁ l₂ h).1) _,
      hsupport (P.tile b) (P.tiles_are_disks b)
      (fun z hz => (hvertices z hz).2)
      (fun x y l₁ l₂ h => (hedges x y l₁ l₂ h).2) _⟩
  · intro t
    have hba : P.plane.adjacent b a := (P.plane.adjacent_symmetric a b).mp hab
    have hotherBA := other_spec f b a hba hfb hfa
    have hp := pair_spec a b hab
    have hf := hp.2.2.2.2.2 f ⟨hfa, hfb⟩
    have hcand := hp.2.2.2.2.2 (other f b a hba)
      ⟨hotherBA.2.2, hotherBA.2.1⟩
    have hotherEq : other f b a hba = other f a b hab := DualEdgesProof.hotherEq ι P a b hab f
        hba hotherBA hp hf hcand
    simp only [half, dite_eq_left hab, dite_eq_left hba]
    rw [hotherEq]
  · intro t
    simp only [half, dite_eq_left hab]

end DualHalfSpecification

theorem P3776T1DualEdgesExist {ι : Type} (P : PeriodicTileCore ι) :
    Nonempty (P3776T1DualEdges P) := by
-- BODY
  classical
  let first (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
    Classical.choose (P.plane.every_edge_two_faces a b hab)
  let second (a b : ι) (hab : P.plane.adjacent a b) : P.plane.Face :=
    Classical.choose (Classical.choose_spec (P.plane.every_edge_two_faces a b hab))
  let other (f : P.plane.Face) (a b : ι) (hab : P.plane.adjacent a b) :=
    @ite P.plane.Face (f = first a b hab) (Classical.propDecidable _)
        (second a b hab) (first a b hab)
  let port (a b : ι) : Real × Real :=
    if hab : P.plane.adjacent a b then
      P3776T1WalkMap (P.facePath (first a b hab) (second a b hab))
        ⟨1 / 2, by norm_num⟩
    else 0
  let half (f : P.plane.Face) (a b : ι) (t : Set.Icc (0 : Real) 1) : Real × Real :=
    if hab : P.plane.adjacent a b then
      P3776T1WalkMap (P.facePath f (other f a b hab))
        ⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
    else 0
  have pair_spec (a b : ι) (hab : P.plane.adjacent a b) :
      first a b hab ≠ second a b hab ∧
      (∃ i, P.plane.faceVertex (first a b hab) i = a) ∧
      (∃ i, P.plane.faceVertex (first a b hab) i = b) ∧
      (∃ i, P.plane.faceVertex (second a b hab) i = a) ∧
      (∃ i, P.plane.faceVertex (second a b hab) i = b) ∧
      ∀ h : P.plane.Face,
        ((∃ i, P.plane.faceVertex h i = a) ∧
         (∃ i, P.plane.faceVertex h i = b)) →
          h = first a b hab ∨ h = second a b hab := DualEdgesProof.pair_spec ι P a b hab
  have midpoint_reverse (p : List GaussianInt) (hp : p ≠ []) :
      P3776T1WalkMap p ⟨1 / 2, by norm_num⟩ =
        P3776T1WalkMap p.reverse ⟨1 / 2, by norm_num⟩ := DualEdgesProof.midpoint_reverse p hp
  have other_spec (f : P.plane.Face) (a b : ι)
      (hab : P.plane.adjacent a b) (hfa : ∃ i, P.plane.faceVertex f i = a)
      (hfb : ∃ i, P.plane.faceVertex f i = b) :
      other f a b hab ≠ f ∧
        (∃ i, P.plane.faceVertex (other f a b hab) i = a) ∧
        (∃ i, P.plane.faceVertex (other f a b hab) i = b) := DualEdgesProof.other_spec ι P
            pair_spec f a b hab hfa hfb
  have faceShift_injective (u : P.lattice) : Function.Injective (P.faceShift u) :=
      DualEdgeDetails.faceShift_injective ι P u
  have shifted_incidence (u : P.lattice) (f : P.plane.Face) (a : ι)
      (ha : ∃ i, P.plane.faceVertex f i = a) :
      ∃ i, P.plane.faceVertex (P.faceShift u f) i = P.shift u a :=
          DualEdgeDetails.shifted_incidence ι P u f a ha
  have unshifted_incidence (u : P.lattice) (f : P.plane.Face) (a : ι)
      (ha : ∃ i, P.plane.faceVertex f i = P.shift u a) :
      ∃ i, P.plane.faceVertex (P.faceShift (-u) f) i = a := DualEdgeDetails.unshifted_incidence ι
          P u f a ha
  have faceShift_cancel (u : P.lattice) (f : P.plane.Face) :
      P.faceShift u (P.faceShift (-u) f) = f := DualEdgeDetails.faceShift_cancel ι P u f
  have walk_translate (p : List GaussianInt) (hp : p ≠ [])
      (u : P.lattice) (t : Set.Icc (0 : Real) 1) :
      P3776T1WalkMap (p.map (fun z => z + (u : GaussianInt))) t =
        P3776T1WalkMap p t + GaussianRealPoint u := DualEdgeDetails.walk_translate ι P p hp u t
  refine ⟨{
    port := port
    half := half
    port_symmetric := ?_
    port_support := ?_
    port_periodic := ?_
    half_spec := ?_
    half_periodic := ?_ }⟩
  · intro a b hab
    have hba : P.plane.adjacent b a := (P.plane.adjacent_symmetric a b).mp hab
    have hp := pair_spec a b hab
    have hq := pair_spec b a hba
    have hfirst : first b a hba = first a b hab ∨
        first b a hba = second a b hab := DualEdgeDetails.hfirstAt497 ι P a b hab hba hp hq
    have hsecond : second b a hba = first a b hab ∨
        second b a hba = second a b hab := DualEdgeDetails.hsecondAt501 ι P a b hab hba hp hq
    have hswap : (first b a hba = first a b hab ∧
        second b a hba = second a b hab) ∨
        (first b a hba = second a b hab ∧
        second b a hba = first a b hab) := DualEdgesProof.hswap ι P a b hab hba hq hfirst hsecond
    unfold port
    simp only [dite_eq_left hab, dite_eq_left hba]
    rcases hswap with ⟨hf, hg⟩ | ⟨hf, hg⟩
    · rw [hf, hg]
    · rw [hf, hg]
      let p := P.facePath (first a b hab) (second a b hab)
      have hhead := (P.facePath_spec a b hab (first a b hab)
        (second a b hab) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1).1
      have hne : p ≠ [] := DualEdgeDetails.hneAt517 ι P a b hab hhead
      obtain ⟨_, _, _, hrev, _, _⟩ := P3776T1WalkMapProperties p hne
      have hpathrev : P.facePath (second a b hab) (first a b hab) =
          (P.facePath (first a b hab) (second a b hab)).reverse :=
        P.facePath_reverse _ _
      rw [hpathrev]
      let t : Set.Icc (0 : Real) 1 := ⟨1 / 2, by norm_num⟩
      have heq : P3776T1WalkMap p t =
          P3776T1WalkMap p ⟨1 - (t : Real), by constructor <;> norm_num⟩ :=
        congrArg (P3776T1WalkMap p) (DualEdgeDetails.ht)
      exact heq.trans (hrev t).symm
  · intro a b hab
    have hp := pair_spec a b hab
    obtain ⟨_, _, hvertices, hedges⟩ := P.facePath_spec a b hab
      (first a b hab) (second a b hab) hp.1 hp.2.1 hp.2.2.1
      hp.2.2.2.1 hp.2.2.2.2.1
    have hhead := P.facePath_spec a b hab (first a b hab) (second a b hab)
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
    have hne : P.facePath (first a b hab) (second a b hab) ≠ [] := DualEdgeDetails.hneAt542 ι P a
        b hab hhead
    obtain ⟨_, _, _, _, _, hsupport⟩ :=
      P3776T1WalkMapProperties _ hne
    unfold port
    simp only [dite_eq_left hab]
    exact ⟨hsupport (P.tile a) (P.tiles_are_disks a)
      (fun z hz => (hvertices z hz).1)
      (fun x y l₁ l₂ h => (hedges x y l₁ l₂ h).1) _,
      hsupport (P.tile b) (P.tiles_are_disks b)
      (fun z hz => (hvertices z hz).2)
      (fun x y l₁ l₂ h => (hedges x y l₁ l₂ h).2) _⟩
  · intro u a b hab
    have hab' : P.plane.adjacent (P.shift u a) (P.shift u b) :=
      (P.edge_periodic u a b).mpr hab
    have hp := pair_spec a b hab
    have hq := pair_spec (P.shift u a) (P.shift u b) hab'
    let f := first a b hab
    let g := second a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    have hfg : f' ≠ g' := DualEdgeDetails.hfgAt566 ι P a b hab faceShift_injective u hp
    have hfirst : first (P.shift u a) (P.shift u b) hab' = f' ∨
        first (P.shift u a) (P.shift u b) hab' = g' := DualEdgesProof.hfirstAt289 ι P a b hab
            unshifted_incidence faceShift_cancel u hab' hp hq
    have hsecond : second (P.shift u a) (P.shift u b) hab' = f' ∨
        second (P.shift u a) (P.shift u b) hab' = g' := DualEdgesProof.hsecondAt312 ι P a b hab
            unshifted_incidence faceShift_cancel u hab' hp hq
    have horder :
        (first (P.shift u a) (P.shift u b) hab' = f' ∧
          second (P.shift u a) (P.shift u b) hab' = g') ∨
        (first (P.shift u a) (P.shift u b) hab' = g' ∧
          second (P.shift u a) (P.shift u b) hab' = f') := DualEdgesProof.horder ι P a b hab u
              hab' hq hfirst hsecond
    have hspec := P.facePath_spec a b hab f g hp.1 hp.2.1 hp.2.2.1
      hp.2.2.2.1 hp.2.2.2.2.1
    have hpne : P.facePath f g ≠ [] := DualEdgeDetails.hpneAt583 ι P a b hab hspec
    have hpath : P.facePath f' g' =
        (P.facePath f g).map (fun z => z + (u : GaussianInt)) := DualEdgeDetails.hpath ι P a b hab u
    simp only [port, dite_eq_left hab, dite_eq_left hab']
    rcases horder with ⟨hf, hg⟩ | ⟨hf, hg⟩
    · rw [hf, hg, hpath]
      exact walk_translate (P.facePath f g) hpne u ⟨1 / 2, by norm_num⟩
    · rw [hf, hg]
      have hrevpath : P.facePath g' f' = (P.facePath f' g').reverse :=
        P.facePath_reverse f' g'
      calc
        P3776T1WalkMap (P.facePath g' f') ⟨1 / 2, by norm_num⟩ =
            P3776T1WalkMap (P.facePath f' g').reverse ⟨1 / 2, by norm_num⟩ := by
          rw [hrevpath]
        _ = P3776T1WalkMap (P.facePath f' g') ⟨1 / 2, by norm_num⟩ :=
          (midpoint_reverse (P.facePath f' g') (DualEdgeDetails.hpathne ι P a b hab u hpne
              hpath)).symm
        _ = P3776T1WalkMap
            ((P.facePath f g).map (fun z => z + (u : GaussianInt)))
              ⟨1 / 2, by norm_num⟩ := by rw [hpath]
        _ = P3776T1WalkMap (P.facePath f g) ⟨1 / 2, by norm_num⟩ +
            GaussianRealPoint u := walk_translate (P.facePath f g) hpne u
              ⟨1 / 2, by norm_num⟩
  · exact DualHalfSpecification.halfSpecification ι P pair_spec midpoint_reverse other_spec
  · intro u f a b hab hfa hfb t
    have hab' : P.plane.adjacent (P.shift u a) (P.shift u b) :=
      (P.edge_periodic u a b).mpr hab
    let g := other f a b hab
    let f' := P.faceShift u f
    let g' := P.faceShift u g
    have hother := other_spec f a b hab hfa hfb
    have hfg : f' ≠ g' := DualEdgeDetails.hfgAt699 ι P a b hab f faceShift_injective u hother
    have hf'a := shifted_incidence u f a hfa
    have hf'b := shifted_incidence u f b hfb
    have hg'a := shifted_incidence u g a hother.2.1
    have hg'b := shifted_incidence u g b hother.2.2
    have hlhs := other_spec f' (P.shift u a) (P.shift u b) hab' hf'a hf'b
    have hq := pair_spec (P.shift u a) (P.shift u b) hab'
    have hfchoice := hq.2.2.2.2.2 f' ⟨hf'a, hf'b⟩
    have hlchoice := hq.2.2.2.2.2
      (other f' (P.shift u a) (P.shift u b) hab')
      ⟨hlhs.2.1, hlhs.2.2⟩
    have hgchoice := hq.2.2.2.2.2 g' ⟨hg'a, hg'b⟩
    have hother_shift : other f' (P.shift u a) (P.shift u b) hab' = g' :=
        DualEdgesProof.hother_shift ι P a b hab f faceShift_injective u hab' hother hlhs hfchoice
        hlchoice hgchoice
    have hspec := P.facePath_spec a b hab f g hother.1.symm hfa hfb
      hother.2.1 hother.2.2
    have hpne : P.facePath f g ≠ [] := DualEdgeDetails.hpneAt718 ι P a b hab f hspec
    simp only [half, dite_eq_left hab', dite_eq_left hab]
    rw [hother_shift, P.facePath_periodic]
    exact walk_translate (P.facePath f g) hpne u
      ⟨(t : Real) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

end ApollonianSuperharmonic

end
