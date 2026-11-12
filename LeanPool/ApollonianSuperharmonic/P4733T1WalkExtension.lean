/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4733T1FacePairOrbit

-- [TABLET NODE: P4733T1WalkExtension]

/-!
# P4733T1WalkExtension

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4733T1WalkExtension {u v : GaussianInt} {L : AddSubgroup GaussianInt}
    (D : P4677T2DrawingData u v L)
    (hinj : Function.Injective (P4733T1FacePairOrbit D))
    (p : Fin 18 → List GaussianInt) :
    ∃ path : PeriodicSubtileFaceIndex → PeriodicSubtileFaceIndex → List GaussianInt,
      (∀ f g, path g f = (path f g).reverse) ∧
      (∀ w f g, path (D.faceShift w f) (D.faceShift w g) =
        (path f g).map (fun x => x + (w : GaussianInt))) ∧
      (∀ t : Fin 18 × L × Bool,
        path (P4733T1FacePairOrbit D t).1 (P4733T1FacePairOrbit D t).2 =
          if t.2.2 then (p t.1).map (fun x => x + (t.2.1 : GaussianInt))
          else ((p t.1).map (fun x => x + (t.2.1 : GaussianInt))).reverse) ∧
      (∀ f, path f f = []) ∧
      ∀ f g, (¬ ∃ t, P4733T1FacePairOrbit D t = (f, g)) → path f g = [] := by
-- BODY
  classical
  let N := P4733T1FacePairOrbit D
  let value (t : Fin 18 × L × Bool) :=
    if t.2.2 then (p t.1).map (fun x => x + (t.2.1 : GaussianInt))
    else ((p t.1).map (fun x => x + (t.2.1 : GaussianInt))).reverse
  let path (f g : PeriodicSubtileFaceIndex) :=
    if h : ∃ t, N t = (f, g) then value h.choose else []
  have on_orbit (t : Fin 18 × L × Bool) : path (N t).1 (N t).2 = value t := by
    dsimp only [path]
    split_ifs with h
    · exact congrArg value (hinj h.choose_spec)
    · exact (h ⟨t, rfl⟩).elim
  let flip (t : Fin 18 × L × Bool) : Fin 18 × L × Bool :=
    (t.1, t.2.1, !t.2.2)
  let shift (w : L) (t : Fin 18 × L × Bool) : Fin 18 × L × Bool :=
    (t.1, w + t.2.1, t.2.2)
  have flip_pair (t) : N (flip t) = ((N t).2, (N t).1) := by
    rcases t with ⟨r, z, s⟩
    cases s <;> rfl
  have flip_value (t) : value (flip t) = (value t).reverse := by
    rcases t with ⟨r, z, s⟩
    cases s <;> simp [value, flip]
  have shift_pair (w) (t) : N (shift w t) =
      (D.faceShift w (N t).1, D.faceShift w (N t).2) := by
    rcases t with ⟨r, z, s⟩
    cases s <;> simp [N, shift, P4733T1FacePairOrbit, D.faceShift_add]
  have shift_value (w) (t) : value (shift w t) =
      (value t).map (fun x => x + (w : GaussianInt)) := by
    rcases t with ⟨r, z, s⟩
    cases s <;> simp [value, shift, List.map_reverse, List.map_map,
      add_comm]
  have outside (f g) (h : ¬ ∃ t, N t = (f, g)) : path f g = [] := dite_eq_right h
  refine ⟨path, ?_, ?_, on_orbit, ?_, outside⟩
  · intro f g
    by_cases h : ∃ t, N t = (f, g)
    · obtain ⟨t, ht⟩ := h
      have hat := on_orbit t
      have hflip := on_orbit (flip t)
      rw [ht] at hat
      rw [flip_pair, ht] at hflip
      exact hflip.trans ((flip_value t).trans (congrArg List.reverse hat.symm))
    · have hrev : ¬ ∃ t, N t = (g, f) := by
        rintro ⟨t, ht⟩
        apply h
        exact ⟨flip t, by rw [flip_pair, ht]⟩
      simp only [path, dite_eq_right h, dite_eq_right hrev, List.reverse_nil]
  · intro w f g
    by_cases h : ∃ t, N t = (f, g)
    · obtain ⟨t, ht⟩ := h
      have hat := on_orbit t
      have hshift := on_orbit (shift w t)
      rw [ht] at hat
      rw [shift_pair, ht] at hshift
      exact hshift.trans ((shift_value w t).trans (congrArg
        (List.map (fun x => x + (w : GaussianInt))) hat.symm))
    · have hshift : ¬ ∃ t, N t = (D.faceShift w f, D.faceShift w g) := by
        rintro ⟨t, ht⟩
        apply h
        refine ⟨shift (-w) t, ?_⟩
        rw [shift_pair, ht]
        simp only [← D.faceShift_add, neg_add_cancel, D.faceShift_zero]
      simp only [path, dite_eq_right h, dite_eq_right hshift, List.map_nil]
  · intro f
    apply outside
    rintro ⟨t, ht⟩
    have heq : flip t = t := hinj (by
      change N (flip t) = N t
      rw [flip_pair, ht])
    have hb := congrArg (fun t : Fin 18 × L × Bool => t.2.2) heq
    rcases t with ⟨r, z, s⟩
    cases s <;> simp [flip] at hb

end ApollonianSuperharmonic

end
