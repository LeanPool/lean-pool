/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex

-- [TABLET NODE: FiniteConnectedCellSetNoCheckerboard]

/-!
# FiniteConnectedCellSetNoCheckerboard

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FiniteConnectedCellSetNoCheckerboard (S : Finset LatticeCell)
    (hinside : FourNeighborConnected (S : Set LatticeCell))
    (houtside : FourNeighborConnected ((S : Set LatticeCell)ᶜ)) :
    NoCheckerboardCellVertex (S : Set LatticeCell) := by
-- BODY
  -- Signed horizontal-ray intersections, with multiplicity.
  let ray (q a b : GaussianInt) : Int :=
    if a.re ≤ q.re ∧ a.re = b.re then
      if a.im = q.im ∧ b.im = q.im + 1 then 1
      else if b.im = q.im ∧ a.im = q.im + 1 then -1 else 0
    else 0
  let potential (q a : GaussianInt) : Int :=
    if a.im = q.im + 1 ∧ a.re ≤ q.re then 1 else 0
  let weight (p : List GaussianInt) (q : GaussianInt) : Int :=
    (List.zipWith (ray q) p p.tail).sum
  -- The rectilinear closing arc SW -> NW -> NE adds this vertical term.
  let correction (z q : GaussianInt) : Int :=
    if q.im = z.im - 1 ∧ z.re - 1 ≤ q.re then 1 else 0
  have eq_iff (a b : GaussianInt) : a = b ↔ a.re = b.re ∧ a.im = b.im := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨hr, hi⟩
      exact Zsqrtd.ext hr hi
  have edge_east (q a b : GaussianInt) (hab : FourNeighborAdjacent a b)
      (ha : a ≠ q + 1) (hb : b ≠ q + 1) :
      ray (q + 1) a b = ray q a b := by
    rcases hab with (rfl | rfl | rfl | rfl) <;>
      simp only [ray, ne_eq, eq_iff, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one] at ha hb ⊢ <;> omega
  have edge_north (q a b : GaussianInt) (hab : FourNeighborAdjacent a b)
      (ha : a ≠ q + ⟨0, 1⟩) (hb : b ≠ q + ⟨0, 1⟩) :
      ray (q + ⟨0, 1⟩) a b - ray q a b = potential q a - potential q b := by
    rcases hab with (rfl | rfl | rfl | rfl) <;>
      simp only [ray, potential, ne_eq, eq_iff, Zsqrtd.re_add, Zsqrtd.im_add,
        Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_one, Zsqrtd.im_one] at ha hb ⊢ <;> omega
  have telescope (p : List GaussianInt) (x y : GaussianInt)
      (f g : GaussianInt → GaussianInt → Int) (t : GaussianInt → Int)
      (hhead : p.head? = some x) (hlast : p.getLast? = some y)
      (hc : p.IsChain (fun a b => f a b - g a b = t a - t b)) :
      (List.zipWith f p p.tail).sum - (List.zipWith g p p.tail).sum = t x - t y := by
    induction p generalizing x y with
    | nil => simp at hhead
    | cons a p ih =>
        cases p with
        | nil =>
            simp at hhead hlast
            subst x
            subst y
            simp
        | cons b p =>
            simp only [List.head?_cons, Option.some.injEq] at hhead
            subst x
            have htail : (b :: p).getLast? = some y := by simpa using hlast
            have hc' := List.isChain_cons_cons.mp hc
            have hi := ih b y rfl htail hc'.2
            simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons]
            simp only [List.tail_cons] at hi
            omega
  have east_correction (z q : GaussianInt) (h : q + 1 ≠ z - 1 - ⟨0, 1⟩) :
      correction z (q + 1) = correction z q := by
    simp [correction, eq_iff] at h ⊢
    omega
  have north_correction (z q : GaussianInt) (h : q ≠ z - 1 - ⟨0, 1⟩) :
      correction z (q + ⟨0, 1⟩) - correction z q +
        potential q z - potential q (z - 1 - ⟨0, 1⟩) = 0 := by
    simp [correction, potential, eq_iff] at h ⊢
    omega
  have constant_path (p : List GaussianInt) (x y : GaussianInt)
      (f : GaussianInt → Int) (hh : p.head? = some x) (hl : p.getLast? = some y)
      (hc : p.IsChain (fun a b => f a = f b)) : f x = f y := by
    induction p generalizing x y with
    | nil => simp at hh
    | cons a p ih =>
        cases p with
        | nil =>
            simp at hh hl
            subst x
            subst y
            rfl
        | cons b p =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst x
            have ht : (b :: p).getLast? = some y := by simpa using hl
            have hc' := List.isChain_cons_cons.mp hc
            exact hc'.1.trans (ih b y rfl ht hc'.2)
  -- Complementary steps avoid occupied edges; the closing term restores
  -- invariance of the open-walk ray count.
  have separation (S : Set LatticeCell) (hi : FourNeighborConnected S)
      (ho : FourNeighborConnected Sᶜ) (z : GaussianInt)
      (hne : z ∈ S) (hsw : z - 1 - ⟨0, 1⟩ ∈ S)
      (hnw : z - 1 ∉ S) (hse : z - ⟨0, 1⟩ ∉ S) : False := by
    obtain ⟨p, hh, hl, hm, ha⟩ := hi.2 z hne (z - 1 - ⟨0, 1⟩) hsw
    have hc : p.IsChain FourNeighborAdjacent :=
      List.isChain_iff_forall_rel_of_append_cons_cons.mpr (by
        intro a b l₁ l₂ h
        exact ha a b l₁ l₂ h)
    have east : ∀ q, q + 1 ∉ S → weight p (q + 1) = weight p q := by
      intro q hq
      have ht := telescope p z (z - 1 - ⟨0, 1⟩) (ray (q + 1)) (ray q)
        (fun _ => 0) hh hl (hc.imp_of_mem_imp (by
          intro a b ham hbm hab
          have he := edge_east q a b hab
            (fun he => hq (he ▸ hm a ham)) (fun he => hq (he ▸ hm b hbm))
          simp only [he, sub_self]))
      unfold weight
      omega
    have north : ∀ q, q + ⟨0, 1⟩ ∉ S →
        weight p (q + ⟨0, 1⟩) - weight p q =
          potential q z - potential q (z - 1 - ⟨0, 1⟩) := by
      intro q hq
      apply telescope p z (z - 1 - ⟨0, 1⟩) _ _ _ hh hl
      apply hc.imp_of_mem_imp
      intro a b ham hbm hab
      exact edge_north q a b hab
        (fun he => hq (he ▸ hm a ham)) (fun he => hq (he ▸ hm b hbm))
    let f : GaussianInt → Int := fun q => weight p q + correction z q
    have fe : ∀ q, q + 1 ∉ S → f (q + 1) = f q := by
      intro q hq
      have hn : q + 1 ≠ z - 1 - ⟨0, 1⟩ := fun he => hq (he ▸ hsw)
      dsimp [f]
      rw [east q hq, east_correction z q hn]
    have fn : ∀ q, q ∉ S → q + ⟨0, 1⟩ ∉ S → f (q + ⟨0, 1⟩) = f q := by
      intro q hq hq'
      have hn : q ≠ z - 1 - ⟨0, 1⟩ := fun he => hq (he ▸ hsw)
      have hw := north q hq'
      have ht := north_correction z q hn
      dsimp [f]
      omega
    obtain ⟨r, rh, rl, rm, ra⟩ := ho.2 (z - 1) hnw (z - ⟨0, 1⟩) hse
    have rc : r.IsChain FourNeighborAdjacent :=
      List.isChain_iff_forall_rel_of_append_cons_cons.mpr (by
        intro a b l₁ l₂ h
        exact ra a b l₁ l₂ h)
    have heq : f (z - 1) = f (z - ⟨0, 1⟩) := by
      apply constant_path r _ _ f rh rl
      apply rc.imp_of_mem_imp
      intro a b ham hbm hab
      have ha' : a ∉ S := rm a ham
      have hb' : b ∉ S := rm b hbm
      rcases hab with (rfl | rfl | rfl | rfl)
      · exact (fe a hb').symm
      · have he : a - 1 + 1 = a := by abel
        have ht := fe (a - 1) (by rwa [he])
        rwa [he] at ht
      · exact (fn a ha' hb').symm
      · have he : a - ⟨0, 1⟩ + ⟨0, 1⟩ = a := by abel
        have ht := fn (a - ⟨0, 1⟩) hb' (by rwa [he])
        rwa [he] at ht
    have he : z - 1 - ⟨0, 1⟩ + 1 = z - ⟨0, 1⟩ := by abel
    have hn : z - 1 - ⟨0, 1⟩ + ⟨0, 1⟩ = z - 1 := by abel
    have we := east (z - 1 - ⟨0, 1⟩) (by rwa [he])
    rw [he] at we
    have wn := north (z - 1 - ⟨0, 1⟩) (by rwa [hn])
    rw [hn] at wn
    have hp : potential (z - 1 - ⟨0, 1⟩) z = 0 := by
      simp [potential]
    have hp' : potential (z - 1 - ⟨0, 1⟩) (z - 1 - ⟨0, 1⟩) = 0 := by
      simp [potential]
    have cn : correction z (z - 1) = 0 := by
      simp [correction]
      omega
    have cs : correction z (z - ⟨0, 1⟩) = 1 := by simp [correction]
    dsimp [f] at heq
    rw [hp, hp'] at wn
    rw [cn, cs] at heq
    omega
  intro z h
  rcases h with ⟨hne, hsw, hnw, hse⟩ | ⟨hnw, hse, hne, hsw⟩
  · exact separation _ hinside houtside z hne hsw hnw hse
  · exact separation _ houtside (by simpa using hinside) z hne hsw
      (by simpa using hnw) (by simpa using hse)

end ApollonianSuperharmonic

end
