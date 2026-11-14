/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3221T2IntegralSquareFilling
public import LeanPool.ApollonianSuperharmonic.P3221T2TileFillingSupport

-- [TABLET NODE: P3221T2ClosedWalkCirculation]

/-!
# P3221T2ClosedWalkCirculation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ClosedWalkCirculationProof

private theorem east :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        ∀ (a : GaussianInt), S 1 a (a + 1) = Finsupp.single a 1 ∧ S ⟨0, 1⟩ a (a + 1) = 0 ) := by
  classical
  intro S a
  simp [S, Zsqrtd.ext_iff]

private theorem west :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        ∀ (a : GaussianInt), S 1 a (a - 1) = Finsupp.single (a - 1) (-1) ∧ S ⟨0, 1⟩ a (a - 1) = 0
            ) := by
  classical
  intro S a
  simp [S, Zsqrtd.ext_iff, sub_eq_add_neg, add_assoc]

private theorem north :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        ∀ (a : GaussianInt), S 1 a (a + ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a + ⟨0, 1⟩) = Finsupp.single a
            1 ) := by
  classical
  intro S a
  simp [S, Zsqrtd.ext_iff]

private theorem south :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        ∀ (a : GaussianInt), S 1 a (a - ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a - ⟨0, 1⟩) = Finsupp.single (a
            - ⟨0, 1⟩) (-1) ) := by
  classical
  intro S a
  simp [S, Zsqrtd.ext_iff, sub_eq_add_neg, add_assoc]

private theorem stepdiv :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        (∀ (a : GaussianInt), S 1 a (a + 1) = Finsupp.single a 1 ∧ S ⟨0, 1⟩ a (a + 1) = 0) → ((∀
            (a : GaussianInt), S 1 a (a - 1) = Finsupp.single (a - 1) (-1) ∧ S ⟨0, 1⟩ a (a - 1) =
            0) → ((∀ (a : GaussianInt), S 1 a (a + ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a + ⟨0, 1⟩) =
            Finsupp.single a 1) → ((∀ (a : GaussianInt), S 1 a (a - ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a -
            ⟨0, 1⟩) = Finsupp.single (a - ⟨0, 1⟩) (-1)) → (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (FourNeighborAdjacent a b) → (S 1 a b - (S 1 a b).mapDomain (fun z => z
            + 1) + S ⟨0, 1⟩ a b - (S ⟨0, 1⟩ a b).mapDomain (fun z => z + ⟨0, 1⟩) = Finsupp.single
            a 1 - Finsupp.single b 1))))) ) := by
  classical
  intro S east west north south a b hab
  rcases hab with rfl | rfl | rfl | rfl
  · rw [(east a).1, (east a).2]
    simp
  · rw [(west a).1, (west a).2, Finsupp.mapDomain_single]
    simp only [Finsupp.mapDomain_zero, sub_add_cancel, add_zero, sub_zero,
      Finsupp.single_neg]
    abel
  · rw [(north a).1, (north a).2]
    simp
  · rw [(south a).1, (south a).2, Finsupp.mapDomain_single]
    simp only [Finsupp.mapDomain_zero, sub_add_cancel, zero_sub,
      Finsupp.single_neg]
    abel

private theorem Hcons :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List GaussianInt), H (a :: b :: l) = S 1
            a b + H (b :: l) ) := by
  classical
  intro S H a b l
  simp [H]

private theorem Vcons :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List GaussianInt), V (a :: b :: l) = S
            ⟨0, 1⟩ a b + V (b :: l) ) := by
  classical
  intro S V a b l
  simp [V]

private theorem translation :
    (by
      classical
      exact
        ∀ (f : GaussianInt →₀ ℤ), ∀ (u : GaussianInt), ∀ (z : GaussianInt), f.mapDomain (fun y =>
            y + u) z = f (z - u) ) := by
  classical
  intro f u z
  have hinj : Function.Injective (fun y : GaussianInt => y + u) :=
    fun _ _ h => add_right_cancel h
  simpa only [sub_add_cancel] using Finsupp.mapDomain_apply_of_injective hinj f (z - u)

private theorem telescope :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → (S 1 a b - (S 1 a
            b).mapDomain (fun z => z + 1) + S ⟨0, 1⟩ a b - (S ⟨0, 1⟩ a b).mapDomain (fun z => z +
            ⟨0, 1⟩) = Finsupp.single a 1 - Finsupp.single b 1)) → (
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List GaussianInt), H (a :: b :: l) = S
            1 a b + H (b :: l)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List
            GaussianInt), V (a :: b :: l) = S ⟨0, 1⟩ a b + V (b :: l)) → (∀ (a : GaussianInt), ∀
            (b : GaussianInt), ∀ (l : List GaussianInt), ((a :: l).getLast? = some b) →
            ((List.IsChain FourNeighborAdjacent (a :: l)) → (H (a :: l) - (H (a :: l)).mapDomain
            (fun z => z + 1) + V (a :: l) - (V (a :: l)).mapDomain (fun z => z + ⟨0, 1⟩) =
            Finsupp.single a 1 - Finsupp.single b 1))))) ) := by
  classical
  intro S stepdiv H V Hcons Vcons a b l hlast hchain
  induction l generalizing a with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst b
      simp [H, V]
  | cons d l ih =>
      have hd := (List.isChain_cons_cons.mp hchain).1
      have ht := ih d (by simpa only [List.getLast?_cons_cons] using hlast)
        (List.isChain_cons_cons.mp hchain).2
      rw [Hcons, Vcons, Finsupp.mapDomain_add, Finsupp.mapDomain_add]
      calc
        _ = (S 1 a d - (S 1 a d).mapDomain (fun z => z + 1) +
            S ⟨0, 1⟩ a d - (S ⟨0, 1⟩ a d).mapDomain (fun z => z + ⟨0, 1⟩)) +
            (H (d :: l) - (H (d :: l)).mapDomain (fun z => z + 1) +
            V (d :: l) - (V (d :: l)).mapDomain (fun z => z + ⟨0, 1⟩)) := by abel
        _ = (Finsupp.single a 1 - Finsupp.single d 1) +
            (Finsupp.single d 1 - Finsupp.single b 1) := by rw [stepdiv a d hd, ht]
        _ = _ := by abel

private theorem divergence :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        (∀ (f : GaussianInt →₀ ℤ), ∀ (u : GaussianInt), ∀ (z : GaussianInt), f.mapDomain (fun y
            => y + u) z = f (z - u)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List
            GaussianInt), ((a :: l).getLast? = some b) → ((List.IsChain FourNeighborAdjacent (a
            :: l)) → (H (a :: l) - (H (a :: l)).mapDomain (fun z => z + 1) + V (a :: l) - (V (a
            :: l)).mapDomain (fun z => z + ⟨0, 1⟩) = Finsupp.single a 1 - Finsupp.single b 1))) →
            (∀ (p : List GaussianInt), ∀ (x : GaussianInt), (p.head? = some x) → ((p.getLast? =
            some x) → ((List.IsChain FourNeighborAdjacent p) → (∀ z, H p z - H p (z - 1) + V p z
            - V p (z - ⟨0, 1⟩) = 0))))) ) := by
  classical
  intro S H V translation telescope p x hfirst hlast hchain
  cases p with
  | nil => simp at hfirst
  | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      subst a
      have ht := telescope x x l hlast hchain
      rw [sub_self] at ht
      intro z
      have hv := congrArg (fun f : GaussianInt →₀ ℤ => f z) ht
      simpa only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.zero_apply,
        translation] using hv

private theorem Qadd :
    (by
      classical
      exact
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        ∀ (f : GaussianInt →₀ ℤ), ∀ (g : GaussianInt →₀ ℤ), ∀ (d : GaussianInt → ℤ), Q (f + g) d
            = Q f d + Q g d ) := by
  classical
  intro Q f g d
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

private theorem Qsub :
    (by
      classical
      exact
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        ∀ (f : GaussianInt →₀ ℤ), ∀ (g : GaussianInt →₀ ℤ), ∀ (d : GaussianInt → ℤ), Q (f - g) d
            = Q f d - Q g d ) := by
  classical
  intro Q f g d
  exact Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

private theorem Qsingle :
    (by
      classical
      exact
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        ∀ (z : GaussianInt), ∀ (n : ℤ), ∀ (d : GaussianInt → ℤ), Q (Finsupp.single z n) d = n * d
            z ) := by
  classical
  intro Q z n d
  exact Finsupp.sum_single_index (zero_mul _)

private theorem Qtranslation :
    (by
      classical
      exact
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        ∀ (f : GaussianInt →₀ ℤ), ∀ (u : GaussianInt), ∀ (d : GaussianInt → ℤ), Q (f.mapDomain
            (fun z => z + u)) d = Q f (fun z => d (z + u)) ) := by
  classical
  intro Q f u d
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

private theorem pairwalk :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        (∀ (a : GaussianInt), S 1 a (a + 1) = Finsupp.single a 1 ∧ S ⟨0, 1⟩ a (a + 1) = 0) → ((∀
            (a : GaussianInt), S 1 a (a - 1) = Finsupp.single (a - 1) (-1) ∧ S ⟨0, 1⟩ a (a - 1) =
            0) → ((∀ (a : GaussianInt), S 1 a (a + ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a + ⟨0, 1⟩) =
            Finsupp.single a 1) → ((∀ (a : GaussianInt), S 1 a (a - ⟨0, 1⟩) = 0 ∧ S ⟨0, 1⟩ a (a -
            ⟨0, 1⟩) = Finsupp.single (a - ⟨0, 1⟩) (-1)) → (
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List GaussianInt), H (a :: b :: l) = S
            1 a b + H (b :: l)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l : List
            GaussianInt), V (a :: b :: l) = S ⟨0, 1⟩ a b + V (b :: l)) → (
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        (∀ (d : GaussianInt → ℤ), Q 0 d = 0) → ((∀ (f : GaussianInt →₀ ℤ), ∀ (g : GaussianInt →₀
            ℤ), ∀ (d : GaussianInt → ℤ), Q (f + g) d = Q f d + Q g d) → ((∀ (z : GaussianInt), ∀
            (n : ℤ), ∀ (d : GaussianInt → ℤ), Q (Finsupp.single z n) d = n * d z) → (∀ (R :
            GaussianInt → GaussianInt → Prop), ∀ (D : GaussianInt → GaussianInt → ℤ), (∀ a, ∀ b,
            FourNeighborAdjacent a b → R a b → D b a = -D a b) → (∀ (p : List GaussianInt),
            (List.IsChain (fun a b => FourNeighborAdjacent a b ∧ R a b) p) → ((List.zipWith D p
            p.tail).sum = Q (H p) (fun z => D z (z + 1)) + Q (V p) (fun z => D z (z + ⟨0,
            1⟩))))))))))))) ) := by
  classical
  intro S east west north south H V Hcons Vcons Q Qzero Qadd Qsingle R D hanti p hchain
  have stepPair (a b : GaussianInt) (hab : FourNeighborAdjacent a b) (hr : R a b) :
      D a b = Q (S 1 a b) (fun z => D z (z + 1)) +
        Q (S ⟨0, 1⟩ a b) (fun z => D z (z + ⟨0, 1⟩)) := by
    have hs : D a b = -D b a := by have := hanti a b hab hr; omega
    rcases hab with rfl | rfl | rfl | rfl
    · rw [(east a).1, (east a).2, Qsingle, Qzero]
      simp
    · rw [(west a).1, (west a).2, Qsingle, Qzero]
      simpa using hs
    · rw [(north a).1, (north a).2, Qzero, Qsingle]
      simp
    · rw [(south a).1, (south a).2, Qzero, Qsingle]
      simpa using hs
  induction p with
  | nil => simp [H, V, Q]
  | cons a l ih =>
      cases l with
      | nil => simp [H, V, Q]
      | cons b l =>
          obtain ⟨⟨hab, hr⟩, ht⟩ := List.isChain_cons_cons.mp hchain
          have hi := ih ht
          simp only [List.tail_cons] at hi
          simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons] at ⊢
          rw [Hcons, Vcons, Qadd, Qadd, hi, stepPair a b hab hr]
          abel

private theorem absent :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        ∀ (E : Set (Finset GaussianInt)), ∀ (u : GaussianInt), ∀ (z : GaussianInt), ∀ (p : List
            GaussianInt), (List.IsChain (fun a b => ({a, b} : Finset GaussianInt) ∈ E) p) →
            ((({z, z + u} : Finset GaussianInt) ∉ E) → ((((p.zip p.tail).map (fun e => S u e.1
            e.2)).sum) z = 0)) ) := by
  classical
  intro S E u z p hchain hmissing
  have stepzero (a b : GaussianInt) (he : ({a, b} : Finset GaussianInt) ∈ E) :
      S u a b z = 0 := by
    dsimp only [S]
    split_ifs with hb ha
    · subst b
      by_cases haz : a = z
      · subst a
        exact False.elim (hmissing he)
      · simp [haz]
    · subst a
      by_cases hbz : b = z
      · subst b
        apply False.elim
        exact hmissing (by simpa only [Finset.pair_comm] using he)
      · simp [hbz]
    · rfl
  induction p with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          obtain ⟨he, ht⟩ := List.isChain_cons_cons.mp hchain
          simpa only [List.tail_cons, List.zip_cons_cons, List.map_cons,
            List.sum_cons, Finsupp.add_apply, stepzero a b he, zero_add] using ih ht

private theorem boundary :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        (∀ (f : GaussianInt →₀ ℤ), ∀ (u : GaussianInt), ∀ (z : GaussianInt), f.mapDomain (fun y
            => y + u) z = f (z - u)) → (
        let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
          f.sum (fun z n => n * d z)
        (∀ (f : GaussianInt →₀ ℤ), ∀ (g : GaussianInt →₀ ℤ), ∀ (d : GaussianInt → ℤ), Q (f - g) d
            = Q f d - Q g d) → ((∀ (f : GaussianInt →₀ ℤ), ∀ (u : GaussianInt), ∀ (d :
            GaussianInt → ℤ), Q (f.mapDomain (fun z => z + u)) d = Q f (fun z => d (z + u))) → (∀
            (c : GaussianInt →₀ ℤ), ∀ (D : GaussianInt → GaussianInt → ℤ), ∀ (p : List
            GaussianInt), (∀ z, H p z = c z - c (z - ⟨0, 1⟩)) → ((∀ z, V p z = c (z - 1) - c z) →
            (Q (H p) (fun z => D z (z + 1)) + Q (V p) (fun z => D z (z + ⟨0, 1⟩)) = ∑ z ∈
            c.support, c z * (D z (z + 1) + D (z + 1) (z + 1 + ⟨0, 1⟩) - D (z + ⟨0, 1⟩) (z + ⟨0,
            1⟩ + 1) - D z (z + ⟨0, 1⟩))))))) ) := by
  classical
  intro S H V translation Q Qsub Qtranslation c D p hH hV
  have hHf : H p = c - c.mapDomain (fun z => z + ⟨0, 1⟩) := by
    ext z
    simp only [Finsupp.sub_apply, translation, hH]
  have hVf : V p = c.mapDomain (fun z => z + 1) - c := by
    ext z
    simp only [Finsupp.sub_apply, translation, hV]
  rw [hHf, hVf, Qsub, Qsub, Qtranslation, Qtranslation]
  simp only [Q, Finsupp.sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  ring

private theorem square_zero :
    (by
      classical
      exact
        ∀ (D : GaussianInt → GaussianInt → ℤ), ∀ (z : GaussianInt), (D (z + 1 + ⟨0, 1⟩) (z + ⟨0,
            1⟩) =
            -D (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩)) → ((D (z + ⟨0, 1⟩) z = -D z (z + ⟨0, 1⟩)) → ((D z
                (z + 1) + D (z + 1) (z + 1 + ⟨0, 1⟩) +
            D (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) + D (z + ⟨0, 1⟩) z = 0) → (D z (z + 1) + D (z + 1) (z
                + 1 + ⟨0, 1⟩) - D (z + ⟨0, 1⟩) (z + ⟨0, 1⟩ + 1) - D z (z + ⟨0, 1⟩) = 0))) ) := by
  classical
  intro D z htop hleft hflat
  have he : z + ⟨0, 1⟩ + 1 = z + 1 + ⟨0, 1⟩ := by abel
  rw [he]
  omega

private theorem top_adjacent :
    (by
      classical
      exact
        (∀ (z : GaussianInt), FourNeighborAdjacent z (z + 1)) → (∀ (z : GaussianInt),
            FourNeighborAdjacent (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩)) ) := by
  classical
  intro horizontal z
  have he : z + 1 + ⟨0, 1⟩ = z + ⟨0, 1⟩ + 1 := by abel
  rw [he]
  exact horizontal _

private theorem hsupport :
    (by
      classical
      exact
        let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
          if b = a + u then Finsupp.single a 1
          else if a = b + u then Finsupp.single b (-1) else 0
        let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
        let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
          ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
        (∀ (E : Set (Finset GaussianInt)), ∀ (u : GaussianInt), ∀ (z : GaussianInt), ∀ (p : List
            GaussianInt), (List.IsChain (fun a b => ({a, b} : Finset GaussianInt) ∈ E) p) →
            ((({z, z + u} : Finset GaussianInt) ∉ E) → ((((p.zip p.tail).map (fun e => S u e.1
            e.2)).sum) z = 0))) → (∀ (T : ProtoTile), (LatticeTile T) → (∀ (p : List
            GaussianInt), ∀ (c : GaussianInt →₀ ℤ), (∀ (x : GaussianInt), (H p : GaussianInt → ℤ)
            x = (c : GaussianInt → ℤ) x - (c : GaussianInt → ℤ) (x - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt))) → ((∀ (x : GaussianInt), (V p : GaussianInt → ℤ) x = (c : GaussianInt
            → ℤ) (x - (1 : GaussianInt)) - (c : GaussianInt → ℤ) x) → ((List.IsChain (fun (x x_1
            : LatticeCell) => {x, x_1} ∈ FootprintEdges T) p) → (∀ z, z ∉ T.cells → c z = 0)))))
            ) := by
  classical
  intro S H V absent T hT p c hH hV hedge
  apply P3221T2TileFillingSupport T hT c
  · intro z hmissing
    rw [← hH z]
    exact absent (FootprintEdges T) 1 z p hedge hmissing
  · intro z hmissing
    rw [← hV z]
    exact absent (FootprintEdges T) ⟨0, 1⟩ z p hedge hmissing

private theorem hzT :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (c : GaussianInt →₀ ℤ), (∀ z, z ∉ T.cells → c z = 0) → (∀ (z :
            GaussianInt), (z ∈ c.support) → (z ∈ T.cells)) ) := by
  classical
  intro T c hsupport z hz
  by_contra hnot
  exact (Finsupp.mem_support_iff.mp hz) (hsupport z hnot)

end ClosedWalkCirculationProof

theorem P3221T2ClosedWalkCirculation :
    (∀ (T : ProtoTile), LatticeTile T →
      ∀ (D : GaussianInt → GaussianInt → ℤ),
      (∀ a b, FourNeighborAdjacent a b →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges T → D b a = -D a b) →
      (∀ x ∈ T.cells,
        D x (x + 1) + D (x + 1) (x + 1 + ⟨0, 1⟩) +
        D (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩) + D (x + ⟨0, 1⟩) x = 0) →
      ∀ (p : List GaussianInt) (x : GaussianInt),
      p.head? = some x → p.getLast? = some x →
      List.IsChain (fun a b => FourNeighborAdjacent a b ∧
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges T) p →
      (List.zipWith D p p.tail).sum = 0) ∧
    (∀ (D : GaussianInt → GaussianInt → ℤ),
      (∀ a b, FourNeighborAdjacent a b → D b a = -D a b) →
      (∀ x,
        D x (x + 1) + D (x + 1) (x + 1 + ⟨0, 1⟩) +
        D (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩) + D (x + ⟨0, 1⟩) x = 0) →
      ∀ (p : List GaussianInt) (x : GaussianInt),
      p.head? = some x → p.getLast? = some x →
      List.IsChain FourNeighborAdjacent p →
      (List.zipWith D p p.tail).sum = 0) := by
-- BODY
  classical
  -- Signed step coefficients retain traversal multiplicities.
  let S (u a b : GaussianInt) : GaussianInt →₀ ℤ :=
    if b = a + u then Finsupp.single a 1
    else if a = b + u then Finsupp.single b (-1) else 0
  have east (a : GaussianInt) := ClosedWalkCirculationProof.east a
  have west (a : GaussianInt) := ClosedWalkCirculationProof.west a
  have north (a : GaussianInt) := ClosedWalkCirculationProof.north a
  have south (a : GaussianInt) := ClosedWalkCirculationProof.south a
  -- The boundary of each signed step is departure minus arrival.
  have stepdiv (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :=
      ClosedWalkCirculationProof.stepdiv east west north south a b hab
  let H (p : List GaussianInt) : GaussianInt →₀ ℤ :=
    ((p.zip p.tail).map (fun e => S 1 e.1 e.2)).sum
  let V (p : List GaussianInt) : GaussianInt →₀ ℤ :=
    ((p.zip p.tail).map (fun e => S ⟨0, 1⟩ e.1 e.2)).sum
  have Hcons (a b : GaussianInt) (l : List GaussianInt) := ClosedWalkCirculationProof.Hcons a b l
  have Vcons (a b : GaussianInt) (l : List GaussianInt) := ClosedWalkCirculationProof.Vcons a b l
  have translation (f : GaussianInt →₀ ℤ) (u z : GaussianInt) :=
      ClosedWalkCirculationProof.translation f u z
  have telescope (a b : GaussianInt) (l : List GaussianInt)
      (hlast : (a :: l).getLast? = some b)
      (hchain : List.IsChain FourNeighborAdjacent (a :: l)) :=
          ClosedWalkCirculationProof.telescope stepdiv Hcons Vcons a b l hlast hchain
  have divergence (p : List GaussianInt) (x : GaussianInt)
      (hfirst : p.head? = some x) (hlast : p.getLast? = some x)
      (hchain : List.IsChain FourNeighborAdjacent p) := ClosedWalkCirculationProof.divergence
          translation telescope p x hfirst hlast hchain
  -- Pairing is additive and commutes with translation of the finite support.
  let Q (f : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) : ℤ :=
    f.sum (fun z n => n * d z)
  have Qzero (d : GaussianInt → ℤ) : Q 0 d = 0 := by simp [Q]
  have Qadd (f g : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) := ClosedWalkCirculationProof.Qadd f g d
  have Qsub (f g : GaussianInt →₀ ℤ) (d : GaussianInt → ℤ) := ClosedWalkCirculationProof.Qsub f g d
  have Qsingle (z : GaussianInt) (n : ℤ) (d : GaussianInt → ℤ) :=
      ClosedWalkCirculationProof.Qsingle z n d
  have Qtranslation (f : GaussianInt →₀ ℤ) (u : GaussianInt) (d : GaussianInt → ℤ) :=
      ClosedWalkCirculationProof.Qtranslation f u d
  have pairwalk (R : GaussianInt → GaussianInt → Prop)
      (D : GaussianInt → GaussianInt → ℤ)
      (hanti : ∀ a b, FourNeighborAdjacent a b → R a b → D b a = -D a b)
      (p : List GaussianInt)
      (hchain : List.IsChain (fun a b => FourNeighborAdjacent a b ∧ R a b) p) :
      (List.zipWith D p p.tail).sum =
        Q (H p) (fun z => D z (z + 1)) + Q (V p) (fun z => D z (z + ⟨0, 1⟩)) :=
            ClosedWalkCirculationProof.pairwalk east west north south Hcons Vcons Qzero Qadd
            Qsingle R D hanti p hchain
  have absent (E : Set (Finset GaussianInt)) (u z : GaussianInt)
      (p : List GaussianInt)
      (hchain : List.IsChain (fun a b => ({a, b} : Finset GaussianInt) ∈ E) p)
      (hmissing : ({z, z + u} : Finset GaussianInt) ∉ E) := ClosedWalkCirculationProof.absent E u
          z p hchain hmissing
  have boundary (c : GaussianInt →₀ ℤ) (D : GaussianInt → GaussianInt → ℤ)
      (p : List GaussianInt)
      (hH : ∀ z, H p z = c z - c (z - ⟨0, 1⟩))
      (hV : ∀ z, V p z = c (z - 1) - c z) :
      Q (H p) (fun z => D z (z + 1)) + Q (V p) (fun z => D z (z + ⟨0, 1⟩)) =
      ∑ z ∈ c.support, c z * (D z (z + 1) + D (z + 1) (z + 1 + ⟨0, 1⟩) -
        D (z + ⟨0, 1⟩) (z + ⟨0, 1⟩ + 1) - D z (z + ⟨0, 1⟩)) :=
            ClosedWalkCirculationProof.boundary translation Qsub Qtranslation c D p hH hV
  have square_zero (D : GaussianInt → GaussianInt → ℤ) (z : GaussianInt)
      (htop : D (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) =
        -D (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩))
      (hleft : D (z + ⟨0, 1⟩) z = -D z (z + ⟨0, 1⟩))
      (hflat : D z (z + 1) + D (z + 1) (z + 1 + ⟨0, 1⟩) +
        D (z + 1 + ⟨0, 1⟩) (z + ⟨0, 1⟩) + D (z + ⟨0, 1⟩) z = 0) :
      D z (z + 1) + D (z + 1) (z + 1 + ⟨0, 1⟩) -
        D (z + ⟨0, 1⟩) (z + ⟨0, 1⟩ + 1) - D z (z + ⟨0, 1⟩) = 0 :=
            ClosedWalkCirculationProof.square_zero D z htop hleft hflat
  have horizontal (z : GaussianInt) : FourNeighborAdjacent z (z + 1) := Or.inl rfl
  have vertical (z : GaussianInt) : FourNeighborAdjacent z (z + ⟨0, 1⟩) :=
    Or.inr (Or.inr (Or.inl rfl))
  have top_adjacent (z : GaussianInt) :
      FourNeighborAdjacent (z + ⟨0, 1⟩) (z + 1 + ⟨0, 1⟩) :=
          ClosedWalkCirculationProof.top_adjacent horizontal z
  constructor
  · intro T hT D hanti hflat p x hfirst hlast hchain
    have hadj : List.IsChain FourNeighborAdjacent p :=
      hchain.imp (fun _ _ h => h.1)
    obtain ⟨hcolumns, c, hformula, hH, hV⟩ :=
      P3221T2IntegralSquareFilling (H p) (V p)
        (divergence p x hfirst hlast hadj)
    have hedge := hchain.imp (fun _ _ h => h.2)
    have hsupport := ClosedWalkCirculationProof.hsupport absent T hT p c hH hV hedge
    rw [pairwalk (fun a b => ({a, b} : Finset GaussianInt) ∈ FootprintEdges T)
      D hanti p hchain, boundary c D p hH hV]
    apply Finset.sum_eq_zero
    intro z hz
    -- The support theorem permits antisymmetry on actual cell sides only.
    have hzT : z ∈ T.cells := ClosedWalkCirculationProof.hzT T c hsupport z hz
    have htop : ({z + ⟨0, 1⟩, z + 1 + ⟨0, 1⟩} : Finset GaussianInt) ∈
        FootprintEdges T := ⟨z, hzT, Or.inr (Or.inr (Or.inr rfl))⟩
    have hleft : ({z, z + ⟨0, 1⟩} : Finset GaussianInt) ∈ FootprintEdges T :=
      ⟨z, hzT, Or.inr (Or.inl rfl)⟩
    rw [square_zero D z
      (hanti _ _ (top_adjacent z) htop) (hanti _ _ (vertical z) hleft) (hflat z hzT),
      mul_zero]
  · intro D hanti hflat p x hfirst hlast hchain
    obtain ⟨hcolumns, c, hformula, hH, hV⟩ :=
      P3221T2IntegralSquareFilling (H p) (V p)
        (divergence p x hfirst hlast hchain)
    have hchain' : List.IsChain (fun a b => FourNeighborAdjacent a b ∧ True) p :=
      hchain.imp (fun _ _ h => ⟨h, trivial⟩)
    rw [pairwalk (fun _ _ => True) D (fun a b h _ => hanti a b h) p hchain',
      boundary c D p hH hV]
    apply Finset.sum_eq_zero
    intro z hz
    rw [square_zero D z (hanti _ _ (top_adjacent z))
      (hanti _ _ (vertical z)) (hflat z), mul_zero]

end ApollonianSuperharmonic

end
