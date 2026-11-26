/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Subpath
import Mathlib.Data.Fintype.Pi

/-!
# Concatenating the local reroutings

The finite local replacements in the circle-intersection step used by
XII (3.1), page 245, preserve the global path homotopy. Concatenation
preserves the homotopies of its pieces, and the concatenation of the
original subpaths is homotopic to the original path. Its range stays
in the union of the new piece ranges and the initial point.
-/

public section

namespace GraphMinor.GM12

open Set

/-- A finite path concatenation stays in any set containing its start
and the ranges of all of its pieces. This also covers the empty family. -/
theorem range_path_concat_subset
    {S : Type*} [TopologicalSpace S] {n : ℕ} (v : Fin (n + 1) → S)
    (q : ∀ i : Fin n, Path (v i.castSucc) (v i.succ)) {X : Set S}
    (hv : v 0 ∈ X) (hq : ∀ i, range (q i) ⊆ X) : range (Path.concat v q) ⊆ X := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    rintro x ⟨r, rfl⟩
    exact hv
  | succ n ih =>
    have hbound : range ((Path.concat (v ∘ Fin.castSucc) (fun i => q i.castSucc)).trans
        (q (Fin.last n))) ⊆ X := by
      rw [Path.trans_range]
      exact union_subset (ih (v ∘ Fin.castSucc) (fun i => q i.castSucc) hv
        (fun i => hq i.castSucc)) (hq (Fin.last n))
    have heq := congrArg (fun γ : Path (v 0) (v (Fin.last (n + 1))) => range γ)
      (Path.concat_succ v q)
    exact heq.subset.trans hbound

/-- The exact range of a finite path concatenation is its starting
point together with the ranges of its pieces. -/
theorem range_path_concat
    {S : Type*} [TopologicalSpace S] {n : ℕ} (v : Fin (n + 1) → S)
    (q : ∀ i : Fin n, Path (v i.castSucc) (v i.succ)) :
    range (Path.concat v q) = {v 0} ∪ ⋃ i, range (q i) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Path.refl_range]
    simp only [iUnion_of_empty, union_empty]
  | succ n ih =>
    have heq := congrArg (fun γ : Path (v 0) (v (Fin.last (n + 1))) => range γ)
      (Path.concat_succ v q)
    calc
      range (Path.concat v q) = range (Path.concat (v ∘ Fin.castSucc) (fun i => q i.castSucc)) ∪
          range (q (Fin.last n)) := heq.trans (Path.trans_range _ _)
      _ = ({v 0} ∪ ⋃ i : Fin n, range (q i.castSucc)) ∪ range (q (Fin.last n)) :=
        congrArg (fun X => X ∪ range (q (Fin.last n))) (ih (v ∘ Fin.castSucc) (fun i
          => q i.castSucc))
      _ = {v 0} ∪ ⋃ i : Fin (n + 1), range (q i) := by
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
        exact union_assoc _ _ _

/-- Homotopies of finitely many subpath replacements concatenate to
a homotopy of the original path with its original endpoints. -/
theorem exists_homotopic_path_with_piecewise_range
    {S : Type*} [TopologicalSpace S] {a b : S} (p : Path a b)
    {n : ℕ} (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (q : ∀ i : Fin n, Path (p (t i.castSucc)) (p (t i.succ)))
    (hh : ∀ i, (p.subpath (t i.castSucc) (t i.succ)).Homotopic (q i)) :
    ∃ r : Path a b, p.Homotopic r ∧ range r = {p 0} ∪ ⋃ i, range (q i) := by
  let c := Path.concat (p ∘ t) q
  have hsource : a = p (t 0) := by rw [ht0, p.source]
  have htarget : b = p (t (Fin.last n)) := by rw [ht1, p.target]
  let r : Path a b := c.cast hsource htarget
  have hsub := Path.Homotopic.concat_subpath p t
  have hcomp := Path.Homotopic.concat_hcomp (p ∘ t)
    (fun i => p.subpath (t i.castSucc) (t i.succ)) q hh
  have hcast := (hsub.symm.trans hcomp).pathCast hsource htarget
  have heq : ((p.subpath (t 0) (t (Fin.last n))).cast hsource htarget) = p := by
    ext s
    change (p.subpath (t 0) (t (Fin.last n))) s = p s
    rw [ht0, ht1, Path.subpath_zero_one]
    rfl
  rw [heq] at hcast
  refine ⟨r, hcast, ?_⟩
  change range c = _
  simpa only [Function.comp_apply, ht0] using range_path_concat (p ∘ t) q

/-- The range-bound form of the finite fixed-end homotopy concatenation. -/
theorem exists_homotopic_path_of_piecewise_reroutes
    {S : Type*} [TopologicalSpace S] {a b : S} (p : Path a b)
    {n : ℕ} (t : Fin (n + 1) → unitInterval) (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1)
    (q : ∀ i : Fin n, Path (p (t i.castSucc)) (p (t i.succ)))
    (hh : ∀ i, (p.subpath (t i.castSucc) (t i.succ)).Homotopic (q i)) :
    ∃ r : Path a b, p.Homotopic r ∧ range r ⊆ {p 0} ∪ ⋃ i, range (q i) := by
  obtain ⟨r, hr, heq⟩ := exists_homotopic_path_with_piecewise_range p t ht0 ht1 q hh
  exact ⟨r, hr, heq.le⟩

end GraphMinor.GM12
