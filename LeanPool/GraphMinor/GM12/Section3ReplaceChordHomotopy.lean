/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Topology.Homotopy.Path
import LeanPool.GraphMinor.Surface.Gluing
import Mathlib.Topology.Piecewise

/-!
# Replacing a chord inside an arbitrary path

The finite-chord reduction used by XII (3.1), page 245, replaces one
chord at a time. A fixed-end homotopy of the chord to a path in the
remaining closed set extends to paths in their union: use the chord
homotopy on the chord and keep the remaining set fixed. These maps
agree at the attachment endpoints. Pasting over two closed sets proves
continuity, including paths which traverse the chord many times.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Replace a chord in any path through its union with a closed set.
The new path lies in the image of the closed set and is homotopic to
the image of the original path, with both ends fixed. -/
theorem exists_homotopic_path_after_replacing_chord
    {S T : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace T]
    {B : Set S} (hB : IsClosed B) {u v a b : S}
    (c : Path u v) (hci : Function.Injective c)
    (hmeet : range c ∩ B ⊆ {u, v})
    (j : C(S, T)) (r : Path (j u) (j v))
    (hcr : (c.map j.continuous).Homotopic r) (hrB : range r ⊆ j '' B)
    (q : Path a b) (hq : range q ⊆ B ∪ range c) (ha : a ∈ B) (hb : b ∈ B) :
    ∃ q' : Path (j a) (j b), (q.map j.continuous).Homotopic q' ∧ range q' ⊆ j '' B := by
  classical
  obtain ⟨k, hkc, hkc_inv⟩ := exists_inv_of_compactOn isCompact_univ
    c.continuous.continuousOn hci.injOn
  rw [image_univ] at hkc
  have hki : ∀ t : unitInterval, k (c t) = t := fun t => hkc_inv (mem_univ t)
  have hck : ∀ x ∈ range c, c (k x) = x := by
    rintro _ ⟨t, rfl⟩
    rw [hki]
  obtain ⟨H⟩ := hcr
  let A : Set (unitInterval × unitInterval) := {z | q z.2 ∈ B}
  let D : Set (unitInterval × unitInterval) := {z | q z.2 ∈ range c}
  have hAc : IsClosed A := hB.preimage (q.continuous.comp continuous_snd)
  have hDc : IsClosed D := (isCompact_range c.continuous).isClosed.preimage
    (q.continuous.comp continuous_snd)
  have hAD : Aᶜ ⊆ D := by
    intro z hz
    rcases hq (mem_range_self z.2) with hzB | hzC
    · exact (hz hzB).elim
    · exact hzC
  have hcl : closure Aᶜ ⊆ D := closure_minimal hAD hDc
  let f : unitInterval × unitInterval → T := fun z => j (q z.2)
  let g : unitInterval × unitInterval → T := fun z => H (z.1, k (q z.2))
  have hfc : Continuous f := j.continuous.comp (q.continuous.comp continuous_snd)
  have hkq : ContinuousOn (fun z : unitInterval × unitInterval => k (q z.2)) D :=
    hkc.comp (q.continuous.comp continuous_snd).continuousOn (fun _ hz => hz)
  have hgc : ContinuousOn g D :=
    H.continuous.comp_continuousOn (continuous_fst.continuousOn.prodMk hkq)
  have hfg : ∀ z ∈ A ∩ D, f z = g z := by
    intro z hz
    have hend := hmeet ⟨hz.2, hz.1⟩
    rcases hend with hu | hv
    · have hku : k (q z.2) = 0 := by rw [hu, ← c.source, hki]
      change j (q z.2) = H (z.1, k (q z.2))
      rw [hku, H.source, hu]
    · have hkv : k (q z.2) = 1 := by rw [hv, ← c.target, hki]
      change j (q z.2) = H (z.1, k (q z.2))
      rw [hkv, H.target, hv]
  let F : unitInterval × unitInterval → T := A.piecewise f g
  have hfr : frontier A ⊆ closure Aᶜ := by
    rw [← frontier_compl A]
    exact frontier_subset_closure
  have hFc : Continuous F := continuous_piecewise (fun z hz =>
    hfg z ⟨hAc.frontier_subset hz, hcl (hfr hz)⟩)
    hfc.continuousOn (hgc.mono hcl)
  have hsource : ∀ t : unitInterval, F (t, 0) = j a := by
    intro t
    have hm : (t, (0 : unitInterval)) ∈ A := by change q 0 ∈ B; rwa [q.source]
    change A.piecewise f g (t, 0) = j a
    rw [piecewise_eq_of_mem A f g hm]
    exact congrArg j q.source
  have htarget : ∀ t : unitInterval, F (t, 1) = j b := by
    intro t
    have hm : (t, (1 : unitInterval)) ∈ A := by change q 1 ∈ B; rwa [q.target]
    change A.piecewise f g (t, 1) = j b
    rw [piecewise_eq_of_mem A f g hm]
    exact congrArg j q.target
  let q' : Path (j a) (j b) := {
    toFun := fun t => F (1, t)
    continuous_toFun := hFc.comp (continuous_const.prodMk continuous_id)
    source' := hsource 1
    target' := htarget 1 }
  refine ⟨q', ⟨{
    toFun := F
    continuous_toFun := hFc
    map_zero_left := ?_
    map_one_left := fun _ => rfl
    prop' := ?_ }⟩, ?_⟩
  · intro t
    by_cases ht : (0, t) ∈ A
    · exact piecewise_eq_of_mem A f g ht
    · have htD := hAD ht
      change A.piecewise f g (0, t) = j (q t)
      rw [piecewise_eq_of_notMem A f g ht]
      change H (0, k (q t)) = j (q t)
      rw [H.apply_zero]
      exact congrArg j (hck (q t) htD)
  · intro t s hs
    rcases hs with rfl | hs
    · exact (hsource t).trans (congrArg j q.source.symm)
    · have hs1 : s = 1 := mem_singleton_iff.mp hs
      subst s
      exact (htarget t).trans (congrArg j q.target.symm)
  · rintro _ ⟨t, rfl⟩
    change F (1, t) ∈ j '' B
    by_cases ht : (1, t) ∈ A
    · change A.piecewise f g (1, t) ∈ j '' B
      rw [piecewise_eq_of_mem A f g ht]
      exact ⟨q t, ht, rfl⟩
    · change A.piecewise f g (1, t) ∈ j '' B
      rw [piecewise_eq_of_notMem A f g ht]
      change H (1, k (q t)) ∈ j '' B
      rw [H.apply_one]
      exact hrB (mem_range_self _)

end GraphMinor.GM12
