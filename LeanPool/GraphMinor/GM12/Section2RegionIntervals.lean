/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM11.Regions

/-!
# The regions between consecutive vertex parameters

In the trace definition of XII, page 243, each open interval between
consecutive hits of the drawing lies in one region. A strictly ordered
enumeration leaves no further hit between consecutive entries, and the
continuous image of that interval is preconnected and misses the drawing.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Consecutive entries of a strictly ordered enumeration of all hits
of a drawing bound an interval with no further hit. -/
theorem no_hit_between_consecutive_parameters {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {f : ℝ → S} {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hcover : ∀ s ∈ Icc (t 0) (t (Fin.last n)), f s ∈ Γ.U → s ∈ range t)
    (i : Fin n) : ∀ s ∈ Ioo (t i.castSucc) (t i.succ), f s ∉ Γ.U := by
  intro s hs hsU
  have hs0 : t 0 ≤ s := (ht.monotone (Fin.zero_le i.castSucc)).trans hs.1.le
  have hsn : s ≤ t (Fin.last n) := hs.2.le.trans (ht.monotone (Fin.le_last i.succ))
  obtain ⟨j, hj⟩ := hcover s ⟨hs0, hsn⟩ hsU
  have hij : i.castSucc < j := ht.lt_iff_lt.mp (hj.symm ▸ hs.1)
  have hji : j < i.succ := ht.lt_iff_lt.mp (hj.symm ▸ hs.2)
  have hij' : i.val < j.val := hij
  have hji' : j.val < i.val + 1 := hji
  omega

/-- A continuous curve interval missing the drawing lies in one region.
This justifies the region assigned to each trace step in XII, page 243. -/
theorem exists_region_of_open_interval {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {f : ℝ → S} (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hoff : ∀ t ∈ Ioo a b, f t ∉ Γ.U) :
    ∃ r ∈ Γ.R, ∀ t ∈ Ioo a b, f t ∈ r := by
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  obtain ⟨r, hr, hmr⟩ := exists_region_of_notMem (hoff m hm)
  have hconn : IsPreconnected (f '' Ioo a b) := isPreconnected_Ioo.image f hf.continuousOn
  have hdis : Disjoint (f '' Ioo a b) Γ.U := Set.disjoint_left.mpr fun z hz hzU => by
    obtain ⟨t, ht, rfl⟩ := hz
    exact hoff t ht hzU
  have hsub := subset_region hr hconn hdis ⟨m, hm, rfl⟩ hmr
  exact ⟨r, hr, fun t ht => hsub ⟨t, ht, rfl⟩⟩

end GraphMinor.GM12
