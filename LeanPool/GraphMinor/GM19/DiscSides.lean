/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section8f
import LeanPool.GraphMinor.Surface.Collar
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The two sides of a closed disc

In a closed connected surface, the complement of a closed disc is connected
(`isPreconnected_compl_disc`). So the complement of an `O`-arc that bounds a closed disc has exactly
two components, and a second closed disc with the same boundary is the closure of the complement of
the first (`discInt_eq_compl`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {T : Type} [TopologicalSpace T] [T2Space T] [ConnectedSpace T]

theorem isPreconnected_annulus : IsPreconnected {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 2} := by
  have hs : IsPreconnected (sphere (0 : ℂ) 1) :=
    isPreconnected_sphere (by simp [Complex.rank_real_complex]) 0 1
  have h := (isPreconnected_Ioo (a := (1 : ℝ)) (b := 2)).prod hs
  have hc : Continuous fun x : ℝ × ℂ ↦ (x.1 : ℂ) * x.2 := by fun_prop
  convert h.image _ hc.continuousOn using 1
  ext z
  constructor
  · rintro ⟨h₁, h₂⟩
    have hz : ‖z‖ ≠ 0 := by linarith
    refine ⟨(‖z‖, z / ‖z‖), ⟨⟨h₁, h₂⟩, ?_⟩, ?_⟩
    · simp [hz]
    · have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hz
      field_simp
  · rintro ⟨⟨r, w⟩, ⟨⟨h₁, h₂⟩, hw⟩, rfl⟩
    have h₁' : 1 < r := h₁
    have h₂' : r < 2 := h₂
    have hw' : ‖w‖ = 1 := by simpa using hw
    have hr : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    change 1 < ‖(r : ℂ) * w‖ ∧ ‖(r : ℂ) * w‖ < 2
    rw [norm_mul, hr, hw', mul_one]
    exact ⟨h₁', h₂'⟩

omit [ConnectedSpace T] in
/-- **Removing a closed disc from a connected open set leaves a connected set.** Take a larger
closed
disc around the disc, inside the open set `G`. A component of `G \ Δ` that misses the open annulus
between the two discs would be open and closed in `G`. So every component contains the annulus. -/
theorem isPreconnected_sdiff_disc (hT : IsClosedSurface T) {G Δ : Set T} (hG : IsOpen G)
    (hGc : IsPreconnected G) (hΔ : IsClosedDisc Δ) (hΔG : Δ ⊆ G) : IsPreconnected (G \ Δ) := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hlc : LocallyConnectedSpace T := GM11.IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Δ', hΔ', hin, hΔ'G⟩ := Surface.exists_disc_around hman hΔ (fun x _ ↦ hT.2.2 x) hG
    ((Surface.discBd_subset _).trans hΔG)
  obtain ⟨p⟩ := hΔ.isOArc_discBd
  obtain ⟨c, c', hc, -, hmap₀, hmap', hinv, hrinv, hball, hsph, -⟩ := exists_disc_collar hΔ hΔ' hin
    p
  let N : Set T := c '' {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 2}
  have hsubA : {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < 2} ⊆ closedBall 0 2 := fun z hz ↦ by
    simpa using hz.2.le
  have hNc : IsPreconnected N := isPreconnected_annulus.image _ (hc.mono hsubA)
  have hNΔ : N ⊆ G \ Δ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, fun hzΔ ↦ ?_⟩
    · have := hΔ'G (hmap₀ (hsubA hz))
      exact this.elim (fun h ↦ hΔG h) id
    rw [← hball] at hzΔ
    obtain ⟨y, hy, hyz⟩ := hzΔ
    have hyb : y ∈ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall (by norm_num) hy
    have : y = z := by
      have := congrArg c' hyz
      rwa [hinv hyb, hinv (hsubA hz)] at this
    have hy' : ‖y‖ ≤ 1 := by simpa using hy
    rw [this] at hy'
    linarith [hz.1]
  have hmemN : ∀ y ∈ discInt Δ', y ∉ Δ → y ∈ N := by
    intro y hy hyΔ
    have hyD : y ∈ c '' closedBall 0 2 := ⟨c' y, hmap' hy.1, hrinv hy.1⟩
    obtain ⟨z, hz, rfl⟩ := hyD
    have h₂ : ‖z‖ ≤ 2 := by simpa using hz
    refine ⟨z, ⟨?_, lt_of_le_of_ne h₂ fun h ↦ hy.2 ?_⟩, rfl⟩
    · by_contra hn
      exact hyΔ (hball ▸ mem_image_of_mem _ (by simpa using not_lt.mp hn))
    · rw [← hsph]
      exact mem_image_of_mem _ (by simpa using h)
  have hopen : IsOpen (G \ Δ) := hG.sdiff hΔ.isClosed
  have hbdint : discBd Δ ⊆ discInt Δ' := fun x hx ↦ hin (Surface.discBd_subset _ hx)
  have key : ∀ y ∈ G \ Δ, (connectedComponentIn (G \ Δ) y ∩ N).Nonempty := by
    intro y hy
    by_contra hn
    set C := connectedComponentIn (G \ Δ) y with hC
    have hCo : IsOpen C := hopen.connectedComponentIn
    have hCne : C.Nonempty := ⟨y, mem_connectedComponentIn hy⟩
    have hCsub : C ⊆ G \ Δ := connectedComponentIn_subset _ _
    have hclosed : closure C ∩ G ⊆ C := by
      rintro x ⟨hx, hxG⟩
      by_cases hxΔ : x ∈ Δ
      · exfalso
        by_cases hxb : x ∈ discBd Δ
        · obtain ⟨z, hzO, hzC⟩ := mem_closure_iff.mp hx _ (hΔ'.isOpen_discInt hman) (hbdint hxb)
          exact hn ⟨z, hzC, hmemN z hzO (hCsub hzC).2⟩
        · obtain ⟨z, hzO, hzC⟩ := mem_closure_iff.mp hx _ (hΔ.isOpen_discInt hman) ⟨hxΔ, hxb⟩
          exact (hCsub hzC).2 hzO.1
      · have hxm : x ∈ G \ Δ := ⟨hxG, hxΔ⟩
        obtain ⟨z, hzx, hzC⟩ := mem_closure_iff.mp hx _ (hopen.connectedComponentIn (x := x))
          (mem_connectedComponentIn hxm)
        have hsame : C = connectedComponentIn (G \ Δ) x := by
          rw [hC, connectedComponentIn_eq hzC, connectedComponentIn_eq hzx]
        rw [hsame]
        exact mem_connectedComponentIn hxm
    have hGC : G ⊆ C := by
      refine hGc.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl
        (disjoint_left.mpr fun w hw hn ↦ hn (subset_closure hw)) (fun x hx ↦ ?_)
        ⟨y, hy.1, mem_connectedComponentIn hy⟩
      by_cases hxc : x ∈ closure C
      · exact Or.inl (hclosed ⟨hxc, hx⟩)
      · exact Or.inr hxc
    obtain ⟨d, hd⟩ := hΔ.nonempty_discInt
    exact (hCsub (hGC (hΔG hd.1))).2 hd.1
  by_cases hemp : G \ Δ = ∅
  · rw [hemp]
    exact isPreconnected_empty
  obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.mpr hemp
  have hall : G \ Δ ⊆ connectedComponentIn (G \ Δ) y := by
    intro z hz
    obtain ⟨t₁, ht₁, ht₁N⟩ := key y hy
    obtain ⟨t₂, ht₂, ht₂N⟩ := key z hz
    have ht : t₂ ∈ connectedComponentIn (G \ Δ) t₁ := hNc.subset_connectedComponentIn ht₁N hNΔ ht₂N
    rw [connectedComponentIn_eq ht₁, connectedComponentIn_eq ht]
    rw [← connectedComponentIn_eq ht₂]
    exact mem_connectedComponentIn hz
  rw [Subset.antisymm hall (connectedComponentIn_subset _ _)]
  exact isPreconnected_connectedComponentIn

/-- **The complement of a closed disc in a closed connected surface is connected.** -/
theorem isPreconnected_compl_disc (hT : IsClosedSurface T) {Δ : Set T} (hΔ : IsClosedDisc Δ) :
    IsPreconnected Δᶜ := by
  have h := isPreconnected_sdiff_disc hT isOpen_univ isPreconnected_univ hΔ (subset_univ _)
  rwa [← compl_eq_univ_sdiff] at h

/-- A second closed disc with the same boundary fills the complement of the first. -/
theorem discInt_eq_compl (hT : IsClosedSurface T) {Δ Δ₂ : Set T} (hΔ : IsClosedDisc Δ)
    (hΔ₂ : IsClosedDisc Δ₂) (hbd : discBd Δ = discBd Δ₂) (hne : Δ ≠ Δ₂) :
    discInt Δ₂ = Δᶜ := by
  have hman : ∀ x : T, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hdis := discInt_disjoint hT hΔ hΔ₂ hbd hne
  have hsub : discInt Δ₂ ⊆ Δᶜ := by
    intro x hx hxΔ
    by_cases hxb : x ∈ discBd Δ
    · exact hx.2 (hbd ▸ hxb)
    · exact disjoint_left.mp hdis ⟨hxΔ, hxb⟩ hx
  refine Subset.antisymm hsub ?_
  obtain ⟨y, hy⟩ := hΔ₂.nonempty_discInt
  refine (isPreconnected_compl_disc hT hΔ).subset_left_of_subset_union (hΔ₂.isOpen_discInt hman)
    hΔ₂.isClosed.isOpen_compl (disjoint_left.mpr fun w hw hn ↦ hn hw.1) (fun x hx ↦ ?_)
    ⟨y, hsub hy, hy⟩
  by_cases hxΔ : x ∈ Δ₂
  · exact Or.inl ⟨hxΔ, fun hb ↦ hx (Surface.discBd_subset _ (hbd.symm ▸ hb))⟩
  · exact Or.inr hxΔ

end GraphMinor.GM19
