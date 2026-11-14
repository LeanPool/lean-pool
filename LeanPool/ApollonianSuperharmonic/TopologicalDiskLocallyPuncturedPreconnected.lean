/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.TopologicalDisk
public import Mathlib.Analysis.Convex.PathConnected

/-!
# TopologicalDiskLocallyPuncturedPreconnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set
open scoped Topology

-- [TABLET NODE: TopologicalDiskLocallyPuncturedPreconnected]
namespace PuncturedDiskConstruction

private theorem punctured_rect_pathConnected
      (a b d : Real × Real) (h1 : a.1 < b.1) (h2 : a.2 < b.2)
      (hd : d ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) :
      IsPathConnected ((Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d}) := by
  classical
  let rx : Real := if d.1 ≤ (a.1 + b.1) / 2 then b.1 else a.1
  let ry : Real := if d.2 ≤ (a.2 + b.2) / 2 then b.2 else a.2
  let X : Real × Real := (rx, d.2)
  let Y : Real × Real := (d.1, ry)
  have hrx_mem : rx ∈ Set.Icc a.1 b.1 := by
    dsimp [rx]
    split <;> simp_all [le_of_lt]
  have hry_mem : ry ∈ Set.Icc a.2 b.2 := by
    dsimp [ry]
    split <;> simp_all [le_of_lt]
  have hrx_ne : rx ≠ d.1 := by
    dsimp [rx]
    split
    · intro he
      have := hd.2.1
      linarith
    · intro he
      have := hd.1.1
      linarith
  have hry_ne : ry ≠ d.2 := by
    dsimp [ry]
    split
    · intro he
      have := hd.2.2
      linarith
    · intro he
      have := hd.1.2
      linarith
  have hX : X ∈ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d} := by
    constructor
    · exact ⟨hrx_mem, hd.2⟩
    · simpa [X, Prod.ext_iff] using hrx_ne
  have hY : Y ∈ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d} := by
    constructor
    · exact ⟨hd.1, hry_mem⟩
    · simpa [Y, Prod.ext_iff] using hry_ne
  have segment_avoid_X {p : Real × Real}
      (hp : p ∈ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d})
      (hp2 : p.2 ≠ d.2) :
      segment Real p X ⊆ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d} := by
    rw [segment_subset_iff]
    intro u v hu hv huv
    constructor
    · exact ((convex_Icc a.1 b.1).prod (convex_Icc a.2 b.2)).segment_subset hp.1 hX.1
        (by exact ⟨u, v, hu, hv, huv, rfl⟩)
    · simp only [X]
      intro heq
      simp only [Set.mem_singleton_iff] at heq
      have hsnd := congrArg Prod.snd heq
      simp only [Prod.smul_snd, Prod.snd_add] at hsnd
      simp only [smul_eq_mul] at hsnd
      have huz : u * (p.2 - d.2) = 0 := by
        linear_combination hsnd - d.2 * huv
      have hu0 : u = 0 := (mul_eq_zero.mp huz).resolve_right (sub_ne_zero.mpr hp2)
      subst u
      have hv1 : v = 1 := by linarith
      subst v
      exact hrx_ne (by simpa [X] using congrArg Prod.fst heq)
  have segment_avoid_Y {p : Real × Real}
      (hp : p ∈ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d})
      (hp1 : p.1 ≠ d.1) :
      segment Real p Y ⊆ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d} := by
    rw [segment_subset_iff]
    intro u v hu hv huv
    constructor
    · exact ((convex_Icc a.1 b.1).prod (convex_Icc a.2 b.2)).segment_subset hp.1 hY.1
        (by exact ⟨u, v, hu, hv, huv, rfl⟩)
    · simp only [Y]
      intro heq
      simp only [Set.mem_singleton_iff] at heq
      have hfst := congrArg Prod.fst heq
      simp only [Prod.smul_fst, Prod.fst_add] at hfst
      simp only [smul_eq_mul] at hfst
      have huz : u * (p.1 - d.1) = 0 := by
        linear_combination hfst - d.1 * huv
      have hu0 : u = 0 := (mul_eq_zero.mp huz).resolve_right (sub_ne_zero.mpr hp1)
      subst u
      have hv1 : v = 1 := by linarith
      subst v
      exact hry_ne (by simpa [Y] using congrArg Prod.snd heq)
  have segment_YX :
      segment Real Y X ⊆ (Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d} := by
    rw [segment_subset_iff]
    intro u v hu hv huv
    constructor
    · exact ((convex_Icc a.1 b.1).prod (convex_Icc a.2 b.2)).segment_subset hY.1 hX.1
        (by exact ⟨u, v, hu, hv, huv, rfl⟩)
    · simp only [X, Y]
      intro heq
      simp only [Set.mem_singleton_iff] at heq
      have hfst := congrArg Prod.fst heq
      have hsnd := congrArg Prod.snd heq
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add] at hfst hsnd
      simp only [smul_eq_mul] at hfst hsnd
      by_cases hu0 : u = 0
      · subst u
        have hv1 : v = 1 := by linarith
        subst v
        exact hrx_ne (by simpa [X, Y] using congrArg Prod.fst heq)
      · have huz : u * (ry - d.2) = 0 := by
          linear_combination hsnd - d.2 * huv
        have : ry = d.2 := sub_eq_zero.mp ((mul_eq_zero.mp huz).resolve_left hu0)
        exact hry_ne this
  refine ⟨X, hX, ?_⟩
  intro p hp
  by_cases hp2 : p.2 = d.2
  · have hp1 : p.1 ≠ d.1 := by
      intro hp1
      exact hp.2 (Prod.ext hp1 hp2)
    exact ((JoinedIn.of_segment_subset (segment_avoid_Y hp hp1)).trans
      (JoinedIn.of_segment_subset segment_YX)).symm
  · exact (JoinedIn.of_segment_subset (segment_avoid_X hp hp2)).symm

private theorem disk_locally_punctured_preconnected
      (d : Metric.closedBall (0 : Real × Real) 1)
      (V₀ : Set (Metric.closedBall (0 : Real × Real) 1)) (hV₀ : V₀ ∈ nhds d) :
      ∃ V ∈ nhds d, V ⊆ V₀ ∧ IsConnected (V \ {d}) := by
  classical
  have punctured_rect_pathConnected
      (a b d : Real × Real) (h1 : a.1 < b.1) (h2 : a.2 < b.2)
      (hd : d ∈ Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) :
      IsPathConnected ((Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2) \ {d}) :=
          punctured_rect_pathConnected a b d h1 h2 hd
  let D : Set (Real × Real) := Metric.closedBall 0 1
  have himage : ((fun x : D => (x : Real × Real)) '' V₀) ∈ 𝓝[D] (d : Real × Real) := by
    exact mem_nhds_subtype_iff_nhdsWithin.mp hV₀
  rcases Metric.mem_nhdsWithin_iff.mp himage with ⟨e, he, heU⟩
  let δ : Real := min (e / 2) (1 / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδe : δ < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let a : Real × Real :=
    (max (-1) ((d : Real × Real).1 - δ), max (-1) ((d : Real × Real).2 - δ))
  let b : Real × Real :=
    (min 1 ((d : Real × Real).1 + δ), min 1 ((d : Real × Real).2 + δ))
  let R : Set (Real × Real) := Set.Icc a.1 b.1 ×ˢ Set.Icc a.2 b.2
  have hdD : (d : Real × Real) ∈ D := d.property
  have hdcoords : (d : Real × Real).1 ∈ Set.Icc (-1 : Real) 1 ∧
      (d : Real × Real).2 ∈ Set.Icc (-1 : Real) 1 := by
    have hDprod : D = Set.Icc (-1 : Real) 1 ×ˢ Set.Icc (-1 : Real) 1 := by
      change Metric.closedBall (0 : Real × Real) 1 = _
      rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
      norm_num
    rw [hDprod] at hdD
    exact hdD
  have ha1 : a.1 < b.1 := by
    dsimp [a, b]
    rcases le_total (-1 : Real) ((d : Real × Real).1 - δ) with h | h <;>
      rcases le_total (1 : Real) ((d : Real × Real).1 + δ) with h' | h' <;>
      simp [h, h'] <;>
        linarith [hdcoords.1.1, hdcoords.1.2]
  have ha2 : a.2 < b.2 := by
    dsimp [a, b]
    rcases le_total (-1 : Real) ((d : Real × Real).2 - δ) with h | h <;>
      rcases le_total (1 : Real) ((d : Real × Real).2 + δ) with h' | h' <;>
      simp [h, h'] <;>
        linarith [hdcoords.2.1, hdcoords.2.2]
  have hdR : (d : Real × Real) ∈ R := by
    constructor <;> constructor <;> dsimp [R, a, b]
    · exact max_le hdcoords.1.1 (sub_le_self _ hδ.le)
    · exact le_min hdcoords.1.2 (le_add_of_nonneg_right hδ.le)
    · exact max_le hdcoords.2.1 (sub_le_self _ hδ.le)
    · exact le_min hdcoords.2.2 (le_add_of_nonneg_right hδ.le)
  have hRball : R ⊆ Metric.closedBall (d : Real × Real) δ := by
    rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
    intro x hx
    exact ⟨⟨(max_le_iff.mp hx.1.1).2, (le_min_iff.mp hx.1.2).2⟩,
      ⟨(max_le_iff.mp hx.2.1).2, (le_min_iff.mp hx.2.2).2⟩⟩
  have hRD : R ⊆ D := by
    change R ⊆ Metric.closedBall (0 : Real × Real) 1
    rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc]
    intro x hx
    simp only [Set.mem_prod, Set.mem_Icc]
    norm_num
    exact ⟨⟨(max_le_iff.mp hx.1.1).1, (le_min_iff.mp hx.1.2).1⟩,
      ⟨(max_le_iff.mp hx.2.1).1, (le_min_iff.mp hx.2.2).1⟩⟩
  let V : Set D := (fun x : D => (x : Real × Real)) ⁻¹' R
  have hVU : V ⊆ V₀ := by
    intro x hx
    have hxball : (x : Real × Real) ∈ Metric.ball (d : Real × Real) e :=
      Metric.closedBall_subset_ball hδe (hRball hx)
    have hximage := heU ⟨hxball, x.2⟩
    rcases hximage with ⟨y, hyU, hyx⟩
    exact Subtype.coe_injective hyx ▸ hyU
  have hVnhds : V ∈ nhds d := by
    apply preimage_coe_mem_nhds_subtype.mpr
    apply Metric.mem_nhdsWithin_iff.mpr
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have hxball : x ∈ Metric.closedBall (d : Real × Real) δ :=
      Metric.mem_closedBall'.mpr (le_of_lt (Metric.mem_ball'.mp hx.1))
    rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc] at hxball
    have hxD : x.1 ∈ Set.Icc (-1 : Real) 1 ∧ x.2 ∈ Set.Icc (-1 : Real) 1 := by
      have hxD' := hx.2
      change x ∈ Metric.closedBall (0 : Real × Real) 1 at hxD'
      rw [← closedBall_prod_same, Real.closedBall_eq_Icc, Real.closedBall_eq_Icc] at hxD'
      simpa only [Set.mem_prod, Set.mem_Icc, Prod.fst_zero, Prod.snd_zero,
        zero_sub, zero_add] using hxD'
    exact ⟨⟨max_le hxD.1.1 hxball.1.1, le_min hxD.1.2 hxball.1.2⟩,
      ⟨max_le hxD.2.1 hxball.2.1, le_min hxD.2.2 hxball.2.2⟩⟩
  have hpathR : IsPathConnected (R \ {(d : Real × Real)}) :=
    punctured_rect_pathConnected a b d ha1 ha2 hdR
  have himageV : (fun x : D => (x : Real × Real)) '' (V \ {d}) =
      R \ {(d : Real × Real)} := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyR, hyd⟩, rfl⟩
      exact ⟨hyR, fun heq => hyd (Subtype.ext heq)⟩
    · rintro ⟨hxR, hxd⟩
      refine ⟨⟨x, hRD hxR⟩, ⟨hxR, ?_⟩, rfl⟩
      intro heq
      exact hxd (congrArg Subtype.val heq)
  have hconn : IsConnected (V \ {d}) := by
    constructor
    · rw [← Set.image_nonempty, himageV]
      exact hpathR.nonempty
    · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himageV]
      exact hpathR.isConnected.isPreconnected
  exact ⟨V, hVnhds, hVU, hconn⟩

end PuncturedDiskConstruction

theorem TopologicalDiskLocallyPuncturedPreconnected
    (S : Set (Real × Real)) (hS : TopologicalDisk S) (z : S)
    (U : Set S) (hU : U ∈ nhds z) :
    ∃ W ∈ nhds z, W ⊆ U ∧ IsConnected (W \ {z}) := by
-- BODY
  have disk_locally_punctured_preconnected
      (d : Metric.closedBall (0 : Real × Real) 1)
      (V₀ : Set (Metric.closedBall (0 : Real × Real) 1)) (hV₀ : V₀ ∈ nhds d) :
      ∃ V ∈ nhds d, V ⊆ V₀ ∧ IsConnected (V \ {d}) :=
          PuncturedDiskConstruction.disk_locally_punctured_preconnected d V₀ hV₀
  rcases hS with ⟨e⟩
  let d : Metric.closedBall (0 : Real × Real) 1 := e.symm z
  have hpreU : e ⁻¹' U ∈ nhds d := by
    have hedz : e d = z := by simp [d]
    rw [← hedz] at hU
    exact e.continuous.continuousAt hU
  rcases disk_locally_punctured_preconnected d (e ⁻¹' U) hpreU with
    ⟨V, hVnhds, hVU, hVconn⟩
  let W : Set S := e.symm ⁻¹' V
  have hWnhds : W ∈ nhds z := by
    exact e.symm.continuous.continuousAt hVnhds
  have hWU : W ⊆ U := by
    intro y hy
    simpa using hVU hy
  have himage : e '' (V \ {d}) = W \ {z} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxV, hxd⟩, rfl⟩
      constructor
      · simpa [W]
      · simp only [Set.mem_singleton_iff]
        intro heq
        apply hxd
        apply e.injective
        simpa [d] using heq
    · rintro ⟨hyW, hyz⟩
      refine ⟨e.symm y, ⟨hyW, ?_⟩, by simp⟩
      simp only [Set.mem_singleton_iff]
      intro heq
      apply hyz
      apply e.symm.injective
      simpa [d] using heq
  have hWconn : IsConnected (W \ {z}) := by
    rw [← himage, e.isConnected_image]
    exact hVconn
  exact ⟨W, hWnhds, hWU, hWconn⟩

end ApollonianSuperharmonic

end
