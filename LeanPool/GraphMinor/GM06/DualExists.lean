/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM06.EdgeChart
public import LeanPool.GraphMinor.GM06.Euler
public import LeanPool.GraphMinor.GM06.Section3Main
public import LeanPool.GraphMinor.GM11.RadialBasics
public import LeanPool.GraphMinor.GM11.RadialChord
public import LeanPool.GraphMinor.Surface.ArcTools
public import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Existence of a Disc Dual Drawing and Graph Minors VI, (3.6)

This file constructs a disc dual drawing `G_dual : Drawing S` satisfying
`IsDiscDualDrawing G G_dual` for every connected proper drawing `G : Drawing S` on a closed disc
space `S` (`exists_isDiscDualDrawing`), and deduces the unconditional characterization of feasible
divisions **Graph Minors VI, (3.6)** (`theorem_3_6 : Statement36`).
-/

public section

namespace GraphMinor.GM06

open Set Function Topology Metric unitInterval Complex GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

private theorem isClosed_of_isLine [T2Space S] {L : Set S} (h : IsLine L) : IsClosed L := by
  obtain ⟨φ⟩ := h
  exact (isCompact_iff_compactSpace.mpr φ.compactSpace).isClosed

private theorem IsLineWithEnds.left_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    a ∈ L := by
  obtain ⟨f, h0, _⟩ := h
  exact h0 ▸ (f 0).2

private theorem IsLineWithEnds.right_mem {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    b ∈ L := by
  obtain ⟨f, _, h1⟩ := h
  exact h1 ▸ (f 1).2

private theorem IsLineWithEnds.isLine {L : Set S} {a b : S} (h : IsLineWithEnds L a b) :
    IsLine L := by
  obtain ⟨f, _, _⟩ := h
  exact ⟨f⟩

/-! ### Section 1: Complex Disc Balls and Radial Segments Around Dual Vertices -/

/-- Closed ball of radius `δ` around `w` in complex disc coordinates `h : S → ℂ`. -/
def discBall (h : S → ℂ) (w : S) (δ : ℝ) : Set S :=
  {x : S | dist (h x) (h w) ≤ δ}

/-- Open ball of radius `δ` around `w` in complex disc coordinates `h : S → ℂ`. -/
def discOpenBall (h : S → ℂ) (w : S) (δ : ℝ) : Set S :=
  {x : S | dist (h x) (h w) < δ}

/-- Interior sphere of radius `δ` around `w` (excluding `bd S`) in complex disc coordinates `h`. -/
def discSphere (h : S → ℂ) (w : S) (δ : ℝ) : Set S :=
  {x : S | dist (h x) (h w) = δ} \ bd S

theorem isClosed_discBall {h : S → ℂ} (hh : Continuous h) (w : S) (δ : ℝ) :
    IsClosed (discBall h w δ) :=
  isClosed_le (hh.dist continuous_const) continuous_const

theorem isOpen_discOpenBall {h : S → ℂ} (hh : Continuous h) (w : S) (δ : ℝ) :
    IsOpen (discOpenBall h w δ) :=
  isOpen_lt (hh.dist continuous_const) continuous_const

omit [TopologicalSpace S] in
theorem discOpenBall_subset_discBall (h : S → ℂ) (w : S) (δ : ℝ) :
    discOpenBall h w δ ⊆ discBall h w δ :=
  fun _ hx => le_of_lt (show dist _ _ < δ from hx)

theorem discSphere_subset_discBall (h : S → ℂ) (w : S) (δ : ℝ) :
    discSphere h w δ ⊆ discBall h w δ :=
  fun _ hx => le_of_eq (show dist _ _ = δ from hx.1)

omit [TopologicalSpace S] in
theorem mem_discOpenBall_self (h : S → ℂ) (w : S) {δ : ℝ} (hδ : 0 < δ) :
    w ∈ discOpenBall h w δ := by
  simp [discOpenBall, hδ]

theorem exists_discBall_subset_of_isOpen [CompactSpace S] {h : S → ℂ}
    (hh : Continuous h) (hinj : Function.Injective h) {U : Set S} (hU : IsOpen U)
    {w : S} (hw : w ∈ U) :
    ∃ δ > 0, discBall h w δ ⊆ U := by
  have hK : IsCompact (h '' Uᶜ) := (hU.isClosed_compl.isCompact).image hh
  have hw_not : h w ∉ h '' Uᶜ := by
    rintro ⟨x, hx, hxw⟩
    exact hx (hinj hxw ▸ hw)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl (h w) hw_not
  refine ⟨ε / 2, half_pos hε, fun x hx => ?_⟩
  by_contra hxU
  have hx_mem : h x ∈ ball (h w) ε :=
    mem_ball.mpr (lt_of_le_of_lt hx (half_lt_self hε))
  exact hball hx_mem ⟨x, hxU, rfl⟩

/-- Uniform radius `δ > 0` for all regions `r : G.R` so that `discBall h (w_of r) δ ⊆ r.1`. -/
theorem exists_uniform_discBall_radius (hS : IsClosedDiscSpace S) {G : Drawing S}
    (hProper : G.IsProper) {h : S → ℂ} (hh : Continuous h) (hinj : Function.Injective h)
    (w_of : G.R → S) (hw_in : ∀ r : G.R, w_of r ∈ r.1) :
    ∃ δ > 0, δ < 1 / 2 ∧ ∀ r : G.R, discBall h (w_of r) δ ⊆ r.1 := by
  classical
  have : CompactSpace S := compactSpace_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have hR_fin : G.R.Finite := disc_finite_R hS G hProper
  have : Finite G.R := hR_fin.to_subtype
  have hex : ∀ r : G.R, ∃ δ > 0, discBall h (w_of r) δ ⊆ r.1 :=
    fun r => exists_discBall_subset_of_isOpen hh hinj (region_isOpen r.2) (hw_in r)
  choose δ_of hδ_pos hδ_sub using hex
  have h_all : ∀ F : Finset G.R, ∃ δ > 0, δ < 1 / 2 ∧
      ∀ r ∈ F, discBall h (w_of r) δ ⊆ r.1 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨1 / 4, by norm_num, by norm_num, fun _ hr => False.elim (Finset.notMem_empty _ hr)⟩
    | insert r₀ F _ ih =>
      obtain ⟨δ₁, hδ₁_pos, hδ₁_lt, hδ₁_sub⟩ := ih
      refine ⟨min δ₁ (δ_of r₀), lt_min hδ₁_pos (hδ_pos r₀),
        lt_of_le_of_lt (min_le_left _ _) hδ₁_lt, ?_⟩
      intro r' hr'
      rcases Finset.mem_insert.mp hr' with rfl | hr'
      · exact fun x hx => hδ_sub r' (le_trans (show dist _ _ ≤ _ from hx) (min_le_right _ _))
      · exact fun x hx => hδ₁_sub r' hr' (le_trans (show dist _ _ ≤ _ from hx) (min_le_left _ _))
  let _ : Fintype G.R := Fintype.ofFinite G.R
  obtain ⟨δ, hδ_pos, hδ_lt, hδ_sub⟩ := h_all Finset.univ
  exact ⟨δ, hδ_pos, hδ_lt, fun r => hδ_sub r (Finset.mem_univ r)⟩

/-- Straight radial segment in complex disc coordinates from `w` (at `t = 0`) to `y` (at `t = 1`).
-/
noncomputable def radMap (h : S → ℂ) (g : ℂ → S) (w y : S) (t : I) : S :=
  g ((1 - (t : ℝ)) • h w + (t : ℝ) • h y)

omit [TopologicalSpace S] in
theorem radMap_arg_mem_closedBall {h : S → ℂ}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1) (w y : S) (t : I) :
    (1 - (t : ℝ)) • h w + (t : ℝ) • h y ∈ closedBall (0 : ℂ) 1 :=
  convex_closedBall (0 : ℂ) 1 (hmem w) (hmem y)
    (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))

omit [TopologicalSpace S] in
theorem h_radMap {h : S → ℂ} {g : ℂ → S}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z) (w y : S) (t : I) :
    h (radMap h g w y t) = (1 - (t : ℝ)) • h w + (t : ℝ) • h y :=
  hgr _ (radMap_arg_mem_closedBall hmem w y t)

omit [TopologicalSpace S] in
theorem radMap_zero {h : S → ℂ} {g : ℂ → S} (hgl : ∀ x : S, g (h x) = x) (w y : S) :
    radMap h g w y 0 = w := by
  simp [radMap, hgl]

omit [TopologicalSpace S] in
theorem radMap_one {h : S → ℂ} {g : ℂ → S} (hgl : ∀ x : S, g (h x) = x) (w y : S) :
    radMap h g w y 1 = y := by
  simp [radMap, hgl]

omit [TopologicalSpace S] in
theorem dist_h_radMap {h : S → ℂ} {g : ℂ → S}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z) (w y : S) (t : I) :
    dist (h (radMap h g w y t)) (h w) = (t : ℝ) * dist (h y) (h w) := by
  rw [h_radMap hmem hgr, dist_eq_norm, dist_eq_norm]
  have heq : (1 - (t : ℝ)) • h w + (t : ℝ) • h y - h w = (t : ℝ) • (h y - h w) := by
    module
  rw [heq, norm_smul, Real.norm_of_nonneg t.2.1]

theorem radMap_notMem_bd {h : S → ℂ} {g : ℂ → S}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    (hball_iff : ∀ x : S, x ∉ bd S ↔ h x ∈ ball (0 : ℂ) 1)
    (w : S) {y : S} (hy : y ∉ bd S) {t : I} (ht : (0 : I) < t) :
    radMap h g w y t ∉ bd S := by
  rw [hball_iff, h_radMap hmem hgr, mem_ball_zero_iff]
  have hw_norm : ‖h w‖ ≤ 1 := mem_closedBall_zero_iff.mp (hmem w)
  have hy_norm : ‖h y‖ < 1 := mem_ball_zero_iff.mp ((hball_iff y).mp hy)
  have ht_pos : (0 : ℝ) < t := ht
  have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  calc
    ‖(1 - (t : ℝ)) • h w + (t : ℝ) • h y‖
      ≤ ‖(1 - (t : ℝ)) • h w‖ + ‖(t : ℝ) • h y‖ := norm_add_le _ _
    _ = (1 - (t : ℝ)) * ‖h w‖ + (t : ℝ) * ‖h y‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg t.2.1]
    _ < (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 := by
      nlinarith
    _ = 1 := by ring

theorem isArcMap_radMap {h : S → ℂ} {g : ℂ → S}
    (hinj : Function.Injective h)
    (hg : ContinuousOn g (closedBall (0 : ℂ) 1))
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    {w y : S} (hyw : y ≠ w) :
    IsArcMap (radMap h g w y) := by
  refine ⟨hg.comp_continuous (by fun_prop) (radMap_arg_mem_closedBall hmem w y), ?_⟩
  intro s t hst
  have h1 : h (radMap h g w y s) = h (radMap h g w y t) := congrArg h hst
  rw [h_radMap hmem hgr, h_radMap hmem hgr] at h1
  have h2 : ((s : ℝ) - (t : ℝ)) • (h y - h w) = 0 := by
    calc
      ((s : ℝ) - (t : ℝ)) • (h y - h w)
        = ((1 - (s : ℝ)) • h w + (s : ℝ) • h y) - ((1 - (t : ℝ)) • h w + (t : ℝ) • h y) := by
          module
      _ = 0 := sub_eq_zero.mpr h1
  have hne : h y - h w ≠ 0 := sub_ne_zero.mpr (hinj.ne hyw)
  have h3 : (s : ℝ) - (t : ℝ) = 0 := (smul_eq_zero.mp h2).resolve_right hne
  exact Subtype.ext (sub_eq_zero.mp h3)

theorem isLineWithEnds_range_radMap [T2Space S] {h : S → ℂ} {g : ℂ → S}
    (hinj : Function.Injective h)
    (hg : ContinuousOn g (closedBall (0 : ℂ) 1))
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgl : ∀ x : S, g (h x) = x)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    {w y : S} (hyw : y ≠ w) :
    IsLineWithEnds (range (radMap h g w y)) y w := by
  have harc := isArcMap_radMap hinj hg hmem hgr hyw
  have hL := IsArcMap.isLineWithEnds harc
  rw [radMap_zero hgl, radMap_one hgl] at hL
  exact Surface.IsLineWithEnds.symm hL

theorem range_radMap_subset_discBall {h : S → ℂ} {g : ℂ → S}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    {w y : S} {δ : ℝ} (hy : y ∈ discSphere h w δ) :
    range (radMap h g w y) ⊆ discBall h w δ := by
  rintro _ ⟨t, rfl⟩
  change dist (h (radMap h g w y t)) (h w) ≤ δ
  rw [dist_h_radMap hmem hgr, hy.1]
  have hδ : 0 ≤ δ := by rw [← hy.1]; exact dist_nonneg
  nlinarith [t.2.1, t.2.2]

theorem range_radMap_inter_discSphere {h : S → ℂ} {g : ℂ → S}
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgl : ∀ x : S, g (h x) = x)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    {w y : S} {δ : ℝ} (hδ : 0 < δ) (hy : y ∈ discSphere h w δ) :
    range (radMap h g w y) ∩ discSphere h w δ = {y} := by
  ext x
  simp only [mem_inter_iff, mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨⟨t, rfl⟩, hx_sph, -⟩
    change dist (h (radMap h g w y t)) (h w) = δ at hx_sph
    rw [dist_h_radMap hmem hgr, hy.1] at hx_sph
    have ht1 : (t : ℝ) = 1 := by nlinarith
    have ht : t = 1 := Subtype.ext ht1
    rw [ht, radMap_one hgl]
  · rintro rfl
    exact ⟨⟨1, radMap_one hgl w x⟩, hy⟩

omit [TopologicalSpace S] in
theorem range_radMap_inter_eq_singleton {h : S → ℂ} {g : ℂ → S}
    (hinj : Function.Injective h)
    (hmem : ∀ x : S, h x ∈ closedBall (0 : ℂ) 1)
    (hgl : ∀ x : S, g (h x) = x)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    {w y₁ y₂ : S} {δ : ℝ} (hδ : 0 < δ)
    (hy₁ : dist (h y₁) (h w) = δ) (hy₂ : dist (h y₂) (h w) = δ) (hne : y₁ ≠ y₂) :
    range (radMap h g w y₁) ∩ range (radMap h g w y₂) = {w} := by
  ext x
  simp only [mem_inter_iff, mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
    have hd : dist (h (radMap h g w y₁ s)) (h w) = dist (h (radMap h g w y₂ t)) (h w) := by
      rw [hst]
    rw [dist_h_radMap hmem hgr, dist_h_radMap hmem hgr, hy₁, hy₂] at hd
    have hst_eq : (s : ℝ) = (t : ℝ) := mul_right_cancel₀ hδ.ne' hd
    by_cases hs0 : (s : ℝ) = 0
    · have hs : s = 0 := Subtype.ext hs0
      rw [hs, radMap_zero hgl]
    · have h1 : h (radMap h g w y₂ t) = h (radMap h g w y₁ s) := congrArg h hst
      rw [h_radMap hmem hgr, h_radMap hmem hgr, ← hst_eq] at h1
      have h2 : (s : ℝ) • (h y₂ - h y₁) = 0 := by
        calc
          (s : ℝ) • (h y₂ - h y₁)
            = ((1 - (s : ℝ)) • h w + (s : ℝ) • h y₂) - ((1 - (s : ℝ)) • h w + (s : ℝ) • h y₁) := by
              module
          _ = 0 := sub_eq_zero.mpr h1
      have h3 : h y₂ - h y₁ = 0 := (smul_eq_zero.mp h2).resolve_left hs0
      exact False.elim (hne (hinj (sub_eq_zero.mp h3).symm))
  · rintro rfl
    exact ⟨⟨0, radMap_zero hgl x y₁⟩, ⟨0, radMap_zero hgl x y₂⟩⟩

/-! ### Section 2: Stub Paths in Edge Charts and Incident Regions -/

/-- Parameterization of the half-edge stub in `ℂ` along the positive (`sgn = true`) or negative
(`sgn = false`) imaginary axis up to `± Complex.I / 2`. -/
noncomputable def zStub (sgn : Bool) (t : I) : ℂ :=
  (t : ℝ) • (if sgn then Complex.I / 2 else -Complex.I / 2)

theorem zStub_zero (sgn : Bool) : zStub sgn 0 = 0 := by
  simp [zStub]

theorem norm_zStub (sgn : Bool) (t : I) : ‖zStub sgn t‖ = (t : ℝ) / 2 := by
  simp only [zStub, norm_smul, Real.norm_of_nonneg t.2.1]
  cases sgn <;> simp <;> ring

theorem zStub_mem_closedBall_half (sgn : Bool) (t : I) :
    zStub sgn t ∈ closedBall (0 : ℂ) (1 / 2) := by
  rw [mem_closedBall_zero_iff, norm_zStub]
  linarith [t.2.2]

theorem zStub_mem_ball_one (sgn : Bool) (t : I) :
    zStub sgn t ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_zStub]
  linarith [t.2.2]

theorem zStub_mem_closedBall_one (sgn : Bool) (t : I) :
    zStub sgn t ∈ closedBall (0 : ℂ) 1 :=
  ball_subset_closedBall (zStub_mem_ball_one sgn t)

theorem zStub_re (sgn : Bool) (t : I) : (zStub sgn t).re = 0 := by
  cases sgn <;> simp [zStub]

theorem zStub_im (sgn : Bool) (t : I) :
    (zStub sgn t).im = if sgn then (t : ℝ) / 2 else -(t : ℝ) / 2 := by
  cases sgn <;> simp [zStub] <;> ring

theorem zStub_im_eq_zero_iff (sgn : Bool) (t : I) :
    (zStub sgn t).im = 0 ↔ t = 0 := by
  rw [zStub_im, Subtype.ext_iff]
  cases sgn <;> simp

theorem zStub_injective (sgn : Bool) : Function.Injective (zStub sgn) := by
  intro s t h
  have him := congrArg Complex.im h
  rw [zStub_im, zStub_im] at him
  cases sgn <;> simp only [ite_true, Bool.false_eq_true, ite_false] at him <;>
    exact Subtype.ext (by linarith)

theorem continuous_zStub (sgn : Bool) : Continuous (zStub sgn) := by
  unfold zStub
  fun_prop

theorem isArcMap_stub {φ : ℂ → S} (hφc : ContinuousOn φ (closedBall (0 : ℂ) 1))
    (hφi : InjOn φ (closedBall (0 : ℂ) 1)) (sgn : Bool) :
    IsArcMap (fun t : I => φ (zStub sgn t)) := by
  refine ⟨hφc.comp_continuous (continuous_zStub sgn) (zStub_mem_closedBall_one sgn), ?_⟩
  intro s t hst
  exact zStub_injective sgn
    (hφi (zStub_mem_closedBall_one sgn s) (zStub_mem_closedBall_one sgn t) hst)

omit [TopologicalSpace S] in
theorem stub_inter_stub_opposite {φ : ℂ → S} (hφi : InjOn φ (closedBall (0 : ℂ) 1)) :
    range (fun t : I => φ (zStub true t)) ∩ range (fun t : I => φ (zStub false t)) = {φ 0} := by
  ext x
  simp only [mem_inter_iff, mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
    have hz := hφi (zStub_mem_closedBall_one false t) (zStub_mem_closedBall_one true s) hst
    have him := congrArg Complex.im hz
    rw [zStub_im, zStub_im] at him
    simp only [Bool.false_eq_true, ↓reduceIte] at him
    have hs0 : (s : ℝ) = 0 := by linarith [s.2.1, t.2.1]
    have hs : s = 0 := Subtype.ext hs0
    rw [hs, zStub_zero]
  · rintro rfl
    exact ⟨⟨0, by simp [zStub_zero]⟩, ⟨0, by simp [zStub_zero]⟩⟩

/-! ### Section 3: Non-Separation by Families of Arcs Attached to `G.U` -/

theorem connectedComponentIn_sdiff_biUnion_arcs (hS : IsClosedDiscSpace S) {G : Drawing S}
    {α : Type*} (F : Finset α)
    (J : α → Set S) (v : α → S)
    (hJ_line : ∀ a ∈ F, IsLine (J a))
    (hJ_U : ∀ a ∈ F, J a ∩ G.U ⊆ {v a})
    (hJ_bd : ∀ a ∈ F, J a ∩ bd S ⊆ {v a})
    (hJ_inter : ∀ a ∈ F, ∀ b ∈ F, b ≠ a → J a ∩ J b ⊆ {v a})
    {r : Set S} (hr : r ∈ G.R)
    {x y : S} (hx : x ∈ (r \ bd S) \ ⋃ a ∈ F, J a) (hy : y ∈ (r \ bd S) \ ⋃ a ∈ F, J a) :
    y ∈ connectedComponentIn ((r \ bd S) \ ⋃ a ∈ F, J a) x := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have hmain : y ∈ connectedComponentIn ((univ \ bd S) \ (G.U ∪ ⋃ a ∈ F, J a)) x := by
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
      exact mem_connectedComponentIn_sdiff_bd_of_region hS hr hx.1 hy.1
    | insert a₀ F ha₀ ih =>
      have hJ_line' : ∀ a ∈ F, IsLine (J a) := fun a ha => hJ_line a (Finset.mem_insert_of_mem ha)
      have hJ_U' : ∀ a ∈ F, J a ∩ G.U ⊆ {v a} := fun a ha => hJ_U a (Finset.mem_insert_of_mem ha)
      have hJ_bd' : ∀ a ∈ F, J a ∩ bd S ⊆ {v a} := fun a ha => hJ_bd a (Finset.mem_insert_of_mem ha)
      have hJ_inter' : ∀ a ∈ F, ∀ b ∈ F, b ≠ a → J a ∩ J b ⊆ {v a} :=
        fun a ha b hb hne => hJ_inter a (Finset.mem_insert_of_mem ha) b
          (Finset.mem_insert_of_mem hb) hne
      have hx' : x ∈ (r \ bd S) \ ⋃ a ∈ F, J a :=
        ⟨hx.1, fun h => hx.2 (by rw [Finset.set_biUnion_insert]; exact Or.inr h)⟩
      have hy' : y ∈ (r \ bd S) \ ⋃ a ∈ F, J a :=
        ⟨hy.1, fun h => hy.2 (by rw [Finset.set_biUnion_insert]; exact Or.inr h)⟩
      have h_ih := ih hJ_line' hJ_U' hJ_bd' hJ_inter' hx' hy'
      let K : Set S := G.U ∪ ⋃ a ∈ F, J a
      have hK_cl : IsClosed K :=
        G.isClosed_U.union (F.finite_toSet.isClosed_biUnion fun a ha => isClosed_of_isLine
          (hJ_line' a ha))
      have ha₀_mem : a₀ ∈ insert a₀ F := Finset.mem_insert_self a₀ F
      have hJK : J a₀ ∩ K ⊆ {v a₀} := by
        rintro z ⟨hzJ, hzU | hzF⟩
        · exact hJ_U a₀ ha₀_mem ⟨hzJ, hzU⟩
        · obtain ⟨b, hbF, hzb⟩ := mem_iUnion₂.mp hzF
          have hba : b ≠ a₀ := fun h => ha₀ (h ▸ hbF)
          exact hJ_inter a₀ ha₀_mem b (Finset.mem_insert_of_mem hbF) hba ⟨hzJ, hzb⟩
      have hx_in : x ∈ (univ \ bd S) \ (K ∪ J a₀) := by
        refine ⟨⟨mem_univ x, hx.1.2⟩, ?_⟩
        rintro ((hxU | hxF) | hxJ₀)
        · exact region_subset hr hx.1.1 hxU
        · exact hx'.2 hxF
        · exact hx.2 (by rw [Finset.set_biUnion_insert]; exact Or.inl hxJ₀)
      have hy_in : y ∈ (univ \ bd S) \ (K ∪ J a₀) := by
        refine ⟨⟨mem_univ y, hy.1.2⟩, ?_⟩
        rintro ((hyU | hyF) | hyJ₀)
        · exact region_subset hr hy.1.1 hyU
        · exact hy'.2 hyF
        · exact hy.2 (by rw [Finset.set_biUnion_insert]; exact Or.inl hyJ₀)
      have h_step :=
        disc_sdiff_arc_connectedComponentIn hS hK_cl (hJ_line a₀ ha₀_mem) hJK
          (hJ_bd a₀ ha₀_mem) hx_in hy_in h_ih
      have heq : K ∪ J a₀ = G.U ∪ ⋃ a ∈ insert a₀ F, J a := by
        dsimp [K]
        rw [Finset.set_biUnion_insert, union_assoc, union_comm (⋃ a ∈ F, J a) (J a₀)]
      rwa [heq] at h_step
  let C := connectedComponentIn ((univ \ bd S) \ (G.U ∪ ⋃ a ∈ F, J a)) x
  have hC_sub : C ⊆ (univ \ bd S) \ (G.U ∪ ⋃ a ∈ F, J a) := connectedComponentIn_subset _ _
  have hx_C : x ∈ C := mem_connectedComponentIn
    ⟨⟨mem_univ x, hx.1.2⟩, fun h => h.elim (region_subset hr hx.1.1) hx.2⟩
  have hC_disj_U : Disjoint C G.U :=
    disjoint_left.mpr fun z hz hzU => (hC_sub hz).2 (Or.inl hzU)
  have hC_r : C ⊆ r :=
    subset_region hr isPreconnected_connectedComponentIn hC_disj_U hx_C hx.1.1
  have hC_target : C ⊆ (r \ bd S) \ ⋃ a ∈ F, J a :=
    fun z hz => ⟨⟨hC_r hz, (hC_sub hz).1.2⟩, fun hzF => (hC_sub hz).2 (Or.inr hzF)⟩
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hx_C hC_target hmain

/-! ### Section 4: Truncating a Path from a Stub to a Dual Vertex Ball -/

private theorem first_hit_mem_discSphere {h : S → ℂ} (hh : Continuous h)
    {w : S} {δ : ℝ} {α : I → S} (hα_cont : Continuous α)
    {τ : I} (hτ_pos' : (0 : ℝ) < τ) (hτ_mem : α τ ∈ discBall h w δ)
    (hbefore_τ : ∀ t : I, t < τ → α t ∉ discBall h w δ)
    (hy_bd : α τ ∉ bd S) : α τ ∈ discSphere h w δ := by
  refine ⟨le_antisymm hτ_mem ?_, hy_bd⟩
  by_contra hlt
  push Not at hlt
  have hopen_pre : IsOpen (α ⁻¹' discOpenBall h w δ) :=
    (isOpen_discOpenBall hh w δ).preimage hα_cont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen_pre τ hlt
  let t' : ℝ := max 0 ((τ : ℝ) - ε / 2)
  have ht'_mem : t' ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (by linarith [τ.2.2])⟩
  let t_sub : I := ⟨t', ht'_mem⟩
  have ht_lt : t_sub < τ := by
    change max 0 ((τ : ℝ) - ε / 2) < (τ : ℝ)
    exact max_lt hτ_pos' (by linarith)
  have ht_in_ball : t_sub ∈ ball τ ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have h1 : (τ : ℝ) - ε / 2 ≤ t' := le_max_right _ _
    have h2 : t' < (τ : ℝ) := ht_lt
    rw [abs_of_neg (by linarith)]
    linarith
  exact hbefore_τ t_sub ht_lt (discOpenBall_subset_discBall h w δ (hball ht_in_ball))

/-- Given a stub `stub : I → S` in region `r` and a connected open subset `Ω ⊆ r \ bd S` containing
`range stub \ {stub 0}` and a point `c ∈ discOpenBall h w δ \ bd S`, we can construct a truncated
spoke arc `T` from `stub 0` to a point `y ∈ discSphere h w δ` inside `{stub 0} ∪ Ω` that meets
`discBall h w δ` only at `y` and agrees with `stub` near `stub 0`. -/
theorem exists_truncated_spoke_of_connected (hS : IsClosedDiscSpace S)
    {h : S → ℂ} (hh : Continuous h) {w : S} {δ : ℝ}
    {Ω : Set S} (hΩ_open : IsOpen Ω) (hΩ_bd : Disjoint Ω (bd S))
    {stub : I → S} (hstub_arc : IsArcMap stub)
    (hstub_0_not_Ω : stub 0 ∉ Ω)
    (hstub_Ω : range stub \ {stub 0} ⊆ Ω)
    (hstub_ball : Disjoint (range stub) (discBall h w δ))
    {c : S} (hc_ball : c ∈ discOpenBall h w δ)
    (hconn : c ∈ connectedComponentIn Ω (stub 1)) :
    ∃ (T A_far : Set S) (y : S) (u₀ : I),
      IsLineWithEnds T (stub 0) y ∧
      y ∈ discSphere h w δ ∧
      T \ {stub 0} ⊆ Ω ∧
      T ∩ discBall h w δ = {y} ∧
      (0 : I) < u₀ ∧
      IsClosed A_far ∧
      stub 0 ∉ A_far ∧
      T = stub '' Icc 0 u₀ ∪ A_far := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have h1_ne_0 : stub 1 ≠ stub 0 := fun heq => by
    exact zero_ne_one (hstub_arc.2 heq.symm)
  have h1_Ω : stub 1 ∈ Ω := hstub_Ω ⟨⟨1, rfl⟩, h1_ne_0⟩
  have hcomp_open : IsOpen (connectedComponentIn Ω (stub 1)) := hΩ_open.connectedComponentIn
  have hcomp_pc : IsPathConnected (connectedComponentIn Ω (stub 1)) :=
    hcomp_open.isConnected_iff_isPathConnected.mp
      ⟨⟨stub 1, mem_connectedComponentIn h1_Ω⟩, isPreconnected_connectedComponentIn⟩
  obtain ⟨P, hP⟩ := hcomp_pc.joinedIn (stub 1) (mem_connectedComponentIn h1_Ω) c hconn
  have h1_ne_c : stub 1 ≠ c := fun heq =>
    disjoint_left.mp hstub_ball ⟨1, rfl⟩ (heq ▸ discOpenBall_subset_discBall h w δ hc_ball)
  obtain ⟨α, hα_cont, hα_inj, hα0, hα1, hα_sub⟩ :=
    exists_arc_of_path P.continuous (by simpa using h1_ne_c)
  have hα0' : α 0 = stub 1 := by simpa using hα0
  have hα1' : α 1 = c := by simpa using hα1
  have hα_arc : IsArcMap α := ⟨hα_cont, hα_inj⟩
  have hα_Ω : range α ⊆ Ω := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hα_sub ⟨t, rfl⟩
    rw [← hs]
    exact connectedComponentIn_subset _ _ (hP s)
  -- Step 1: First hit `τ` of `discBall h w δ` along `α`.
  let S_hit : Set I := α ⁻¹' discBall h w δ
  have hS_hit_cl : IsClosed S_hit := (isClosed_discBall hh w δ).preimage hα_cont
  have h1_hit : (1 : I) ∈ S_hit := by
    change α 1 ∈ discBall h w δ
    rw [hα1']
    exact discOpenBall_subset_discBall h w δ hc_ball
  obtain ⟨τ, hτ_mem, hτ_min⟩ := hS_hit_cl.isCompact.exists_isLeast ⟨1, h1_hit⟩
  have h0_not_hit : (0 : I) ∉ S_hit := by
    change α 0 ∉ discBall h w δ
    rw [hα0']
    exact disjoint_left.mp hstub_ball ⟨1, rfl⟩
  have hτ_pos : (0 : I) < τ :=
    lt_of_le_of_ne (unitInterval.nonneg τ) (fun heq => h0_not_hit (heq ▸ hτ_mem))
  have hτ_pos' : (0 : ℝ) < τ := hτ_pos
  have hbefore_τ : ∀ t : I, t < τ → α t ∉ discBall h w δ :=
    fun t hlt ht => not_le.mpr hlt (hτ_min ht)
  let y : S := α τ
  have hy_Ω : y ∈ Ω := hα_Ω ⟨τ, rfl⟩
  have hy_sph : y ∈ discSphere h w δ :=
    first_hit_mem_discSphere hh hα_cont hτ_pos' hτ_mem hbefore_τ (disjoint_left.mp hΩ_bd hy_Ω)
  let α₁ : I → S := pieceA α 0 τ
  have hα₁_arc : IsArcMap α₁ := isArcMap_pieceA hα_arc le_rfl hτ_pos' τ.2.2
  have hα₁_0 : α₁ 0 = stub 1 := by
    dsimp [α₁]
    rw [pieceA_zero]
    exact (extI_coe α 0).trans hα0'
  have hα₁_1 : α₁ 1 = y := by dsimp [α₁]; rw [pieceA_one, extI_coe]
  have hα₁_range : range α₁ = α '' Icc 0 τ := by
    dsimp [α₁]
    rw [range_pieceA α le_rfl hτ_pos'.le τ.2.2]
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans τ.2.2⟩
      exact ⟨⟨r, hrI⟩, hr, (extI_of_mem α hrI).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.1, ht, extI_coe α t⟩
  have hα₁_Ω : range α₁ ⊆ Ω := by
    rw [hα₁_range]
    exact (image_subset_range α _).trans hα_Ω
  have hα₁_ball : ∀ s : I, α₁ s ∈ discBall h w δ ↔ s = 1 := by
    intro s
    constructor
    · intro hs
      have hs_mem : α₁ s ∈ range α₁ := mem_range_self s
      rw [hα₁_range] at hs_mem
      obtain ⟨t, ht, hts⟩ := hs_mem
      have ht_in : t ∈ S_hit := by
        change α t ∈ discBall h w δ
        rw [hts]
        exact hs
      have ht_ge : τ ≤ t := hτ_min ht_in
      have ht_eq : t = τ := le_antisymm ht.2 ht_ge
      subst ht_eq
      exact hα₁_arc.2 (hts.symm.trans hα₁_1.symm)
    · rintro rfl
      rw [hα₁_1]
      exact discSphere_subset_discBall h w δ hy_sph
  -- Step 2: Last hit `s₀` of `range stub` along `α₁`.
  let S_stub : Set I := α₁ ⁻¹' range stub
  have hstub_cl : IsClosed (range stub) := (isCompact_range hstub_arc.1).isClosed
  have hS_stub_cl : IsClosed S_stub := hstub_cl.preimage hα₁_arc.1
  have h0_stub : (0 : I) ∈ S_stub := by
    change α₁ 0 ∈ range stub
    rw [hα₁_0]
    exact ⟨1, rfl⟩
  obtain ⟨s₀, hs₀_mem, hs₀_max⟩ := hS_stub_cl.isCompact.exists_isGreatest ⟨0, h0_stub⟩
  have h1_not_stub : (1 : I) ∉ S_stub := by
    change α₁ 1 ∉ range stub
    rw [hα₁_1]
    exact fun hy_stub => disjoint_left.mp hstub_ball hy_stub (discSphere_subset_discBall h w δ
      hy_sph)
  have hs₀_lt : s₀ < (1 : I) :=
    lt_of_le_of_ne (unitInterval.le_one s₀) (fun heq => h1_not_stub (heq ▸ hs₀_mem))
  have hs₀_lt' : (s₀ : ℝ) < 1 := hs₀_lt
  have hafter_s₀ : ∀ s : I, s₀ < s → α₁ s ∉ range stub :=
    fun s hgt hs => not_le.mpr hgt (hs₀_max hs)
  obtain ⟨u₀, hu₀_eq⟩ : α₁ s₀ ∈ range stub := hs₀_mem
  have hu₀_pos : (0 : I) < u₀ := by
    refine lt_of_le_of_ne (unitInterval.nonneg u₀) fun heq => ?_
    have h_in_Ω : α₁ s₀ ∈ Ω := hα₁_Ω ⟨s₀, rfl⟩
    rw [← hu₀_eq, ← heq] at h_in_Ω
    exact hstub_0_not_Ω h_in_Ω
  have hu₀_pos' : (0 : ℝ) < u₀ := hu₀_pos
  let β₀ : I → S := pieceA stub 0 u₀
  let α₂ : I → S := pieceA α₁ s₀ 1
  have hβ₀_arc : IsArcMap β₀ := isArcMap_pieceA hstub_arc le_rfl hu₀_pos' u₀.2.2
  have hα₂_arc : IsArcMap α₂ := isArcMap_pieceA hα₁_arc s₀.2.1 hs₀_lt' le_rfl
  have hβ₀_0 : β₀ 0 = stub 0 := by
    dsimp [β₀]
    rw [pieceA_zero]
    exact extI_coe stub 0
  have hβ₀_1 : β₀ 1 = stub u₀ := by dsimp [β₀]; rw [pieceA_one, extI_coe]
  have hα₂_0 : α₂ 0 = stub u₀ := by dsimp [α₂]; rw [pieceA_zero, extI_coe, hu₀_eq]
  have hα₂_1 : α₂ 1 = y := by
    dsimp [α₂]
    rw [pieceA_one]
    exact (extI_coe α₁ 1).trans hα₁_1
  have hβ₀_range : range β₀ = stub '' Icc 0 u₀ := by
    dsimp [β₀]
    rw [range_pieceA stub le_rfl hu₀_pos'.le u₀.2.2]
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans u₀.2.2⟩
      exact ⟨⟨r, hrI⟩, hr, (extI_of_mem stub hrI).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.1, ht, extI_coe stub t⟩
  have hα₂_range : range α₂ = α₁ '' Icc s₀ 1 := by
    dsimp [α₂]
    rw [range_pieceA α₁ s₀.2.1 hs₀_lt'.le le_rfl]
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨s₀.2.1.trans hr.1, hr.2⟩
      exact ⟨⟨r, hrI⟩, hr, (extI_of_mem α₁ hrI).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.1, ht, extI_coe α₁ t⟩
  have hβ₀_L : IsLineWithEnds (range β₀) (stub 0) (stub u₀) := by
    have hL := IsArcMap.isLineWithEnds hβ₀_arc
    rwa [hβ₀_0, hβ₀_1] at hL
  have hα₂_L : IsLineWithEnds (range α₂) (stub u₀) y := by
    have hL := IsArcMap.isLineWithEnds hα₂_arc
    rwa [hα₂_0, hα₂_1] at hL
  have hinter : range β₀ ∩ range α₂ = {stub u₀} := by
    rw [hβ₀_range, hα₂_range]
    ext z
    simp only [mem_inter_iff, mem_image, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨s, hs, hsu⟩⟩
      have hs_eq : s = s₀ := by
        refine le_antisymm ?_ hs.1
        by_contra hlt
        push Not at hlt
        exact hafter_s₀ s hlt ⟨u, hsu.symm⟩
      subst hs_eq
      rw [← hsu, hu₀_eq]
    · rintro rfl
      exact ⟨⟨u₀, ⟨unitInterval.nonneg u₀, le_rfl⟩, rfl⟩,
        ⟨s₀, ⟨le_rfl, unitInterval.le_one s₀⟩, hu₀_eq.symm⟩⟩
  have hT_line : IsLineWithEnds (range β₀ ∪ range α₂) (stub 0) y :=
    Surface.IsLineWithEnds.union hβ₀_L hα₂_L hinter
  refine ⟨range β₀ ∪ range α₂, range α₂, y, u₀, hT_line, hy_sph, ?_, ?_, hu₀_pos,
    (isCompact_range hα₂_arc.1).isClosed, ?_, by rw [hβ₀_range]⟩
  · rintro z ⟨hz_mem | hz_mem, hz_ne⟩
    · rw [hβ₀_range] at hz_mem
      obtain ⟨u, _, rfl⟩ := hz_mem
      exact hstub_Ω ⟨⟨u, rfl⟩, hz_ne⟩
    · rw [hα₂_range] at hz_mem
      obtain ⟨s, _, rfl⟩ := hz_mem
      exact hα₁_Ω ⟨s, rfl⟩
  · ext z
    simp only [mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz_β | hz_α, hz_ball⟩
      · rw [hβ₀_range] at hz_β
        obtain ⟨u, _, rfl⟩ := hz_β
        exact False.elim (disjoint_left.mp hstub_ball ⟨u, rfl⟩ hz_ball)
      · rw [hα₂_range] at hz_α
        obtain ⟨s, _, rfl⟩ := hz_α
        have hs1 : s = 1 := (hα₁_ball s).mp hz_ball
        rw [hs1, hα₁_1]
    · rintro rfl
      exact ⟨Or.inr ⟨1, hα₂_1⟩, discSphere_subset_discBall h w δ hy_sph⟩
  · intro h0_in
    rw [hα₂_range] at h0_in
    obtain ⟨s, _, hs0⟩ := h0_in
    exact hstub_0_not_Ω (hs0 ▸ hα₁_Ω ⟨s, rfl⟩)

/-! ### Section 5: Assembling the Dual Drawing from Half-Edge Spokes -/

theorem isPathConnected_sdiff_right_and_closure [T2Space S] {L : Set S} {u v : S}
    (hL : IsLineWithEnds L u v) :
    u ∈ L \ {v} ∧ IsPathConnected (L \ {v}) ∧ closure (L \ {v}) = L := by
  obtain ⟨f, h0, h1⟩ := hL
  have huv : u ≠ v := fun he => by
    have : f 0 = f 1 := Subtype.ext (by rw [h0, h1, he])
    exact zero_ne_one (f.injective this)
  let g : I → S := fun t => (f t).1
  have hgc : Continuous g := continuous_subtype_val.comp f.continuous
  have hgi : Function.Injective g := fun s t h => f.injective (Subtype.ext h)
  have hg0 : g 0 = u := h0
  have hg1 : g 1 = v := h1
  have hrange : range g = L := by
    ext x
    exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hx => ⟨f.symm ⟨x, hx⟩, by simp [g]⟩⟩
  have hsdiff : L \ {v} = g '' Ico (0 : I) 1 := by
    ext x
    simp only [mem_sdiff, mem_singleton_iff, mem_image, mem_Ico]
    constructor
    · rintro ⟨hxL, hxv⟩
      rw [← hrange] at hxL
      obtain ⟨t, rfl⟩ := hxL
      refine ⟨t, ⟨unitInterval.nonneg t, lt_of_le_of_ne (unitInterval.le_one t) ?_⟩, rfl⟩
      intro ht1
      exact hxv (ht1 ▸ hg1)
    · rintro ⟨t, ⟨_, ht1⟩, rfl⟩
      refine ⟨hrange ▸ mem_range_self t, fun hgv => ?_⟩
      exact ht1.ne (hgi (hgv.trans hg1.symm))
  have hIco_eq : Ico (0 : I) 1 = projIcc 0 1 zero_le_one '' Ico (0 : ℝ) 1 := by
    ext t
    constructor
    · intro ht
      exact ⟨t.1, ⟨ht.1, ht.2⟩, projIcc_val zero_le_one t⟩
    · rintro ⟨r, hr, rfl⟩
      rw [mem_Ico, ← Subtype.coe_le_coe, ← Subtype.coe_lt_coe,
        projIcc_of_mem zero_le_one (Ico_subset_Icc_self hr)]
      exact hr
  have hIco_pc : IsPathConnected (Ico (0 : I) 1) := by
    rw [hIco_eq]
    exact ((convex_Ico (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩).image continuous_projIcc
  have hL_cl : IsClosed L := hrange ▸ (isCompact_range hgc).isClosed
  refine ⟨⟨hrange ▸ ⟨0, hg0⟩, huv⟩, hsdiff ▸ hIco_pc.image hgc, ?_⟩
  refine Subset.antisymm (closure_minimal sdiff_subset hL_cl) ?_
  rw [hsdiff, ← hrange]
  rintro _ ⟨t, rfl⟩
  have ht_cl : t ∈ closure (Ico (0 : I) 1) := by
    have hsub : Ioo (0 : I) 1 ⊆ Ico (0 : I) 1 := Ioo_subset_Ico_self
    have hcl_Ioo : closure (Ioo (0 : I) 1) = Icc (0 : I) 1 := closure_Ioo zero_ne_one
    exact closure_mono hsub (hcl_Ioo ▸ ⟨unitInterval.nonneg t, unitInterval.le_one t⟩)
  exact map_mem_closure hgc ht_cl fun s hs => ⟨s, hs, rfl⟩

/-- Given a finite vertex set `W` and for each edge `e : G.E` two half-edge spokes `H e true` and
`H e false` joining `m e` to `w_end e true ∈ W` and `w_end e false ∈ W`, their union forms a valid
`Drawing S` whose vertex set is `W` and whose edges are `{ (H e true ∪ H e false) \ W | e : G.E }`.
-/
theorem exists_dual_drawing_of_spokes [T2Space S] {G : Drawing S}
    {W : Set S} (hW_fin : W.Finite)
    (m : G.E → S) (w_end : G.E → Bool → S) (H : G.E → Bool → Set S)
    (hm_not_W : ∀ e : G.E, m e ∉ W)
    (hw_mem : ∀ e sgn, w_end e sgn ∈ W)
    (hH_line : ∀ e sgn, IsLineWithEnds (H e sgn) (m e) (w_end e sgn))
    (hH_W : ∀ e sgn, H e sgn ∩ W = {w_end e sgn})
    (hH_opp : ∀ e, H e true ∩ H e false ⊆ {m e, w_end e true})
    (hH_opp_ne : ∀ e, w_end e true ≠ w_end e false → H e true ∩ H e false = {m e})
    (hH_disj : ∀ e₁ e₂ sgn₁ sgn₂, e₁ ≠ e₂ → H e₁ sgn₁ ∩ H e₂ sgn₂ ⊆ W) :
    ∃ (G_dual : Drawing S) (edgeEquiv : G.E ≃ G_dual.E),
      G_dual.V = W ∧
      G_dual.U = W ∪ (⋃ e : G.E, (H e true ∪ H e false)) ∧
      (∀ e : G.E, (edgeEquiv e).1 = (H e true ∪ H e false) \ W) ∧
      (∀ e : G.E, G_dual.toGraph.IsLink (edgeEquiv e).1 (w_end e true) (w_end e false)) := by
  classical
  have : Finite G.E := G.finite_edges.to_subtype
  let _ : Fintype G.E := Fintype.ofFinite G.E
  let K : G.E → Set S := fun e => H e true ∪ H e false
  let eStar : G.E → Set S := fun e => K e \ W
  have hK_cl : ∀ e : G.E, IsClosed (K e) :=
    fun e => (isClosed_of_isLine (IsLineWithEnds.isLine (hH_line e true))).union
      (isClosed_of_isLine (IsLineWithEnds.isLine (hH_line e false)))
  have hK_W : ∀ e : G.E, K e ∩ W = {w_end e true, w_end e false} := by
    intro e
    dsimp [K]
    rw [union_inter_distrib_right, hH_W e true, hH_W e false, pair_comm (w_end e true),
      insert_eq, union_comm]
  have heStar_eq : ∀ e : G.E,
      eStar e = (H e true \ {w_end e true}) ∪ (H e false \ {w_end e false}) := by
    intro e
    ext x
    simp only [eStar, K, mem_sdiff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hx | hx, hxW⟩
      · exact Or.inl ⟨hx, fun heq => hxW (heq ▸ hw_mem e true)⟩
      · exact Or.inr ⟨hx, fun heq => hxW (heq ▸ hw_mem e false)⟩
    · rintro (⟨hx, hne⟩ | ⟨hx, hne⟩)
      · refine ⟨Or.inl hx, fun hxW => hne ?_⟩
        have : x ∈ H e true ∩ W := ⟨hx, hxW⟩
        rwa [hH_W e true, mem_singleton_iff] at this
      · refine ⟨Or.inr hx, fun hxW => hne ?_⟩
        have : x ∈ H e false ∩ W := ⟨hx, hxW⟩
        rwa [hH_W e false, mem_singleton_iff] at this
  have hm_eStar : ∀ e : G.E, m e ∈ eStar e := by
    intro e
    rw [heStar_eq]
    exact Or.inl (isPathConnected_sdiff_right_and_closure (hH_line e true)).1
  have heStar_pc : ∀ e : G.E, IsPathConnected (eStar e) := by
    intro e
    rw [heStar_eq]
    obtain ⟨hm1, hpc1, _⟩ := isPathConnected_sdiff_right_and_closure (hH_line e true)
    obtain ⟨hm2, hpc2, _⟩ := isPathConnected_sdiff_right_and_closure (hH_line e false)
    exact hpc1.union hpc2 ⟨m e, hm1, hm2⟩
  have heStar_cl : ∀ e : G.E, closure (eStar e) = K e := by
    intro e
    rw [heStar_eq, closure_union,
      (isPathConnected_sdiff_right_and_closure (hH_line e true)).2.2,
      (isPathConnected_sdiff_right_and_closure (hH_line e false)).2.2]
  have hK_disj : ∀ e₁ e₂ : G.E, e₁ ≠ e₂ → K e₁ ∩ K e₂ ⊆ W := by
    rintro e₁ e₂ hne x ⟨hx1 | hx1, hx2 | hx2⟩
    · exact hH_disj e₁ e₂ true true hne ⟨hx1, hx2⟩
    · exact hH_disj e₁ e₂ true false hne ⟨hx1, hx2⟩
    · exact hH_disj e₁ e₂ false true hne ⟨hx1, hx2⟩
    · exact hH_disj e₁ e₂ false false hne ⟨hx1, hx2⟩
  let U_dual : Set S := W ∪ ⋃ e : G.E, K e
  have hU_sdiff_W : U_dual \ W = ⋃ e : G.E, eStar e := by
    ext x
    simp only [U_dual, eStar, mem_sdiff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hxW | ⟨e, hxe⟩, hnotW⟩
      · exact False.elim (hnotW hxW)
      · exact ⟨e, hxe, hnotW⟩
    · rintro ⟨e, hxe, hnotW⟩
      exact ⟨Or.inr ⟨e, hxe⟩, hnotW⟩
  have hsub_eStar : ∀ {D : Set S} (e : G.E),
      D ⊆ U_dual \ W → IsPathConnected D → (D ∩ eStar e).Nonempty → D ⊆ eStar e := by
    intro D e hD_sub hD_pc ⟨x₀, hx₀D, hx₀e⟩
    let X : Set S := K e
    let Y : Set S := ⋃ e' ∈ Finset.univ.erase e, K e'
    have hX : IsClosed X := hK_cl e
    have hY : IsClosed Y := (Finset.univ.erase e).finite_toSet.isClosed_biUnion fun e' _ => hK_cl e'
    have hD_XY : D ⊆ X ∪ Y := by
      intro x hx
      have hx_u := hD_sub hx
      rw [hU_sdiff_W, mem_iUnion] at hx_u
      obtain ⟨e', hxe'⟩ := hx_u
      by_cases he' : e' = e
      · subst he'; exact Or.inl hxe'.1
      · exact Or.inr (mem_iUnion₂.mpr ⟨e', Finset.mem_erase.mpr ⟨he', Finset.mem_univ e'⟩, hxe'.1⟩)
    have hdis : ∀ x ∈ D, x ∈ X → x ∉ Y := by
      intro x hx hxX hxY
      obtain ⟨e', he', hxK'⟩ := mem_iUnion₂.mp hxY
      have hne : e ≠ e' := (Finset.mem_erase.mp he').1.symm
      exact (hD_sub hx).2 (hK_disj e e' hne ⟨hxX, hxK'⟩)
    rcases subset_or_subset_of_closed hD_pc.isConnected.isPreconnected hX hY hD_XY hdis with hDX |
      hDY
    · exact fun x hx => ⟨hDX hx, (hD_sub hx).2⟩
    · exact False.elim (hdis x₀ hx₀D hx₀e.1 (hDY hx₀D))
  have harc_eq : arcComponentsIn (U_dual \ W) = range eStar := by
    ext C
    simp only [mem_range]
    constructor
    · rintro ⟨⟨x₀, hx₀C⟩, hC_sub, hC_pc, hC_max⟩
      have hx₀_u := hC_sub hx₀C
      rw [hU_sdiff_W, mem_iUnion] at hx₀_u
      obtain ⟨e, hx₀e⟩ := hx₀_u
      have hC_sub_e : C ⊆ eStar e := hsub_eStar e hC_sub hC_pc ⟨x₀, hx₀C, hx₀e⟩
      have he_sub_u : eStar e ⊆ U_dual \ W := by
        rw [hU_sdiff_W]; exact subset_iUnion eStar e
      exact ⟨e, hC_max (eStar e) he_sub_u (heStar_pc e) hC_sub_e⟩
    · rintro ⟨e, rfl⟩
      have he_sub_u : eStar e ⊆ U_dual \ W := by
        rw [hU_sdiff_W]; exact subset_iUnion eStar e
      refine ⟨⟨m e, hm_eStar e⟩, he_sub_u, heStar_pc e, fun D hD hD_pc hsub => ?_⟩
      exact Subset.antisymm (hsub_eStar e hD hD_pc ⟨m e, hsub (hm_eStar e), hm_eStar e⟩) hsub
  let G_dual : Drawing S := {
    U := U_dual
    V := W
    V_subset_U := subset_union_left
    isClosed_U := hW_fin.isClosed.union (isClosed_iUnion_of_finite hK_cl)
    finite_V := hW_fin
    finite_edges := by
      rw [harc_eq]
      exact finite_range eStar
    edge_cond := by
      intro C hC
      change C ∈ arcComponentsIn (U_dual \ W) at hC
      rw [harc_eq] at hC
      obtain ⟨e, rfl⟩ := hC
      rw [heStar_cl e, hK_W e]
      by_cases hne : w_end e true ≠ w_end e false
      · left
        refine ⟨w_end e true, w_end e false, hne, rfl, ?_⟩
        exact Surface.IsLineWithEnds.union
          (Surface.IsLineWithEnds.symm (hH_line e true)) (hH_line e false)
          (hH_opp_ne e hne)
      · right
        push Not at hne
        rw [hne, pair_eq_singleton]
        refine ⟨w_end e false, rfl, ?_⟩
        have hL1 : IsLineWithEnds (H e true) (m e) (w_end e false) := hne ▸ hH_line e true
        have hcap : H e true ∩ H e false ⊆ {m e, w_end e false} := hne ▸ hH_opp e
        exact isOArc_union hL1 (hH_line e false) hcap
  }
  have hGd_E : G_dual.E = range eStar := harc_eq
  have heStar_inj : Function.Injective eStar := by
    intro e₁ e₂ heq
    have hm1 : m e₁ ∈ eStar e₂ := heq ▸ hm_eStar e₁
    by_contra hne
    exact hm_not_W e₁ (hK_disj e₁ e₂ hne ⟨(hm_eStar e₁).1, hm1.1⟩)
  let f_equiv : G.E → G_dual.E := fun e => ⟨eStar e, hGd_E ▸ mem_range_self e⟩
  have hf_bij : Function.Bijective f_equiv := by
    refine ⟨fun e₁ e₂ h => heStar_inj (congrArg Subtype.val h), ?_⟩
    rintro ⟨C, hC⟩
    rw [hGd_E] at hC
    obtain ⟨e, rfl⟩ := hC
    exact ⟨e, rfl⟩
  let edgeEquiv : G.E ≃ G_dual.E := Equiv.ofBijective f_equiv hf_bij
  refine ⟨G_dual, edgeEquiv, rfl, rfl, fun e => rfl, fun e => ?_⟩
  refine ⟨(edgeEquiv e).2, hw_mem e true, hw_mem e false, ?_⟩
  change closure (eStar e) ∩ W = {w_end e true, w_end e false}
  rw [heStar_cl e, hK_W e]

/-! ### Section 6: Main Existence Theorem `exists_isDiscDualDrawing` and `(3.6)` -/

private theorem exists_truncated_spokes (hS : IsClosedDiscSpace S) {G : Drawing S}
    {h : S → ℂ} (hh : Continuous h) {w_of c_of : G.R → S} {δ : ℝ}
    (hδ_sub : ∀ r : G.R, discBall h (w_of r) δ ⊆ r.1)
    (hc_of : ∀ r : G.R, c_of r ∈ discOpenBall h (w_of r) δ \ bd S)
    {m_of : G.E → S} (hm_mem_U : ∀ e : G.E, m_of e ∈ G.U)
    (hm_not_bd : ∀ e : G.E, m_of e ∉ bd S) (hm_inj : Function.Injective m_of) :
    let Half := G.E × Bool
    ∀ (stub : Half → I → S) (r_of : Half → G.R),
    let Stub : Half → Set S := fun a => range (stub a)
    (∀ a, IsArcMap (stub a)) →
    (∀ a, stub a 0 = m_of a.1) →
    (∀ a, Stub a ∩ G.U = {m_of a.1}) →
    (∀ a, Stub a ∩ bd S = ∅) →
    (∀ a (r : G.R), Disjoint (Stub a) (discBall h (w_of r) δ)) →
    (∀ a b, b ≠ a → Stub a ∩ Stub b = if a.1 = b.1 then {m_of a.1} else ∅) →
    (∀ a (t : I), (0 : I) < t → stub a t ∈ (r_of a).1 \ bd S) →
    ∀ F : Finset Half,
    ∃ (T A_far : Half → Set S) (y : Half → S) (u₀ : Half → I),
      (∀ a ∉ F, T a = Stub a) ∧
      (∀ a ∈ F,
        IsLineWithEnds (T a) (m_of a.1) (y a) ∧
        y a ∈ discSphere h (w_of (r_of a)) δ ∧
        T a ∩ discBall h (w_of (r_of a)) δ = {y a} ∧
        (0 : I) < u₀ a ∧
        IsClosed (A_far a) ∧
        m_of a.1 ∉ A_far a ∧
        T a = stub a '' Icc 0 (u₀ a) ∪ A_far a) ∧
      (∀ a : Half,
        IsLine (T a) ∧
        T a \ {m_of a.1} ⊆ (r_of a).1 \ bd S ∧
        T a ∩ G.U = {m_of a.1} ∧
        T a ∩ bd S = ∅ ∧
        (∀ r : G.R, r ≠ r_of a → Disjoint (T a) (discBall h (w_of r) δ)) ∧
        (∀ r : G.R, Disjoint (T a) (discOpenBall h (w_of r) δ)) ∧
        (∀ b : Half, b ≠ a → T a ∩ T b = if a.1 = b.1 then {m_of a.1} else ∅)) := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : Finite G.E := G.finite_edges.to_subtype
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  intro Half stub r_of Stub hstub_arc hstub_0 hStub_U hStub_bd hStub_D hStub_inter hr_of
  let _ : Fintype Half := Fintype.ofFinite Half
  intro F
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨Stub, fun _ => ∅, fun a => stub a 1, fun _ => 1,
      fun _ _ => rfl, fun _ ha => False.elim (Finset.notMem_empty _ ha), fun a => ?_⟩
    refine ⟨IsLineWithEnds.isLine (IsArcMap.isLineWithEnds (hstub_arc a)), ?_, hStub_U a,
      hStub_bd a, fun r _ => hStub_D a r,
      fun r => (hStub_D a r).mono_right (discOpenBall_subset_discBall h (w_of r) δ),
      fun b hne => hStub_inter a b hne⟩
    rintro _ ⟨⟨t, rfl⟩, hne⟩
    have ht_pos : (0 : I) < t :=
      lt_of_le_of_ne (unitInterval.nonneg t) (fun heq => hne (heq ▸ hstub_0 a))
    exact hr_of a t ht_pos
  | insert a₀ F ha₀_not_F ih =>
    obtain ⟨T, A_far, y, u₀, hT_out, hT_in, hT_all⟩ := ih
    have hT_a₀ : T a₀ = Stub a₀ := hT_out a₀ ha₀_not_F
    let E₀ : Finset Half := Finset.univ.erase a₀
    let r₀ : G.R := r_of a₀
    let Ω : Set S := (r₀.1 \ bd S) \ ⋃ b ∈ E₀, T b
    have hΩ_open : IsOpen Ω := by
      refine ((region_isOpen r₀.2).sdiff hbd_cl).sdiff ?_
      exact E₀.finite_toSet.isClosed_biUnion fun b _ => isClosed_of_isLine (hT_all b).1
    have hΩ_bd : Disjoint Ω (bd S) := disjoint_left.mpr fun _ hx => hx.1.2
    have h0_not_Ω : stub a₀ 0 ∉ Ω := by
      rw [hstub_0]
      intro hm
      exact region_subset r₀.2 hm.1.1 (hm_mem_U a₀.1)
    have hstub_Ω : range (stub a₀) \ {stub a₀ 0} ⊆ Ω := by
      rw [hstub_0]
      rintro x ⟨hx_stub, hx_ne⟩
      have hx_T : x ∈ T a₀ \ {m_of a₀.1} := ⟨hT_a₀.symm ▸ hx_stub, hx_ne⟩
      refine ⟨(hT_all a₀).2.1 hx_T, ?_⟩
      intro hx_union
      obtain ⟨b, hbE₀, hxb⟩ := mem_iUnion₂.mp hx_union
      have hba : b ≠ a₀ := (Finset.mem_erase.mp hbE₀).1
      have hinter : x ∈ T a₀ ∩ T b := ⟨hx_T.1, hxb⟩
      rw [(hT_all a₀).2.2.2.2.2.2 b hba] at hinter
      split_ifs at hinter with heq
      · exact hx_ne hinter
      · exact hinter
    have hc₀_Ω : c_of r₀ ∈ Ω := by
      have hc_in : c_of r₀ ∈ discOpenBall h (w_of r₀) δ \ bd S := hc_of r₀
      refine ⟨⟨hδ_sub r₀ (discOpenBall_subset_discBall h (w_of r₀) δ hc_in.1), hc_in.2⟩, ?_⟩
      intro hx_union
      obtain ⟨b, _, hxb⟩ := mem_iUnion₂.mp hx_union
      exact disjoint_left.mp ((hT_all b).2.2.2.2.2.1 r₀) hxb hc_in.1
    have h1_Ω : stub a₀ 1 ∈ Ω := by
      apply hstub_Ω
      refine ⟨⟨1, rfl⟩, fun heq => ?_⟩
      exact one_ne_zero ((hstub_arc a₀).2 heq)
    have hconn_Ω : c_of r₀ ∈ connectedComponentIn Ω (stub a₀ 1) := by
      refine connectedComponentIn_sdiff_biUnion_arcs hS E₀ T (fun b => m_of b.1)
        (fun b _ => (hT_all b).1)
        (fun b _ => by rw [(hT_all b).2.2.1])
        (fun b _ => by rw [(hT_all b).2.2.2.1]; exact empty_subset _)
        (fun b _ c _ hne => by
          rw [(hT_all b).2.2.2.2.2.2 c hne]
          split_ifs <;> simp)
        r₀.2 h1_Ω hc₀_Ω
    obtain ⟨T_new, A_new, y_new, u_new, hTn_line, hyn_sph, hTn_Ω, hTn_ball,
        hun_pos, hAn_cl, hm_not_An, hTn_eq⟩ :=
      exists_truncated_spoke_of_connected hS hh hΩ_open hΩ_bd (hstub_arc a₀)
        h0_not_Ω hstub_Ω (hStub_D a₀ r₀) (hc_of r₀).1 hconn_Ω
    rw [hstub_0] at hTn_line hTn_Ω hm_not_An
    let T' : Half → Set S := fun a => if a = a₀ then T_new else T a
    let A' : Half → Set S := fun a => if a = a₀ then A_new else A_far a
    let y' : Half → S := fun a => if a = a₀ then y_new else y a
    let u' : Half → I := fun a => if a = a₀ then u_new else u₀ a
    have hTn_0 : m_of a₀.1 ∈ T_new := IsLineWithEnds.left_mem hTn_line
    have hTn_U : T_new ∩ G.U = {m_of a₀.1} := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxT, hxU⟩
        by_contra hne
        exact region_subset r₀.2 (hTn_Ω ⟨hxT, hne⟩).1.1 hxU
      · rintro rfl
        exact ⟨hTn_0, hm_mem_U a₀.1⟩
    have hTn_bd : T_new ∩ bd S = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxT, hxbd⟩
      by_cases hxm : x = m_of a₀.1
      · exact hm_not_bd a₀.1 (hxm ▸ hxbd)
      · exact (hTn_Ω ⟨hxT, hxm⟩).1.2 hxbd
    have hTn_D_other : ∀ r : G.R, r ≠ r₀ → Disjoint T_new (discBall h (w_of r) δ) := by
      intro r hne
      refine disjoint_left.mpr fun x hxT hxD => ?_
      by_cases hxm : x = m_of a₀.1
      · exact region_subset r.2 (hδ_sub r hxD) (hxm ▸ hm_mem_U a₀.1)
      · have hx_r₀ : x ∈ r₀.1 := (hTn_Ω ⟨hxT, hxm⟩).1.1
        have hx_r : x ∈ r.1 := hδ_sub r hxD
        exact hne (Subtype.ext (region_eq_of_mem r.2 r₀.2 hx_r hx_r₀))
    have hTn_openBall : ∀ r : G.R, Disjoint T_new (discOpenBall h (w_of r) δ) := by
      intro r
      by_cases hr : r = r₀
      · subst r
        refine disjoint_left.mpr fun x hxT hxB => ?_
        have hx_mem : x ∈ T_new ∩ discBall h (w_of r₀) δ :=
          ⟨hxT, discOpenBall_subset_discBall h (w_of r₀) δ hxB⟩
        rw [hTn_ball, mem_singleton_iff] at hx_mem
        subst hx_mem
        exact ne_of_lt (show dist _ _ < δ from hxB) hyn_sph.1
      · exact (hTn_D_other r hr).mono_right (discOpenBall_subset_discBall h (w_of r) δ)
    have hTn_inter : ∀ b : Half, b ≠ a₀ →
        T_new ∩ T b = if a₀.1 = b.1 then {m_of a₀.1} else ∅ := by
      intro b hba
      have hbE₀ : b ∈ E₀ := Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩
      ext x
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨hxTn, hxTb⟩
        have hxm : x = m_of a₀.1 := by
          by_contra hne
          exact (hTn_Ω ⟨hxTn, hne⟩).2 (mem_iUnion₂.mpr ⟨b, hbE₀, hxTb⟩)
        subst hxm
        have hm_in_b : m_of a₀.1 ∈ T b ∩ G.U := ⟨hxTb, hm_mem_U a₀.1⟩
        rw [(hT_all b).2.2.1, mem_singleton_iff] at hm_in_b
        have heq := hm_inj hm_in_b
        rw [ite_eq_left heq, mem_singleton_iff]
      · intro hx
        split_ifs at hx with heq
        · rw [mem_singleton_iff] at hx
          subst hx
          have hm_b : m_of b.1 ∈ T b := by
            have : m_of b.1 ∈ T b ∩ G.U := by rw [(hT_all b).2.2.1]; rfl
            exact this.1
          exact ⟨hTn_0, heq ▸ hm_b⟩
        · exact False.elim hx
    refine ⟨T', A', y', u', ?_, ?_, ?_⟩
    · intro a ha
      have ha_ne : a ≠ a₀ := fun h => ha (h ▸ Finset.mem_insert_self a₀ F)
      have ha_not_F : a ∉ F := fun h => ha (Finset.mem_insert_of_mem h)
      dsimp [T']
      rw [ite_eq_right ha_ne, hT_out a ha_not_F]
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | haF
      · simp only [T', A', y', u', ↓reduceIte]
        exact ⟨hTn_line, hyn_sph, hTn_ball, hun_pos, hAn_cl, hm_not_An, hTn_eq⟩
      · have ha_ne : a ≠ a₀ := fun h => ha₀_not_F (h ▸ haF)
        simp only [T', A', y', u', ha_ne, ↓reduceIte]
        exact hT_in a haF
    · intro a
      by_cases ha : a = a₀
      · subst a
        have hT'_a₀ : T' a₀ = T_new := by simp [T']
        rw [hT'_a₀]
        refine ⟨IsLineWithEnds.isLine hTn_line,
          fun z hz => (hTn_Ω hz).1,
          hTn_U,
          hTn_bd,
          fun r hr => hTn_D_other r hr,
          fun r => hTn_openBall r,
          fun b hba => ?_⟩
        have hT'_b : T' b = T b := by simp [T', hba]
        rw [hT'_b]
        exact hTn_inter b hba
      · have hT'_a : T' a = T a := by simp [T', ha]
        rw [hT'_a]
        refine ⟨(hT_all a).1, (hT_all a).2.1, (hT_all a).2.2.1, (hT_all a).2.2.2.1,
          (hT_all a).2.2.2.2.1, (hT_all a).2.2.2.2.2.1, fun b hba => ?_⟩
        by_cases hb : b = a₀
        · subst b
          have hT'_a₀ : T' a₀ = T_new := by simp [T']
          rw [hT'_a₀, inter_comm, hTn_inter a (show a ≠ a₀ from ha)]
          by_cases heq : a₀.1 = a.1
          · simp [heq]
          · have heq' : a.1 ≠ a₀.1 := Ne.symm heq
            simp [heq, heq']
        · have hT'_b : T' b = T b := by simp [T', hb]
          rw [hT'_b]
          exact (hT_all a).2.2.2.2.2.2 b hba

private theorem radial_spoke_properties {G : Drawing S} [T2Space S]
    {h : S → ℂ} {g : ℂ → S} (hinj : Function.Injective h)
    (hg : ContinuousOn g (closedBall 0 1))
    (hmem : ∀ x, h x ∈ closedBall (0 : ℂ) 1) (hgl : ∀ x, g (h x) = x)
    (hgr : ∀ z ∈ closedBall (0 : ℂ) 1, h (g z) = z)
    (hball_iff : ∀ x, x ∉ bd S ↔ h x ∈ ball (0 : ℂ) 1)
    {w_of : G.R → S} {m_of : G.E → S} {W : Set S} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_sub : ∀ r : G.R, discBall h (w_of r) δ ⊆ r.1)
    (hm_mem_U : ∀ e : G.E, m_of e ∈ G.U) (hm_not_W : ∀ e : G.E, m_of e ∉ W)
    (hw_W : ∀ r : G.R, w_of r ∈ W)
    (hw_of_uniq : ∀ (r : G.R) x, x ∈ r.1 ∧ x ∈ W → x = w_of r) :
    let Half := G.E × Bool
    ∀ {r_of : Half → G.R} {T : Half → Set S} {y : Half → S} {A_far : Half → Set S}
      {u₀ : Half → I} {stub : Half → I → S},
    Function.Injective y →
    (∀ a : Half,
      IsLineWithEnds (T a) (m_of a.1) (y a) ∧ y a ∈ discSphere h (w_of (r_of a)) δ ∧
      T a ∩ discBall h (w_of (r_of a)) δ = {y a} ∧ (0 : I) < u₀ a ∧
      IsClosed (A_far a) ∧ m_of a.1 ∉ A_far a ∧ T a = stub a '' Icc 0 (u₀ a) ∪ A_far a) →
    (∀ a : Half, IsLine (T a) ∧ T a \ {m_of a.1} ⊆ (r_of a).1 \ bd S ∧
      T a ∩ G.U = {m_of a.1} ∧ T a ∩ bd S = ∅ ∧
      (∀ r : G.R, r ≠ r_of a → Disjoint (T a) (discBall h (w_of r) δ)) ∧
      (∀ r : G.R, Disjoint (T a) (discOpenBall h (w_of r) δ)) ∧
      (∀ b : Half, b ≠ a → T a ∩ T b = if a.1 = b.1 then {m_of a.1} else ∅)) →
    let R_seg : Half → Set S := fun a => range (radMap h g (w_of (r_of a)) (y a))
    let H : G.E → Bool → Set S := fun e sgn => T (e, sgn) ∪ R_seg (e, sgn)
    let w_end : G.E → Bool → S := fun e sgn => w_of (r_of (e, sgn))
    (∀ a : Half, R_seg a ⊆ discBall h (w_of (r_of a)) δ) ∧
    (∀ e sgn, IsLineWithEnds (H e sgn) (m_of e) (w_end e sgn)) ∧
    (∀ e sgn, H e sgn ∩ G.U = {m_of e}) ∧
    (∀ e sgn, H e sgn ∩ bd S ⊆ {w_end e sgn}) ∧
    (∀ e sgn, H e sgn ∩ W = {w_end e sgn}) ∧
    (∀ e : G.E, H e true ∩ H e false ⊆ {m_of e, w_end e true}) ∧
    (∀ e : G.E, w_end e true ≠ w_end e false → H e true ∩ H e false = {m_of e}) ∧
    (∀ e₁ e₂ sgn₁ sgn₂, e₁ ≠ e₂ → H e₁ sgn₁ ∩ H e₂ sgn₂ ⊆ W) := by
  classical
  intro Half r_of T y A_far u₀ stub hy_inj hT_props hT_all R_seg H w_end
  have hy_ne_w : ∀ a : Half, y a ≠ w_of (r_of a) := by
    intro a heq
    have h1 := (hT_props a).2.1.1
    change dist (h (y a)) (h (w_of (r_of a))) = δ at h1
    rw [heq, dist_self] at h1
    exact hδ_pos.ne h1
  have hR_line : ∀ a : Half, IsLineWithEnds (R_seg a) (y a) (w_of (r_of a)) :=
    fun a => isLineWithEnds_range_radMap hinj hg hmem hgl hgr (hy_ne_w a)
  have hR_sub_D : ∀ a : Half, R_seg a ⊆ discBall h (w_of (r_of a)) δ :=
    fun a => range_radMap_subset_discBall hmem hgr (hT_props a).2.1
  have hTR_inter : ∀ a : Half, T a ∩ R_seg a = {y a} := by
    intro a
    refine Subset.antisymm ?_ ?_
    · intro x ⟨hxT, hxR⟩
      have hxD : x ∈ T a ∩ discBall h (w_of (r_of a)) δ := ⟨hxT, hR_sub_D a hxR⟩
      rwa [(hT_props a).2.2.1] at hxD
    · rintro x rfl
      exact ⟨IsLineWithEnds.right_mem (hT_props a).1, IsLineWithEnds.left_mem (hR_line a)⟩
  have hH_line : ∀ e sgn, IsLineWithEnds (H e sgn) (m_of e) (w_end e sgn) :=
    fun e sgn => Surface.IsLineWithEnds.union
      (hT_props (e, sgn)).1 (hR_line (e, sgn)) (hTR_inter (e, sgn))
  have hH_sub_r : ∀ a : Half, H a.1 a.2 \ {m_of a.1} ⊆ (r_of a).1 := by
    rintro a x ⟨hxT | hxR, hne⟩
    · exact ((hT_all a).2.1 ⟨hxT, hne⟩).1
    · exact hδ_sub (r_of a) (hR_sub_D a hxR)
  have hH_U : ∀ e sgn, H e sgn ∩ G.U = {m_of e} := by
    intro e sgn
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxH, hxU⟩
      by_contra hne
      exact region_subset (r_of (e, sgn)).2 (hH_sub_r (e, sgn) ⟨hxH, hne⟩) hxU
    · rintro rfl
      exact ⟨Or.inl (IsLineWithEnds.left_mem (hT_props (e, sgn)).1), hm_mem_U e⟩
  have hH_bd : ∀ e sgn, H e sgn ∩ bd S ⊆ {w_end e sgn} := by
    rintro e sgn x ⟨hxT | hxR, hxbd⟩
    · have : x ∈ T (e, sgn) ∩ bd S := ⟨hxT, hxbd⟩
      rw [(hT_all (e, sgn)).2.2.2.1] at this
      exact False.elim this
    · obtain ⟨t, rfl⟩ := hxR
      by_cases ht0 : t = 0
      · subst ht0
        rw [radMap_zero hgl]
        rfl
      · have ht_pos : (0 : I) < t := unitInterval.pos_iff_ne_zero.mpr ht0
        exact False.elim
          (radMap_notMem_bd hmem hgr hball_iff _ (hT_props (e, sgn)).2.1.2 ht_pos hxbd)
  have hH_W : ∀ e sgn, H e sgn ∩ W = {w_end e sgn} := by
    intro e sgn
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxH, hxW⟩
      have hne : x ≠ m_of e := fun h => hm_not_W e (h ▸ hxW)
      have hxr : x ∈ (r_of (e, sgn)).1 := hH_sub_r (e, sgn) ⟨hxH, hne⟩
      exact hw_of_uniq (r_of (e, sgn)) x ⟨hxr, hxW⟩
    · rintro rfl
      exact ⟨Or.inr (IsLineWithEnds.right_mem (hR_line (e, sgn))), hw_W (r_of (e, sgn))⟩
  have hTR_disj_other : ∀ a b : Half, a ≠ b → Disjoint (T a) (R_seg b) := by
    intro a b hne
    by_cases hr : r_of a = r_of b
    · refine disjoint_left.mpr fun x hxT hxR => ?_
      have hxD : x ∈ T a ∩ discBall h (w_of (r_of a)) δ :=
        ⟨hxT, hr ▸ hR_sub_D b hxR⟩
      rw [(hT_props a).2.2.1, mem_singleton_iff] at hxD
      subst hxD
      have hy_in : y a ∈ R_seg b ∩ discSphere h (w_of (r_of b)) δ :=
        ⟨hxR, hr ▸ (hT_props a).2.1⟩
      rw [range_radMap_inter_discSphere hmem hgl hgr hδ_pos (hT_props b).2.1,
        mem_singleton_iff] at hy_in
      exact hne (hy_inj hy_in)
    · exact ((hT_all a).2.2.2.2.1 (r_of b) (Ne.symm hr)).mono_right (hR_sub_D b)
  have hRR_inter_other : ∀ a b : Half, a ≠ b →
      R_seg a ∩ R_seg b = if r_of a = r_of b then {w_of (r_of a)} else ∅ := by
    intro a b hne
    by_cases hr : r_of a = r_of b
    · rw [ite_eq_left hr]
      dsimp [R_seg]
      have hyb : dist (h (y b)) (h (w_of (r_of a))) = δ := hr ▸ (hT_props b).2.1.1
      rw [← hr]
      exact range_radMap_inter_eq_singleton hinj hmem hgl hgr hδ_pos
        (hT_props a).2.1.1 hyb (hy_inj.ne hne)
    · rw [ite_eq_right hr, eq_empty_iff_forall_notMem]
      rintro x ⟨hxa, hxb⟩
      have hx_ra : x ∈ (r_of a).1 := hδ_sub (r_of a) (hR_sub_D a hxa)
      have hx_rb : x ∈ (r_of b).1 := hδ_sub (r_of b) (hR_sub_D b hxb)
      exact hr (Subtype.ext (region_eq_of_mem (r_of a).2 (r_of b).2 hx_ra hx_rb))
  have hne_ft : ∀ e : G.E, (e, false) ≠ (e, true) :=
    fun _ h => Bool.false_ne_true (congrArg Prod.snd h)
  have hne_tf : ∀ e : G.E, (e, true) ≠ (e, false) :=
    fun _ h => Bool.false_ne_true (congrArg Prod.snd h).symm
  have hH_opp : ∀ e : G.E, H e true ∩ H e false ⊆ {m_of e, w_end e true} := by
    rintro e x ⟨hx1 | hx1, hx2 | hx2⟩
    · have hinter : x ∈ T (e, true) ∩ T (e, false) := ⟨hx1, hx2⟩
      rw [(hT_all (e, true)).2.2.2.2.2.2 (e, false) (hne_ft e)] at hinter
      simp only [↓reduceIte, mem_singleton_iff] at hinter
      exact Or.inl hinter
    · exact False.elim (disjoint_left.mp (hTR_disj_other (e, true) (e, false) (hne_tf e)) hx1 hx2)
    · exact False.elim (disjoint_left.mp (hTR_disj_other (e, false) (e, true) (hne_ft e)) hx2 hx1)
    · have hinter : x ∈ R_seg (e, true) ∩ R_seg (e, false) := ⟨hx1, hx2⟩
      rw [hRR_inter_other (e, true) (e, false) (hne_tf e)] at hinter
      split_ifs at hinter with hr
      · exact Or.inr hinter
      · exact False.elim hinter
  have hH_opp_ne : ∀ e : G.E, w_end e true ≠ w_end e false → H e true ∩ H e false = {m_of e} := by
    intro e hne
    have hr : r_of (e, true) ≠ r_of (e, false) := fun h => hne (congrArg w_of h)
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx1 | hx1, hx2 | hx2⟩
      · have hinter : x ∈ T (e, true) ∩ T (e, false) := ⟨hx1, hx2⟩
        rw [(hT_all (e, true)).2.2.2.2.2.2 (e, false) (hne_ft e)] at hinter
        simpa using hinter
      · exact False.elim (disjoint_left.mp (hTR_disj_other (e, true) (e, false) (hne_tf e)) hx1 hx2)
      · exact False.elim (disjoint_left.mp (hTR_disj_other (e, false) (e, true) (hne_ft e)) hx2 hx1)
      · have hinter : x ∈ R_seg (e, true) ∩ R_seg (e, false) := ⟨hx1, hx2⟩
        rw [hRR_inter_other (e, true) (e, false) (hne_tf e), ite_eq_right hr] at hinter
        exact False.elim hinter
    · rintro rfl
      exact ⟨Or.inl (IsLineWithEnds.left_mem (hT_props (e, true)).1),
        Or.inl (IsLineWithEnds.left_mem (hT_props (e, false)).1)⟩
  have hH_disj : ∀ e₁ e₂ sgn₁ sgn₂, e₁ ≠ e₂ → H e₁ sgn₁ ∩ H e₂ sgn₂ ⊆ W := by
    rintro e₁ e₂ sgn₁ sgn₂ hne x ⟨hx1 | hx1, hx2 | hx2⟩
    · have hinter : x ∈ T (e₁, sgn₁) ∩ T (e₂, sgn₂) := ⟨hx1, hx2⟩
      have hne_pair : (e₂, sgn₂) ≠ (e₁, sgn₁) := fun h => hne (congrArg Prod.fst h).symm
      rw [(hT_all (e₁, sgn₁)).2.2.2.2.2.2 (e₂, sgn₂) hne_pair,
        ite_eq_right hne] at hinter
      exact False.elim hinter
    · have hne_pair : (e₁, sgn₁) ≠ (e₂, sgn₂) := fun h => hne (congrArg Prod.fst h)
      exact False.elim
        (disjoint_left.mp (hTR_disj_other (e₁, sgn₁) (e₂, sgn₂) hne_pair) hx1 hx2)
    · have hne_pair : (e₂, sgn₂) ≠ (e₁, sgn₁) := fun h => hne (congrArg Prod.fst h).symm
      exact False.elim
        (disjoint_left.mp (hTR_disj_other (e₂, sgn₂) (e₁, sgn₁) hne_pair) hx2 hx1)
    · have hinter : x ∈ R_seg (e₁, sgn₁) ∩ R_seg (e₂, sgn₂) := ⟨hx1, hx2⟩
      have hne_pair : (e₁, sgn₁) ≠ (e₂, sgn₂) := fun h => hne (congrArg Prod.fst h)
      rw [hRR_inter_other (e₁, sgn₁) (e₂, sgn₂) hne_pair] at hinter
      split_ifs at hinter with hr
      · rw [mem_singleton_iff] at hinter
        exact hinter ▸ hw_W (r_of (e₁, sgn₁))
      · exact False.elim hinter
  exact ⟨hR_sub_D, hH_line, hH_U, hH_bd, hH_W, hH_opp, hH_opp_ne, hH_disj⟩

private theorem dual_region_meets_primal_edge (hS : IsClosedDiscSpace S)
    {G G_dual : Drawing S} (hGd_prop : G_dual.IsProper) (edgeEquiv : G.E ≃ G_dual.E)
    {h : S → ℂ} {δ : ℝ} {W : Set S} (hW_fin : W.Finite)
    {w_of : G.R → S} {m_of : G.E → S} (hm_mem_U : ∀ e : G.E, m_of e ∈ G.U)
    (hm_not_W : ∀ e : G.E, m_of e ∉ W) (hm_inj : Function.Injective m_of)
    (hedge_inter_e : ∀ e : G.E, (edgeEquiv e).1 ∩ e.1 = {m_of e})
    {φ_e : G.E → ℂ → S} (hφc : ∀ e : G.E, ContinuousOn (φ_e e) (closedBall 0 1))
    (hφi : ∀ e : G.E, InjOn (φ_e e) (closedBall 0 1))
    (hφ0 : ∀ e : G.E, φ_e e 0 = m_of e)
    (hφ_real_sub : ∀ e : G.E, φ_e e '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} ⊆ e.1) :
    let Half := G.E × Bool
    ∀ {r_of : Half → G.R} {T R_seg A_far : Half → Set S} {u₀ : Half → I} {y : Half → S},
    let D_union : Set S := ⋃ r : G.R, discBall h (w_of r) δ
    let H : G.E → Bool → Set S := fun e sgn => T (e, sgn) ∪ R_seg (e, sgn)
    let stub : Half → I → S := fun a t => φ_e a.1 (zStub a.2 t)
    IsClosed D_union → Disjoint D_union G.U →
    (∀ (a : Half), IsLineWithEnds (T a) (m_of a.1) (y a) ∧
      y a ∈ discSphere h (w_of (r_of a)) δ ∧
      T a ∩ discBall h (w_of (r_of a)) δ = {y a} ∧
      (0 : I) < u₀ a ∧ IsClosed (A_far a) ∧ m_of a.1 ∉ A_far a ∧
      T a = stub a '' Icc 0 (u₀ a) ∪ A_far a) →
    (∀ a : Half, R_seg a ⊆ discBall h (w_of (r_of a)) δ) →
    (∀ e sgn, IsLineWithEnds (H e sgn) (m_of e) (w_of (r_of (e, sgn)))) →
    (∀ e : G.E, (H e true ∪ H e false) ∩ G.U = {m_of e}) →
    G_dual.U = W ∪ ⋃ e : G.E, (H e true ∪ H e false) →
    ∀ e : G.E, ∀ r' ∈ G_dual.R,
      G_dual.EdgeRegionIncident (edgeEquiv e).1 r' → (r' ∩ e.1).Nonempty := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : Finite G.E := G.finite_edges.to_subtype
  intro Half r_of T R_seg A_far u₀ y D_union H stub hD_union_cl hD_union_disj_U hT_props
    hR_sub_D hH_line hK_U hGd_U
  let _ : Fintype G.E := Fintype.ofFinite G.E
  intro e r' hr' hinc
  have he'_sub : (edgeEquiv e).1 ⊆ closure r' :=
    disc_edge_subset_closure_of_incident hS hGd_prop (edgeEquiv e).2 hr' hinc.2.2
  have hm_in_e' : m_of e ∈ (edgeEquiv e).1 := by
    have : m_of e ∈ (edgeEquiv e).1 ∩ e.1 := by rw [hedge_inter_e e]; rfl
    exact this.1
  have hm_cl : m_of e ∈ closure r' := he'_sub hm_in_e'
  let B_bad : Set S :=
    A_far (e, true) ∪ A_far (e, false) ∪ D_union ∪ W ∪
      ⋃ e' ∈ Finset.univ.erase e, (H e' true ∪ H e' false)
  have hB_bad_cl : IsClosed B_bad := by
    refine (((( (hT_props (e, true)).2.2.2.2.1.union (hT_props (e, false)).2.2.2.2.1 ).union
      hD_union_cl).union hW_fin.isClosed).union ?_)
    exact (Finset.univ.erase e).finite_toSet.isClosed_biUnion fun e' _ =>
      (isClosed_of_isLine (IsLineWithEnds.isLine (hH_line e' true))).union
        (isClosed_of_isLine (IsLineWithEnds.isLine (hH_line e' false)))
  have hm_not_bad : m_of e ∉ B_bad := by
    rintro ((((hmA1 | hmA2) | hmD) | hmW) | hm_other)
    · exact (hT_props (e, true)).2.2.2.2.2.1 hmA1
    · exact (hT_props (e, false)).2.2.2.2.2.1 hmA2
    · exact disjoint_left.mp hD_union_disj_U hmD (hm_mem_U e)
    · exact hm_not_W e hmW
    · obtain ⟨e', he', hmK'⟩ := mem_iUnion₂.mp hm_other
      have hne : e' ≠ e := (Finset.mem_erase.mp he').1
      have : m_of e ∈ (H e' true ∪ H e' false) ∩ G.U := ⟨hmK', hm_mem_U e⟩
      rw [hK_U e', mem_singleton_iff] at this
      exact hne (hm_inj this).symm
  let ρ : ℝ := min ((u₀ (e, true) : ℝ) / 2) ((u₀ (e, false) : ℝ) / 2)
  have hρ_pos : 0 < ρ := by
    have h1 : (0 : ℝ) < u₀ (e, true) := (hT_props (e, true)).2.2.2.1
    have h2 : (0 : ℝ) < u₀ (e, false) := (hT_props (e, false)).2.2.2.1
    exact lt_min (half_pos h1) (half_pos h2)
  have hρ_le_one : ρ ≤ 1 := by
    have h1 : (u₀ (e, true) : ℝ) ≤ 1 := (u₀ (e, true)).2.2
    exact le_trans (min_le_left _ _) (by linarith)
  -- Choose `ε_e > 0` (`ε_e ≤ ρ`) so that `φ_e e '' ball (0 : ℂ) ε_e ⊆ B_badᶜ`.
  have hpre_open : IsOpen (ball (0 : ℂ) 1 ∩ φ_e e ⁻¹' B_badᶜ) :=
    ((hφc e).mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball hB_bad_cl.isOpen_compl
  have h0_pre : (0 : ℂ) ∈ ball (0 : ℂ) 1 ∩ φ_e e ⁻¹' B_badᶜ :=
    ⟨mem_ball_self zero_lt_one, by change φ_e e 0 ∉ B_bad; rwa [hφ0 e]⟩
  obtain ⟨δ_e, hδ_e_pos, hδ_e_ball⟩ := Metric.isOpen_iff.mp hpre_open 0 h0_pre
  let ε_e : ℝ := min ρ (δ_e / 2)
  have hε_pos : 0 < ε_e := lt_min hρ_pos (half_pos hδ_e_pos)
  have hε_le_ρ : ε_e ≤ ρ := min_le_left _ _
  have hε_le_one : ε_e ≤ 1 := le_trans hε_le_ρ hρ_le_one
  have hε_not_bad : ∀ w ∈ ball (0 : ℂ) ε_e, φ_e e w ∉ B_bad := by
    intro w hw
    have hw_δ : w ∈ ball (0 : ℂ) δ_e :=
      ball_subset_ball (le_trans (min_le_right _ _) (half_lt_self hδ_e_pos).le) hw
    exact (hδ_e_ball hw_δ).2
  have hGdU_iff_re_zero : ∀ w ∈ ball (0 : ℂ) ε_e, φ_e e w ∈ G_dual.U ↔ w.re = 0 := by
    intro w hw_ball
    have hw_cl1 : w ∈ closedBall (0 : ℂ) 1 :=
      ball_subset_closedBall (ball_subset_ball hε_le_one hw_ball)
    have hw_not_bad : φ_e e w ∉ B_bad := hε_not_bad w hw_ball
    constructor
    · intro hw_GdU
      rw [hGd_U] at hw_GdU
      rcases hw_GdU with hwW | ⟨_, ⟨e', rfl⟩, hwK⟩
      · exact False.elim (hw_not_bad (Or.inl (Or.inr hwW)))
      · by_cases he' : e' = e
        · subst e'
          rcases hwK with (hwT | hwR) | (hwT | hwR)
          · rw [(hT_props (e, true)).2.2.2.2.2.2] at hwT
            rcases hwT with ⟨t, _, htw⟩ | hwA
            · have hzw := hφi e (zStub_mem_closedBall_one true t) hw_cl1 htw
              rw [← hzw, zStub_re]
            · exact False.elim (hw_not_bad (Or.inl (Or.inl (Or.inl (Or.inl hwA)))))
          · exact False.elim (hw_not_bad (Or.inl (Or.inl (Or.inr
              ⟨_, ⟨r_of (e, true), rfl⟩, hR_sub_D (e, true) hwR⟩))))
          · rw [(hT_props (e, false)).2.2.2.2.2.2] at hwT
            rcases hwT with ⟨t, _, htw⟩ | hwA
            · have hzw := hφi e (zStub_mem_closedBall_one false t) hw_cl1 htw
              rw [← hzw, zStub_re]
            · exact False.elim (hw_not_bad (Or.inl (Or.inl (Or.inl (Or.inr hwA)))))
          · exact False.elim (hw_not_bad (Or.inl (Or.inl (Or.inr
              ⟨_, ⟨r_of (e, false), rfl⟩, hR_sub_D (e, false) hwR⟩))))
        · exact False.elim (hw_not_bad (Or.inr (mem_iUnion₂.mpr
            ⟨e', Finset.mem_erase.mpr ⟨he', Finset.mem_univ e'⟩, hwK⟩)))
    · intro hw_re
      have hw_norm : ‖w‖ < ε_e := mem_ball_zero_iff.mp hw_ball
      have him_abs : |w.im| < ε_e := (abs_im_le_norm w).trans_lt hw_norm
      rw [hGd_U]
      right
      refine ⟨_, ⟨e, rfl⟩, ?_⟩
      rcases le_or_gt 0 w.im with him_nonneg | him_neg
      · left
        left
        rw [(hT_props (e, true)).2.2.2.2.2.2]
        left
        have ht_le_u : 2 * w.im ≤ (u₀ (e, true) : ℝ) := by
          have h1 : w.im < (u₀ (e, true) : ℝ) / 2 :=
            lt_of_lt_of_le (by rwa [abs_of_nonneg him_nonneg] at him_abs)
              (le_trans hε_le_ρ (min_le_left _ _))
          linarith
        let t : I := ⟨2 * w.im, by linarith, le_trans ht_le_u (u₀ (e, true)).2.2⟩
        refine ⟨t, ⟨unitInterval.nonneg t, ht_le_u⟩, ?_⟩
        dsimp [stub]
        congr 1
        apply Complex.ext
        · rw [zStub_re, hw_re]
        · simp [zStub_im, t]
      · right
        left
        rw [(hT_props (e, false)).2.2.2.2.2.2]
        left
        have ht_le_u : -2 * w.im ≤ (u₀ (e, false) : ℝ) := by
          have h1 : -w.im < (u₀ (e, false) : ℝ) / 2 :=
            lt_of_lt_of_le (by rwa [abs_of_neg him_neg] at him_abs)
              (le_trans hε_le_ρ (min_le_right _ _))
          linarith
        let t : I := ⟨-2 * w.im, by linarith, le_trans ht_le_u (u₀ (e, false)).2.2⟩
        refine ⟨t, ⟨unitInterval.nonneg t, ht_le_u⟩, ?_⟩
        dsimp [stub]
        congr 1
        apply Complex.ext
        · rw [zStub_re, hw_re]
        · simp [zStub_im, t]
  have hO_ball_open : IsOpen (φ_e e '' ball (0 : ℂ) ε_e) :=
    isOpen_image_ball_of_disc hS (hφc e) (hφi e) hε_le_one
  obtain ⟨x, ⟨z, hz_ball, rfl⟩, hxr'⟩ :=
    _root_.mem_closure_iff.mp hm_cl (φ_e e '' ball (0 : ℂ) ε_e) hO_ball_open
      ⟨0, mem_ball_self hε_pos, hφ0 e⟩
  have hx_not_GdU : φ_e e z ∉ G_dual.U := region_subset hr' hxr'
  have hz_re_ne : z.re ≠ 0 := fun h => hx_not_GdU ((hGdU_iff_re_zero z hz_ball).mpr h)
  let q_real : ℝ := if 0 < z.re then ε_e / 2 else -ε_e / 2
  let q : ℂ := (q_real : ℂ)
  have hq_ball : q ∈ ball (0 : ℂ) ε_e := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs]
    dsimp [q_real]
    split_ifs
    · rw [abs_of_pos (half_pos hε_pos)]
      linarith
    · have hneg_div : -ε_e / 2 = -(ε_e / 2) := neg_div _ _
      rw [hneg_div, abs_neg, abs_of_pos (half_pos hε_pos)]
      linarith
  have hq_ball1 : q ∈ ball (0 : ℂ) 1 := ball_subset_ball hε_le_one hq_ball
  have hq_im : q.im = 0 := ofReal_im q_real
  have hq_mem_e : φ_e e q ∈ e.1 := hφ_real_sub e ⟨q, ⟨hq_ball1, hq_im⟩, rfl⟩
  let seg : I → S := fun t => φ_e e ((1 - (t : ℝ)) • z + (t : ℝ) • q)
  have hseg_ball : ∀ t : I, (1 - (t : ℝ)) • z + (t : ℝ) • q ∈ ball (0 : ℂ) ε_e :=
    fun t => convex_ball (0 : ℂ) ε_e hz_ball hq_ball
      (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))
  have hseg_cl1 : ∀ t : I, (1 - (t : ℝ)) • z + (t : ℝ) • q ∈ closedBall (0 : ℂ) 1 :=
    fun t => ball_subset_closedBall (ball_subset_ball hε_le_one (hseg_ball t))
  have hseg_cont : Continuous seg := (hφc e).comp_continuous (by fun_prop) hseg_cl1
  have hseg_disj : Disjoint (range seg) G_dual.U := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ hU
    have hre0 : ((1 - (t : ℝ)) • z + (t : ℝ) • q).re = 0 :=
      (hGdU_iff_re_zero _ (hseg_ball t)).mp hU
    simp only [add_re, real_smul, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, q] at hre0
    have ht0 := t.2.1
    have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
    rcases lt_or_gt_of_ne hz_re_ne with hneg | hpos
    · have hq_neg : q_real = -ε_e / 2 := ite_eq_right (not_lt.mpr hneg.le)
      rw [hq_neg] at hre0
      have h1 : (1 - (t : ℝ)) * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht1 hneg.le
      have h2 : (t : ℝ) * (-ε_e / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by linarith)
      have h3 : (t : ℝ) * (-ε_e / 2) = 0 := by linarith
      have ht_zero : (t : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right (by linarith)
      rw [ht_zero] at hre0
      linarith
    · have hq_pos : q_real = ε_e / 2 := ite_eq_left hpos
      rw [hq_pos] at hre0
      have h1 : 0 ≤ (1 - (t : ℝ)) * z.re := mul_nonneg ht1 hpos.le
      have h2 : 0 ≤ (t : ℝ) * (ε_e / 2) := mul_nonneg ht0 (by linarith)
      have h3 : (t : ℝ) * (ε_e / 2) = 0 := by linarith
      have ht_zero : (t : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right (by linarith)
      rw [ht_zero] at hre0
      linarith
  have hseg_sub : range seg ⊆ r' :=
    subset_region hr' (isPreconnected_range hseg_cont) hseg_disj ⟨0, by simp [seg]⟩ hxr'
  exact ⟨φ_e e q, hseg_sub ⟨1, by simp [seg]⟩, hq_mem_e⟩

private theorem incident_regions_of_edge_charts (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hProper : G.IsProper)
    {m_of : G.E → S} (hm_mem_e : ∀ e : G.E, m_of e ∈ e.1)
    {φ_e : G.E → ℂ → S} (hφc : ∀ e : G.E, ContinuousOn (φ_e e) (closedBall 0 1))
    (hφi : ∀ e : G.E, InjOn (φ_e e) (closedBall 0 1))
    (hφ0 : ∀ e : G.E, φ_e e 0 = m_of e)
    (hφU : ∀ e : G.E, ∀ z ∈ closedBall (0 : ℂ) 1, φ_e e z ∈ G.U ↔ z.im = 0) :
    let Half := G.E × Bool
    let stub : Half → I → S := fun a t => φ_e a.1 (zStub a.2 t)
    ∀ {r_of : Half → G.R},
    (∀ a : Half, IsArcMap (stub a)) → (∀ a : Half, stub a 0 = m_of a.1) →
    (∀ a : Half, ∀ t : I, (0 : I) < t → stub a t ∈ (r_of a).1 \ bd S) →
    (∀ a : Half, G.EdgeRegionIncident a.1.1 (r_of a).1) ∧
    ∀ (e : G.E) (r : Set S), r ∈ G.R →
      G.EdgeRegionIncident e.1 r → r = (r_of (e, true)).1 ∨ r = (r_of (e, false)).1 := by
  intro Half stub r_of hstub_arc hstub_0 hr_of
  have hm_cl_r : ∀ a : Half, m_of a.1 ∈ closure (r_of a).1 := by
    intro a
    have h0_mem : stub a 0 ∈ stub a '' closure (Ioc (0 : I) 1) :=
      ⟨0, by rw [closure_Ioc zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hsub_r : stub a '' Ioc (0 : I) 1 ⊆ (r_of a).1 := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hr_of a t ht.1).1
    rw [← hstub_0 a]
    exact closure_mono hsub_r (image_closure_subset_closure_image (hstub_arc a).1 h0_mem)
  have hinc_r_of : ∀ a : Half, G.EdgeRegionIncident a.1.1 (r_of a).1 :=
    fun a => ⟨a.1.2, (r_of a).2, m_of a.1, hm_mem_e a.1, hm_cl_r a⟩
  have hall_inc_r : ∀ (e : G.E) (r : Set S), r ∈ G.R →
      G.EdgeRegionIncident e.1 r → r = (r_of (e, true)).1 ∨ r = (r_of (e, false)).1 := by
    intro e r hr hinc
    have he_sub : e.1 ⊆ closure r :=
      disc_edge_subset_closure_of_incident hS hProper e.2 hr hinc.2.2
    have hm_cl : m_of e ∈ closure r := he_sub (hm_mem_e e)
    have hO_open1 : IsOpen (φ_e e '' ball (0 : ℂ) 1) :=
      isOpen_image_ball_of_disc hS (hφc e) (hφi e) le_rfl
    obtain ⟨x, ⟨z, hz_ball, rfl⟩, hxr⟩ :=
      _root_.mem_closure_iff.mp hm_cl (φ_e e '' ball (0 : ℂ) 1) hO_open1
        ⟨0, mem_ball_self zero_lt_one, hφ0 e⟩
    have hz_cl1 : z ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hz_ball
    have hx_not_U : φ_e e z ∉ G.U := region_subset hr hxr
    have hz_im_ne : z.im ≠ 0 := fun h => hx_not_U ((hφU e z hz_cl1).mpr h)
    let sgn : Bool := decide (0 < z.im)
    let p : ℂ := zStub sgn 1
    have hp_ball : p ∈ ball (0 : ℂ) 1 := zStub_mem_ball_one sgn 1
    let seg_r : I → S := fun t => φ_e e ((1 - (t : ℝ)) • z + (t : ℝ) • p)
    have hseg_r_ball : ∀ t : I, (1 - (t : ℝ)) • z + (t : ℝ) • p ∈ ball (0 : ℂ) 1 :=
      fun t => convex_ball (0 : ℂ) 1 hz_ball hp_ball
        (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))
    have hseg_r_cl1 : ∀ t : I, (1 - (t : ℝ)) • z + (t : ℝ) • p ∈ closedBall (0 : ℂ) 1 :=
      fun t => ball_subset_closedBall (hseg_r_ball t)
    have hseg_r_cont : Continuous seg_r := (hφc e).comp_continuous (by fun_prop) hseg_r_cl1
    have hseg_r_disj : Disjoint (range seg_r) G.U := by
      refine disjoint_left.mpr ?_
      rintro _ ⟨t, rfl⟩ hU
      have him0 : ((1 - (t : ℝ)) • z + (t : ℝ) • p).im = 0 :=
        (hφU e _ (hseg_r_cl1 t)).mp hU
      simp only [add_im, real_smul, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] at him0
      have ht0 := t.2.1
      have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
      rcases lt_or_gt_of_ne hz_im_ne with hneg | hpos
      · have hsgn_f : sgn = false := decide_eq_false (not_lt.mpr hneg.le)
        have hp_im : p.im = -1 / 2 := by
          dsimp [p]
          rw [zStub_im, hsgn_f]
          simp
        rw [hp_im] at him0
        have h1 : (1 - (t : ℝ)) * z.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht1 hneg.le
        have h2 : (t : ℝ) * (-1 / 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 (by norm_num)
        have h3 : (t : ℝ) * (-1 / 2) = 0 := by linarith
        have ht_zero : (t : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right (by norm_num)
        rw [ht_zero] at him0
        linarith
      · have hsgn_t : sgn = true := decide_eq_true hpos
        have hp_im : p.im = 1 / 2 := by
          dsimp [p]
          rw [zStub_im, hsgn_t]
          simp
        rw [hp_im] at him0
        have h1 : 0 ≤ (1 - (t : ℝ)) * z.im := mul_nonneg ht1 hpos.le
        have h2 : 0 ≤ (t : ℝ) * (1 / 2) := mul_nonneg ht0 (by norm_num)
        have h3 : (t : ℝ) * (1 / 2) = 0 := by linarith
        have ht_zero : (t : ℝ) = 0 := (mul_eq_zero.mp h3).resolve_right (by norm_num)
        rw [ht_zero] at him0
        linarith
    have hseg_r_sub : range seg_r ⊆ r :=
      subset_region hr (isPreconnected_range hseg_r_cont) hseg_r_disj ⟨0, by simp [seg_r]⟩ hxr
    have h1_in_r : stub (e, sgn) 1 ∈ r := hseg_r_sub ⟨1, by simp [seg_r, stub, p]⟩
    have h1_in_rof : stub (e, sgn) 1 ∈ (r_of (e, sgn)).1 := (hr_of (e, sgn) 1 zero_lt_one).1
    have hr_eq : r = (r_of (e, sgn)).1 := region_eq_of_mem hr (r_of (e, sgn)).2 h1_in_r h1_in_rof
    rcases Bool.dichotomy sgn with hsgn | hsgn
    · rw [hsgn] at hr_eq
      exact Or.inr hr_eq
    · rw [hsgn] at hr_eq
      exact Or.inl hr_eq
  exact ⟨hinc_r_of, hall_inc_r⟩

private theorem dual_edge_link_iff_of_incident_regions {G G_dual : Drawing S}
    (edgeEquiv : G.E ≃ G_dual.E) {W : Set S} (hGd_V : G_dual.V = W)
    {w_of : G.R → S} (hw_in : ∀ r : G.R, w_of r ∈ r.1)
    (hw_of_uniq : ∀ (r : G.R) x, x ∈ r.1 ∧ x ∈ W → x = w_of r)
    {r_of : G.E × Bool → G.R}
    (hinc_r_of : ∀ a : G.E × Bool, G.EdgeRegionIncident a.1.1 (r_of a).1)
    (hall_inc_r : ∀ (e : G.E) (r : Set S), r ∈ G.R →
      G.EdgeRegionIncident e.1 r → r = (r_of (e, true)).1 ∨ r = (r_of (e, false)).1)
    (hedge_link : ∀ e : G.E, G_dual.toGraph.IsLink (edgeEquiv e).1
      (w_of (r_of (e, true))) (w_of (r_of (e, false)))) :
    ∀ (e : G.E) (r₁ : Set S), r₁ ∈ G.R → ∀ (r₂ : Set S), r₂ ∈ G.R →
    ∀ w₁ ∈ r₁ ∩ G_dual.V, ∀ w₂ ∈ r₂ ∩ G_dual.V,
      G_dual.toGraph.IsLink (edgeEquiv e).1 w₁ w₂ ↔
        G.EdgeRegionIncident e.1 r₁ ∧ G.EdgeRegionIncident e.1 r₂ ∧
        ∀ r ∈ G.R, G.EdgeRegionIncident e.1 r → r = r₁ ∨ r = r₂ := by
  have hw_of_inj : Function.Injective w_of := by
    intro r₁ r₂ heq
    have hwr₁ : w_of r₁ ∈ r₁.1 := hw_in r₁
    have hwr₂ : w_of r₁ ∈ r₂.1 := heq ▸ hw_in r₂
    exact Subtype.ext (region_eq_of_mem r₁.2 r₂.2 hwr₁ hwr₂)
  intro e r₁ hr₁ r₂ hr₂ w₁ hw₁ w₂ hw₂
  have hw₁_eq : w₁ = w_of ⟨r₁, hr₁⟩ :=
    hw_of_uniq ⟨r₁, hr₁⟩ w₁ ⟨hw₁.1, hGd_V ▸ hw₁.2⟩
  have hw₂_eq : w₂ = w_of ⟨r₂, hr₂⟩ :=
    hw_of_uniq ⟨r₂, hr₂⟩ w₂ ⟨hw₂.1, hGd_V ▸ hw₂.2⟩
  have hlink_e := hedge_link e
  let rt := r_of (e, true)
  let rf := r_of (e, false)
  constructor
  · intro hlink'
    have hpair : ({w₁, w₂} : Set S) = {w_of rt, w_of rf} :=
      hlink'.2.2.2.symm.trans hlink_e.2.2.2
    have hw₁_mem : w₁ = w_of rt ∨ w₁ = w_of rf := by
      have : w₁ ∈ ({w₁, w₂} : Set S) := mem_insert w₁ {w₂}
      rwa [hpair, mem_insert_iff, mem_singleton_iff] at this
    have hw₂_mem : w₂ = w_of rt ∨ w₂ = w_of rf := by
      have : w₂ ∈ ({w₁, w₂} : Set S) := mem_insert_of_mem w₁ (mem_singleton w₂)
      rwa [hpair, mem_insert_iff, mem_singleton_iff] at this
    have hrt_mem : w_of rt = w₁ ∨ w_of rt = w₂ := by
      have : w_of rt ∈ ({w_of rt, w_of rf} : Set S) := mem_insert (w_of rt) {w_of rf}
      rwa [← hpair, mem_insert_iff, mem_singleton_iff] at this
    have hrf_mem : w_of rf = w₁ ∨ w_of rf = w₂ := by
      have : w_of rf ∈ ({w_of rt, w_of rf} : Set S) :=
        mem_insert_of_mem (w_of rt) (mem_singleton (w_of rf))
      rwa [← hpair, mem_insert_iff, mem_singleton_iff] at this
    have hr₁_mem : r₁ = rt.1 ∨ r₁ = rf.1 := by
      rcases hw₁_mem with h1 | h1
      · exact Or.inl (congrArg Subtype.val (hw_of_inj (hw₁_eq.symm.trans h1)))
      · exact Or.inr (congrArg Subtype.val (hw_of_inj (hw₁_eq.symm.trans h1)))
    have hr₂_mem : r₂ = rt.1 ∨ r₂ = rf.1 := by
      rcases hw₂_mem with h2 | h2
      · exact Or.inl (congrArg Subtype.val (hw_of_inj (hw₂_eq.symm.trans h2)))
      · exact Or.inr (congrArg Subtype.val (hw_of_inj (hw₂_eq.symm.trans h2)))
    have hrt_12 : rt.1 = r₁ ∨ rt.1 = r₂ := by
      rcases hrt_mem with ht | ht
      · exact Or.inl (congrArg Subtype.val (hw_of_inj (ht.trans hw₁_eq)))
      · exact Or.inr (congrArg Subtype.val (hw_of_inj (ht.trans hw₂_eq)))
    have hrf_12 : rf.1 = r₁ ∨ rf.1 = r₂ := by
      rcases hrf_mem with hf | hf
      · exact Or.inl (congrArg Subtype.val (hw_of_inj (hf.trans hw₁_eq)))
      · exact Or.inr (congrArg Subtype.val (hw_of_inj (hf.trans hw₂_eq)))
    refine ⟨?_, ?_, fun r hr hinc => ?_⟩
    · rcases hr₁_mem with rfl | rfl
      · exact hinc_r_of (e, true)
      · exact hinc_r_of (e, false)
    · rcases hr₂_mem with rfl | rfl
      · exact hinc_r_of (e, true)
      · exact hinc_r_of (e, false)
    · rcases hall_inc_r e r hr hinc with rfl | rfl
      · exact hrt_12
      · exact hrf_12
  · rintro ⟨hinc1, hinc2, hall⟩
    have hw₁_tf : w₁ = w_of rt ∨ w₁ = w_of rf := by
      rcases hall_inc_r e r₁ hr₁ hinc1 with heq | heq
      · exact Or.inl (hw₁_eq.trans (congrArg w_of (Subtype.ext heq)))
      · exact Or.inr (hw₁_eq.trans (congrArg w_of (Subtype.ext heq)))
    have hw₂_tf : w₂ = w_of rt ∨ w₂ = w_of rf := by
      rcases hall_inc_r e r₂ hr₂ hinc2 with heq | heq
      · exact Or.inl (hw₂_eq.trans (congrArg w_of (Subtype.ext heq)))
      · exact Or.inr (hw₂_eq.trans (congrArg w_of (Subtype.ext heq)))
    have hrt_12 : w_of rt = w₁ ∨ w_of rt = w₂ := by
      rcases hall rt.1 rt.2 (hinc_r_of (e, true)) with heq | heq
      · exact Or.inl ((congrArg w_of (Subtype.ext heq)).trans hw₁_eq.symm)
      · exact Or.inr ((congrArg w_of (Subtype.ext heq)).trans hw₂_eq.symm)
    have hrf_12 : w_of rf = w₁ ∨ w_of rf = w₂ := by
      rcases hall rf.1 rf.2 (hinc_r_of (e, false)) with heq | heq
      · exact Or.inl ((congrArg w_of (Subtype.ext heq)).trans hw₁_eq.symm)
      · exact Or.inr ((congrArg w_of (Subtype.ext heq)).trans hw₂_eq.symm)
    refine ⟨(edgeEquiv e).2, hw₁.2, hw₂.2, ?_⟩
    rw [hlink_e.2.2.2]
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact hrt_12
      · exact hrf_12
    · rintro (rfl | rfl)
      · exact hw₁_tf
      · exact hw₂_tf

private theorem exists_disjoint_edge_charts (hS : IsClosedDiscSpace S) {G : Drawing S}
    (hProper : G.IsProper) {h : S → ℂ} (hh : Continuous h) (hinj : Function.Injective h)
    {D_union : Set S} (hD_union_cl : IsClosed D_union) (hD_union_disj_U : Disjoint D_union G.U) :
    ∃ (m_of : G.E → S) (O_of : G.E → Set S) (φ_e : G.E → ℂ → S),
      (∀ e : G.E, m_of e ∈ e.1) ∧ (∀ e : G.E, m_of e ∈ G.U) ∧
      (∀ e : G.E, m_of e ∉ bd S) ∧ Function.Injective m_of ∧
      (∀ e₁ e₂ : G.E, e₁ ≠ e₂ → Disjoint (O_of e₁) (O_of e₂)) ∧
      (∀ e : G.E, φ_e e '' closedBall (0 : ℂ) 1 ⊆ O_of e \ bd S) ∧
      (∀ e : G.E, Disjoint (O_of e) D_union) ∧
      (∀ e : G.E, ContinuousOn (φ_e e) (closedBall 0 1)) ∧
      (∀ e : G.E, InjOn (φ_e e) (closedBall 0 1)) ∧
      (∀ e : G.E, φ_e e 0 = m_of e) ∧
      (∀ e : G.E, ∀ z ∈ closedBall (0 : ℂ) 1, φ_e e z ∈ G.U ↔ z.im = 0) ∧
      (∀ e : G.E, φ_e e '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} ⊆ e.1) := by
  classical
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : Finite G.E := G.finite_edges.to_subtype
  let _ : Fintype G.E := Fintype.ofFinite G.E
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  choose γ_e hγ_cont hγ_0 hγ_1 hγ_inj hγ_img _ _ using
    fun e : G.E => exists_edge_param_isLink G e.2
  let tLeft : I := ⟨1 / 4, by norm_num, by norm_num⟩
  let tMid : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let tRight : I := ⟨3 / 4, by norm_num, by norm_num⟩
  have htMid_Ioo : tMid ∈ Ioo (0 : I) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have htLeft_lt : tLeft < tMid := by change (1 / 4 : ℝ) < 1 / 2; norm_num
  have htMid_lt : tMid < tRight := by change (1 / 2 : ℝ) < 3 / 4; norm_num
  let m_of : G.E → S := fun e => γ_e e tMid
  have hm_mem_e : ∀ e : G.E, m_of e ∈ e.1 :=
    fun e => hγ_img e ▸ mem_image_of_mem (γ_e e) htMid_Ioo
  have hm_mem_U : ∀ e : G.E, m_of e ∈ G.U :=
    fun e => (e.2.2.1 (hm_mem_e e)).1
  have hm_not_bd : ∀ e : G.E, m_of e ∉ bd S :=
    fun e hbd => (e.2.2.1 (hm_mem_e e)).2 (hProper ⟨hbd, hm_mem_U e⟩)
  have hm_inj : Function.Injective m_of := by
    intro e₁ e₂ heq
    by_contra hne
    have hdisj := disjoint_edges_of_ne G e₁.2 e₂.2 (Subtype.coe_ne_coe.mpr hne)
    exact disjoint_left.mp hdisj (hm_mem_e e₁) (heq ▸ hm_mem_e e₂)
  let Voro : G.E → Set S := fun e =>
    ⋂ e' ∈ Finset.univ.erase e, {x : S | dist (h x) (h (m_of e)) < dist (h x) (h (m_of e'))}
  have hVoro_open : ∀ e : G.E, IsOpen (Voro e) := by
    intro e
    exact isOpen_biInter_finset fun e' _ =>
      isOpen_lt (hh.dist continuous_const) (hh.dist continuous_const)
  have hm_Voro : ∀ e : G.E, m_of e ∈ Voro e := by
    intro e
    simp only [Voro, mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
    intro e' hne
    change dist (h (m_of e)) (h (m_of e)) < dist (h (m_of e)) (h (m_of e'))
    rw [dist_self, dist_pos]
    exact hinj.ne (hm_inj.ne hne.symm)
  have hVoro_disj : ∀ e₁ e₂ : G.E, e₁ ≠ e₂ → Disjoint (Voro e₁) (Voro e₂) := by
    intro e₁ e₂ hne
    refine disjoint_left.mpr fun x hx1 hx2 => ?_
    have h1 : dist (h x) (h (m_of e₁)) < dist (h x) (h (m_of e₂)) := by
      have := mem_iInter₂.mp hx1 e₂ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ e₂⟩)
      exact this
    have h2 : dist (h x) (h (m_of e₂)) < dist (h x) (h (m_of e₁)) := by
      have := mem_iInter₂.mp hx2 e₁ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ e₁⟩)
      exact this
    exact lt_irrefl _ (h1.trans h2)
  let O_of : G.E → Set S := fun e =>
    Voro e ∩ (G.V ∪ (G.U \ e.1) ∪ D_union ∪ bd S)ᶜ
  have hO_open : ∀ e : G.E, IsOpen (O_of e) := by
    intro e
    refine (hVoro_open e).inter ?_
    exact (((G.finite_V.isClosed.union (isClosed_U_sdiff_edge G e.2)).union hD_union_cl).union
      hbd_cl).isOpen_compl
  have hm_O : ∀ e : G.E, m_of e ∈ O_of e := by
    intro e
    refine ⟨hm_Voro e, ?_⟩
    rintro (((hmV | hm_sdiff) | hmD) | hmbd)
    · exact (e.2.2.1 (hm_mem_e e)).2 hmV
    · exact hm_sdiff.2 (hm_mem_e e)
    · exact disjoint_left.mp hD_union_disj_U hmD (hm_mem_U e)
    · exact hm_not_bd e hmbd
  have hchart_exists : ∀ e : G.E,
      ∃ (φ : ℂ → S) (a b : I), ContinuousOn φ (closedBall 0 1) ∧ InjOn φ (closedBall 0 1) ∧
        tLeft < a ∧ a < tMid ∧ tMid < b ∧ b < tRight ∧ φ 0 = m_of e ∧
        φ '' closedBall (0 : ℂ) 1 ⊆ O_of e \ bd S ∧
        (∀ z ∈ closedBall (0 : ℂ) 1, φ z ∈ G.U ↔ z.im = 0) ∧
        φ '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} = γ_e e '' Ioo a b := by
    intro e
    obtain ⟨φ, a, b, hφc, hφi, ha1, ha2, hb1, hb2, hφ0, hφ_sub, hφU, hφ_real, _, _⟩ :=
      disc_exists_edge_chart hS G hProper e.2 (hγ_cont e) (hγ_0 e) (hγ_1 e) (hγ_inj e)
        (hγ_img e) htMid_Ioo htLeft_lt htMid_lt (hO_open e) (hm_O e)
    exact ⟨φ, a, b, hφc, hφi, ha1, ha2, hb1, hb2, hφ0, hφ_sub, hφU, hφ_real⟩
  choose φ_e a_e b_e hφc hφi ha1 ha2 hb1 hb2 hφ0 hφ_sub hφU hφ_real using hchart_exists
  have hφ_real_sub : ∀ e : G.E, φ_e e '' {z | z ∈ ball (0 : ℂ) 1 ∧ z.im = 0} ⊆ e.1 := by
    intro e
    rw [hφ_real e, ← hγ_img e]
    have hLeft : (0 : I) < tLeft := by
      change (0 : ℝ) < 1 / 4
      norm_num
    have hRight : tRight < (1 : I) := by
      change (3 / 4 : ℝ) < 1
      norm_num
    exact image_mono fun _ ht => ⟨hLeft.trans ((ha1 e).trans ht.1),
      ht.2.trans ((hb2 e).trans hRight)⟩
  refine ⟨m_of, O_of, φ_e, hm_mem_e, hm_mem_U, hm_not_bd, hm_inj, ?_, hφ_sub, ?_,
    hφc, hφi, hφ0, hφU, hφ_real_sub⟩
  · intro e₁ e₂ hne
    exact (hVoro_disj e₁ e₂ hne).mono inter_subset_left inter_subset_left
  · intro e
    exact disjoint_left.mpr fun _ hx hxD => hx.2 (Or.inl (Or.inr hxD))

private theorem edge_stubs_and_incident_regions {G : Drawing S}
    {h : S → ℂ} {w_of : G.R → S} {δ : ℝ} {m_of : G.E → S}
    (hm_mem_U : ∀ e : G.E, m_of e ∈ G.U)
    {O_of : G.E → Set S} {φ_e : G.E → ℂ → S}
    (hO_disj : ∀ e₁ e₂ : G.E, e₁ ≠ e₂ → Disjoint (O_of e₁) (O_of e₂))
    (hO_disj_D : ∀ e : G.E, Disjoint (O_of e) (⋃ r : G.R, discBall h (w_of r) δ))
    (hφ_sub : ∀ e : G.E, φ_e e '' closedBall (0 : ℂ) 1 ⊆ O_of e \ bd S)
    (hφc : ∀ e : G.E, ContinuousOn (φ_e e) (closedBall 0 1))
    (hφi : ∀ e : G.E, InjOn (φ_e e) (closedBall 0 1))
    (hφ0 : ∀ e : G.E, φ_e e 0 = m_of e)
    (hφU : ∀ e : G.E, ∀ z ∈ closedBall (0 : ℂ) 1, φ_e e z ∈ G.U ↔ z.im = 0) :
    let Half := G.E × Bool
    let stub : Half → I → S := fun a t => φ_e a.1 (zStub a.2 t)
    let Stub : Half → Set S := fun a => range (stub a)
    ∃ r_of : Half → G.R,
      (∀ a : Half, IsArcMap (stub a)) ∧ (∀ a : Half, stub a 0 = m_of a.1) ∧
      (∀ a : Half, Stub a ∩ G.U = {m_of a.1}) ∧ (∀ a : Half, Stub a ∩ bd S = ∅) ∧
      (∀ (a : Half) (r : G.R), Disjoint (Stub a) (discBall h (w_of r) δ)) ∧
      (∀ a b : Half, b ≠ a → Stub a ∩ Stub b = if a.1 = b.1 then {m_of a.1} else ∅) ∧
      (∀ (a : Half) (t : I), (0 : I) < t → stub a t ∈ (r_of a).1 \ bd S) := by
  classical
  intro Half stub Stub
  have hstub_arc : ∀ a : Half, IsArcMap (stub a) :=
    fun a => isArcMap_stub (hφc a.1) (hφi a.1) a.2
  have hstub_0 : ∀ a : Half, stub a 0 = m_of a.1 := by
    intro a; simp [stub, zStub_zero, hφ0]
  have hstub_mem_O : ∀ a : Half, ∀ t : I, stub a t ∈ O_of a.1 \ bd S :=
    fun a t => hφ_sub a.1 ⟨zStub a.2 t, zStub_mem_closedBall_one a.2 t, rfl⟩
  have hstub_U_iff : ∀ a : Half, ∀ t : I, stub a t ∈ G.U ↔ t = 0 := by
    intro a t
    rw [hφU a.1 (zStub a.2 t) (zStub_mem_closedBall_one a.2 t), zStub_im_eq_zero_iff]
  have hStub_U : ∀ a : Half, Stub a ∩ G.U = {m_of a.1} := by
    intro a
    ext x
    simp only [Stub, mem_inter_iff, mem_range, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, rfl⟩, hxU⟩
      rw [(hstub_U_iff a t).mp hxU, hstub_0]
    · rintro rfl
      exact ⟨⟨0, hstub_0 a⟩, hm_mem_U a.1⟩
  have hStub_bd : ∀ a : Half, Stub a ∩ bd S = ∅ := by
    intro a
    rw [eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨t, rfl⟩, hbd⟩
    exact (hstub_mem_O a t).2 hbd
  have hStub_D : ∀ (a : Half) (r : G.R), Disjoint (Stub a) (discBall h (w_of r) δ) := by
    intro a r
    refine (hO_disj_D a.1).mono ?_ ?_
    · rintro _ ⟨t, rfl⟩
      exact (hstub_mem_O a t).1
    · exact subset_iUnion (fun r : G.R => discBall h (w_of r) δ) r
  have hStub_inter : ∀ a b : Half, b ≠ a → Stub a ∩ Stub b = if a.1 = b.1 then {m_of a.1} else ∅
    := by
    intro a b hne
    by_cases he : a.1 = b.1
    · rw [ite_eq_left he]
      rcases a with ⟨e, sgn₁⟩
      rcases b with ⟨e₂, sgn₂⟩
      dsimp at he
      subst e₂
      have hsgn : sgn₁ ≠ sgn₂ := fun h => hne (Prod.ext rfl h.symm)
      cases sgn₁ <;> cases sgn₂
      · exact False.elim (hsgn rfl)
      · rw [inter_comm, stub_inter_stub_opposite (hφi e), hφ0]
      · rw [stub_inter_stub_opposite (hφi e), hφ0]
      · exact False.elim (hsgn rfl)
    · rw [ite_eq_right he, eq_empty_iff_forall_notMem]
      rintro x ⟨⟨s, rfl⟩, ⟨t, hst⟩⟩
      have hx1 : stub a s ∈ O_of a.1 := (hstub_mem_O a s).1
      have hx2 : stub a s ∈ O_of b.1 := hst ▸ (hstub_mem_O b t).1
      exact disjoint_left.mp (hO_disj a.1 b.1 he) hx1 hx2
  -- Region `r_of a` containing `stub a '' Ioc 0 1`.
  have hr_exists : ∀ a : Half, ∃ r : G.R, ∀ t : I, (0 : I) < t → stub a t ∈ r.1 \ bd S := by
    intro a
    have h1_not_U : stub a 1 ∉ G.U := by
      rw [hstub_U_iff]; exact one_ne_zero
    obtain ⟨r, hr, h1_r⟩ := exists_region_of_notMem h1_not_U
    refine ⟨⟨r, hr⟩, fun t ht => ⟨?_, (hstub_mem_O a t).2⟩⟩
    have hIoc_sub : stub a '' Ioc 0 1 ⊆ univ \ G.U := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨mem_univ _, fun hsU => hs.1.ne' ((hstub_U_iff a s).mp hsU)⟩
    have hIoc_conn : IsPreconnected (stub a '' Ioc 0 1) :=
      isPreconnected_Ioc.image (stub a) (hstub_arc a).1.continuousOn
    have hIoc_r : stub a '' Ioc 0 1 ⊆ r :=
      subset_region hr hIoc_conn (disjoint_left.mpr fun z hz => (hIoc_sub hz).2)
        ⟨1, right_mem_Ioc.mpr zero_lt_one, rfl⟩ h1_r
    exact hIoc_r ⟨t, ⟨ht, unitInterval.le_one t⟩, rfl⟩
  choose r_of hr_of using hr_exists
  exact ⟨r_of, hstub_arc, hstub_0, hStub_U, hStub_bd, hStub_D, hStub_inter, hr_of⟩

/-- Every connected proper drawing `G` on a closed disc space `S` has a disc dual drawing
`G_dual : Drawing S` satisfying `IsDiscDualDrawing G G_dual`. -/
theorem exists_isDiscDualDrawing (hS : IsClosedDiscSpace S) {G : Drawing S}
    (hProper : G.IsProper) (hConn : IsGraphConnected G.toGraph) :
    ∃ G_dual : Drawing S, IsDiscDualDrawing G G_dual := by
  classical
  by_cases hE_emp : G.E = ∅
  · exact exists_isDiscDualDrawing_of_edges_empty hS hProper hConn hE_emp
  have hT2 : T2Space S := t2Space_of_isClosedDiscSpace hS
  have : CompactSpace S := compactSpace_of_isClosedDiscSpace hS
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have hbd_cl : IsClosed (bd S) := isClosed_bd_of_isClosedDiscSpace hS
  obtain ⟨h, g, hh, hinj, hg, hmem, hgl, hgr, _, _, hball_iff⟩ := exists_disc_complex_chart hS
  obtain ⟨W, hW_fin, hW_uniq, hW_in_R, hW_bd⟩ :=
    exists_dual_vertices_of_connected hS hProper hConn
  have hR_fin : G.R.Finite := disc_finite_R hS G hProper
  have : Finite G.R := hR_fin.to_subtype
  have : Finite G.E := G.finite_edges.to_subtype
  let _ : Fintype G.R := Fintype.ofFinite G.R
  let _ : Fintype G.E := Fintype.ofFinite G.E
  choose w_of hw_of_mem hw_of_uniq using fun r : G.R => hW_uniq r.1 r.2
  have hw_in : ∀ r : G.R, w_of r ∈ r.1 := fun r => (hw_of_mem r).1
  have hw_W : ∀ r : G.R, w_of r ∈ W := fun r => (hw_of_mem r).2
  have hW_disj_U : Disjoint W G.U := by
    refine disjoint_left.mpr fun w hw hwU => ?_
    obtain ⟨r, hr, hwr⟩ := hW_in_R w hw
    exact region_subset hr hwr hwU
  -- Step 1: Uniform radius `δ > 0` for `discBall h (w_of r) δ ⊆ r.1` and interior centers `c_of r`.
  obtain ⟨δ, hδ_pos, _, hδ_sub⟩ :=
    exists_uniform_discBall_radius hS hProper hh hinj w_of hw_in
  have hc_exists : ∀ r : G.R, ∃ c : S, c ∈ discOpenBall h (w_of r) δ \ bd S := by
    intro r
    exact open_sdiff_bd_nonempty hS (isOpen_discOpenBall hh (w_of r) δ)
      ⟨w_of r, mem_discOpenBall_self h (w_of r) hδ_pos⟩
  choose c_of hc_of using hc_exists
  let D_union : Set S := ⋃ r : G.R, discBall h (w_of r) δ
  have hD_union_cl : IsClosed D_union :=
    isClosed_iUnion_of_finite fun r => isClosed_discBall hh (w_of r) δ
  have hD_union_disj_U : Disjoint D_union G.U := by
    refine disjoint_left.mpr ?_
    rintro x ⟨_, ⟨r, rfl⟩, hxr⟩ hxU
    exact region_subset r.2 (hδ_sub r hxr) hxU
  obtain ⟨m_of, O_of, φ_e, hm_mem_e, hm_mem_U, hm_not_bd, hm_inj, hO_disj, hφ_sub, hO_disj_D,
      hφc, hφi, hφ0, hφU, hφ_real_sub⟩ :=
    exists_disjoint_edge_charts hS hProper hh hinj hD_union_cl hD_union_disj_U
  have hm_not_W : ∀ e : G.E, m_of e ∉ W :=
    fun e hmW => disjoint_left.mp hW_disj_U hmW (hm_mem_U e)
  let Half := G.E × Bool
  let stub : Half → I → S := fun a t => φ_e a.1 (zStub a.2 t)
  let Stub : Half → Set S := fun a => range (stub a)
  obtain ⟨r_of, hstub_arc, hstub_0, hStub_U, hStub_bd, hStub_D, hStub_inter, hr_of⟩ :=
    edge_stubs_and_incident_regions hm_mem_U hO_disj hO_disj_D hφ_sub hφc hφi hφ0 hφU
  have h_ind := exists_truncated_spokes hS hh hδ_sub hc_of hm_mem_U hm_not_bd hm_inj
    stub r_of hstub_arc hstub_0 hStub_U hStub_bd hStub_D hStub_inter hr_of
  obtain ⟨T, A_far, y, u₀, _, hT_in, hT_all⟩ := h_ind Finset.univ
  have hT_props : ∀ a : Half,
      IsLineWithEnds (T a) (m_of a.1) (y a) ∧
      y a ∈ discSphere h (w_of (r_of a)) δ ∧
      T a ∩ discBall h (w_of (r_of a)) δ = {y a} ∧
      (0 : I) < u₀ a ∧
      IsClosed (A_far a) ∧
      m_of a.1 ∉ A_far a ∧
      T a = stub a '' Icc 0 (u₀ a) ∪ A_far a :=
    fun a => hT_in a (Finset.mem_univ a)
  have hy_inj : Function.Injective y := by
    intro a b hab
    by_contra hne
    have hya : y a ∈ T a \ {m_of a.1} := by
      refine ⟨IsLineWithEnds.right_mem (hT_props a).1, fun heq => ?_⟩
      exact disjoint_left.mp hD_union_disj_U
        ⟨_, ⟨r_of a, rfl⟩, discSphere_subset_discBall h (w_of (r_of a)) δ (hT_props a).2.1⟩
        (heq ▸ hm_mem_U a.1)
    have hyb : y a ∈ T b := hab ▸ IsLineWithEnds.right_mem (hT_props b).1
    have hinter : y a ∈ T a ∩ T b := ⟨hya.1, hyb⟩
    rw [(hT_all a).2.2.2.2.2.2 b (Ne.symm hne)] at hinter
    split_ifs at hinter with heq
    · exact hya.2 hinter
    · exact hinter
  -- Step 5: Attach radial segments `R_seg a` in `discBall h (w_of (r_of a)) δ` to form `H e sgn`.
  let R_seg : Half → Set S := fun a => range (radMap h g (w_of (r_of a)) (y a))
  let H : G.E → Bool → Set S := fun e sgn => T (e, sgn) ∪ R_seg (e, sgn)
  let w_end : G.E → Bool → S := fun e sgn => w_of (r_of (e, sgn))
  obtain ⟨hR_sub_D, hH_line, hH_U, hH_bd, hH_W, hH_opp, hH_opp_ne, hH_disj⟩ :=
    radial_spoke_properties hinj hg hmem hgl hgr hball_iff hδ_pos hδ_sub hm_mem_U hm_not_W
      hw_W hw_of_uniq hy_inj hT_props hT_all
  -- Step 6: Obtain `G_dual` and `edgeEquiv` from `exists_dual_drawing_of_spokes`.
  obtain ⟨G_dual, edgeEquiv, hGd_V, hGd_U, hedge_eq, hedge_link⟩ :=
    exists_dual_drawing_of_spokes hW_fin m_of w_end H hm_not_W
      (fun e sgn => hw_W (r_of (e, sgn))) hH_line hH_W hH_opp hH_opp_ne hH_disj
  have hGd_prop : G_dual.IsProper := by
    rintro x ⟨hxbd, hxU⟩
    rw [hGd_V]
    rw [hGd_U] at hxU
    rcases hxU with hxW | ⟨_, ⟨e, rfl⟩, hxH | hxH⟩
    · exact hxW
    · have : x ∈ H e true ∩ bd S := ⟨hxH, hxbd⟩
      rw [mem_singleton_iff.mp (hH_bd e true this)]
      exact hw_W (r_of (e, true))
    · have : x ∈ H e false ∩ bd S := ⟨hxH, hxbd⟩
      rw [mem_singleton_iff.mp (hH_bd e false this)]
      exact hw_W (r_of (e, false))
  have hK_U : ∀ e : G.E, (H e true ∪ H e false) ∩ G.U = {m_of e} := by
    intro e
    rw [union_inter_distrib_right, hH_U e true, hH_U e false, union_self]
  have hedge_inter_U : ∀ e : G.E, (edgeEquiv e).1 ∩ G.U = {m_of e} := by
    intro e
    rw [hedge_eq e]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨hxK, _⟩, hxU⟩
      have : x ∈ (H e true ∪ H e false) ∩ G.U := ⟨hxK, hxU⟩
      rwa [hK_U e, mem_singleton_iff] at this
    · rintro rfl
      exact ⟨⟨Or.inl (IsLineWithEnds.left_mem (hH_line e true)), hm_not_W e⟩, hm_mem_U e⟩
  have hedge_inter_e : ∀ e : G.E, (edgeEquiv e).1 ∩ e.1 = {m_of e} := by
    intro e
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxe', hxe⟩
      have : x ∈ (edgeEquiv e).1 ∩ G.U := ⟨hxe', (e.2.2.1 hxe).1⟩
      rwa [hedge_inter_U e, mem_singleton_iff] at this
    · rintro rfl
      have : m_of e ∈ (edgeEquiv e).1 ∩ G.U := by rw [hedge_inter_U e]; rfl
      exact ⟨this.1, hm_mem_e e⟩
  have he_inter_GdU : ∀ e : G.E, e.1 ∩ G_dual.U = {m_of e} := by
    intro e
    ext x
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxe, hxU⟩
      have hxGU : x ∈ G.U := (e.2.2.1 hxe).1
      rw [hGd_U] at hxU
      rcases hxU with hxW | ⟨_, ⟨e', rfl⟩, hxK⟩
      · exact False.elim (disjoint_left.mp hW_disj_U hxW hxGU)
      · have : x ∈ (H e' true ∪ H e' false) ∩ G.U := ⟨hxK, hxGU⟩
        rw [hK_U e', mem_singleton_iff] at this
        subst this
        have he'_eq : e' = e := by
          by_contra hne
          exact disjoint_left.mp (disjoint_edges_of_ne G e'.2 e.2 (Subtype.coe_ne_coe.mpr hne))
            (hm_mem_e e') hxe
        rw [he'_eq]
    · rintro rfl
      have : m_of e ∈ (edgeEquiv e).1 ∩ e.1 := by rw [hedge_inter_e e]; rfl
      exact ⟨this.2, (edgeEquiv e).2.2.1 this.1 |>.1⟩
  have hedge_clause2 := dual_region_meets_primal_edge hS hGd_prop edgeEquiv hW_fin hm_mem_U hm_not_W
    hm_inj hedge_inter_e hφc hφi hφ0 hφ_real_sub
    hD_union_cl hD_union_disj_U hT_props hR_sub_D hH_line hK_U hGd_U
  obtain ⟨hinc_r_of, hall_inc_r⟩ :=
    incident_regions_of_edge_charts hS hProper hm_mem_e hφc hφi hφ0 hφU hstub_arc hstub_0 hr_of
  have hedge_link_iff :=
    dual_edge_link_iff_of_incident_regions edgeEquiv hGd_V hw_in hw_of_uniq hinc_r_of hall_inc_r
      hedge_link
  have hedge_4 : ∀ e : G.E,
      ((edgeEquiv e).1 ∩ G.U = (edgeEquiv e).1 ∩ e.1) ∧
      (e.1 ∩ G_dual.U = e.1 ∩ (edgeEquiv e).1) ∧
      ((edgeEquiv e).1 ∩ e.1).ncard = 1 ∧
      (∀ r' ∈ G_dual.R, G_dual.EdgeRegionIncident (edgeEquiv e).1 r' → (r' ∩ e.1).Nonempty) := by
    intro e
    refine ⟨?_, ?_, ?_, hedge_clause2 e⟩
    · rw [hedge_inter_U e, hedge_inter_e e]
    · rw [he_inter_GdU e, inter_comm e.1, hedge_inter_e e]
    · rw [hedge_inter_e e, ncard_singleton]
  have hDual_V_uniq : ∀ r ∈ G.R, ∃! w, w ∈ r ∧ w ∈ G_dual.V := by
    rwa [hGd_V]
  have hDual_V_in_R : ∀ w ∈ G_dual.V, ∃ r ∈ G.R, w ∈ r := by
    rwa [hGd_V]
  have hDual_bd : IsDualPointSet (bd S) (G.V ∩ bd S) (G_dual.V ∩ bd S) := by
    rwa [hGd_V]
  have hV_inj : ∀ v₁ ∈ G.V, ∀ v₂ ∈ G.V,
      connectedComponentIn (univ \ G_dual.U) v₁ = connectedComponentIn (univ \ G_dual.U) v₂ →
        v₁ = v₂ :=
    dual_region_injective_on_V hS hProper hConn hGd_prop hDual_V_uniq hDual_V_in_R
      hDual_bd edgeEquiv hedge_4
  refine ⟨G_dual, hProper, hGd_prop, hDual_V_uniq, hDual_V_in_R, hDual_bd, hV_inj,
    ⟨edgeEquiv, fun e => ?_⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := hedge_4 e
  exact ⟨h1, h2, h3, h4, hedge_link_iff e⟩

/-- **Graph Minors VI, (3.6)** (pages 121–122):
Let $\Gamma$ be a drawing in a closed disc $\Delta$, let $U$ be a dual point set for
$(\operatorname{bd}(\Delta), V(\Gamma) \cap \operatorname{bd}(\Delta))$, and let $\mathcal{D}$ be a
division of $V(\Gamma) \cap \operatorname{bd}(\Delta)$. Then $\mathcal{D}$ is feasible if and only
if $\mathcal{D}$ is cross-free and every $xy$-chain has non-negative redundancy, for all
$x, y \in U \cup (V(\Gamma) \cap \operatorname{bd}(\Delta))$. -/
theorem theorem_3_6_proof : Statement36 := by
  intro S _ G Δ U hS hProper hΔ hΔ_eq hU
  exact isFeasible_iff_of_exists_isDiscDualDrawing hS
    (fun _ hP' hC' => exists_isDiscDualDrawing hS hP' hC')
    G Δ hProper hΔ hΔ_eq hU

end GraphMinor.GM06
