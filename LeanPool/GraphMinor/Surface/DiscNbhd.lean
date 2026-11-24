/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscFan

/-!
# A point with a closed disc as a neighbourhood

A point with a closed disc as a neighbourhood is a manifold point (`isManifoldPoint_of_disc`). The
chart is the
Möbius map of the closed disc without a point onto the closed right half plane. Such a point is on
the boundary of the
space if it is on the boundary of the disc (`mem_bd_of_disc`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A chart to the half plane given as a pair of functions gives a manifold point. -/
theorem isManifoldPoint_of_chart {U : Set X} {O : Set ℂ} {j : X → ℂ} {k : ℂ → X} (hU : IsOpen U)
  (hO : IsOpen O)
    (hj : ContinuousOn j U) (hk : ContinuousOn k (O ∩ halfPlane)) (hm : MapsTo j U (O ∩ halfPlane))
    (hk' : MapsTo k (O ∩ halfPlane) U) (hl : LeftInvOn k j U) (hr : LeftInvOn j k
      (O ∩ halfPlane)) {y : X}
    (hy : y ∈ U) : IsManifoldPoint y := by
  let P : ℂ → EuclideanHalfSpace 2 := fun z => if h : 0 ≤ z.re then ⟨complexPlane z, by
    rw [complexPlane_zero]; exact h⟩ else 0
  have hP : ∀ z (hz : 0 ≤ z.re), (P z).1 = complexPlane z := fun z hz => by simp [P, hz]
  let V : Set (EuclideanHalfSpace 2) := (fun p => complexPlane.symm p.1) ⁻¹' O
  have hcs : Continuous fun p : EuclideanHalfSpace 2 => complexPlane.symm p.1 :=
    complexPlane.symm.continuous.comp continuous_subtype_val
  have hV : IsOpen V := hO.preimage hcs
  have hsz : ∀ p : EuclideanHalfSpace 2, complexPlane.symm p.1 ∈ halfPlane := fun p => by
    change 0 ≤ (complexPlane.symm p.1).re
    rw [← complexPlane_zero, complexPlane.apply_symm_apply]
    exact p.2
  have hPs : ∀ z (hz : z ∈ halfPlane), complexPlane.symm (P z).1 = z := fun z hz => by
    rw [hP z hz, complexPlane.symm_apply_apply]
  have hPV : ∀ x : U, P (j x.1) ∈ V := fun x => by
    change complexPlane.symm (P (j x.1)).1 ∈ O
    rw [hPs _ (hm x.2).2]
    exact (hm x.2).1
  have hcP : Continuous fun x : U => (P (j x.1)).1 := by
    have h1 : Continuous fun x : U => j x.1 := continuousOn_iff_continuous_domRestrict.mp hj
    refine (complexPlane.continuous.comp h1).congr fun x => ?_
    exact (hP _ (hm x.2).2).symm
  refine ⟨U, V, hU, hV, hy, ⟨?_⟩⟩
  refine { toFun := fun x => ⟨P (j x.1), hPV x⟩, invFun := fun p => ⟨k (complexPlane.symm p.1.1),
    ?_⟩,
           left_inv := fun x => ?_, right_inv := fun p => ?_, continuous_toFun
             := ?_, continuous_invFun := ?_ }
  · exact hk' ⟨p.2, hsz p.1⟩
  · apply Subtype.ext
    change k (complexPlane.symm (P (j x.1)).1) = x.1
    rw [hPs _ (hm x.2).2]
    exact hl x.2
  · apply Subtype.ext
    apply Subtype.ext
    change (P (j (k (complexPlane.symm p.1.1)))).1 = p.1.1
    rw [hr ⟨p.2, hsz p.1⟩, hP _ (hsz p.1), complexPlane.apply_symm_apply]
  · exact Continuous.subtype_mk (Continuous.subtype_mk hcP _) _
  · refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun p : V => complexPlane.symm p.1.1 := hcs.comp continuous_subtype_val
    exact hk.comp_continuous h1 fun p => ⟨p.2, hsz p.1⟩

/-- The Möbius map of the closed disc without `u` onto the right half plane. -/
noncomputable def mobC (u z : ℂ) : ℂ := (u + z) / (u - z)

/-- The inverse of `mobC`. -/
noncomputable def mobD (u w : ℂ) : ℂ := u * (w - 1) / (w + 1)

theorem mobC_re {u z : ℂ} (hu : ‖u‖ = 1) (hz : ‖z‖ ≤ 1) : 0 ≤ (mobC u z).re := by
  rw [mobC, Complex.div_re]
  have h1 : u.re * u.re + u.im * u.im = 1 := by
    have := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at this
    linarith
  have h2 : z.re * z.re + z.im * z.im ≤ 1 := by
    have := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at this
    have h3 : ‖z‖ ^ 2 ≤ 1 := by
      have := norm_nonneg z
      nlinarith
    linarith
  have h3 : 0 ≤ Complex.normSq (u - z) := Complex.normSq_nonneg _
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im]
  rw [← add_div]
  refine div_nonneg ?_ h3
  nlinarith

theorem add_one_ne {w : ℂ} (hw : 0 ≤ w.re) : w + 1 ≠ 0 := fun h => by
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
  linarith

theorem norm_mobD {u w : ℂ} (hu : ‖u‖ = 1) (hw : 0 ≤ w.re) : ‖mobD u w‖ ≤ 1 := by
  rw [mobD, norm_div, norm_mul, hu, one_mul, div_le_one (norm_pos_iff.mpr (add_one_ne hw))]
  have h1 : ‖w - 1‖ ^ 2 ≤ ‖w + 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

theorem mobD_ne {u w : ℂ} (hu : ‖u‖ = 1) (hw : 0 ≤ w.re) : mobD u w ≠ u := fun h => by
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have h1 := add_one_ne hw
  rw [mobD, div_eq_iff h1] at h
  have h2 : u * (w - 1) = u * (w + 1) := h
  have h3 := mul_left_cancel₀ hu0 h2
  have h4 : (2 : ℂ) = 0 := by linear_combination -h3
  norm_num at h4

theorem mobC_mobD {u w : ℂ} (hu : ‖u‖ = 1) (hw : 0 ≤ w.re) : mobC u (mobD u w) = w := by
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have h1 := add_one_ne hw
  rw [mobC, mobD]
  have h2 : u - u * (w - 1) / (w + 1) ≠ 0 := sub_ne_zero.mpr (mobD_ne hu hw).symm
  rw [div_eq_iff h2]
  field_simp
  ring

theorem mobD_mobC {u z : ℂ} (hu : ‖u‖ = 1) (hz : ‖z‖ ≤ 1) (hne : z ≠ u) : mobD u (mobC u z) = z
  := by
  have h0 : u - z ≠ 0 := sub_ne_zero.mpr hne.symm
  have hre := mobC_re hu hz
  have h1 := add_one_ne hre
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  rw [mobD, div_eq_iff h1, mobC]
  field_simp
  ring

theorem isManifoldPoint_of_disc [T2Space X] {E : Set X} (hE : IsClosedDisc E) {y : X}
  (hy : E ∈ 𝓝 y) :
    IsManifoldPoint y := by
  classical
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  have hyE : y ∈ E := mem_of_mem_nhds hy
  obtain ⟨u, hu, hne⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ h y ≠ u := by
    by_cases h1 : h y = 1
    · exact ⟨-1, by simp, by rw [h1]; norm_num⟩
    · exact ⟨1, by simp, h1⟩
  have hu1 : u ∈ closedBall (0 : ℂ) 1 := by simpa using hu.le
  let U : Set X := interior E \ {g u}
  have hU : IsOpen U := isOpen_interior.sdiff isClosed_singleton
  have hUE : U ⊆ E := sdiff_subset.trans interior_subset
  have hyU : y ∈ U := by
    refine ⟨mem_interior_iff_mem_nhds.mpr hy, fun he => hne ?_⟩
    have he' : y = g u := he
    rw [he', c.hg hu1]
  have hhn : ∀ x ∈ U, h x ≠ u := fun x hx he => hx.2 (by
    change x = g u
    rw [← he, c.gh (hUE hx)])
  have hhm : ∀ x ∈ U, ‖h x‖ ≤ 1 := fun x hx => by simpa using c.hm (hUE hx)
  let k : ℂ → X := fun w => g (mobD u w)
  have hmd : MapsTo (mobD u) halfPlane (closedBall 0 1) := fun w hw => by
    simpa using norm_mobD hu hw
  have hmdc : ContinuousOn (mobD u) halfPlane := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun w hw => add_one_ne hw
  have hkc : ContinuousOn k halfPlane := c.gc.comp hmdc hmd
  obtain ⟨O, hO, e⟩ := (continuousOn_iff'.mp hkc) U hU
  have hkj : ∀ x ∈ U, k (mobC u (h x)) = x := fun x hx => by
    change g (mobD u (mobC u (h x))) = x
    rw [mobD_mobC hu (hhm x hx) (hhn x hx)]
    exact c.gh (hUE hx)
  have hjk : ∀ w ∈ halfPlane, mobC u (h (k w)) = w := fun w hw => by
    change mobC u (h (g (mobD u w))) = w
    rw [c.hg (hmd hw)]
    exact mobC_mobD hu hw
  refine isManifoldPoint_of_chart (j := fun x => mobC u (h x)) hU hO ?_
    (hkc.mono inter_subset_right) ?_ ?_ hkj
    (fun w hw => hjk w hw.2) hyU
  · refine ContinuousOn.div (by
      exact continuousOn_const.add (c.hc.mono hUE)) (continuousOn_const.sub
        (c.hc.mono hUE)) fun x hx => ?_
    exact sub_ne_zero.mpr (hhn x hx).symm
  · intro x hx
    have hre : mobC u (h x) ∈ halfPlane := mobC_re hu (hhm x hx)
    have h1 : mobC u (h x) ∈ k ⁻¹' U ∩ halfPlane := ⟨by
      change k _ ∈ U
      rw [hkj x hx]
      exact hx, hre⟩
    rw [e] at h1
    exact ⟨h1.1, hre⟩
  · intro w hw
    have h1 : w ∈ k ⁻¹' U ∩ halfPlane := by
      rw [e]
      exact hw
    exact h1.1

/-- A point on the boundary of a closed disc that is a neighbourhood is on the boundary of the
space. -/
theorem mem_bd_of_disc {E : Set X} {y : X} (hy : E ∈ 𝓝 y)
  (hb : y ∈ discBd E) : y ∈ bd X := by
  rintro ⟨U, hU, hyU, ⟨f⟩⟩
  have hV : IsOpen (U ∩ interior E) := hU.inter isOpen_interior
  have h1 := subset_discInt_of_isOpen (Δ := E) (V := U ∩ interior E)
    (fun x hx => ⟨U, hU, hx.1, ⟨f⟩⟩) hV (inter_subset_right.trans interior_subset)
  exact (h1 ⟨hyU, mem_interior_iff_mem_nhds.mpr hy⟩).2 hb

end GraphMinor.Surface
