/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.OneManifold
public import LeanPool.GraphMinor.Surface.SphereDisc

/-!
# The boundary of a surface

`cuff_statement : CuffStatement`: the boundary of a surface is closed, and it has finitely many
components, each of them an `O`-arc.

By invariance of domain, the points of a half plane chart that lie on the boundary line are exactly
the points of the chart in `bd S` (`mem_bd_iff_of_chart`). So `bd S` is locally an interval. Each
component is then a compact connected curve, which is a circle by `exists_homeomorph_circle`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u v

variable {S : Type u} [TopologicalSpace S]

/-- A homeomorphism of subsets is given by a pair of functions. -/
theorem exists_functions_of_homeomorph {T : Type v} [TopologicalSpace T] [Nonempty S] [Nonempty T]
    {A : Set S} {B : Set T} (e : A ≃ₜ B) :
    ∃ (h : S → T) (k : T → S), ContinuousOn h A ∧ ContinuousOn k B ∧ MapsTo h A B ∧ MapsTo k B A ∧
      LeftInvOn k h A ∧ LeftInvOn h k B := by
  classical
  obtain ⟨s₀⟩ := ‹Nonempty S›
  obtain ⟨t₀⟩ := ‹Nonempty T›
  let h : S → T := fun z => if hz : z ∈ A then (e ⟨z, hz⟩).1 else t₀
  let k : T → S := fun z => if hz : z ∈ B then (e.symm ⟨z, hz⟩).1 else s₀
  have hv : ∀ x : A, h x.1 = (e x).1 := fun x => by simp [h]
  have kv : ∀ x : B, k x.1 = (e.symm x).1 := fun x => by simp [k]
  refine ⟨h, k, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : A.domRestrict h = fun x => (e x).1 := funext hv
    rw [this]
    exact continuous_subtype_val.comp e.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have : B.domRestrict k = fun x => (e.symm x).1 := funext kv
    rw [this]
    exact continuous_subtype_val.comp e.symm.continuous
  · intro z hz
    rw [hv ⟨z, hz⟩]
    exact (e _).2
  · intro z hz
    rw [kv ⟨z, hz⟩]
    exact (e.symm _).2
  · intro z hz
    show k (h z) = z
    rw [hv ⟨z, hz⟩, kv]
    simp
  · intro z hz
    show h (k z) = z
    rw [kv ⟨z, hz⟩, hv]
    simp

/-- The right half plane of `ℂ`. -/
def halfPlane : Set ℂ := {z | 0 ≤ z.re}

theorem complexPlane_zero (z : ℂ) : (complexPlane z) 0 = z.re := by
  simp [complexPlane]

/-- Half plane charts, in terms of functions to `ℂ`. -/
theorem IsManifoldPoint.exists_chart {x : S} (hx : IsManifoldPoint x) :
    ∃ (U : Set S) (O : Set ℂ) (j : S → ℂ) (k : ℂ → S), IsOpen U ∧ IsOpen O ∧ x ∈ U ∧
      ContinuousOn j U ∧ ContinuousOn k (O ∩ halfPlane) ∧ MapsTo j U (O ∩ halfPlane) ∧
      MapsTo k (O ∩ halfPlane) U ∧ LeftInvOn k j U ∧ LeftInvOn j k (O ∩ halfPlane) := by
  obtain ⟨U, V, hU, hV, hxU, ⟨e⟩⟩ := hx
  have : Nonempty S := ⟨x⟩
  obtain ⟨V', hV', hVV⟩ := isOpen_induced_iff.mp hV
  let O : Set ℂ := complexPlane ⁻¹' V'
  have hO : IsOpen O := hV'.preimage complexPlane.continuous
  let f : V → ℂ := fun v => complexPlane.symm v.1.1
  have hf : IsEmbedding f :=
    (complexPlane.symm.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal).comp
      IsEmbedding.subtypeVal
  have hr : range f = O ∩ halfPlane := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨?_, ?_⟩
      · change complexPlane (complexPlane.symm v.1.1) ∈ V'
        rw [complexPlane.apply_symm_apply]
        have : v.1 ∈ Subtype.val ⁻¹' V' := hVV ▸ v.2
        exact this
      · have h1 := v.1.2
        change 0 ≤ (complexPlane.symm v.1.1).re
        rw [← complexPlane_zero, complexPlane.apply_symm_apply]
        exact h1
    · rintro ⟨h1, h2⟩
      have hz : 0 ≤ (complexPlane z) 0 := by
        rw [complexPlane_zero]
        exact h2
      have hmem : (⟨complexPlane z, hz⟩ : EuclideanHalfSpace 2) ∈ V := by
        rw [← hVV]
        exact h1
      exact ⟨⟨_, hmem⟩, complexPlane.symm_apply_apply z⟩
  let E : U ≃ₜ (O ∩ halfPlane : Set ℂ) :=
    e.trans (hf.toHomeomorph.trans (Homeomorph.setCongr hr))
  obtain ⟨j, k, h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph E
  exact ⟨U, O, j, k, hU, hO, hxU, h1, h2, h3, h4, h5, h6⟩

/-- A ball of `ℂ` has the open unit disc as a model. -/
theorem exists_homeomorph_ball (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Nonempty (ball c ρ ≃ₜ OpenUnitDisc) := by
  let f : ℂ → EuclideanPlane := fun z => complexPlane (((ρ : ℂ)⁻¹) * (z - c))
  let f' : EuclideanPlane → ℂ := fun w => c + (ρ : ℂ) * complexPlane.symm w
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hfc : Continuous f := complexPlane.continuous.comp (by fun_prop)
  have hf'c : Continuous f' := by
    refine continuous_const.add (continuous_const.mul ?_)
    exact complexPlane.symm.continuous
  have hl : LeftInvOn f' f (ball c ρ) := fun z _ => by
    simp only [f, f', complexPlane.symm_apply_apply]
    field_simp
    ring
  have hnorm : ∀ z, ‖f z‖ = ‖z - c‖ / ρ := fun z => by
    simp only [f]
    rw [LinearIsometryEquiv.norm_map, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ]
    field_simp
  have himg : f '' ball c ρ = OpenUnitDisc := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [OpenUnitDisc, mem_ball_zero_iff, hnorm, div_lt_one hρ]
      rwa [mem_ball, dist_eq_norm] at hz
    · intro hw
      have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
      have hfw : f (f' w) = w := by
        simp only [f, f']
        rw [add_sub_cancel_left, inv_mul_cancel_left₀ hρ', complexPlane.apply_symm_apply]
      refine ⟨f' w, ?_, hfw⟩
      rw [mem_ball, dist_eq_norm]
      have h1 := hnorm (f' w)
      rw [hfw] at h1
      have h2 : ‖f' w - c‖ = ‖w‖ * ρ := by
        rw [h1]
        field_simp
      rw [h2]
      nlinarith
  obtain ⟨e, -⟩ := exists_homeomorph_image hfc.continuousOn hf'c.continuousOn hl
  exact ⟨e.trans (Homeomorph.setCongr himg)⟩

/-- In a half plane chart, a point off the boundary line is an interior point. -/
theorem isInteriorPoint_of_chart {U : Set S} {O : Set ℂ} {j : S → ℂ} {k : ℂ → S} (hU : IsOpen U)
    (hO : IsOpen O) (hj : ContinuousOn j U) (hk : ContinuousOn k (O ∩ halfPlane))
    (hm : MapsTo j U (O ∩ halfPlane)) (hk' : MapsTo k (O ∩ halfPlane) U) (hl : LeftInvOn k j U)
    (hr : LeftInvOn j k (O ∩ halfPlane)) {y : S} (hy : y ∈ U) (hre : 0 < (j y).re) :
    IsInteriorPoint y := by
  have hopen : IsOpen (O ∩ {z : ℂ | 0 < z.re}) :=
    hO.inter (isOpen_lt continuous_const Complex.continuous_re)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (j y) ⟨(hm hy).1, hre⟩
  have hsub : ball (j y) ρ ⊆ O ∩ halfPlane := fun z hz =>
    ⟨(hball hz).1, (show 0 < z.re from (hball hz).2).le⟩
  have hW : IsOpen (U ∩ j ⁻¹' ball (j y) ρ) := hj.isOpen_inter_preimage hU isOpen_ball
  have hkm : k '' ball (j y) ρ = U ∩ j ⁻¹' ball (j y) ρ := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hk' (hsub hz), ?_⟩
      change j (k z) ∈ ball (j y) ρ
      rwa [hr (hsub hz)]
    · rintro ⟨h1, h2⟩
      exact ⟨j p, h2, hl h1⟩
  obtain ⟨E, -⟩ := exists_homeomorph_image (hk.mono hsub)
    (hj.mono (by rw [hkm]; exact inter_subset_left)) (hr.mono hsub)
  obtain ⟨b⟩ := exists_homeomorph_ball (j y) hρ
  refine ⟨_, hW, ⟨hy, mem_ball_self hρ⟩, ⟨?_⟩⟩
  exact (Homeomorph.setCongr hkm.symm).trans (E.symm.trans b)

/-- In a half plane chart, a point on the boundary line is not an interior point, by invariance of
domain. -/
theorem not_isInteriorPoint_of_chart {U : Set S} {O : Set ℂ} {j : S → ℂ} (hU : IsOpen U)
    (hj : ContinuousOn j U) (hm : MapsTo j U (O ∩ halfPlane)) (hinj : InjOn j U) {y : S}
    (hy : y ∈ U) (hre : (j y).re = 0) : ¬ IsInteriorPoint y := by
  rintro ⟨W, hW, hyW, ⟨f⟩⟩
  have : Nonempty S := ⟨y⟩
  obtain ⟨b⟩ := exists_homeomorph_ball (0 : ℂ) one_pos
  obtain ⟨a, a', h1, h2, h3, h4, h5, h6⟩ := exists_functions_of_homeomorph (b.trans f.symm)
  have hD : IsOpen (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := h1.isOpen_inter_preimage isOpen_ball hU
  have hG : ContinuousOn (j ∘ a) (ball (0 : ℂ) 1 ∩ a ⁻¹' U) :=
    hj.comp (h1.mono inter_subset_left) fun z hz => hz.2
  have hGi : InjOn (j ∘ a) (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := fun z hz w hw he =>
    h5.injOn hz.1 hw.1 (hinj hz.2 hw.2 he)
  have hopen := isOpen_image_of_injOn hD hG hGi
  have hmem : j y ∈ (j ∘ a) '' (ball (0 : ℂ) 1 ∩ a ⁻¹' U) := by
    refine ⟨a' y, ⟨h4 hyW, ?_⟩, ?_⟩
    · change a (a' y) ∈ U
      rwa [h6 hyW]
    · change j (a (a' y)) = j y
      rw [h6 hyW]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
  have hz : j y - ((ε / 2 : ℝ) : ℂ) ∈ ball (j y) ε := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  obtain ⟨v, hv, he⟩ := hball hz
  have hH : 0 ≤ ((j ∘ a) v).re := (hm hv.2).2
  rw [he, Complex.sub_re, hre, Complex.ofReal_re] at hH
  linarith

theorem isClosed_bd (S : Type u) [TopologicalSpace S] : IsClosed (bd S) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  have hx' : IsInteriorPoint x := not_not.mp hx
  obtain ⟨U, hU, hxU, ⟨f⟩⟩ := hx'
  exact ⟨U, fun y hy hn => hn ⟨U, hU, hy, ⟨f⟩⟩, hU, hxU⟩

/-- A boundary point of a surface has an interval around it in the boundary. -/
theorem exists_boundary_chart {x : S} (hx : IsManifoldPoint x) (hb : x ∈ bd S) :
    ∃ (ψ : ℝ → S) (W : Set S), ContinuousOn ψ (Icc (-1) 1) ∧ InjOn ψ (Icc (-1) 1) ∧ IsOpen W ∧
      x ∈ W ∧ ψ '' Ioo (-1) 1 = W ∩ bd S ∧ ψ '' Icc (-1) 1 ⊆ bd S := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hk', hl, hr⟩ := hx.exists_chart
  have hre : (j x).re = 0 := by
    refine le_antisymm (not_lt.mp fun h => hb ?_) (hm hxU).2
    exact isInteriorPoint_of_chart hU hO hj hk hm hk' hl hr hxU h
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hO _ (hm hxU).1
  let c : ℝ → ℂ := fun s => j x + (((ρ / 2) * s : ℝ) : ℂ) * Complex.I
  have hcn : ∀ s : ℝ, ‖c s - j x‖ = ρ / 2 * |s| := fun s => by
    simp only [c, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hρ)]
  have hcre : ∀ s : ℝ, (c s).re = 0 := fun s => by
    simp [c, hre]
  have hcO : ∀ s ∈ Icc (-1 : ℝ) 1, c s ∈ O ∩ halfPlane := fun s hs => by
    refine ⟨hball ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hcn]
      have h1 : |s| ≤ 1 := abs_le.mpr hs
      nlinarith
    · change 0 ≤ (c s).re
      rw [hcre]
  have hcc : Continuous c := by fun_prop
  have hci : Function.Injective c := fun s s' he => by
    have h1 : ((ρ / 2) * s : ℝ) = (ρ / 2) * s' := by
      have h2 : (((ρ / 2) * s : ℝ) : ℂ) * Complex.I = (((ρ / 2) * s' : ℝ) : ℂ) * Complex.I :=
        add_left_cancel he
      exact Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h2)
    exact mul_left_cancel₀ (half_pos hρ).ne' h1
  have hbd : ∀ s ∈ Icc (-1 : ℝ) 1, k (c s) ∈ bd S := by
    intro s hs
    refine not_isInteriorPoint_of_chart hU hj hm hl.injOn (hk' (hcO s hs)) ?_
    rw [hr (hcO s hs), hcre]
  refine ⟨k ∘ c, U ∩ j ⁻¹' ball (j x) (ρ / 2), hk.comp hcc.continuousOn hcO, ?_,
    hj.isOpen_inter_preimage hU isOpen_ball, ⟨hxU, mem_ball_self (half_pos hρ)⟩, ?_, ?_⟩
  · intro s hs s' hs' he
    exact hci ((show LeftInvOn j k (O ∩ halfPlane) from hr).injOn (hcO s hs) (hcO s' hs') he)
  · ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' := Ioo_subset_Icc_self hs
      refine ⟨⟨hk' (hcO s hs'), ?_⟩, hbd s hs'⟩
      change j (k (c s)) ∈ ball (j x) (ρ / 2)
      rw [hr (hcO s hs'), mem_ball, dist_eq_norm, hcn]
      have h1 : |s| < 1 := abs_lt.mpr hs
      nlinarith [half_pos hρ]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hyre : (j y).re = 0 := by
        refine le_antisymm (not_lt.mp fun h => h3 ?_) (hm h1).2
        exact isInteriorPoint_of_chart hU hO hj hk hm hk' hl hr h1 h
      have hd : ‖j y - j x‖ < ρ / 2 := by
        have : j y ∈ ball (j x) (ρ / 2) := h2
        rwa [mem_ball, dist_eq_norm] at this
      let s : ℝ := (j y - j x).im / (ρ / 2)
      have hρ2 := half_pos hρ
      have hcs : c s = j y := by
        refine Complex.ext ?_ ?_
        · rw [hcre, hyre]
        · simp only [c, s, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
            Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, Complex.sub_im]
          field_simp
          ring
      have hsa : |s| < 1 := by
        have h4 := hcn s
        rw [hcs] at h4
        rw [h4] at hd
        nlinarith
      refine ⟨s, abs_lt.mp hsa, ?_⟩
      change k (c s) = y
      rw [hcs]
      exact hl h1
  · rintro _ ⟨s, hs, rfl⟩
    exact hbd s hs

/-- **Cuffs.** The boundary of a surface is closed, with finitely many components, each an `O`-arc.
-/
theorem cuff_statement : CuffStatement.{u} := by
  classical
  intro S _ hS
  obtain ⟨hcpt, ht2, hman⟩ := hS
  have hcl := isClosed_bd S
  refine ⟨hcl, ?_, ?_⟩
  · have hchart : ∀ x : bd S, ∃ W : Set S, IsOpen W ∧ x.1 ∈ W ∧
        W ∩ bd S ⊆ connectedComponentIn (bd S) x.1 := by
      rintro ⟨x, hx⟩
      obtain ⟨ψ, W, hc, -, hW, hxW, he, hsub⟩ := exists_boundary_chart (hman x) hx
      refine ⟨W, hW, hxW, ?_⟩
      rw [← he]
      have hmem : x ∈ ψ '' Ioo (-1) 1 := he ▸ ⟨hxW, hx⟩
      exact ((isPreconnected_Ioo).image ψ (hc.mono Ioo_subset_Icc_self)).subset_connectedComponentIn
        hmem ((image_mono Ioo_subset_Icc_self).trans hsub)
    choose W hWo hxW hWsub using hchart
    obtain ⟨t, ht⟩ := hcl.isCompact.elim_finite_subcover (fun x => W x) (fun x => hWo x)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxW _⟩)
    refine (t.finite_toSet.image fun x => connectedComponentIn (bd S) x.1).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hxt, hyW⟩ := mem_iUnion₂.mp (ht hy)
    exact ⟨x, hxt, connectedComponentIn_eq (hWsub x ⟨hyW, hy⟩)⟩
  · rintro _ ⟨x, hx, rfl⟩
    set C := connectedComponentIn (bd S) x with hC
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hCsub : C ⊆ bd S := connectedComponentIn_subset _ _
    have hCcl : IsClosed C := by
      refine isClosed_of_closure_subset ?_
      exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure hxC) (closure_minimal hCsub hcl)
    have : CompactSpace C := isCompact_iff_compactSpace.mp hCcl.isCompact
    have : ConnectedSpace C := isConnected_iff_connectedSpace.mp ⟨⟨x, hxC⟩,
      isPreconnected_connectedComponentIn⟩
    refine exists_homeomorph_circle fun y => ?_
    obtain ⟨ψ, W, hc, hi, hW, hyW, he, hsub⟩ := exists_boundary_chart (hman y.1) (hCsub y.2)
    have hIcc : ψ '' Icc (-1) 1 ⊆ C := by
      obtain ⟨s, hs, hse⟩ : y.1 ∈ ψ '' Ioo (-1) 1 := he ▸ ⟨hyW, hCsub y.2⟩
      have h1 : IsPreconnected (ψ '' Icc (-1) 1) := isPreconnected_Icc.image ψ hc
      have h2 := h1.subset_connectedComponentIn ⟨s, Ioo_subset_Icc_self hs, hse⟩ hsub
      have h3 : connectedComponentIn (bd S) y.1 = C := (connectedComponentIn_eq y.2).symm
      rwa [h3] at h2
    have hm1 : (-1 : ℝ) ≤ 1 := by norm_num
    let cl : ℝ → ℝ := fun s => (projIcc (-1) 1 hm1 s).1
    have hcl1 : ∀ s, cl s ∈ Icc (-1 : ℝ) 1 := fun s => (projIcc (-1) 1 hm1 s).2
    have hcl2 : ∀ s ∈ Icc (-1 : ℝ) 1, cl s = s := fun s hs => by
      change (projIcc (-1) 1 hm1 s).1 = s
      rw [projIcc_of_mem hm1 hs]
    have hclc : Continuous cl := continuous_subtype_val.comp continuous_projIcc
    let χ : ℝ → C := fun s => ⟨ψ (cl s), hIcc (mem_image_of_mem ψ (hcl1 s))⟩
    refine ⟨χ, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (Continuous.subtype_mk (hc.comp_continuous hclc hcl1) _).continuousOn
    · intro s hs s' hs' he
      have h1 : ψ (cl s) = ψ (cl s') := congrArg Subtype.val he
      rw [hcl2 s hs, hcl2 s' hs'] at h1
      exact hi hs hs' h1
    · have heq : χ '' Ioo (-1) 1 = Subtype.val ⁻¹' W := by
        ext p
        constructor
        · rintro ⟨s, hs, rfl⟩
          have h1 : ψ s ∈ ψ '' Ioo (-1) 1 := mem_image_of_mem ψ hs
          rw [he] at h1
          change ψ (cl s) ∈ W
          rw [hcl2 s (Ioo_subset_Icc_self hs)]
          exact h1.1
        · intro hp
          have h1 : p.1 ∈ ψ '' Ioo (-1) 1 := by
            rw [he]
            exact ⟨hp, hCsub p.2⟩
          obtain ⟨s, hs, hse⟩ := h1
          refine ⟨s, hs, Subtype.ext ?_⟩
          change ψ (cl s) = p.1
          rw [hcl2 s (Ioo_subset_Icc_self hs), hse]
      rw [heq]
      exact hW.preimage continuous_subtype_val
    · have h1 : y.1 ∈ ψ '' Ioo (-1) 1 := by
        rw [he]
        exact ⟨hyW, hCsub y.2⟩
      obtain ⟨s, hs, hse⟩ := h1
      refine ⟨s, hs, Subtype.ext ?_⟩
      change ψ (cl s) = y.1
      rw [hcl2 s (Ioo_subset_Icc_self hs), hse]

end GraphMinor.Surface
