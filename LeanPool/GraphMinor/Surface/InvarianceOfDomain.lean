/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Jordan
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Invariance of domain in the plane and the boundary of a closed disc

This file proves two things.

* `isOpen_image_of_injOn`: an injective continuous map from an open subset of the plane to the
  plane has open image. The route is the classical one from the Jordan curve theorem. Take a
  closed round disc `B` in the domain, and let `J` be the image of its boundary. An embedded closed
  disc does not separate the plane (`preconnected_compl_image_closedBall`), since every function
  without zeros on it has a logarithm. So the complement of `g(B)` lies in the unbounded component
  of the complement of `J`, and the image of the open disc must be the whole bounded component.
* `disc_boundary : DiscBoundaryStatement`: the manifold boundary of a closed disc is the image of
  the unit circle.

The file also shows that `bd` is invariant under homeomorphisms (`Homeomorph.image_bd`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

local notation "𝕀" => unitInterval

universe u v

/-- A continuous function without zeros on a closed disc has a logarithm: contract to the centre. -/
theorem hasLogOn_closedBall {c : ℂ} {r : ℝ} (hr : 0 ≤ r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall c r)) (hne : ∀ z ∈ closedBall c r, f z ≠ 0) :
    HasLogOn (closedBall c r) f := by
  have hc : c ∈ closedBall c r := mem_closedBall_self hr
  have hmem : ∀ (t : 𝕀), ∀ z ∈ closedBall c r, c + (t : ℝ) • (z - c) ∈ closedBall c r := by
    intro t z hz
    have := (convex_closedBall c r).add_smul_sub_mem hc hz t.2
    exact this
  have h := hasLogOn_of_homotopy (K := closedBall c r)
    (fun t z => f (c + (t : ℝ) • (z - c)) / f c) ?_ (fun z _ => by simp [hne c hc])
    (fun t z hz => div_ne_zero (hne _ (hmem t z hz)) (hne c hc))
  · refine (h.mul (hasLogOn_const (hne c hc))).congr fun z _ => ?_
    simp [hne c hc]
  · refine ContinuousOn.div_const (hf.comp (by fun_prop) ?_) _
    rintro ⟨t, z⟩ ⟨-, hz⟩
    exact hmem t z hz

/-- The image of a closed disc under an injective continuous map does not separate the plane. -/
theorem component_eq_of_image_closedBall {c : ℂ} {r : ℝ} (hr : 0 ≤ r) {g : ℂ → ℂ}
    (hg : ContinuousOn g (closedBall c r)) (hinj : InjOn g (closedBall c r)) {a b : ℂ}
    (ha : a ∉ g '' closedBall c r) (hb : b ∉ g '' closedBall c r) :
    connectedComponentIn (g '' closedBall c r)ᶜ a = connectedComponentIn (g '' closedBall c r)ᶜ b
      := by
  have hcomp : IsCompact (g '' closedBall c r) := (isCompact_closedBall c r).image_of_continuousOn
    hg
  refine component_eq_of_hasLogOn hcomp ha hb ?_
  have hsne : ∀ z ∈ closedBall c r, g z - a ≠ 0 ∧ g z - b ≠ 0 := fun z hz =>
    ⟨fun h => ha ⟨z, hz, sub_eq_zero.mp h⟩, fun h => hb ⟨z, hz, sub_eq_zero.mp h⟩⟩
  refine hasLogOn_image (isCompact_closedBall c r) hg hinj (hasLogOn_closedBall hr ?_ ?_)
  · exact (hg.sub continuousOn_const).div (hg.sub continuousOn_const) fun z hz => (hsne z hz).2
  · exact fun z hz => div_ne_zero (hsne z hz).1 (hsne z hz).2

/-- **Invariance of domain in the plane.** An injective continuous map from an open subset of the
plane to the plane has open image. -/
theorem isOpen_image_of_injOn {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : ContinuousOn g U)
    (hinj : InjOn g U) : IsOpen (g '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  have hgB : ContinuousOn g (closedBall p r) := hg.mono hball
  have hiB : InjOn g (closedBall p r) := hinj.mono hball
  have hK : IsCompact (g '' closedBall p r) := (isCompact_closedBall p r).image_of_continuousOn hgB
  -- The image `J` of the circle, as an `O`-arc.
  let c : Circle → ℂ := fun w => p + r * (w : ℂ)
  have hcm : ∀ w, c w ∈ sphere p r := fun w => by
    simp [c, abs_of_pos hr]
  have hcB : ∀ w, c w ∈ closedBall p r := fun w => sphere_subset_closedBall (hcm w)
  have hcsurj : ∀ z ∈ sphere p r, ∃ w, c w = z := by
    intro z hz
    have hz' : ‖z - p‖ = r := by simpa [dist_eq_norm] using hz
    have hne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hn : ‖(z - p) / r‖ = 1 := by
      rw [norm_div, hz', norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    refine ⟨⟨(z - p) / r, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
    change p + r * ((z - p) / r) = z
    field_simp
    ring
  have hccont : Continuous c := by fun_prop
  have hcinj : Function.Injective c := by
    intro x y hxy
    have hne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have : (x : ℂ) = y := mul_left_cancel₀ hne (add_left_cancel hxy)
    exact Circle.ext this
  let γ : Circle → ℂ := fun w => g (c w)
  have hγc : Continuous γ := hgB.comp_continuous hccont hcB
  have hγi : Function.Injective γ := fun x y hxy => hcinj (hiB (hcB x) (hcB y) hxy)
  have hemb := hγc.isClosedEmbedding hγi
  obtain ⟨A, B, ⟨hne, hcomp, hAf, hBf⟩, hAb, hBb⟩ :=
    jordan_complex (F := range γ) hemb.isEmbedding.toHomeomorph
  have hJc : IsClosed (range γ) := hemb.isClosed_range
  have hset : (univ : Set ℂ) \ range γ = (range γ)ᶜ := (compl_eq_univ_sdiff _).symm
  rw [hset] at hcomp
  have hAmem : A ∈ componentsIn (range γ)ᶜ := by rw [hcomp]; simp
  have hBmem : B ∈ componentsIn (range γ)ᶜ := by rw [hcomp]; simp
  obtain ⟨xa, hxa, rfl⟩ := hAmem
  obtain ⟨xb, hxb, rfl⟩ := hBmem
  set A := connectedComponentIn (range γ)ᶜ xa with hAdef
  set B := connectedComponentIn (range γ)ᶜ xb with hBdef
  have hdisj : Disjoint A B := Set.disjoint_left.mpr fun y h1 h2 => hne (by
    rw [hAdef, hBdef, connectedComponentIn_eq h1, connectedComponentIn_eq h2])
  have hcover : ∀ y, y ∉ range γ → y ∈ A ∨ y ∈ B := by
    intro y hy
    have h1 : connectedComponentIn (range γ)ᶜ y ∈ ({A, B} : Set (Set ℂ)) :=
      hcomp ▸ mem_image_of_mem _ hy
    rcases h1 with h1 | h1
    · exact Or.inl (h1 ▸ mem_connectedComponentIn hy)
    · exact Or.inr (h1 ▸ mem_connectedComponentIn hy)
  have hJsub : range γ ⊆ g '' closedBall p r := by
    rintro _ ⟨w, rfl⟩
    exact ⟨_, hcB w, rfl⟩
  -- The complement `W` of the image of the closed disc lies in `B`.
  set W := (g '' closedBall p r)ᶜ with hW
  have hWsub : W ⊆ (range γ)ᶜ := compl_subset_compl.mpr hJsub
  have hWpre : IsPreconnected W := by
    by_cases hemp : W.Nonempty
    · obtain ⟨y, hy⟩ := hemp
      have : W = connectedComponentIn W y := by
        refine Subset.antisymm (fun z hz => ?_) (connectedComponentIn_subset _ _)
        rw [hW, component_eq_of_image_closedBall hr.le hgB hiB hy hz]
        exact mem_connectedComponentIn hz
      rw [this]
      exact isPreconnected_connectedComponentIn
    · rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp]
      exact isPreconnected_empty
  have hWbdd : ¬ Bornology.IsBounded W := fun h => by
    have : Bornology.IsBounded (univ : Set ℂ) := by
      rw [← union_compl_self (g '' closedBall p r)]
      exact hK.isBounded.union h
    exact NormedSpace.unbounded_univ ℝ ℂ this
  have hAo : IsOpen A := isOpen_component hJc xa
  have hBo : IsOpen B := isOpen_component hJc xb
  have hWB : W ⊆ B := by
    have hsub : W ⊆ A ∪ B := fun y hy => hcover y (hWsub hy)
    by_cases hcase : (W ∩ A).Nonempty
    · have := hWpre.subset_left_of_subset_union hAo hBo hdisj hsub hcase
      exact absurd (hAb.subset this) hWbdd
    · have hWne : W.Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        exact hWbdd (hemp ▸ Bornology.isBounded_empty)
      obtain ⟨y, hy⟩ := hWne
      refine hWpre.subset_right_of_subset_union hAo hBo hdisj hsub ⟨y, hy, ?_⟩
      exact (hcover y (hWsub hy)).resolve_left fun h => hcase ⟨y, hy, h⟩
  -- The image of the open disc is `A`.
  have hball2 : ∀ z ∈ ball p r, g z ∉ range γ := by
    rintro z hz ⟨w, hw⟩
    have h1 := hiB (hcB w) (ball_subset_closedBall hz) hw
    have h2 := hcm w
    rw [h1, mem_sphere] at h2
    rw [mem_ball] at hz
    exact hz.ne h2
  have hgball : IsPreconnected (g '' ball p r) :=
    (convex_ball p r).isPreconnected.image _ (hgB.mono ball_subset_closedBall)
  have hgsub : g '' ball p r ⊆ A ∪ B := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcover _ (hball2 z hz)
  have hcl : ∀ z ∈ closedBall p r, z ∈ ball p r ∨ z ∈ sphere p r := by
    intro z hz
    rcases lt_or_eq_of_le (mem_closedBall.mp hz) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hAsub : A ⊆ g '' ball p r := by
    intro y hy
    have hyJ : y ∉ range γ := connectedComponentIn_subset _ _ hy
    have hyW : y ∉ W := fun h => Set.disjoint_left.mp hdisj hy (hWB h)
    obtain ⟨z, hz, rfl⟩ : y ∈ g '' closedBall p r := by simpa [hW] using hyW
    rcases hcl z hz with h | h
    · exact ⟨z, h, rfl⟩
    · obtain ⟨w, rfl⟩ := hcsurj z h
      exact absurd ⟨w, rfl⟩ hyJ
  have hgA : g '' ball p r ⊆ A := by
    have hnA : A.Nonempty := ⟨xa, mem_connectedComponentIn hxa⟩
    obtain ⟨y, hy⟩ := hnA
    obtain ⟨z, hz, rfl⟩ := hAsub hy
    exact hgball.subset_left_of_subset_union hAo hBo hdisj hgsub ⟨_, ⟨z, hz, rfl⟩, hy⟩
  have hAeq : A = g '' ball p r := Subset.antisymm hAsub hgA
  refine Filter.mem_of_superset (hAo.mem_nhds (hgA ⟨p, mem_ball_self hr, rfl⟩)) ?_
  rw [hAeq]
  exact image_mono (ball_subset_closedBall.trans hball)

/-- `bd` is invariant under homeomorphisms. -/
theorem isInteriorPoint_homeomorph_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) : IsInteriorPoint (e x) ↔ IsInteriorPoint x := by
  have key : ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
      (x : X), IsInteriorPoint x → IsInteriorPoint (e x) := by
    intro X Y _ _ e x ⟨U, hU, hx, ⟨f⟩⟩
    exact ⟨e '' U, e.isOpenMap _ hU, mem_image_of_mem _ hx, ⟨(e.image U).symm.trans f⟩⟩
  refine ⟨fun h => ?_, key e x⟩
  have h' : IsInteriorPoint (e.symm (e x)) := by
    obtain ⟨U, hU, hx, ⟨f⟩⟩ := h
    exact ⟨e.symm '' U, e.symm.isOpenMap _ hU, mem_image_of_mem _ hx, ⟨(e.symm.image U).symm.trans
      f⟩⟩
  simpa using h'

/-- `bd` is invariant under homeomorphisms. -/
theorem image_bd_homeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : e '' bd X = bd Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ h
    exact hx ((isInteriorPoint_homeomorph_iff e x).mp h)
  · intro hy
    refine ⟨e.symm y, fun h => hy ?_, by simp⟩
    have := (isInteriorPoint_homeomorph_iff e (e.symm y)).mpr h
    simpa using this

/-- The points of the closed disc in the open disc form a copy of the open disc. -/
noncomputable def openPartHomeomorph :
    (Subtype.val ⁻¹' OpenUnitDisc : Set ClosedUnitDisc) ≃ₜ OpenUnitDisc where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, ball_subset_closedBall z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    exact continuous_subtype_val

/-- The manifold boundary of the closed unit disc is the unit circle. Points of the open disc are
interior points. A point of the circle has no neighbourhood homeomorphic to an open disc, since by
invariance of domain the neighbourhood would be open in the plane. -/
theorem bd_closedUnitDisc : bd (ClosedUnitDisc) = {x | x.1 ∈ UnitCircle} := by
  classical
  ext x
  have hxn : ‖x.1‖ ≤ 1 := mem_closedBall_zero_iff.mp x.2
  constructor
  · intro hx
    change x.1 ∈ UnitCircle
    rw [UnitCircle, mem_sphere_zero_iff_norm]
    by_contra hne
    apply hx
    have hlt : ‖x.1‖ < 1 := lt_of_le_of_ne hxn hne
    exact ⟨Subtype.val ⁻¹' OpenUnitDisc, isOpen_ball.preimage continuous_subtype_val,
      mem_ball_zero_iff.mpr hlt, ⟨openPartHomeomorph⟩⟩
  · intro hx hint
    have hx1 : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    obtain ⟨U, hU, hxU, ⟨f⟩⟩ := hint
    have hmem : ∀ z : ℂ, ‖z‖ < 1 → complexPlane z ∈ OpenUnitDisc := fun z hz => by
      refine mem_ball_zero_iff.mpr ?_
      rwa [LinearIsometryEquiv.norm_map]
    let g : ℂ → ℂ := fun z =>
      if h : ‖z‖ < 1 then complexPlane.symm (f.symm ⟨complexPlane z, hmem z h⟩).1.1 else 0
    have hgb : ∀ z (h : z ∈ ball (0 : ℂ) 1), g z =
        complexPlane.symm (f.symm ⟨complexPlane z, hmem z (by simpa using h)⟩).1.1 := by
      intro z h
      have h' : ‖z‖ < 1 := by simpa using h
      simp only [g, h', dite_true]
    have hgc : ContinuousOn g (ball (0 : ℂ) 1) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (ball (0 : ℂ) 1).domRestrict g = fun z : ball (0 : ℂ) 1 =>
          complexPlane.symm (f.symm ⟨complexPlane z.1, hmem z.1 (mem_ball_zero_iff.mp z.2)⟩).1.1
            := by
        ext z
        exact hgb z.1 z.2
      rw [this]
      have h2 : Continuous fun z : ball (0 : ℂ) 1 =>
          (⟨complexPlane z.1, hmem z.1 (mem_ball_zero_iff.mp z.2)⟩ : OpenUnitDisc) := by
        refine Continuous.subtype_mk ?_ _
        exact complexPlane.continuous.comp continuous_subtype_val
      exact complexPlane.symm.continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp (f.symm.continuous.comp h2)))
    have hgi : InjOn g (ball (0 : ℂ) 1) := by
      intro a ha b hb hab
      rw [hgb a ha, hgb b hb] at hab
      have h1 := complexPlane.symm.injective hab
      have h2 := f.symm.injective (Subtype.ext (Subtype.ext h1))
      exact complexPlane.injective (congr_arg Subtype.val h2)
    have hopen := isOpen_image_of_injOn isOpen_ball hgc hgi
    have hy : complexPlane.symm x.1 ∈ g '' ball (0 : ℂ) 1 := by
      have hn : ‖complexPlane.symm (f ⟨x, hxU⟩).1‖ < 1 := by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_ball_zero_iff.mp (f ⟨x, hxU⟩).2
      refine ⟨complexPlane.symm (f ⟨x, hxU⟩).1, by simpa using hn, ?_⟩
      rw [hgb _ (by simpa using hn)]
      simp
    have hsmall : ∀ w ∈ g '' ball (0 : ℂ) 1, ‖w‖ ≤ 1 := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hgb z hz, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp (f.symm ⟨complexPlane z, hmem z (by simpa using hz)⟩).1.2
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hy
    set y := complexPlane.symm x.1 with hydef
    have hyn : ‖y‖ = 1 := by rw [hydef, LinearIsometryEquiv.norm_map, hx1]
    have h1 : y + ((ε / 2 : ℝ) : ℂ) * y ∈ ball y ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hyn, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have h2 := hsmall _ (hball h1)
    have h3 : y + ((ε / 2 : ℝ) : ℂ) * y = ((1 + ε / 2 : ℝ) : ℂ) * y := by push_cast; ring
    rw [h3, norm_mul, hyn, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith

/-- The boundary of a closed disc is the image of the unit circle. -/
theorem disc_boundary : DiscBoundaryStatement.{u} := by
  intro S _ Δ φ
  have h := image_bd_homeomorph φ
  rw [bd_closedUnitDisc] at h
  rw [discBd, ← h, image_image]

/-- The boundary of a closed disc is an `O`-arc. -/
theorem IsClosedDisc.isOArc_discBd {S : Type u} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsOArc (discBd Δ) := by
  obtain ⟨φ⟩ := hΔ
  have hmem : ∀ w : Circle, complexPlane (w : ℂ) ∈ ClosedUnitDisc := fun w => by
    refine mem_closedBall_zero_iff.mpr ?_
    rw [LinearIsometryEquiv.norm_map, Circle.norm_coe]
  let c : Circle → S := fun w => (φ ⟨complexPlane w, hmem w⟩).1
  have hc : IsEmbedding c := by
    have h1 : IsEmbedding fun w : Circle => (⟨complexPlane w, hmem w⟩ : ClosedUnitDisc) := by
      refine IsEmbedding.of_comp ?_ continuous_subtype_val ?_
      · exact Continuous.subtype_mk (complexPlane.continuous.comp continuous_subtype_val) _
      · exact complexPlane.isometry.isEmbedding.comp IsEmbedding.subtypeVal
    exact IsEmbedding.subtypeVal.comp (φ.isEmbedding.comp h1)
  have hrange : range c = discBd Δ := by
    rw [disc_boundary Δ φ]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨⟨complexPlane w, hmem w⟩, ?_, rfl⟩
      change complexPlane (w : ℂ) ∈ UnitCircle
      rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, Circle.norm_coe]
    · rintro ⟨x, hx, rfl⟩
      have hn : ‖complexPlane.symm x.1‖ = 1 := by
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp hx
      refine ⟨⟨complexPlane.symm x.1, mem_sphere_zero_iff_norm.mpr hn⟩, ?_⟩
      change (φ ⟨complexPlane (complexPlane.symm x.1), _⟩).1 = _
      simp
  exact ⟨hc.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

end GraphMinor.Surface
