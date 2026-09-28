/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Classical.Foundations.Development001
public import LeanPool.MovingSofa.Curve.Foundations.Development001












public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.JordanPick.JordanCurve
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Connected.Basic
/-!
# Moving sofa: related mathematical developments

* `Curve.Jordan.Separation`.
* `Curve.Jordan.Interior`.
* `Curve.Jordan.OrientationTransport`.
* `Curve.Jordan.AreaTransport`.
* `Curve.Jordan.ClosedArea`.
* `Curve.Jordan.SignedArea`.
* `Curve.Jordan.SupportingOrientation`.
* `Curve.Jordan.Subarc`.
* `Curve.Reparametrization`.
* `Curve.SegmentAreaProperties`.
* `Curve.Jordan.SubarcArea`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Separation
-/

@[expose] public section

namespace MovingSofa

private theorem IsJordanCurve.exists_sphere_parametrization {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) :
    ∃ r : Metric.sphere (0 : Point) 1 → Point,
      Continuous r ∧ Function.Injective r ∧ Set.range r = Γ := by
  obtain ⟨f, hf, hfi, hfr⟩ := hΓ
  let e := Complex.orthonormalBasisOneI.repr.symm
  let φ : Metric.sphere (0 : Point) 1 → Circle := fun p ↦
    ⟨e p.val, mem_sphere_zero_iff_norm.mpr (by
      rw [e.norm_map]
      exact mem_sphere_zero_iff_norm.mp p.property)⟩
  have hφc : Continuous φ := (e.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Function.Injective φ := by
    intro p q h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  have hφs : Function.Surjective φ := by
    intro z
    refine ⟨⟨e.symm z.val, mem_sphere_zero_iff_norm.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [e.symm.norm_map]
      exact Circle.norm_coe z
    · exact e.apply_symm_apply z.val
  refine ⟨f ∘ φ, hf.comp hφc, hfi.comp hφi, ?_⟩
  rw [Set.range_comp, hφs.range_eq, Set.image_univ, hfr]

theorem jordan_separation {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    ∃ U V : Set Point,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Bornology.IsBounded U ∧ ¬Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = Γᶜ ∧ frontier U = Γ ∧ frontier V = Γ ∧
      (∀ p ∈ U, connectedComponentIn Γᶜ p = U) ∧
      (∀ p ∈ V, connectedComponentIn Γᶜ p = V) := by
  obtain ⟨r, hr, hri, hrΓ⟩ := hΓ.exists_sphere_parametrization
  rw [← hrΓ]
  obtain ⟨u, hu, hub⟩ := JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT hr hri
  obtain ⟨v, hv, hvu⟩ := JordanCurve.exists_unbounded_component r hr
  let U := connectedComponentIn (Set.range r)ᶜ u
  let V := connectedComponentIn (Set.range r)ᶜ v
  have hne : U ≠ V := by
    intro h
    change connectedComponentIn (Set.range r)ᶜ u = connectedComponentIn (Set.range r)ᶜ v at h
    exact hvu (h ▸ hub)
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro p hpU hpV
    exact hne ((connectedComponentIn_eq hpU).trans (connectedComponentIn_eq hpV).symm)
  have hcover : U ∪ V = (Set.range r)ᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro p hp
      by_cases hpb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ p)
      · left
        have h := JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT hr hri
          p hp u hu hpb hub
        simpa only [U, ← h] using mem_connectedComponentIn hp
      · right
        have h := JordanCurve.unbounded_component_unique r hr hpb hvu
        simpa only [V, ← h] using mem_connectedComponentIn hp
  refine ⟨U, V, JordanCurve.isOpen_component r hr u, JordanCurve.isOpen_component r hr v,
    isConnected_connectedComponentIn_iff.mpr hu, isConnected_connectedComponentIn_iff.mpr hv,
    hub, hvu, hdis, hcover, ?_, ?_, ?_, ?_⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hu
      ⟨v, hv, hne.symm⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hv
      ⟨u, hu, hne⟩
  · intro p hp
    exact (connectedComponentIn_eq hp).symm
  · intro p hp
    exact (connectedComponentIn_eq hp).symm

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Interior
-/

@[expose] public section

namespace MovingSofa

/-- A Jordan curve has a point in its bounded complementary component. -/
theorem IsJordanCurve.jordanInterior_nonempty {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : (jordanInterior Γ).Nonempty := by
  obtain ⟨U, V, _, _, hU, _, hUb, _, _, hcover, _, _, hcomp, _⟩ :=
    jordan_separation hΓ
  obtain ⟨p, hp⟩ := hU.nonempty
  refine ⟨p, ?_, ?_⟩
  · have : p ∈ Γᶜ := hcover ▸ Set.mem_union_left V hp
    exact this
  · rw [hcomp p hp]
    exact hUb

/-- The frontier of the bounded complementary component of a Jordan curve is the curve
itself. -/
theorem IsJordanCurve.frontier_jordanInterior {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    frontier (jordanInterior Γ) = Γ := by
  obtain ⟨U, V, -, -, -, -, hUbdd, hVunbdd, -, hcover, hfrontU, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  have hUeq : jordanInterior Γ = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      rcases hcover.symm.subset hpΓ with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ Γᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  rw [hUeq]
  exact hfrontU

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Orientation Transport
-/

@[expose] public section

noncomputable section
namespace MovingSofa

/-- Endpoint-preserving continuous parameter changes preserve Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩)
    (hxy : y = x ∘ φ) : ccw₂ = ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

/-- Exchanging the parameter endpoints reverses Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_not_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)
    (hxy : y = x ∘ φ) : ccw₂ = !ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_reversed_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Area Transport
-/

@[expose] public section

namespace MovingSofa

/-- A monotone or antitone transition between oriented Jordan paths determines their
signed areas. -/
theorem curveArea_eq_of_oriented_reparametrization
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {Γ : Set Point} {ccw₁ ccw₂ : Bool}
    (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x.val)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y.val)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ)
    (hcomp : y.val = x.val ∘ φ) :
    (ccw₁ = ccw₂ → curveAreaFunctional x = curveAreaFunctional y) ∧
    (ccw₁ ≠ ccw₂ → curveAreaFunctional x = -curveAreaFunctional y) := by
  obtain ⟨z, hz, hmarea, haarea⟩ :=
    curveArea_comp_monotone_or_antitone_surjective hab hcd x φ hφc hφs hφ
  have hzy : z = y := Subtype.ext (hz.trans hcomp.symm)
  subst z
  obtain ⟨u, hu⟩ := hφs ⟨a, le_rfl, hab⟩
  obtain ⟨v, hv⟩ := hφs ⟨b, hab, le_rfl⟩
  rcases hφ with hm | ha
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          hm (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ u from u.property.1)
      · exact (φ ⟨c, le_rfl, hcd⟩).property.1
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨d, hcd, le_rfl⟩).property.2
      · simpa only [hv] using
          hm (show v ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from v.property.2)
    have horient := hx.orientation_eq_of_comp hy φ hφc hleft hright hcomp
    exact ⟨fun _ ↦ (hmarea hm).symm, fun hn ↦ (hn horient.symm).elim⟩
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨c, le_rfl, hcd⟩).property.2
      · simpa only [hv] using
          ha (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ v from v.property.1)
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          ha (show u ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from u.property.2)
      · exact (φ ⟨d, hcd, le_rfl⟩).property.1
    have horient := hx.orientation_eq_not_of_comp hy φ hφc hleft hright hcomp
    constructor
    · intro heq
      have hf : ccw₁ = !ccw₁ := heq.trans horient
      cases ccw₁ <;> contradiction
    · intro _
      have heq := haarea ha
      linarith

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Closed Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Same-carrier closed Jordan parametrizations have signed areas determined by orientation. -/
theorem curveArea_closed_same_carrier (Γ Δ : OrientedJordanCurve)
    (x : ClosedBVParametrization Γ) (y : ClosedBVParametrization Δ)
    (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.counterclockwise = Δ.counterclockwise →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.counterclockwise ≠ Δ.counterclockwise →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  have hy : IsOrientedJordanParametrization y.ordered Γ.carrier Δ.counterclockwise y.path.val := by
    rw [hcarrier]
    exact y.oriented
  have hcompare (z : ClosedBVParametrization Γ)
      (hstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
        y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional z.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional z.path = -curveAreaFunctional y.path) := by
    obtain ⟨φ, hφc, hφs, hφo, hcomp⟩ :=
      z.exists_reparametrization_of_start_eq y hcarrier hstart
    exact curveArea_eq_of_oriented_reparametrization z.ordered y.ordered z.path y.path
      z.oriented hy φ hφc hφs hφo hcomp
  by_cases hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩
  · exact hcompare x hstart
  have hmem : y.path.val ⟨y.a, le_rfl, y.ordered⟩ ∈ Set.range x.path.val := by
    rw [x.oriented.2.2.2.1, hcarrier, ← y.oriented.2.2.2.1]
    exact Set.mem_range_self _
  obtain ⟨s, hsb, hs⟩ := exists_param_lt_top_of_mem_range x.oriented.1 x.path.val
    x.oriented.2.2.2.2.1 hmem
  have has : x.a < (s : ℝ) := by
    apply lt_of_le_of_ne s.property.1
    intro heq
    have hsa : s = ⟨x.a, le_rfl, x.ordered⟩ := Subtype.ext heq.symm
    apply hstart
    simpa only [hsa] using hs
  obtain ⟨r, hr, hrstart, hrarea⟩ :=
    exists_oriented_cyclic_rotation x.ordered x.path x.oriented s has hsb
  let z : ClosedBVParametrization Γ :=
    { a := 0, b := 2, ordered := by norm_num, path := r, oriented := hr }
  have hzstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩ := hrstart.trans hs
  simpa only [show z.path = r from rfl, hrarea] using hcompare z hzstart

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Signed Area
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem windingKernel_disk_integral (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    Integrable (windingKernel z) (volume.restrict (Metric.ball 0 R)) ∧
    (∀ i : Fin 2, Integrable (fun p ↦ windingKernel z p i)
      (volume.restrict (Metric.ball 0 R))) ∧
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R ∧
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  exact ⟨hInt, fun i ↦ by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hInt,
    setIntegral_norm_windingKernel_ball_le R hR z hz,
    setIntegral_windingKernel_ball R z hz⟩

theorem jordanBV_winding_integral (a b : ℝ) (hab : a < b) (x : ContinuousBVPaths a b)
    (hclosed : x.val ⟨a, le_rfl, hab.le⟩ = x.val ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) :
    volume (Set.range x.val) = 0 ∧
    (∀ p ∉ Set.range x.val,
      (∀ i : Fin 2, Continuous (fun t ↦ windingKernel (x.val t) p i) ∧
        ∃ C : ℝ, ∀ t, |windingKernel (x.val t) p i| ≤ C) ∧
      2 * Real.pi * curveWinding hab.le x.val p =
        intervalStieltjesIntegral (continuousBVCoordinate x 1)
          (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
        intervalStieltjesIntegral (continuousBVCoordinate x 0)
          (fun t ↦ windingKernel (x.val t) p 1) Set.univ) ∧
    (∀ p ∉ Set.range x.val, ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, q ∉ Set.range x.val ∧
        curveWinding hab.le x.val q = curveWinding hab.le x.val p) ∧
    (∀ p ∉ Set.range x.val,
      ¬Bornology.IsBounded (connectedComponentIn (Set.range x.val)ᶜ p) →
      curveWinding hab.le x.val p = 0) := by
  refine ⟨x.volume_range_eq_zero_of_injOn hab.le hinj, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨fun i ↦ windingKernel_coord_continuous_bounded x.property.1 hp i, ?_⟩
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab x.property.1 hp
    have hnormpos : ∀ t, 0 < ‖x.val t - p‖ := by
      intro t
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact hp ⟨t, h⟩
    have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
      ((x.property.1.sub continuous_const).norm).continuousOn
    set m : ℝ := ‖x.val t₀ - p‖ with hmdef
    have hmpos : 0 < m := hnormpos t₀
    have hmle : ∀ t, m ≤ ‖x.val t - p‖ := fun t ↦ ht₀ (Set.mem_univ t)
    obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous x.property.1) (m / 2) (by linarith)
    have hclose : ∀ t u : Set.Icc a b, |(u : ℝ) - (t : ℝ)| < δ₀ →
        ‖x.val u - x.val t‖ < m / 2 := by
      intro t u hlt
      have hd : dist u t < δ₀ := by
        rw [Subtype.dist_eq, Real.dist_eq]; exact hlt
      simpa only [dist_eq_norm] using hmod hd
    set D : Point → Fin 2 → ℝ := fun z ↦ ![windingKernel z p 1, windingKernel z p 0] with hDdef
    have hD0 : ∀ z, D z 0 = windingKernel z p 1 := fun z ↦ rfl
    have hD1 : ∀ z, D z 1 = windingKernel z p 0 := fun z ↦ rfl
    have hDcont : ∀ i, Continuous (fun t ↦ D (x.val t) i) := by
      intro i
      fin_cases i
      · change Continuous (fun t ↦ D (x.val t) 0)
        simpa only [hD0] using (windingKernel_coord_continuous_bounded x.property.1 hp 1).1
      · change Continuous (fun t ↦ D (x.val t) 1)
        simpa only [hD1] using (windingKernel_coord_continuous_bounded x.property.1 hp 0).1
    have hcoordsub : ∀ (v w : Point) (i : Fin 2), (v - w) i = v i - w i := by
      intro v w i; simp
    have hkey : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
        |θ u - θ t -
          (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
            D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤
          6 / m ^ 2 * ‖x.val u - x.val t‖ ^ 2 := by
      intro t u htu hlt
      have hnwpos : 0 < ‖x.val t - p‖ := hnormpos t
      have hnw2 : ‖x.val t - p‖ ^ 2 = (x.val t - p) 0 ^ 2 + (x.val t - p) 1 ^ 2 :=
        Point.norm_sq_eq _
      have hnd2 : ‖x.val u - x.val t‖ ^ 2 =
          (x.val u - x.val t) 0 ^ 2 + (x.val u - x.val t) 1 ^ 2 := Point.norm_sq_eq _
      have hndlt : ‖x.val u - x.val t‖ < m / 2 :=
        hclose t u (by rw [abs_of_nonneg (by linarith)]; exact hlt)
      have hsmall : 2 * ‖x.val u - x.val t‖ ≤ ‖x.val t - p‖ := by
        have := hmle t; linarith
      have hposdot : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
          0 < (x.val t - p) 0 * (x.val s - p) 0 + (x.val t - p) 1 * (x.val s - p) 1 := by
        intro s hts hsu
        have hds : ‖x.val s - x.val t‖ < m / 2 :=
          hclose t s (by rw [abs_of_nonneg (by linarith)]; linarith)
        have hdot := Point.abs_inner_coords_le (x.val t - p) (x.val s - x.val t)
        have he0 : (x.val s - p) 0 = (x.val t - p) 0 + (x.val s - x.val t) 0 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        have he1 : (x.val s - p) 1 = (x.val t - p) 1 + (x.val s - x.val t) 1 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        rw [he0, he1]
        have hmt := hmle t
        have hnn := norm_nonneg (x.val s - x.val t)
        nlinarith [abs_le.mp hdot, hnw2]
      have hangle := hθ.sub_eq_arctan_of_dot_pos x.property.1 htu hposdot
      have hest := Real.abs_arctan_div_sub_le_of_small (w0 := (x.val t - p) 0)
        (w1 := (x.val t - p) 1) (d0 := (x.val u - x.val t) 0)
        (d1 := (x.val u - x.val t) 1) (nw := ‖x.val t - p‖)
        (nd := ‖x.val u - x.val t‖) hnwpos hnw2 (norm_nonneg _) hnd2 hsmall
      have he0 : (x.val u - p) 0 = (x.val t - p) 0 + (x.val u - x.val t) 0 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have he1 : (x.val u - p) 1 = (x.val t - p) 1 + (x.val u - x.val t) 1 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have harg :
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
              (x.val t - p) 1 * (x.val u - x.val t) 0) /
            (‖x.val t - p‖ ^ 2 +
              ((x.val t - p) 0 * (x.val u - x.val t) 0 +
                (x.val t - p) 1 * (x.val u - x.val t) 1)) =
          ((x.val t - p) 0 * (x.val u - p) 1 - (x.val t - p) 1 * (x.val u - p) 0) /
            ((x.val t - p) 0 * (x.val u - p) 0 + (x.val t - p) 1 * (x.val u - p) 1) := by
        have hquot : ∀ A B C E : ℝ,
            (A * E - B * C) / (A ^ 2 + B ^ 2 + (A * C + B * E)) =
              (A * (B + E) - B * (A + C)) / (A * (A + C) + B * (B + E)) := by
          intro A B C E
          congr 1 <;> ring
        rw [hnw2, he0, he1]
        exact hquot _ _ _ _
      rw [harg, ← hangle] at hest
      have hlin : D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0) =
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
            (x.val t - p) 1 * (x.val u - x.val t) 0) / ‖x.val t - p‖ ^ 2 := by
        have hne : ‖x.val t - p‖ ≠ 0 := ne_of_gt hnwpos
        rw [hD0, hD1]
        simp only [windingKernel, PiLp.smul_apply, smul_eq_mul, hcoordsub]
        field_simp
      rw [hlin]
      refine hest.trans ?_
      have hmsq : m ^ 2 ≤ ‖x.val t - p‖ ^ 2 := by
        have := hmle t; nlinarith
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hmsq
    have hchain := ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
      hab.le x x.boundedVariationOn θ D hDcont (by positivity) hδ₀ hkey
    simp only [hD0, hD1] at hchain
    rw [hθ.curveWinding_eq hab.le, ← hchain]
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp
  · intro p hp
    exact curveWinding_locally_constant_on_compl_range hab.le x.property.1 hclosed hp
  · intro p hp hub
    exact curveWinding_eq_zero_of_unbounded_component hab.le x.property.1 hclosed hp hub

/-- Joint measurability of the winding kernel along a continuous path. -/
private theorem measurable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b) :
    Measurable fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 := by
  have h1 : Measurable fun q : Point × Set.Icc a b ↦ x.val q.2 - q.1 :=
    (x.property.1.measurable.comp measurable_snd).sub measurable_fst
  have h2 : Measurable fun q : Point × Set.Icc a b ↦
      (‖x.val q.2 - q.1‖ ^ 2)⁻¹ • (x.val q.2 - q.1) :=
    Measurable.smul ((h1.norm.pow_const 2).inv) h1
  exact h2

/-- The winding kernel of a path is product-integrable against area on an enclosing disk
and any finite measure in the time variable. -/
private theorem integrable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R)
    (ν : Measure (Set.Icc a b)) [IsFiniteMeasure ν] :
    Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod ν) := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmeas := measurable_windingKernel_prod x
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbound : ∀ t : Set.Icc a b,
      (∫⁻ p, ‖windingKernel (x.val t) p‖ₑ ∂(volume.restrict (Metric.ball (0 : Point) R)))
        ≤ ENNReal.ofReal (4 * Real.pi * R) := by
    intro t
    obtain ⟨hint, -, hnorm, -⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.ofReal_le_ofReal hnorm
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
  calc
    (∫⁻ t, ∫⁻ p, ‖windingKernel (x.val t) p‖ₑ
        ∂(volume.restrict (Metric.ball (0 : Point) R)) ∂ν)
        ≤ ∫⁻ _, ENNReal.ofReal (4 * Real.pi * R) ∂ν := lintegral_mono hbound
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ)

/-- Fubini exchange between the coordinate Stieltjes measure of a continuous BV path and
planar area on an enclosing disk, evaluated through the disk mean of the winding kernel. -/
private theorem setIntegral_ball_stieltjes_windingKernel {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R) (i j : Fin 2) :
    Integrable (fun p ↦ intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ)
      (volume.restrict (Metric.ball (0 : Point) R)) ∧
    (∫ p in Metric.ball (0 : Point) R, intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ) =
      Real.pi * intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ x.val t i) Set.univ := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfinvar : IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure
      (continuousBVCoordinate x j).boundedVariation
  have hfinmu : IsFiniteMeasure
      ((volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure).variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  simp only [intervalStieltjesIntegral_univ]
  have hprodK : Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 i)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation) := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp
      (integrable_windingKernel_prod x hR hxR
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation)
  have hintI : Integrable (fun p ↦ VectorMeasure.integral
      (intervalStieltjesMeasure (continuousBVCoordinate x j))
      (fun t ↦ windingKernel (x.val t) p i) (ContinuousLinearMap.mul ℝ ℝ))
      (volume.restrict (Metric.ball (0 : Point) R)) := by
    have hh := Integrable.integral_vectorMeasure_prod_left
      (B := ContinuousLinearMap.mul ℝ ℝ) hprodK
    simpa using hh
  refine ⟨hintI, ?_⟩
  have hinner : ∀ t : Set.Icc a b,
      (∫ p in Metric.ball (0 : Point) R, windingKernel (x.val t) p i) =
        Real.pi * x.val t i := by
    intro t
    obtain ⟨hint, -, -, heq⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
    rw [heq] at hc
    simpa using hc
  have hfub := VectorMeasure.integral_integral_swap
    (μ := (volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure)
    (ν := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (C := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (A := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (D := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun (p : Point) (t : Set.Icc a b) ↦ windingKernel (x.val t) p i)
    (by rw [Measure.variation_toSignedMeasure]; exact hprodK)
    (by intro u v w; simp; ring)
  simp only [VectorMeasure.integral_toSignedMeasure] at hfub
  rw [hfub]
  simp only [hinner]
  simpa [smul_eq_mul] using VectorMeasure.integral_fun_smul
    (μ := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ) Real.pi (fun t ↦ x.val t i)

theorem curveArea_eq_jordanInterior_area (a b : ℝ) (hab : a ≤ b)
    (Γ : Set Point) (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ true x.val) :
    curveAreaFunctional x = ClassicalResults.area (jordanInterior Γ) := by
  obtain ⟨hlt, hΓ, hcont, hrange, hclosed, hinj, hwind⟩ := hx
  subst hrange
  obtain ⟨U, V, hUopen, -, -, -, hUbdd, hVunbdd, -, hcover, -, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  obtain ⟨hnull, hwindint, -, hext⟩ := jordanBV_winding_integral a b hlt x hclosed hinj
  have hUeq : jordanInterior (Set.range x.val) = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      have hpc : p ∈ U ∪ V := by rw [hcover]; exact hpΓ
      rcases hpc with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ (Set.range x.val)ᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  obtain ⟨R, hR, hxR, hUR⟩ :
      ∃ R : ℝ, 0 < R ∧ (∀ t, ‖x.val t‖ < R) ∧ U ⊆ Metric.ball (0 : Point) R := by
    have hcpt : IsCompact (Set.range x.val) := isCompact_range hcont
    obtain ⟨r, hr⟩ := (hcpt.isBounded.union hUbdd).subset_closedBall (0 : Point)
    refine ⟨max r 0 + 1, by have := le_max_right r 0; linarith, ?_, ?_⟩
    · intro t
      have h1 : x.val t ∈ Metric.closedBall (0 : Point) r :=
        hr (Set.mem_union_left _ ⟨t, rfl⟩)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have := le_max_left r 0
      linarith
    · intro p hp
      have h1 : p ∈ Metric.closedBall (0 : Point) r := hr (Set.mem_union_right _ hp)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      rw [Metric.mem_ball, dist_zero_right]
      have := le_max_left r 0
      linarith
  have hae : ∀ᵐ p ∂(volume : Measure Point), p ∉ Set.range x.val :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  -- winding equals the indicator of the bounded component off the curve
  have hwind_eq : ∀ p ∉ Set.range x.val,
      curveWinding hab x.val p = U.indicator (fun _ ↦ (1 : ℝ)) p := by
    intro p hp
    by_cases hpU : p ∈ U
    · rw [Set.indicator_of_mem hpU]
      have hw := hwind p (by rw [hUeq]; exact hpU)
      simpa using hw
    · rw [Set.indicator_of_notMem hpU]
      have hpV : p ∈ V := by
        have hpc : p ∈ U ∪ V := by rw [hcover]; exact hp
        rcases hpc with h | h
        · exact absurd h hpU
        · exact h
      refine hext p hp ?_
      rw [hVcomp p hpV]
      exact hVunbdd
  have hArea : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      ClassicalResults.area (jordanInterior (Set.range x.val)) := by
    have h1 : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
        ∫ p in Metric.ball (0 : Point) R, U.indicator (fun _ ↦ (1 : ℝ)) p := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact hwind_eq p hp
    rw [h1, setIntegral_indicator hUopen.measurableSet,
      Set.inter_eq_self_of_subset_right hUR, setIntegral_const, hUeq]
    simp [ClassicalResults.area, measureReal_def]
  have hFunctional : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      curveAreaFunctional x := by
    obtain ⟨hint01, heq01⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 0 1
    obtain ⟨hint10, heq10⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 1 0
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hL : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p) =
        2 * Real.pi * ∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p :=
      integral_const_mul _ _
    have hcong : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p)
        = ∫ p in Metric.ball (0 : Point) R,
            (intervalStieltjesIntegral (continuousBVCoordinate x 1)
              (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
             intervalStieltjesIntegral (continuousBVCoordinate x 0)
              (fun t ↦ windingKernel (x.val t) p 1) Set.univ) := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact (hwindint p hp).2
    rw [hcong, integral_sub hint01 hint10, heq01, heq10] at hL
    refine mul_left_cancel₀ (ne_of_gt hpi) ?_
    rw [← hL, curveAreaFunctional]
    ring
  rw [← hFunctional, hArea]

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Supporting Orientation
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_me89eded (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_me89eded (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_me89eded (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

private theorem continuous_arg_comp_of_re_nonneg {A : Type*} [TopologicalSpace A]
    {z : A → ℂ} (hz : Continuous z) (hre : ∀ u, 0 ≤ (z u).re) (hne : ∀ u, z u ≠ 0) :
    Continuous (fun u ↦ Complex.arg (z u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hmem : z u ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · intro harg
      have hneg := (Complex.arg_eq_pi_iff.mp harg).1
      linarith [hre u]
    · exact hne u
  exact (Complex.continuousAt_arg hmem).comp_of_eq hz.continuousAt rfl

private def frameComplex (t : Real.Angle) (v : Point) : ℂ :=
  inner ℝ v (normalVector t) + inner ℝ v (tangentVector t) * Complex.I

@[simp] private theorem frameComplex_re (t : Real.Angle) (v : Point) :
    (frameComplex t v).re = inner ℝ v (normalVector t) := by
  simp [frameComplex]

@[simp] private theorem frameComplex_im (t : Real.Angle) (v : Point) :
    (frameComplex t v).im = inner ℝ v (tangentVector t) := by
  simp [frameComplex]

private theorem norm_frameComplex (t : Real.Angle) (v : Point) :
    ‖frameComplex t v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [frameComplex, Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.norm_sq_eq,
    normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring_nf
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * t.cos_sq_add_sin_sq

private theorem conj_pointComplex_mul_eq_conj_frameComplex_mul (t : Real.Angle)
    (v w : Point) :
    starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w =
      starRingEnd ℂ (frameComplex t v) * frameComplex t w := by
  apply Complex.ext <;>
    simp [Complex.orthonormalBasisOneI_repr_symm_apply, frameComplex, normalVector, tangentVector,
        frame,
      PiLp.inner_apply, Fin.sum_univ_two] <;> ring_nf
  · linear_combination -(v 0 * w 0 + v 1 * w 1) * t.cos_sq_add_sin_sq
  · linear_combination -(v 0 * w 1 - v 1 * w 0) * t.cos_sq_add_sin_sq

private theorem frameComplex_ne_zero {t : Real.Angle} {v : Point} (hv : v ≠ 0) :
    frameComplex t v ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_frameComplex, norm_ne_zero_iff]
  exact hv

private theorem normalized_frameComplex_arg (t : Real.Angle) (v : Point) (hv : v ≠ 0) :
    Real.cos (t.toReal + Complex.arg (frameComplex t v)) = v 0 / ‖v‖ ∧
      Real.sin (t.toReal + Complex.arg (frameComplex t v)) = v 1 / ‖v‖ := by
  have hf := frameComplex_ne_zero (t := t) hv
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hf, Complex.sin_arg,
    norm_frameComplex]
  simp [frameComplex, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  constructor
  · field_simp
    ring_nf
    linear_combination (v 0) * t.cos_sq_add_sin_sq
  · field_simp
    ring_nf
    linear_combination (v 1) * t.cos_sq_add_sin_sq

/-- The frame argument gives an angle lift when a path lies on the nonnegative side of a normal
through its basepoint. -/
private theorem isCurveAngleLift_frameArg_of_inner_nonneg {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, 0 ≤ inner ℝ (x u - p) (normalVector t))
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p
      (fun u ↦ t.toReal + Complex.arg (frameComplex t (x u - p))) := by
  have hz : Continuous (fun u ↦ frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  refine ⟨continuous_const.add (continuous_arg_comp_of_re_nonneg hz
    (fun u ↦ by simpa using hre u) hzne),
    fun u ↦ ?_⟩
  exact normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))

/-- Negating frame coordinates and adding `π` gives the corresponding lift on the nonpositive
side of a normal through the basepoint. -/
private theorem isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, inner ℝ (x u - p) (normalVector t) ≤ 0)
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p (fun u ↦
      t.toReal + Complex.arg (-frameComplex t (x u - p)) + Real.pi) := by
  have hz : Continuous (fun u ↦ -frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  have harg : Continuous (fun u ↦ Complex.arg (-frameComplex t (x u - p))) :=
    continuous_arg_comp_of_re_nonneg hz (by
      intro u
      simpa using neg_nonneg.mpr (hre u)) (fun u ↦ neg_ne_zero.mpr (hzne u))
  refine ⟨(continuous_const.add harg).add continuous_const, fun u ↦ ?_⟩
  have hbase := normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))
  have hneg :
      Real.cos (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).re / ‖frameComplex t (x u - p)‖ ∧
        Real.sin (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).im / ‖frameComplex t (x u - p)‖ := by
    rw [Real.cos_add_pi, Real.sin_add_pi,
      Complex.cos_arg (neg_ne_zero.mpr (hzne u)), Complex.sin_arg, norm_neg]
    simp only [Complex.neg_re, Complex.neg_im, neg_div, neg_neg]
    exact ⟨trivial, trivial⟩
  dsimp only
  rw [add_assoc, Real.cos_add t.toReal, Real.sin_add t.toReal, hneg.1, hneg.2,
    norm_frameComplex]
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg (hzne u), Complex.sin_arg,
    norm_frameComplex] at hbase
  exact hbase

private def cyclicComplement {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point)
    (s t : Set.Icc a b) : Set.Icc (0 : ℝ) 2 → Point :=
  Function.concatUnitIntervals
    (x ∘ Set.Icc.convexComb t ⟨b, hab, le_rfl⟩)
    (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)

private theorem continuous_cyclicComplement {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s t : Set.Icc a b) : Continuous (cyclicComplement hab x s t) := by
  apply Function.continuous_concatUnitIntervals
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · simpa [Function.comp_apply] using hclosed.symm

@[simp] private theorem cyclicComplement_zero {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨0, by norm_num⟩ = x t := by
  simp [cyclicComplement]

@[simp] private theorem cyclicComplement_two {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨2, by norm_num⟩ = x s := by
  simp [cyclicComplement]

private theorem tangentVector_ne_zero (t : Real.Angle) : tangentVector t ≠ 0 := by
  intro h
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [← t.coe_toReal]
    exact inner_tangentVector_self t.toReal
  rw [h] at hone
  simp at hone

private theorem convexComb_between {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (r : Set.Icc (0 : ℝ) 1) :
    l ≤ Set.Icc.convexComb l u r ∧ Set.Icc.convexComb l u r ≤ u := by
  change (l : ℝ) ≤ (1 - (r : ℝ)) * l + (r : ℝ) * u ∧
    (1 - (r : ℝ)) * l + (r : ℝ) * u ≤ u
  constructor <;> nlinarith [r.property.1, r.property.2, show (l : ℝ) ≤ u from hlu]

private theorem range_comp_convexComb {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (x : Set.Icc a b → Point) :
    Set.range (x ∘ Set.Icc.convexComb l u) = x '' Set.Icc l u := by
  by_cases heq : l = u
  · subst u
    simp [Set.Icc_self]
  have hneval : (l : ℝ) ≠ (u : ℝ) := fun h ↦ heq (Subtype.ext h)
  have hlt : (l : ℝ) < (u : ℝ) := lt_of_le_of_ne hlu hneval
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, convexComb_between hlu r, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    let r : I := ⟨((v : ℝ) - l) / ((u : ℝ) - l), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hv.1)
          (sub_nonneg.mpr (show (l : ℝ) ≤ u from hlu))
      · exact (div_le_one (sub_pos.mpr hlt)).2
          (by
            have hv₂ : (v : ℝ) ≤ (u : ℝ) := hv.2
            linarith)⟩
    refine ⟨r, congrArg x ?_⟩
    apply Subtype.ext
    simp [r]
    field_simp [sub_ne_zero.mpr hlt.ne']
    ring

private theorem inner_eq_of_mem_segment {P Q z v : Point} {c : ℝ}
    (hP : inner ℝ P v = c) (hQ : inner ℝ Q v = c)
    (hz : z ∈ segment ℝ P Q) : inner ℝ z v = c := by
  rw [segment_eq_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hP, hQ]
  nlinarith [hr.1, hr.2]

private theorem arg_conj_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ Complex.I * z) = Complex.arg z - Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    ring
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem arg_conj_neg_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ (-Complex.I) * z) = Complex.arg z + Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    ring
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem relative_arg_of_frame_eq_pos_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = (D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) - Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ ((D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ Complex.I * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_I_mul_of_re_pos hw

private theorem relative_arg_of_frame_eq_neg_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = -(D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) + Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ (-(D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ (-Complex.I) * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_neg_I_mul_of_re_pos hw

/-- The midpoint of a nontrivial segment traversed on `[s,t]` is avoided by the cyclic
complementary path. -/
private theorem cyclicComplement_ne_midpoint {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point}
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {u | (u : ℝ) < b})
    (s t : Set.Icc a b) (hst : s < t) (hxt : x s ≠ x t)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    ∀ u, cyclicComplement hab.le x s t u ≠ midpoint ℝ (x s) (x t) := by
  have hmseg : midpoint ℝ (x s) (x t) ∈ x '' Set.Icc s t := by
    rw [hsegment]
    exact midpoint_mem_segment _ _
  obtain ⟨v, hvst, hv⟩ := hmseg
  have hmvP : midpoint ℝ (x s) (x t) ≠ x s := by
    intro hm
    exact hxt ((midpoint_eq_left_iff ℝ).mp hm)
  have hmvQ : midpoint ℝ (x s) (x t) ≠ x t := by
    intro hm
    exact hxt ((midpoint_eq_right_iff ℝ).mp hm)
  have hsv : s < v := lt_of_le_of_ne hvst.1 (fun h ↦ hmvP (hv ▸ congrArg x h.symm))
  have hvt : v < t := lt_of_le_of_ne hvst.2 (fun h ↦ hmvQ (hv ▸ congrArg x h))
  have hsv' : (s : ℝ) < v := hsv
  have hvt' : (v : ℝ) < t := hvt
  have hvb : (v : ℝ) < b := lt_of_lt_of_le hvt t.property.2
  intro u hu
  have heval :
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
          (Set.projIcc 0 1 (by norm_num) (u : ℝ)) =
          midpoint ℝ (x s) (x t) ∨
        (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)
            (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)) =
              midpoint ℝ (x s) (x t) := by
    unfold cyclicComplement Function.concatUnitIntervals at hu
    split_ifs at hu with h
    · exact Or.inl hu
    · exact Or.inr hu
  rcases heval with htail | hhead
  · let w := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
      (Set.projIcc 0 1 (by norm_num) (u : ℝ))
    have htw : t ≤ w := (convexComb_between t.property.2 _).1
    have hxwv : x w = x v := htail.trans hv.symm
    by_cases hwb : (w : ℝ) = b
    · have hwtop : w = (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) := Subtype.ext hwb
      have hxav : x ⟨a, le_rfl, hab.le⟩ = x v := hclosed.trans (hwtop ▸ hxwv)
      have hav := hinj (by simp [hab]) (by exact hvb) hxav
      have hav' := congrArg Subtype.val hav
      linarith [s.property.1]
    · have hwb' : (w : ℝ) < b := lt_of_le_of_ne w.property.2 hwb
      have hwv := hinj hwb' hvb hxwv
      have hwv' := congrArg Subtype.val hwv
      have htw' : (t : ℝ) ≤ w := htw
      linarith
  · let w := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
      (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1))
    have hws : w ≤ s := (convexComb_between s.property.1 _).2
    have hxwv : x w = x v := hhead.trans hv.symm
    have hwb : (w : ℝ) < b := lt_of_le_of_lt hws (lt_of_lt_of_le hst t.property.2)
    have hwv := hinj hwb hvb hxwv
    have hwv' := congrArg Subtype.val hwv
    have hws' : (w : ℝ) ≤ s := hws
    linarith

private theorem jordan_counterclockwise_of_winding_one
    (a b : ℝ) (hab : a < b) (x : Set.Icc a b → Point)
    (hx : Continuous x) (hΓ : IsJordanCurve (Set.range x))
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (q : Point) (hqrange : q ∉ Set.range x)
    (hwinding_q : curveWinding hab.le x q = 1) :
    IsOrientedJordanParametrization hab.le (Set.range x) true x := by
  refine ⟨hab, hΓ, hx, rfl, hclosed, hinj, ?_⟩
  intro p hp
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have hqcompl : q ∈ (Set.range x)ᶜ := hqrange
  have hqUV : q ∈ U ∪ V := hcover.symm.subset hqcompl
  have hqU : q ∈ U := by
    rcases hqUV with hqU | hqV
    · exact hqU
    · exfalso
      let _ : PreconnectedSpace V := Subtype.preconnectedSpace hVconn.isPreconnected
      have hlc : IsLocallyConstant
          (fun z : V ↦ curveWinding hab.le x z.val) := by
        apply (IsLocallyConstant.iff_exists_open _).mpr
        intro z
        have hzout : z.val ∉ Set.range x := by
          have hzcompl : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inr z.property
          exact hzcompl
        obtain ⟨W, hWopen, hzW, hWeq⟩ :=
          curveWinding_locally_constant_off_range hab.le hx hclosed hzout
        exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
          fun z' hz' ↦ hWeq z'.val hz'⟩
      have hrangeBounded : Bornology.IsBounded (Set.range x) :=
        by simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
        hrangeBounded
      have hRnonneg : 0 ≤ R := by
        have := hR (Set.mem_range_self ⟨a, le_rfl, hab.le⟩)
        have hnorm : ‖x ⟨a, le_rfl, hab.le⟩‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using this
        exact (norm_nonneg _).trans hnorm
      have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
        by_contra hn
        push Not at hn
        apply hVunbounded
        refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
        intro v hv
        simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
      obtain ⟨v, hvV, hvnorm⟩ := hvfar
      have hvzero : curveWinding hab.le x v = 0 := by
        apply curveWinding_eq_zero_of_inner_pos hab.le hx hclosed v (-v)
        · exact neg_ne_zero.mpr (by
            intro hv0
            rw [hv0, norm_zero] at hvnorm
            linarith)
        · intro u
          rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
          rw [← real_inner_comm v (x u)]
          have hxu := hR (Set.mem_range_self u)
          have hinner := abs_real_inner_le_norm (x u) v
          have hxnorm : ‖x u‖ ≤ R := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hxu
          have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
          have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
          have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
          have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
            lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
              (mul_lt_mul_of_pos_right hvlarge hvpos)
          rw [pow_two]
          linarith
      have heq := hlc.apply_eq_of_preconnectedSpace ⟨q, hqV⟩ ⟨v, hvV⟩
      rw [hwinding_q, hvzero] at heq
      norm_num at heq
  have hqInterior : q ∈ jordanInterior (Set.range x) := by
    refine ⟨hqrange, ?_⟩
    rw [hcompU q hqU]
    exact hUbounded
  have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
  have hpU : p ∈ U := by
    rcases hpUV with hpU | hpV
    · exact hpU
    · exfalso
      apply hVunbounded
      rw [← hcompV p hpV]
      exact hp.2
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hUconn.isPreconnected
  have hlcU : IsLocallyConstant (fun z : U ↦ curveWinding hab.le x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := by
      have : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inl z.property
      exact this
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab.le hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  exact (hlcU.apply_eq_of_preconnectedSpace ⟨p, hpU⟩ ⟨q, hqU⟩).trans hwinding_q

private theorem supporting_segment_argument_corrections (P Q : Point) (θ : Real.Angle)
    (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) (hdirection : Q = P + d • tangentVector θ) :
    let m := midpoint ℝ P Q
    let q := m - ε • normalVector θ
    (Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (Q - m)) *
    Complex.orthonormalBasisOneI.repr.symm (Q - q)) =
  Complex.arg (frameComplex θ (Q - q)) - Real.pi / 2) ∧
    (Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (P - m)) *
    Complex.orthonormalBasisOneI.repr.symm (P - q)) =
  Complex.arg (frameComplex θ (P - q)) + Real.pi / 2) ∧
    (Complex.arg ((d / 2 : ℝ) * Complex.I) = Real.pi / 2) ∧
    (Complex.arg (-((d / 2 : ℝ) * Complex.I)) = -Real.pi / 2) ∧
    (-frameComplex θ (P - m) = (d / 2 : ℝ) * Complex.I) ∧
    (-frameComplex θ (Q - m) = -((d / 2 : ℝ) * Complex.I)) := by
  let m := midpoint ℝ P Q
  let q := m - ε • normalVector θ
  have htn : inner ℝ (tangentVector θ) (normalVector θ) = 0 := by
    rw [← θ.coe_toReal, real_inner_comm]
    exact inner_normalVector_tangentVector θ.toReal
  have htm : Q - m = (d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hsm : P - m = -(d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hTT : inner ℝ (tangentVector θ) (tangentVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_tangentVector_self θ.toReal
  have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_normalVector_self θ.toReal
  have hNT : inner ℝ (normalVector θ) (tangentVector θ) = 0 := by
    rw [real_inner_comm]
    exact htn
  have hframe_tm : frameComplex θ (Q - m) = (d / 2 : ℝ) * Complex.I := by
    rw [htm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have hframe_sm : frameComplex θ (P - m) = -(d / 2 : ℝ) * Complex.I := by
    rw [hsm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have htq : Q - q = ε • normalVector θ + (d / 2) • tangentVector θ := by
    calc
      Q - q = (Q - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [htm]; abel
  have hsq : P - q = ε • normalVector θ - (d / 2) • tangentVector θ := by
    calc
      P - q = (P - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [hsm]; module
  have hframe_tq : frameComplex θ (Q - q) = ε + (d / 2 : ℝ) * Complex.I := by
    rw [htq]
    apply Complex.ext
    · rw [frameComplex_re, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hframe_sq : frameComplex θ (P - q) = ε - (d / 2 : ℝ) * Complex.I := by
    rw [hsq]
    apply Complex.ext
    · rw [frameComplex_re, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hcorr_t :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (Q - m)) *
          Complex.orthonormalBasisOneI.repr.symm (Q - q)) =
        Complex.arg (frameComplex θ (Q - q)) - Real.pi / 2 := by
    apply relative_arg_of_frame_eq_pos_I (half_pos hd) hframe_tm
    rw [hframe_tq]
    simpa using hε
  have hcorr_s :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (P - m)) *
          Complex.orthonormalBasisOneI.repr.symm (P - q)) =
        Complex.arg (frameComplex θ (P - q)) + Real.pi / 2 := by
    apply relative_arg_of_frame_eq_neg_I (half_pos hd) hframe_sm
    rw [hframe_sq]
    simpa using hε
  have harg_tm : Complex.arg ((d / 2 : ℝ) * Complex.I) = Real.pi / 2 := by
    rw [Complex.arg_real_mul _ (half_pos hd), Complex.arg_I]
  have harg_sm : Complex.arg (-((d / 2 : ℝ) * Complex.I)) = -Real.pi / 2 := by
    rw [show -((d / 2 : ℝ) * Complex.I) = (d / 2 : ℝ) * (-Complex.I) by ring,
      Complex.arg_real_mul _ (half_pos hd), Complex.arg_neg_I]
    ring
  have hneg_frame_sm : -frameComplex θ (P - m) = (d / 2 : ℝ) * Complex.I := by
    rw [hframe_sm]
    ring
  have hneg_frame_tm : -frameComplex θ (Q - m) = -((d / 2 : ℝ) * Complex.I) := by
    rw [hframe_tm]
  exact ⟨hcorr_t, hcorr_s, harg_tm, harg_sm, hneg_frame_sm, hneg_frame_tm⟩

private theorem cyclic_partition_range {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (s t : Set.Icc a b) (hst : s < t) :
    let y := cyclicComplement hab.le x s t
    let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
    let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
    let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
    Set.range (Function.concatUnitIntervals z y₁) = Set.range x := by
  let y := cyclicComplement hab.le x s t
  let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
  let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
  let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
  have hjoin : z ⟨1, by norm_num⟩ = y₁ ⟨0, by norm_num⟩ := by
    simp [z, y₁, doubleParam, y]
  have hdouble_surj : Function.Surjective doubleParam := by
    intro u
    refine ⟨⟨(u : ℝ) / 2, by constructor <;> nlinarith [u.property.1, u.property.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [doubleParam]
    ring
  have hrange_y₁ : Set.range y₁ = Set.range y := by
    change Set.range (y ∘ doubleParam) = Set.range y
    rw [Set.range_comp, hdouble_surj.range_eq, Set.image_univ]
  have hrange_w : Set.range (Function.concatUnitIntervals z y₁) = Set.range x := by
    rw [Function.range_concatUnitIntervals z y₁ hjoin, hrange_y₁]
    change Set.range z ∪ Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)) = Set.range x
    rw [Function.range_concatUnitIntervals _ _ (by simpa using hclosed.symm),
      show Set.range z = x '' Set.Icc s t by
        change Set.range (x ∘ Set.Icc.convexComb s t) = _
        exact range_comp_convexComb hst.le x,
      range_comp_convexComb t.property.2 x, range_comp_convexComb s.property.1 x]
    ext p
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;>
        exact Set.mem_range_self u
    · rintro ⟨u, rfl⟩
      by_cases hus : u ≤ s
      · exact Or.inr (Or.inr ⟨u, ⟨u.property.1, hus⟩, rfl⟩)
      by_cases hut : u ≤ t
      · exact Or.inl ⟨u, ⟨le_of_not_ge hus, hut⟩, rfl⟩
      · exact Or.inr (Or.inl ⟨u, ⟨le_of_not_ge hut, u.property.2⟩, rfl⟩)
  exact hrange_w

theorem jordan_counterclockwise_of_supporting_segment
    (a b : ℝ) (hab : a < b) (x : Set.Icc a b → Point)
    (hx : Continuous x) (hΓ : IsJordanCurve (Set.range x))
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : ∀ t, x t ∈ normalHalfPlane θ h false false)
    (s t : Set.Icc a b) (hst : s < t)
    (hline : x s ∈ normalLine θ h)
    (d : ℝ) (hd : 0 < d) (hdirection : x t = x s + d • tangentVector θ)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    IsOrientedJordanParametrization hab.le (Set.range x) true x := by
  have hxt : x s ≠ x t := by
    intro heq
    have hz : d • tangentVector θ = 0 := by
      calc
        d • tangentVector θ = x t - x s := by rw [hdirection]; abel
        _ = 0 := by rw [← heq, sub_self]
    exact tangentVector_ne_zero θ ((smul_eq_zero.mp hz).resolve_left hd.ne')
  let m := midpoint ℝ (x s) (x t)
  let y := cyclicComplement hab.le x s t
  have hy : Continuous y := continuous_cyclicComplement hab.le hx hclosed s t
  have hym (u : Set.Icc (0 : ℝ) 2) : y u ≠ m := by
    exact cyclicComplement_ne_midpoint hab hclosed hinj s t hst hxt hsegment u
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos (by norm_num) hy (by
    intro hm
    obtain ⟨u, hu⟩ := hm
    exact hym u hu)
  have hxsN : inner ℝ (x s) (normalVector θ) = h := hline
  have htn : inner ℝ (tangentVector θ) (normalVector θ) = 0 := by
    rw [← θ.coe_toReal, real_inner_comm]
    exact inner_normalVector_tangentVector θ.toReal
  have hxtN : inner ℝ (x t) (normalVector θ) = h := by
    rw [hdirection, inner_add_left, real_inner_smul_left, hxsN, htn, mul_zero, add_zero]
  have hmN : inner ℝ m (normalVector θ) = h := by
    dsimp [m]
    rw [midpoint_eq_smul_add, real_inner_smul_left, inner_add_left, hxsN, hxtN]
    norm_num
    ring
  have hyhalf (u : Set.Icc (0 : ℝ) 2) :
      inner ℝ (y u - m) (normalVector θ) ≤ 0 := by
    unfold y cyclicComplement Function.concatUnitIntervals
    split_ifs
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
        (Set.projIcc 0 1 (by norm_num) (u : ℝ)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
        (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
  have hymLift : IsCurveAngleLift y m (fun u ↦
      θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi) :=
    isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos θ hy hyhalf hym
  let ε := min (r / 2) (d / 4)
  have hε : 0 < ε := lt_min (half_pos hr) (by positivity)
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  let q := m - ε • normalVector θ
  have hnormN : ‖normalVector θ‖ = 1 := by
    rw [← θ.coe_toReal]
    exact norm_normalVector_real θ.toReal
  have hqm : dist q m = ε := by
    rw [dist_eq_norm]
    simp only [q, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, hnormN,
      mul_one, abs_of_pos hε]
  have hqclose : dist q m < r := hqm.trans_lt hεr
  have hyqLift := hymLift.add_principal_basepoint_correction hy (hdot q hqclose)
  let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
  have hz : Continuous z := hx.comp (Set.Icc.continuous_convexComb _ _)
  have hzN (u : Set.Icc (0 : ℝ) 1) : inner ℝ (z u) (normalVector θ) = h := by
    apply inner_eq_of_mem_segment hxsN hxtN
    rw [← hsegment]
    exact ⟨Set.Icc.convexComb s t u, convexComb_between hst.le u, rfl⟩
  have hqN : inner ℝ q (normalVector θ) = h - ε := by
    dsimp [q]
    rw [inner_sub_left, real_inner_smul_left, hmN]
    have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
      rw [← θ.coe_toReal]
      exact inner_normalVector_self θ.toReal
    rw [hNN, mul_one]
  have hzright (u : Set.Icc (0 : ℝ) 1) :
      0 ≤ inner ℝ (z u - q) (normalVector θ) := by
    rw [inner_sub_left, hzN, hqN]
    linarith
  have hzq (u : Set.Icc (0 : ℝ) 1) : z u ≠ q := by
    intro heq
    have := congrArg (fun w : Point ↦ inner ℝ w (normalVector θ)) heq
    rw [hzN, hqN] at this
    linarith
  have hzqLift : IsCurveAngleLift z q
      (fun u ↦ θ.toReal + Complex.arg (frameComplex θ (z u - q))) :=
    isCurveAngleLift_frameArg_of_inner_nonneg θ hz hzright hzq
  let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
  have hdouble : Continuous doubleParam := by
    exact Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
  have hy₁ : Continuous y₁ := hy.comp hdouble
  have hy₁qLift : IsCurveAngleLift y₁ q
      ((fun u ↦ θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi +
        Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (y u - m)) *
            Complex.orthonormalBasisOneI.repr.symm (y u - q))) ∘
          doubleParam) := hyqLift.comp hdouble
  have hjoin : z ⟨1, by norm_num⟩ = y₁ ⟨0, by norm_num⟩ := by
    simp [z, y₁, doubleParam, y]
  obtain ⟨hcorr_t, hcorr_s, harg_tm, harg_sm, hneg_frame_sm, hneg_frame_tm⟩ :=
    supporting_segment_argument_corrections (x s) (x t) θ d ε hd hε hdirection
  change Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x t - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x t - q)) =
        Complex.arg (frameComplex θ (x t - q)) - Real.pi / 2 at hcorr_t
  change Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x s - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x s - q)) =
        Complex.arg (frameComplex θ (x s - q)) + Real.pi / 2 at hcorr_s
  have hz0 : z ⟨0, by norm_num⟩ = x s := by simp [z]
  have hz1 : z ⟨1, by norm_num⟩ = x t := by simp [z]
  have hy₁0 : y₁ ⟨0, by norm_num⟩ = x t := by
    simp [y₁, doubleParam, y]
  have hy₁1 : y₁ ⟨1, by norm_num⟩ = x s := by
    simp [y₁, doubleParam, y]
  have hwinding : curveWinding (by norm_num)
      (Function.concatUnitIntervals z y₁) q = 1 := by
    rw [curveWinding_concatUnitIntervals hzqLift hy₁qLift hjoin,
      hzqLift.curveWinding_eq, hy₁qLift.curveWinding_eq]
    rw [hz1, hz0]
    simp only [Function.comp_apply]
    simp only [add_sub_add_left_eq_sub, cyclicComplement, mul_one, Function.concatUnitIntervals_two,
      Set.Icc.mk_one, Function.comp_apply, Set.Icc.convexComb_one,
      Complex.orthonormalBasisOneI_repr_symm_apply, Fin.isValue, map_add, map_sub,
        Complex.conj_ofReal, map_mul, Complex.conj_I,
      mul_neg, mul_zero, Function.concatUnitIntervals_zero, Set.Icc.mk_zero,
      Set.Icc.convexComb_zero, y, doubleParam]
    simp only [Complex.orthonormalBasisOneI_repr_symm_apply, Fin.isValue, map_add, map_sub,
      Complex.conj_ofReal, map_mul, Complex.conj_I,
      mul_neg] at hcorr_t hcorr_s
    rw [hneg_frame_sm, hneg_frame_tm, harg_tm, harg_sm, hcorr_t, hcorr_s]
    field_simp [Real.pi_ne_zero]
    ring
  have hrange_w := cyclic_partition_range hab x hclosed s t hst
  have hwinding_eq_x (p : Point) (hp : p ∉ Set.range x) :
      curveWinding (by norm_num) (Function.concatUnitIntervals z y₁) p =
        curveWinding hab.le x p := by
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_avoids hab hx hp
    let φst := Set.Icc.convexComb s t
    let φtb := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
    let φas := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
    have hzα : IsCurveAngleLift z p (α ∘ φst) := hα.comp (Set.Icc.continuous_convexComb _ _)
    have htbα : IsCurveAngleLift (x ∘ φtb) p (α ∘ φtb) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have hasα : IsCurveAngleLift (x ∘ φas) p (α ∘ φas) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have htailJoin : (x ∘ φtb) ⟨1, by norm_num⟩ = (x ∘ φas) ⟨0, by norm_num⟩ := by
      simpa [φtb, φas] using hclosed.symm
    have hyp : p ∉ Set.range y := by
      rintro ⟨u, rfl⟩
      apply hp
      unfold y cyclicComplement Function.concatUnitIntervals
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ := exists_curveAngleLift_of_avoids (by norm_num) hy hyp
    have hy₁wind : curveWinding (by norm_num) y₁ p = curveWinding (by norm_num) y p := by
      apply curveWinding_comp_of_endpoints (by norm_num) (by norm_num) ⟨β, hβ⟩ hdouble
      · apply Subtype.ext
        simp [doubleParam]
      · apply Subtype.ext
        simp [doubleParam]
    rw [curveWinding_concatUnitIntervals hzα (hβ.comp hdouble) hjoin, hy₁wind]
    change curveWinding (by norm_num) z p +
      curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φtb) (x ∘ φas)) p = _
    rw [curveWinding_concatUnitIntervals htbα hasα htailJoin]
    rw [hzα.curveWinding_eq, htbα.curveWinding_eq, hasα.curveWinding_eq,
      hα.curveWinding_eq]
    have hst0 : α (φst ⟨0, by norm_num⟩) = α s := congrArg α (by simp [φst])
    have hst1 : α (φst ⟨1, by norm_num⟩) = α t := congrArg α (by simp [φst])
    have htb0 : α (φtb ⟨0, by norm_num⟩) = α t := congrArg α (by simp [φtb])
    have htb1 : α (φtb ⟨1, by norm_num⟩) = α ⟨b, hab.le, le_rfl⟩ :=
      congrArg α (by simp [φtb])
    have has0 : α (φas ⟨0, by norm_num⟩) = α ⟨a, le_rfl, hab.le⟩ :=
      congrArg α (by simp [φas])
    have has1 : α (φas ⟨1, by norm_num⟩) = α s := congrArg α (by simp [φas])
    simp only [Function.comp_apply]
    rw [hst0, hst1, htb0, htb1, has0, has1]
    ring
  have hqrange : q ∉ Set.range x := by
    rw [← hrange_w]
    intro hq
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_curveWinding_ne_zero
      (a := 0) (b := 2) (by norm_num)
      (by rw [hwinding]; norm_num)
    obtain ⟨u, hu⟩ := hq
    have hc := (hα.2 u).1
    have hs := (hα.2 u).2
    rw [hu, sub_self] at hc hs
    simp at hc hs
    nlinarith only [hc, hs, Real.cos_sq_add_sin_sq (α u)]
  have hwinding_q : curveWinding hab.le x q = 1 := by
    rw [← hwinding_eq_x q hqrange, hwinding]
  exact jordan_counterclockwise_of_winding_one a b hab x hx hΓ hclosed hinj q
    hqrange hwinding_q

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Subarc
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set

/-- Reversing the parameter of a closed path preserves injectivity away from the
identified terminal endpoint. -/
theorem injOn_comp_reverse_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a < b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.InjOn (x ∘ Set.Icc.reverse hab.le) {t | (t : ℝ) < b} := by
  intro s hs t ht hst
  change (s : ℝ) < b at hs
  change (t : ℝ) < b at ht
  have hrs_pos : a < (Set.Icc.reverse hab.le s : ℝ) := by
    change a < a + b - (s : ℝ)
    linarith
  have hrt_pos : a < (Set.Icc.reverse hab.le t : ℝ) := by
    change a < a + b - (t : ℝ)
    linarith
  by_cases hrs : (Set.Icc.reverse hab.le s : ℝ) < b
  · by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · exact (Set.Icc.involutive_reverse hab.le).injective (hinj hrs hrt hst)
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      have hra : x (Set.Icc.reverse hab.le s) = x ⟨a, le_rfl, hab.le⟩ := by
        rw [hclosed, ← hrteq]
        exact hst
      have heq := hinj hrs hab hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
  · have hrseq : Set.Icc.reverse hab.le s = ⟨b, hab.le, le_rfl⟩ := by
      apply Subtype.ext
      exact le_antisymm (Set.Icc.reverse hab.le s).property.2 (le_of_not_gt hrs)
    by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · have hra : x ⟨a, le_rfl, hab.le⟩ = x (Set.Icc.reverse hab.le t) := by
        rw [hclosed, ← hrseq]
        exact hst
      have heq := hinj hab hrt hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      exact (Set.Icc.involutive_reverse hab.le).injective (hrseq.trans hrteq.symm)

/-- Parameter reversal sends the reversed closed interval to the original interval image. -/
theorem image_Icc_reverse_interval {α : Type*} {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → α) (l u : Set.Icc a b) (_hlu : l ≤ u) :
    (x ∘ Set.Icc.reverse hab) ''
        Set.Icc (Set.Icc.reverse hab u) (Set.Icc.reverse hab l) =
      x '' Set.Icc l u := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, rfl⟩
    constructor
    · simpa only [Set.Icc.involutive_reverse hab l] using
        Set.Icc.antitone_reverse hab hs.2
    · simpa only [Set.Icc.involutive_reverse hab u] using
        Set.Icc.antitone_reverse hab hs.1
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, ?_⟩
    · constructor
      · exact Set.Icc.antitone_reverse hab hs.2
      · exact Set.Icc.antitone_reverse hab hs.1
    · simp only [Function.comp_apply, Set.Icc.involutive_reverse hab s]

-- Duplicate of the current private UpperGraph helper; promote to Geometry.Support.
private theorem exists_Icc_coe_image_of_compact_connected_Ioo {a b : ℝ}
    {S : Set (Set.Ioo a b)} (hS : IsCompact S) (hconn : IsConnected S) :
    ∃ l u : ℝ, ((fun t : Set.Ioo a b ↦ (t : ℝ)) '' S) = Set.Icc l u := by
  let T := (fun t : Set.Ioo a b ↦ (t : ℝ)) '' S
  have hTc : IsCompact T := hS.image continuous_subtype_val
  have hTconn : IsConnected T := hconn.image _ continuous_subtype_val.continuousOn
  exact ⟨sInf T, sSup T, eq_Icc_of_connected_compact hTconn hTc⟩

private theorem exists_Icc_pullback_of_compact_connected_puncturedLoop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set (puncturedLoopRangeSet hab x)) (hC : IsCompact C)
    (hconn : IsConnected C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm '' C) =
        Set.Icc l u := by
  let e := openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj
  exact exists_Icc_coe_image_of_compact_connected_Ioo
    (hC.image e.symm.continuous) (hconn.image e.symm e.symm.continuous.continuousOn)

private theorem exists_Icc_parameters_of_compact_pathConnected_subset_loop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set Point) (hC : IsCompact C) (hpath : IsPathConnected C)
    (hCrange : C ⊆ Set.range x) (hbase : x ⟨a, le_rfl, hab⟩ ∉ C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm ''
            {q : puncturedLoopRangeSet hab x | (q : Point) ∈ C}) = Set.Icc l u := by
  let D : Set (puncturedLoopRangeSet hab x) := {q | (q : Point) ∈ C}
  let f : puncturedLoopRangeSet hab x → Point := fun q ↦ q
  have hf_ind : Topology.IsInducing f :=
    Topology.IsInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
      Topology.IsEmbedding.subtypeVal.isInducing
  have hCrange' : C ⊆ Set.range f := by
    intro p hp
    obtain ⟨t, ht⟩ := hCrange hp
    let q : Set.range x := ⟨p, ⟨t, ht⟩⟩
    have hq : (q : Point) ≠ x ⟨a, le_rfl, hab⟩ := by
      intro heq
      exact hbase (heq ▸ hp)
    exact ⟨⟨q, hq⟩, rfl⟩
  have hDcompact : IsCompact D := by
    change IsCompact (f ⁻¹' C)
    exact hf_ind.isCompact_preimage' hC hCrange'
  have hDrange : {q : Set.range x | (q : Point) ∈ C} ⊆ puncturedLoopRangeSet hab x := by
    intro q hq
    exact fun heq ↦ hbase (heq ▸ hq)
  have hDpath : IsPathConnected D := by
    have h₁ := hpath.preimage_coe hCrange
    exact h₁.preimage_coe hDrange
  exact exists_Icc_pullback_of_compact_connected_puncturedLoop hab hab' hx hclosed hinj
    D hDcompact hDpath.isConnected

private theorem exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u := by
  let y := ContinuousBVPaths.restrict x l u hlu
  have hyinj : Function.Injective y.val := by
    intro s t hst
    apply Subtype.ext
    have hs : (s : ℝ) < b := lt_of_le_of_lt s.property.2 hub
    have ht : (t : ℝ) < b := lt_of_le_of_lt t.property.2 hub
    have h := hx.2.2.2.2.2.1 hs ht hst
    exact congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) h
  let A0 : OrientedJordanArc :=
    { carrier := Set.range y.val
      startPoint := x.val l
      endPoint := x.val u
      parametrizable := ⟨l, u, hlu, y.val, y.property.1, hyinj, rfl, rfl, rfl⟩ }
  let p : ArcBVParametrization A0 :=
    { a := l, b := u, ordered := hlu, path := y, injective := hyinj,
      range_eq := rfl, start_eq := rfl, end_eq := rfl }
  exact ⟨⟨A0, ⟨p⟩⟩, rfl, rfl, rfl⟩

/-- Convex interpolation between ordered interval points is strictly increasing. -/
theorem strictMono_convexComb_of_lt {a b : ℝ}
    (l u : Set.Icc a b) (hlu : l < u) : StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- The two closed pieces outside an interior parameter interval trace exactly the
closed curve with the open interval image removed. -/
theorem image_complement_interval_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hal : a < l) (hub : (u : ℝ) < b) :
    x '' {t | t ≤ l ∨ u ≤ t} =
      Set.range x \ x '' {t | l < t ∧ t < u} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Set.mem_range_self t, ?_⟩
    rintro ⟨s, hs, heq⟩
    have hsb : (s : ℝ) < b := lt_trans hs.2 hub
    by_cases htb : (t : ℝ) < b
    · have hst := hinj hsb htb heq
      subst t
      exact ht.elim (not_le_of_gt hs.1) (not_le_of_gt hs.2)
    · have hte : t = ⟨b, hab, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm t.2.2 (le_of_not_gt htb)
      have hab' : a < b := hal.trans_le l.2.2
      have hsa : s = ⟨a, le_rfl, hab⟩ :=
        hinj hsb hab' (heq.trans ((congrArg x hte).trans hclosed.symm))
      have : (l : ℝ) < a := by
        have h := hs.1
        rw [hsa] at h
        exact h
      exact (not_lt_of_ge hal.le) this
  · rintro ⟨⟨t, rfl⟩, hp⟩
    refine ⟨t, ?_, rfl⟩
    by_contra ht
    have hs : l < t ∧ t < u := ⟨lt_of_not_ge (fun h ↦ ht (Or.inl h)),
      lt_of_not_ge (fun h ↦ ht (Or.inr h))⟩
    exact hp ⟨t, hs, rfl⟩

/-- Convex interpolation between the interval endpoints covers the interval. -/
theorem surjective_convexComb_endpoints (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective
      (Set.Icc.convexComb (⟨a, le_rfl, hab⟩ : Set.Icc a b) ⟨b, hab, le_rfl⟩) := by
  intro x
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨⟨0, by norm_num⟩, Subtype.ext ?_⟩
    change (1 - (0 : ℝ)) * a + 0 * a = (x : ℝ)
    have hx : (x : ℝ) = a := le_antisymm x.property.2 x.property.1
    simp [hx]
  · refine ⟨⟨((x : ℝ) - a) / (b - a), ?_⟩, Subtype.ext ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right x.property.2 a)
    · change (1 - ((x : ℝ) - a) / (b - a)) * a +
        ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

/-- The initial restriction of a cyclically concatenated closed path traces the
complement of an interior parameter interval. -/
theorem range_cyclicConcat_restrict_to_complement
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → α)
    (hclosed : f ⟨a, le_rfl, hab⟩ = f ⟨b, hab, le_rfl⟩)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l) :
    let v : ℝ := 1 + θ
    Set.range (fun z : Set.Icc (0 : ℝ) v ↦
      Function.concatUnitIntervals
        (f ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
        (f ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
        ⟨z, z.property.1, z.property.2.trans (by
          have hθle : (θ : ℝ) ≤ 1 := θ.property.2
          dsimp only [v]
          linarith)⟩) = f '' {z | z ≤ l ∨ u ≤ z} := by
  dsimp only
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : (z : ℝ) ≤ 1
    · let q : Set.Icc (0 : ℝ) 1 := ⟨z, z.property.1, hz⟩
      let y := Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q
      refine ⟨y, Or.inr ?_, ?_⟩
      · change (u : ℝ) ≤ (1 - (q : ℝ)) * u + (q : ℝ) * b
        nlinarith [q.property.1, q.property.2, u.property.2]
      · have hvnonneg : 0 ≤ 1 + (θ : ℝ) := by linarith [θ.property.1]
        have hzmem : (z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨z.property.1, hz⟩
        change f y = Function.concatUnitIntervals _ _
          (⟨z, z.property.1, z.property.2.trans (by linarith [θ.property.2])⟩ :
            Set.Icc (0 : ℝ) 2)
        simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) hzmem]
    · have hz1 : 1 < (z : ℝ) := lt_of_not_ge hz
      have hzsub0 : 0 ≤ (z : ℝ) - 1 := by linarith
      have hzsub1 : (z : ℝ) - 1 ≤ 1 := by
        have := z.property.2
        nlinarith [θ.property.2]
      let q : Set.Icc (0 : ℝ) 1 := ⟨(z : ℝ) - 1, hzsub0, hzsub1⟩
      let y := Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q
      refine ⟨y, Or.inl ?_, ?_⟩
      · have hzθ : (q : ℝ) ≤ θ := by
          dsimp only [q]
          linarith [z.property.2]
        change (1 - (q : ℝ)) * a + (q : ℝ) * u ≤ (l : ℝ)
        have hθval := congrArg Subtype.val hθ
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        nlinarith [hzθ, le_of_lt (lt_trans hal hlu)]
      · simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) ⟨hzsub0, hzsub1⟩]
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hyl | huy
    · let y' : Set.Icc a (u : ℝ) := ⟨y, y.property.1, hyl.trans hlu.le⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints a u
        (le_trans l.property.1 hlu.le) y'
      have hq : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      have hqθ : (q : ℝ) ≤ θ := by
        have hqval := congrArg Subtype.val hq
        have hθval := congrArg Subtype.val hθ
        change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        have hau : a < (u : ℝ) := hal.trans hlu
        by_contra hn
        have hθq : (θ : ℝ) < q := lt_of_not_ge hn
        have hprod : 0 < ((q : ℝ) - θ) * ((u : ℝ) - a) :=
          mul_pos (sub_pos.mpr hθq) (sub_pos.mpr hau)
        have : (l : ℝ) < y := by nlinarith [hqval, hθval, hprod]
        exact (not_lt_of_ge hyl) this
      by_cases hq0 : (q : ℝ) = 0
      · let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨1, by
          constructor
          · norm_num
          · linarith [θ.property.1]⟩
        refine ⟨z, ?_⟩
        have hyA : y = ⟨a, le_rfl, hab⟩ := by
          apply Subtype.ext
          have hqval := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hq
          change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
          simp [hq0] at hqval
          exact hqval.symm
        rw [hyA, hclosed]
        simp [z, Function.comp_def]
      · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
        let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨(q : ℝ) + 1, by
          constructor <;> linarith⟩
        refine ⟨z, ?_⟩
        have hznot : ¬(z : ℝ) ≤ 1 := by dsimp only [z]; linarith
        rw [← hq]
        simp [z, Function.concatUnitIntervals, hznot,
          Set.projIcc_of_mem (by norm_num) q.property]
    · let y' : Set.Icc (u : ℝ) b := ⟨y, huy, y.property.2⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints u b hub.le y'
      have hq : Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc (u : ℝ) b ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨q, by
        constructor
        · exact q.property.1
        · linarith [q.property.2, θ.property.1]⟩
      refine ⟨z, ?_⟩
      have hzle : (z : ℝ) ≤ 1 := q.property.2
      rw [← hq]
      simp [z, Function.concatUnitIntervals, hzle,
        Set.projIcc_of_mem (by norm_num) q.property]

private theorem exists_complementary_rectifiableOrientedArc
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let l' : Set.Icc a (u : ℝ) := ⟨l, l.property.1, hlu.le⟩
  obtain ⟨θ, hθ'⟩ := surjective_convexComb_endpoints a u
    (le_trans l.property.1 hlu.le) l'
  have hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l := by
    apply Subtype.ext
    have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hθ'
    simpa only [Set.Icc.coe_convexComb] using h
  have hθpos : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  obtain ⟨r, hrJordan, hr⟩ :=
    exists_oriented_cyclic_rotation_eq_concat hab x hx u
      (hal.trans hlu) hub
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith⟩
  have hzv : z ≤ v := by change (0 : ℝ) ≤ 1 + θ; linarith
  have hvtop : (v : ℝ) < 2 := by dsimp only [v]; linarith
  obtain ⟨A, hAcarrier, hAstart, hAend⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
      (a := 0) (b := 2) (x := r) (Γ := Γ) (by norm_num) hrJordan z v hzv hvtop
  have hrzero : r.val z = P := by
    rw [hr]
    simp [z, Function.comp_def, huP]
  have hrv : r.val v = Q := by
    rw [hr]
    have hvnot : ¬(v : ℝ) ≤ 1 := by dsimp only [v]; linarith
    have hθmem : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ.property
    have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) ((v : ℝ) - 1) = θ := by
      apply Subtype.ext
      simp [v]
    simp [Function.concatUnitIntervals, hvnot, hproj, hθ, hlQ]
  refine ⟨A, ?_, hAstart.trans hrzero, hAend.trans hrv⟩
  rw [hAcarrier]
  have hrange : Set.range (ContinuousBVPaths.restrict r z v hzv).val =
      Set.range (fun w : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) ↦
        Function.concatUnitIntervals
          (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
          (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
          ⟨w, w.property.1, w.property.2.trans (by linarith [θ.property.2])⟩) := by
    change Set.range (r.val ∘ fun w : Set.Icc (0 : ℝ) (v : ℝ) ↦
      (⟨w, w.property.1, w.property.2.trans v.property.2⟩ : Set.Icc (0 : ℝ) 2)) = _
    rw [hr]
    rfl
  rw [hrange, range_cyclicConcat_restrict_to_complement hab x.val
    hx.2.2.2.2.1 l u hal hlu hub θ hθ]
  exact image_complement_interval_of_closed_injOn hab x.val hx.2.2.2.2.1
    hx.2.2.2.2.2.1 l u hal hub

/-- If a closed parameter interval traces a nondegenerate segment injectively, its
open interval traces the segment with its endpoints removed. -/
theorem image_Ioo_eq_segment_diff_endpoints_of_image_Icc
    {a b : ℝ} {x : Set.Icc a b → Point}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x l = Q) (hu : x u = P)
    (himage : x '' Set.Icc l u = segment ℝ P Q) :
    x '' {z | l < z ∧ z < u} = segment ℝ P Q \ {P, Q} := by
  apply Set.Subset.antisymm
  · rintro p ⟨z, hz, rfl⟩
    refine ⟨himage ▸ ⟨z, ⟨hz.1.le, hz.2.le⟩, rfl⟩, ?_⟩
    intro hp
    rcases hp with hp | hp
    · have hzu := hinj (show (z : ℝ) < b from lt_trans hz.2 hub) hub
        (hp.trans hu.symm)
      exact (ne_of_lt hz.2) hzu
    · have hzl := hinj (show (z : ℝ) < b from lt_trans hz.2 hub)
        (show (l : ℝ) < b from lt_trans hlu hub) (hp.trans hl.symm)
      exact (ne_of_gt hz.1) hzl
  · rintro p ⟨hpseg, hpends⟩
    rw [← himage] at hpseg
    obtain ⟨z, hz, rfl⟩ := hpseg
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · refine lt_of_le_of_ne hz.1 ?_
      intro h
      apply hpends
      exact Or.inr ((congrArg x h).symm.trans hl)
    · refine lt_of_le_of_ne hz.2 ?_
      intro h
      apply hpends
      exact Or.inl ((congrArg x h).trans hu)

private theorem exists_rectifiableOrientedArc_of_cut_parametrization
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  obtain ⟨A, hA, hstart, hend⟩ :=
    exists_complementary_rectifiableOrientedArc hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend⟩
  rw [hA, hx.2.2.2.1, hfrontier,
    image_Ioo_eq_segment_diff_endpoints_of_image_Icc
      hx.2.2.2.2.2.1 l u hlu hub P Q hl hu himage]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with hpU | hpseg
    · exact hpU
    · have hpends : p ∈ ({P, Q} : Set Point) := by
        by_contra hn
        exact hpnot ⟨hpseg, hn⟩
      rw [← hinter] at hpends
      exact hpends.1
  · intro hpU
    refine ⟨Or.inl hpU, ?_⟩
    rintro ⟨hpseg, hpnotends⟩
    apply hpnotends
    rw [← hinter]
    exact ⟨hpU, hpseg⟩

/-- A nondegenerate segment in a closed Jordan curve, away from the base point,
is traced by an interior parameter interval. -/
theorem exists_parameter_interval_of_segment_subset_closedJordan
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q) (hsegment : segment ℝ P Q ⊆ Γ)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q) :
    ∃ l u : Set.Icc a b, a < l ∧ l < u ∧ (u : ℝ) < b ∧
      x.val '' Set.Icc l u = segment ℝ P Q := by
  have hcompact : IsCompact (segment ℝ P Q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hpath : IsPathConnected (segment ℝ P Q) :=
    (convex_segment P Q).isPathConnected ⟨P, left_mem_segment ℝ P Q⟩
  have hCrange : segment ℝ P Q ⊆ Set.range x.val := by
    rw [hx.2.2.2.1]
    exact hsegment
  obtain ⟨l, u, hlu⟩ := exists_Icc_parameters_of_compact_pathConnected_subset_loop
    hab.le hab x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1
    (segment ℝ P Q) hcompact hpath hCrange hbase
  have hpre_nonempty :
      ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
        {q : puncturedLoopRangeSet hab.le x.val | (q : Point) ∈ segment ℝ P Q}).Nonempty := by
    let q : Set.range x.val := ⟨P, hCrange (left_mem_segment ℝ P Q)⟩
    have hq : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
      intro heq
      exact hbase (heq ▸ left_mem_segment ℝ P Q)
    let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hq⟩
    refine ⟨(openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
      hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q', ?_⟩
    exact ⟨q', left_mem_segment ℝ P Q, rfl⟩
  have hIcc_nonempty : (Set.Icc l u).Nonempty := by
    rw [← hlu]
    exact hpre_nonempty.image _
  have hlu_order : l ≤ u := Set.nonempty_Icc.mp hIcc_nonempty
  have hlmem : l ∈ Set.Icc l u := ⟨le_rfl, hlu_order⟩
  have humem : u ∈ Set.Icc l u := ⟨hlu_order, le_rfl⟩
  rw [← hlu] at hlmem humem
  obtain ⟨sl, hsl, hslval⟩ := hlmem
  obtain ⟨su, hsu, hsuval⟩ := humem
  change (sl : ℝ) = l at hslval
  change (su : ℝ) = u at hsuval
  let l' : Set.Icc a b := ⟨sl, sl.property.1.le, sl.property.2.le⟩
  let u' : Set.Icc a b := ⟨su, su.property.1.le, su.property.2.le⟩
  have hlstrict : a < (l' : ℝ) := sl.property.1
  have hustricttop : (u' : ℝ) < b := su.property.2
  have hlu' : l' ≤ u' := by
    change (sl : ℝ) ≤ su
    linarith
  have himage : x.val '' Set.Icc l' u' = segment ℝ P Q := by
    apply Set.Subset.antisymm
    · rintro p ⟨s, hs, rfl⟩
      let si : Set.Ioo a b := ⟨s, lt_of_lt_of_le hlstrict hs.1,
        lt_of_le_of_lt hs.2 hustricttop⟩
      have hscoord : (s : ℝ) ∈
          (fun z : Set.Ioo a b ↦ (z : ℝ)) ''
            ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
              hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
              {q : puncturedLoopRangeSet hab.le x.val |
                (q : Point) ∈ segment ℝ P Q}) := by
        rw [hlu]
        change l ≤ (s : ℝ) ∧ (s : ℝ) ≤ u
        constructor
        · calc l = (sl : ℝ) := hslval.symm
               _ ≤ s := hs.1
        · calc (s : ℝ) ≤ su := hs.2
               _ = u := hsuval
      obtain ⟨z, hz, hzval⟩ := hscoord
      obtain ⟨q, hqseg, hzq⟩ := hz
      have hzcoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 z
      have hzs : z = si := Subtype.ext hzval
      rw [hzs] at hzcoe hzq
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e si = q := by
        exact e.eq_symm_apply.mp hzq.symm
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      rw [hzcoe] at heq'
      change (q : Point) ∈ segment ℝ P Q at hqseg
      have heq'' : x.val s = (q : Point) := by simpa [si] using heq'
      rw [heq'']
      exact hqseg
    · intro p hp
      let q : Set.range x.val := ⟨p, hCrange hp⟩
      have hqbase : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
        intro heq
        exact hbase (heq ▸ hp)
      let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hqbase⟩
      let s := (openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q'
      have hscoord : (s : ℝ) ∈ Set.Icc l u := by
        rw [← hlu]
        exact ⟨s, ⟨q', hp, rfl⟩, rfl⟩
      let s' : Set.Icc a b := ⟨s, s.property.1.le, s.property.2.le⟩
      refine ⟨s', ?_, ?_⟩
      · change l' ≤ s' ∧ s' ≤ u'
        constructor <;> change (_ : ℝ) ≤ _ <;> dsimp only [l', u', s'] <;>
          linarith [hscoord.1, hscoord.2]
      have hscoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 s
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e s = q' := e.apply_symm_apply q'
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      exact hscoe.symm.trans heq'
  have hlune : l' ≠ u' := by
    intro heq
    have hsingle : segment ℝ P Q = {x.val l'} := by
      rw [← himage, heq, Set.Icc_self, Set.image_singleton]
    have hPm : P ∈ ({x.val l'} : Set Point) := hsingle ▸ left_mem_segment ℝ P Q
    have hQm : Q ∈ ({x.val l'} : Set Point) := hsingle ▸ right_mem_segment ℝ P Q
    exact hPQ (by simpa using hPm.trans hQm.symm)
  exact ⟨l', u', hlstrict, lt_of_le_of_ne hlu' hlune,
    hustricttop, himage⟩

private theorem inner_sub_right_injOn_segment (P Q : Point) (hPQ : P ≠ Q) :
    Set.InjOn (fun p : Point ↦ inner ℝ (p - P) (Q - P)) (segment ℝ P Q) := by
  intro p hp q hq hpq
  rw [segment_eq_image' ℝ P Q] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hd : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hnorm : 0 < ‖Q - P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hst : s = t := by
    simp only [add_sub_cancel_left, inner_smul_left, real_inner_self_eq_norm_sq] at hpq
    have hpq' : s * ‖Q - P‖ ^ 2 = t * ‖Q - P‖ ^ 2 := by simpa using hpq
    nlinarith
  rw [hst]

private theorem exists_rectifiableOrientedArc_reverse (A : RectifiableOrientedArc) :
    ∃ B : RectifiableOrientedArc,
      B.val.carrier = A.val.carrier ∧ B.val.startPoint = A.val.endPoint ∧
        B.val.endPoint = A.val.startPoint := by
  let p := Classical.choice A.property
  let r := Set.Icc.reverse p.ordered
  let y : ContinuousBVPaths p.a p.b :=
    ⟨p.path.val ∘ r, p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered),
      fun i ↦ BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
          (Set.Icc.surjective_reverse p.ordered)⟩
  have hyinj : Function.Injective y.val :=
    p.injective.comp (Set.Icc.involutive_reverse p.ordered).injective
  have hyrange : Set.range y.val = A.val.carrier := by
    have hrange : Set.range y.val = Set.range p.path.val := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, rfl⟩
        exact ⟨r t, rfl⟩
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hs⟩ := Set.Icc.surjective_reverse p.ordered t
        refine ⟨s, ?_⟩
        change p.path.val (r s) = p.path.val t
        rw [show r s = t by exact hs]
    rw [hrange]
    exact p.range_eq
  have hystart : y.val ⟨p.a, le_rfl, p.ordered⟩ = A.val.endPoint := by
    simpa [y, r, Set.Icc.reverse] using p.end_eq
  have hyend : y.val ⟨p.b, p.ordered, le_rfl⟩ = A.val.startPoint := by
    simpa [y, r, Set.Icc.reverse] using p.start_eq
  let B0 : OrientedJordanArc :=
    { carrier := A.val.carrier
      startPoint := A.val.endPoint
      endPoint := A.val.startPoint
      parametrizable := ⟨p.a, p.b, p.ordered, y.val, y.property.1, hyinj,
        hyrange, hystart, hyend⟩ }
  let q : ArcBVParametrization B0 :=
    { a := p.a
      b := p.b
      ordered := p.ordered
      path := y
      injective := hyinj
      range_eq := hyrange
      start_eq := hystart
      end_eq := hyend }
  exact ⟨⟨B0, ⟨q⟩⟩, rfl, rfl, rfl⟩

/-- The endpoints of an injectively parametrized nondegenerate segment are the
parameter-interval endpoints, in one of the two possible orders. -/
theorem endpoints_eq_or_eq_swap_of_image_Icc_eq_segment
    {a b : ℝ} {x : ContinuousBVPaths a b}
    (hab : a ≤ b) (hinj : Set.InjOn x.val {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    (x.val l = P ∧ x.val u = Q) ∨ (x.val l = Q ∧ x.val u = P) := by
  let f : ℝ → ℝ := fun t ↦
    inner ℝ (x.val (Set.projIcc a b hab t) - P) (Q - P)
  have hf_cont : Continuous f := by
    exact (x.property.1.comp continuous_projIcc).sub continuous_const |>.inner
      continuous_const
  have hproj (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      Set.projIcc a b hab t =
        ⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩ := by
    exact Set.projIcc_of_mem hab ⟨l.property.1.trans ht.1, ht.2.trans u.property.2⟩
  have hparam (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      x.val (Set.projIcc a b hab t) ∈ segment ℝ P Q := by
    rw [← himage]
    refine ⟨⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩, ?_, ?_⟩
    · exact ht
    · apply congrArg x.val
      apply Subtype.ext
      exact congrArg Subtype.val (hproj t ht).symm
  have hf_inj : Set.InjOn f (Set.Icc (l : ℝ) u) := by
    intro s hs t ht hst
    have hxs := inner_sub_right_injOn_segment P Q hPQ
      (hparam s hs) (hparam t ht) hst
    have hst' := hinj
      (show ((Set.projIcc a b hab s : Set.Icc a b) : ℝ) < b by
        simpa [hproj s hs] using lt_of_le_of_lt hs.2 hub)
      (show ((Set.projIcc a b hab t : Set.Icc a b) : ℝ) < b by
        simpa [hproj t ht] using lt_of_le_of_lt ht.2 hub)
      hxs
    simpa [hproj s hs, hproj t ht] using congrArg Subtype.val hst'
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc'
    (show (l : ℝ) ≤ u from hlu.le) hf_cont.continuousOn hf_inj
  have hP : P ∈ x.val '' Set.Icc l u := himage ▸ left_mem_segment ℝ P Q
  have hQ : Q ∈ x.val '' Set.Icc l u := himage ▸ right_mem_segment ℝ P Q
  obtain ⟨s, hs, hsP⟩ := hP
  obtain ⟨t, ht, htQ⟩ := hQ
  have hs' : (s : ℝ) ∈ Set.Icc (l : ℝ) u := hs
  have ht' : (t : ℝ) ∈ Set.Icc (l : ℝ) u := ht
  have hl' : (l : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨le_rfl, hlu.le⟩
  have hu' : (u : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨hlu.le, le_rfl⟩
  rcases hmono with hmono | hanti
  · left
    constructor
    · have hfls : f l ≤ f s := hmono.monotoneOn hl' hs' hs.1
      have hflP : f l = f s := by
        have hnonneg : 0 ≤ f l := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam s hs') hflP |>.trans
            (by simpa [hproj s hs'] using hsP))
    · have hftu : f t ≤ f u := hmono.monotoneOn ht' hu' ht.2
      have hfuQ : f u = f t := by
        have hupper : f u ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam t ht') hfuQ |>.trans
            (by simpa [hproj t ht'] using htQ))
  · right
    constructor
    · have hftl : f t ≤ f l := hanti.antitoneOn hl' ht' ht.1
      have hflQ : f l = f t := by
        have hupper : f l ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam t ht') hflQ |>.trans
            (by simpa [hproj t ht'] using htQ))
    · have hfus : f u ≤ f s := hanti.antitoneOn hs' hu' hs.2
      have hfuP : f u = f s := by
        have hnonneg : 0 ≤ f u := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam s hs') hfuP |>.trans
            (by simpa [hproj s hs'] using hsP))

/-- Removing a supporting chord from a counterclockwise closed Jordan path yields the oriented
complementary arc. -/
theorem exists_rectifiableOrientedArc_of_closedJordan_cut
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q}) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan hab hx P Q hPQ hsegment hbase
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hend | hend
  · have hfrontier' : Γ = U ∪ segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using hfrontier
    have hinter' : U ∩ segment ℝ Q P = {Q, P} := by
      rw [segment_symm ℝ Q P, hinter]
      exact Set.pair_comm P Q
    have himage' : x.val '' Set.Icc l u = segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using himage
    obtain ⟨A, hA, hstart, hend'⟩ :=
      exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
        Q P hend.1 hend.2 hfrontier' hinter' himage'
    obtain ⟨B, hB, hBstart, hBend⟩ := exists_rectifiableOrientedArc_reverse A
    exact ⟨B, hB.trans hA, hBstart.trans hend', hBend.trans hstart⟩
  · exact exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Reparametrization
-/

@[expose] public section

namespace MovingSofa

theorem curveArea_reparametrization :
    (∀ (a b c d : ℝ), a < b → c < d →
      ∀ (x : ContinuousBVPaths a b) (φ : Set.Icc c d → Set.Icc a b),
      Continuous φ → Function.Surjective φ → (Monotone φ ∨ Antitone φ) →
      ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
        (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
        (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x)) ∧
    (∀ (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
      (y : ArcBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (Γ Δ : OrientedJordanCurve) (x : ClosedBVParametrization Γ)
      (y : ClosedBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (a b : ℝ) (x : ContinuousBVPaths a b) (p : Point),
      (∀ t, x.val t = p) → curveAreaFunctional x = 0) := by
  refine ⟨?_, curveArea_arc_same_carrier, ?_, ?_⟩
  · intro a b c d hab hcd x φ hφc hφs hφ
    exact curveArea_comp_monotone_or_antitone_surjective hab.le hcd.le x φ hφc hφs hφ
  · exact curveArea_closed_same_carrier
  · intro a b x p hx
    exact curveAreaFunctional_eq_zero_of_constant x p hx

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Segment Area Properties
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

theorem segmentArea_jordan_and_frame (p q : Point) :
    (∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ p q ∧ A.val.startPoint = p ∧ A.val.endPoint = q ∧
      jordanArcArea A = segmentArea p q) ∧
    (∀ (t : Real.Angle) (h d : ℝ), p ∈ normalLine t h → q ∈ normalLine t h →
      q - p = d • tangentVector t → segmentArea p q = h * d / 2) := by
  constructor
  · by_cases hpq : p = q
    · subst q
      let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p p
          startPoint := p
          endPoint := p
          parametrizable := by
            refine ⟨0, 0, le_rfl, (constBVPath 0 0 p).val,
              (constBVPath 0 0 p).property.1, ?_, ?_, rfl, rfl⟩
            · intro s t _
              apply Subtype.ext
              exact le_antisymm (s.property.2.trans t.property.1)
                (t.property.2.trans s.property.1)
            · simp [constBVPath] }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 0
          ordered := le_rfl
          path := constBVPath 0 0 p
          injective := by
            intro s t _
            apply Subtype.ext
            exact le_antisymm (s.property.2.trans t.property.1)
              (t.property.2.trans s.property.1)
          range_eq := by simp [constBVPath, Γ]
          start_eq := rfl
          end_eq := rfl }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p p
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = 0 := curveArea_reparametrization.2.2.2 0 0 z.path p (by intro t; rfl)
        _ = segmentArea p p := by simp [segmentArea, planeCrossProduct]; ring
    · let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p q
          startPoint := p
          endPoint := q
          parametrizable := by
            refine ⟨0, 1, by norm_num, Path.segment p q,
              (Path.segment p q).continuous, Path.segment_injective_of_ne hpq,
              Path.range_segment p q, ?_, ?_⟩
            · simp
            · simp }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 1
          ordered := by norm_num
          path := lineSegmentBVPath p q
          injective := Path.segment_injective_of_ne hpq
          range_eq := Path.range_segment p q
          start_eq := by simp [lineSegmentBVPath, Γ]
          end_eq := by simp [lineSegmentBVPath, Γ] }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p q
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = segmentArea p q := curveAreaFunctional_lineSegmentBVPath p q
  · intro t h d hp hq hd
    simp only [normalLine, Set.mem_ofPred_eq, segmentArea, planeCrossProduct] at hp hq ⊢
    have hd0 := congrArg (fun x : Point => x 0) hd
    have hd1 := congrArg (fun x : Point => x 1) hd
    simp only [normalVector, frame, Fin.isValue, PiLp.sub_apply, tangentVector, PiLp.smul_apply,
      Matrix.cons_val_zero, smul_eq_mul, mul_neg, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj'] at hp hq hd0 hd1 ⊢
    rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at hp hq
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hp hq
    have hq0 : q.ofLp 0 = p.ofLp 0 - d * t.sin := by linarith [hd0]
    have hq1 : q.ofLp 1 = p.ofLp 1 + d * t.cos := by linarith [hd1]
    rw [hq0, hq1]
    calc
      p.ofLp 0 * (p.ofLp 1 + d * t.cos) - p.ofLp 1 * (p.ofLp 0 - d * t.sin) =
          d * (p.ofLp 0 * t.cos + p.ofLp 1 * t.sin) := by ring
      _ = d * h := by rw [hp]
      _ = h * d := by ring

theorem segmentArea_collinear_origin (p q : Point)
    (h : Collinear ℝ ({0, p, q} : Set Point)) : segmentArea p q = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : (0 : Point) ∈ ({0, p, q} : Set Point))).mp h
  obtain ⟨a, ha⟩ := hv p (by simp)
  obtain ⟨b, hb⟩ := hv q (by simp)
  simp only [vadd_eq_add, add_zero] at ha hb
  rw [ha, hb]
  simp [segmentArea, planeCrossProduct]
  ring

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Curve / Jordan / Subarc Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open Set
/-- A proper restriction of a closed BV Jordan parametrization realizes an arc with the same
signed area as the restricted path. -/
theorem exists_rectifiableOrientedArc_restrict_closedJordan_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u ∧
      jordanArcArea A =
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
  let y := ContinuousBVPaths.restrict x l u hlu
  have hyinj : Function.Injective y.val := by
    intro s t hst
    apply Subtype.ext
    have hs : (s : ℝ) < b := lt_of_le_of_lt s.property.2 hub
    have ht : (t : ℝ) < b := lt_of_le_of_lt t.property.2 hub
    have h := hx.2.2.2.2.2.1 hs ht hst
    exact congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) h
  let A0 : OrientedJordanArc :=
    { carrier := Set.range y.val
      startPoint := x.val l
      endPoint := x.val u
      parametrizable := ⟨l, u, hlu, y.val, y.property.1, hyinj, rfl, rfl, rfl⟩ }
  let p : ArcBVParametrization A0 :=
    { a := l, b := u, ordered := hlu, path := y, injective := hyinj,
      range_eq := rfl, start_eq := rfl, end_eq := rfl }
  let A : RectifiableOrientedArc := ⟨A0, ⟨p⟩⟩
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  change curveAreaFunctional (Classical.choice A.property).path = curveAreaFunctional y
  exact (curveArea_reparametrization.2.1 A0 A0
    (Classical.choice A.property) p rfl).1 rfl rfl

/-- The suffix of the cyclic rotation, after the complementary arc, is an increasing
reparametrization of the removed interval. -/
theorem curveArea_cyclicSuffix_eq_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l)
    (r : ContinuousBVPaths 0 2)
    (hr : r.val = Function.concatUnitIntervals
      (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
      (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)) :
    let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
      constructor <;> linarith [θ.property.1, θ.property.2]⟩
    curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith [θ.property.1, θ.property.2]⟩
  change curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2) =
    curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le)
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  have hθpos_suffix : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hvlt : (v : ℝ) < 2 := by dsimp only [v]; linarith
  let ψ : Set.Icc (v : ℝ) 2 → Set.Icc (0 : ℝ) 1 := fun w ↦
    ⟨((w : ℝ) - (v : ℝ)) / (2 - (v : ℝ)), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr w.property.1) (sub_nonneg.mpr hvlt.le)
      · exact (div_le_one (sub_pos.mpr hvlt)).2
          (sub_le_sub_right w.property.2 (v : ℝ))⟩
  let φ : Set.Icc (v : ℝ) 2 → Set.Icc (l : ℝ) u := fun w ↦
    Set.Icc.convexComb (⟨l, le_rfl, hlu.le⟩ : Set.Icc (l : ℝ) u)
      ⟨u, hlu.le, le_rfl⟩ (ψ w)
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hψm : Monotone ψ := by
    intro s t hst
    apply Subtype.coe_le_coe.mp
    dsimp only [ψ]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (sub_nonneg.mpr hvlt.le)
  have hψs : Function.Surjective ψ := by
    intro q
    let w : Set.Icc (v : ℝ) 2 := ⟨(v : ℝ) + (2 - (v : ℝ)) * (q : ℝ), by
      constructor
      · nlinarith [q.property.1, sub_pos.mpr hvlt]
      · nlinarith [q.property.2, sub_pos.mpr hvlt]⟩
    refine ⟨w, Subtype.ext ?_⟩
    dsimp only [ψ, w]
    field_simp [ne_of_gt (sub_pos.mpr hvlt)]
    ring
  have hφc : Continuous φ :=
    (Set.Icc.continuous_convexComb _ _).comp hψc
  have hφm : Monotone φ := by
    intro s t hst
    change (1 - (ψ s : ℝ)) * (l : ℝ) + (ψ s : ℝ) * (u : ℝ) ≤
      (1 - (ψ t : ℝ)) * (l : ℝ) + (ψ t : ℝ) * (u : ℝ)
    have hψ := show (ψ s : ℝ) ≤ ψ t from hψm hst
    nlinarith [show (l : ℝ) < u from hlu]
  have hφs : Function.Surjective φ :=
    (surjective_convexComb_endpoints (l : ℝ) u hlu.le).comp hψs
  let xu := ContinuousBVPaths.restrict x l u hlu.le
  obtain ⟨y, hy, hyarea⟩ := curveArea_comp_monotone_surjective
    hlu.le v.property.2 xu φ hφc hφm hφs
  have hyval : y.val = (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2).val := by
    rw [hy]
    funext w
    simp only [xu, ContinuousBVPaths.restrict, Function.comp_apply]
    rw [hr]
    have hwlow : 1 + (θ : ℝ) ≤ (w : ℝ) := w.property.1
    have hwsub : (w : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [w.property.2]
    have hwnle : ¬(w : ℝ) ≤ 1 := by
      linarith
    simp only [Function.concatUnitIntervals, hwnle, ↓reduceIte,
      Set.projIcc_of_mem (by norm_num) hwsub]
    apply congrArg x.val
    apply Subtype.ext
    have hθval := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
    dsimp only [φ, ψ]
    simp only [Set.Icc.coe_convexComb]
    dsimp only [v]
    rw [← hθval]
    have hdenne : 2 - (1 + (θ : ℝ)) ≠ 0 := by linarith
    field_simp [hdenne]
    ring
  have hyEq : y = ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2 := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun hyval w)
  rw [← hyEq, hyarea]

private theorem exists_complementary_rectifiableOrientedArc_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  let l' : Set.Icc a (u : ℝ) := ⟨l, l.property.1, hlu.le⟩
  obtain ⟨θ, hθ'⟩ := surjective_convexComb_endpoints a u
    (le_trans l.property.1 hlu.le) l'
  have hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l := by
    apply Subtype.ext
    have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hθ'
    simpa only [Set.Icc.coe_convexComb] using h
  have hθpos : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  obtain ⟨r, hrJordan, hr⟩ :=
    exists_oriented_cyclic_rotation_eq_concat hab x hx u
      (hal.trans hlu) hub
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith⟩
  have hzv : z ≤ v := by change (0 : ℝ) ≤ 1 + θ; linarith
  have hvtop : (v : ℝ) < 2 := by dsimp only [v]; linarith
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
      (a := 0) (b := 2) (x := r) (Γ := Γ) (by norm_num) hrJordan z v hzv hvtop
  have hrzero : r.val z = P := by
    rw [hr]
    simp [z, Function.comp_def, huP]
  have hrv : r.val v = Q := by
    rw [hr]
    have hvnot : ¬(v : ℝ) ≤ 1 := by dsimp only [v]; linarith
    have hθmem : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ.property
    have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) ((v : ℝ) - 1) = θ := by
      apply Subtype.ext
      simp [v]
    simp [Function.concatUnitIntervals, hvnot, hproj, hθ, hlQ]
  have hcarrier : A.val.carrier =
      Set.range x.val \ x.val '' {z | l < z ∧ z < u} := by
    rw [hAcarrier]
    have hrange : Set.range (ContinuousBVPaths.restrict r z v hzv).val =
        Set.range (fun w : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) ↦
          Function.concatUnitIntervals
            (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
            (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
            ⟨w, w.property.1, w.property.2.trans (by linarith [θ.property.2])⟩) := by
      change Set.range (r.val ∘ fun w : Set.Icc (0 : ℝ) (v : ℝ) ↦
        (⟨w, w.property.1, w.property.2.trans v.property.2⟩ : Set.Icc (0 : ℝ) 2)) = _
      rw [hr]
      rfl
    rw [hrange, range_cyclicConcat_restrict_to_complement hab x.val
      hx.2.2.2.2.1 l u hal hlu hub θ hθ]
    exact image_complement_interval_of_closed_injOn hab x.val hx.2.2.2.2.1
      hx.2.2.2.2.2.1 l u hal hub
  have hsuffix : curveAreaFunctional
      (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) :=
    curveArea_cyclicSuffix_eq_restriction hab x l u hal hlu θ hθ r hr
  obtain ⟨r', hr', _, hrotate'⟩ :=
    exists_cyclic_rotation_eq_concat hab x u hx.2.2.2.2.1.symm
  have hrr : r = r' := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun (hr.trans hr'.symm) w)
  have hrotate : curveAreaFunctional r = curveAreaFunctional x := by
    rw [hrr]
    exact hrotate'
  have hsplit := curveArea_eq_restriction_add_restriction (by norm_num) r v
  dsimp only at hsplit
  refine ⟨A, hcarrier, hAstart.trans hrzero, hAend.trans hrv, ?_⟩
  rw [← hrotate, hsplit, ← hAarea, hsuffix]

private theorem exists_rectifiableOrientedArc_of_cut_parametrization_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  obtain ⟨A, hA, hstart, hend, harea⟩ :=
    exists_complementary_rectifiableOrientedArc_with_area
      hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend, harea⟩
  rw [hA, hx.2.2.2.1, hfrontier,
    image_Ioo_eq_segment_diff_endpoints_of_image_Icc
      hx.2.2.2.2.2.1 l u hlu hub P Q hl hu himage]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with hpU | hpseg
    · exact hpU
    · have hpends : p ∈ ({P, Q} : Set Point) := by
        by_contra hn
        exact hpnot ⟨hpseg, hn⟩
      rw [← hinter] at hpends
      exact hpends.1
  · intro hpU
    refine ⟨Or.inl hpU, ?_⟩
    rintro ⟨hpseg, hpnotends⟩
    apply hpnotends
    rw [← hinter]
    exact ⟨hpU, hpseg⟩

theorem endpoints_eq_of_counterclockwise_supporting_chord
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q)
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    x.val l = Q ∧ x.val u = P := by
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hbad | hgood
  · exfalso
    let r := Set.Icc.reverse hab.le
    let y : Set.Icc a b → Point := x.val ∘ r
    let l' := r u
    let u' := r l
    have hl'u' : l' < u' := by
      have hlu' : (l : ℝ) < u := hlu
      change a + b - (u : ℝ) < a + b - (l : ℝ)
      linarith
    have hyrange : Set.range y = Γ := by
      rw [show Set.range y = Set.range x.val by
        apply Set.Subset.antisymm
        · rintro z ⟨s, rfl⟩; exact ⟨r s, rfl⟩
        · rintro z ⟨s, rfl⟩
          obtain ⟨q, hq⟩ := Set.Icc.surjective_reverse hab.le s
          exact ⟨q, by simpa [y, r] using congrArg x.val hq⟩]
      exact hx.2.2.2.1
    have hyl : y l' = Q := by
      change x.val (r (r u)) = Q
      rw [show r (r u) = u by exact Set.Icc.involutive_reverse hab.le u, hbad.2]
    have hyu : y u' = P := by
      change x.val (r (r l)) = P
      rw [show r (r l) = l by exact Set.Icc.involutive_reverse hab.le l, hbad.1]
    have hytrue := jordan_counterclockwise_of_supporting_segment a b hab y
      (hx.2.2.1.comp (Set.Icc.continuous_reverse hab.le))
      (by rw [hyrange]; exact hx.2.1)
      (by simpa [y, r, Set.Icc.reverse] using hx.2.2.2.2.1.symm)
      (injOn_comp_reverse_of_closed_injOn hab x.val hx.2.2.2.2.1
        hx.2.2.2.2.2.1) θ h
      (fun z ↦ hhalf (by rw [← hyrange]; exact Set.mem_range_self z)) l' u' hl'u'
      (by rw [hyl]; exact hQline) d hd
      (by rw [hyl, hyu, hdir])
      (by rw [image_Icc_reverse_interval hab.le x.val l u hlu.le, himage,
        segment_symm ℝ P Q, hyl, hyu])
    rw [hyrange] at hytrue
    have horient := hx.orientation_eq_not_of_comp hytrue r
      (Set.Icc.continuous_reverse hab.le) (by simp [r, Set.Icc.reverse])
      (by simp [r, Set.Icc.reverse]) rfl
    norm_num at horient
  · exact hgood

/-- Removing a supporting chord from a counterclockwise closed BV Jordan path gives the
complementary arc, and closed signed area splits into arc area and the oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_supportingChord_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan
      hab hx P Q hPQ hsegment hbase
  have hend := endpoints_eq_of_counterclockwise_supporting_chord hab hx l u hlu hub
    P Q hPQ himage θ h hhalf hQline d hd hdir
  obtain ⟨A, hA, hAstart, hAend, harea⟩ :=
    exists_rectifiableOrientedArc_of_cut_parametrization_with_area hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage
  obtain ⟨B, hBcarrier, hBstart, hBend, hBarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
      hab.le hx l u hlu.le hub
  obtain ⟨S, hScarrier, hSstart, hSend, hSarea⟩ :=
    (segmentArea_jordan_and_frame Q P).1
  have hBcarrier' : B.val.carrier = segment ℝ Q P := by
    rw [hBcarrier]
    change Set.range (x.val ∘ fun z : Set.Icc (l : ℝ) u ↦
      (⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩ : Set.Icc a b)) = _
    rw [segment_symm ℝ Q P, ← himage]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hBstart' : B.val.startPoint = Q := hBstart.trans hend.1
  have hBend' : B.val.endPoint = P := hBend.trans hend.2
  have hBSarea : jordanArcArea B = jordanArcArea S := by
    change curveAreaFunctional (Classical.choice B.property).path =
      curveAreaFunctional (Classical.choice S.property).path
    exact (curveArea_reparametrization.2.1 B.val S.val
      (Classical.choice B.property) (Classical.choice S.property)
      (hBcarrier'.trans hScarrier.symm)).1
        (hBstart'.trans hSstart.symm) (hBend'.trans hSend.symm)
  refine ⟨A, hA, hAstart, hAend, ?_⟩
  rw [harea, ← hBarea, hBSarea, hSarea]

end MovingSofa

end

end

end
