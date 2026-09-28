/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.Curves.Foundations.Development001
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Moving sofa: related mathematical developments

* `Area.Foundations.Development002`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
/-!
# Moving sofa: related mathematical developments

* `Area.MonotoneRoof`.
* `Area.ThreePieceRoof`.
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
# Area / Monotone Roof
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Recover the vertical coordinate using a chosen inverse of the path’s horizontal
coordinate. -/
def monotoneRoofHeight {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : ℝ) : ℝ := by
  classical
  letI : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  exact γ.val (Function.invFun (fun t ↦ γ.val t 0) s) 1

/-- The closed region between the horizontal axis and the path’s roof graph. -/
def monotoneRoofRegion {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b) : Set Point :=
  {p | γ.val ⟨a, le_rfl, hab.le⟩ 0 ≤ p 0 ∧
    p 0 ≤ γ.val ⟨b, hab.le, le_rfl⟩ 0 ∧ 0 ≤ p 1 ∧
    p 1 ≤ monotoneRoofHeight hab γ (p 0)}

/-- Traverse the roof path backwards and return along its horizontal base. -/
def monotoneRoofLoop {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : Set.Icc (0 : ℝ) 2) : Point :=
  if hs : s.val ≤ 1 then
    γ.val ⟨b - (b - a) * s.val, by
      constructor
      · nlinarith [s.property.1]
      · nlinarith [s.property.1]⟩
  else
    (2 - s.val) • γ.val ⟨a, le_rfl, hab.le⟩ +
      (s.val - 1) • γ.val ⟨b, hab.le, le_rfl⟩

private theorem monotoneRoofLoop_concatenation {a b : ℝ} (hab : a < b)
    (γ γrev : ContinuousBVPaths a b)
    (hγrev : γrev.val = γ.val ∘ Set.Icc.reverse hab.le)
    (Γ : ContinuousBVPaths 0 2) (hΓval : Γ.val = monotoneRoofLoop hab γ) :
    IsPathConcatenation (⟨0, 2, by norm_num, Γ⟩ : RectifiablePathData)
      ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
        ⟨0, 1, zero_le_one, lineSegmentBVPath
          (γ.val ⟨a, le_rfl, hab.le⟩) (γ.val ⟨b, hab.le, le_rfl⟩)⟩] := by
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  refine ⟨by norm_num,
    ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩], ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exact absurd hij (by decide))
        | (refine Subtype.mk_le_mk.mpr ?_; norm_num)
  · rfl
  · rfl
  · intro i
    fin_cases i
    · change ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
          (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b),
          Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
            Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
            ∀ u, Γ.val ⟨(ϕ u : ℝ), (ϕ u).property.1,
              le_trans (ϕ u).property.2 (by norm_num)⟩ = γrev.val (ψ u)
      refine ⟨fun u ↦ ⟨(u : ℝ), u.property.1, u.property.2⟩,
        fun u ↦ ⟨a + (b - a) * (u : ℝ),
          by linarith only [mul_nonneg hba.le u.property.1],
          by linarith only [mul_le_mul_of_nonneg_left u.property.2 hba.le]⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact continuous_subtype_val.subtype_mk _
      · exact fun x y hxy ↦ hxy
      · exact fun z ↦ ⟨⟨(z : ℝ), z.property.1, z.property.2⟩, Subtype.ext rfl⟩
      · exact (continuous_const.add
          (continuous_const.mul continuous_subtype_val)).subtype_mk _
      · intro x y hxy
        have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
        change a + (b - a) * (x : ℝ) ≤ a + (b - a) * (y : ℝ)
        linarith only [mul_le_mul_of_nonneg_left hxy' hba.le]
      · intro t
        refine ⟨⟨((t : ℝ) - a) / (b - a), ?_, ?_⟩, ?_⟩
        · exact div_nonneg (by linarith only [t.property.1]) hba.le
        · rw [div_le_one hba]
          linarith only [t.property.2]
        · apply Subtype.ext
          change a + (b - a) * (((t : ℝ) - a) / (b - a)) = (t : ℝ)
          field_simp
          ring
      · intro u
        have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
        have h1 : (u : ℝ) ≤ 1 := u.property.2
        rw [hΓval, hγrev]
        change monotoneRoofLoop hab γ ⟨(u : ℝ), h0, by linarith⟩ =
          γ.val (Set.Icc.reverse hab.le ⟨a + (b - a) * (u : ℝ),
            by linarith only [mul_nonneg hba.le h0],
            by linarith only [mul_le_mul_of_nonneg_left h1 hba.le]⟩)
        unfold monotoneRoofLoop
        rw [dite_eq_left (show ((⟨(u : ℝ), h0, by linarith⟩ : Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1
          from h1)]
        exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
          change b - (b - a) * (u : ℝ) = a + b - (a + (b - a) * (u : ℝ))
          ring))
    · change ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (1 : ℝ) 2)
          (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
          Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
            Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
            ∀ u, Γ.val ⟨(ϕ u : ℝ), le_trans (by norm_num) (ϕ u).property.1,
              (ϕ u).property.2⟩ =
              (lineSegmentBVPath (γ.val A) (γ.val B)).val (ψ u)
      refine ⟨fun u ↦ ⟨1 + (u : ℝ), by linarith [u.property.1], by
          linarith [u.property.2]⟩,
        fun u ↦ u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact (continuous_const.add continuous_subtype_val).subtype_mk _
      · intro x y hxy
        have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
        change (1 : ℝ) + (x : ℝ) ≤ 1 + (y : ℝ)
        linarith
      · intro z
        refine ⟨⟨(z : ℝ) - 1, by linarith [z.property.1], by
          linarith [z.property.2]⟩, ?_⟩
        apply Subtype.ext
        change (1 : ℝ) + ((z : ℝ) - 1) = (z : ℝ)
        ring
      · exact continuous_id
      · exact fun x y hxy ↦ hxy
      · exact fun z ↦ ⟨z, rfl⟩
      · intro u
        have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
        have h1 : (u : ℝ) ≤ 1 := u.property.2
        rw [hΓval]
        change monotoneRoofLoop hab γ ⟨1 + (u : ℝ), by linarith, by linarith⟩ =
          Path.segment (γ.val A) (γ.val B) u
        unfold monotoneRoofLoop
        rcases eq_or_lt_of_le h0 with hu0 | hu0
        · rw [dite_eq_left (show ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
            Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by simp [← hu0])]
          have huval : (u : ℝ) = 0 := hu0.symm
          have hseg : Path.segment (γ.val A) (γ.val B) u = γ.val A := by
            rw [Path.segment_apply]
            rw [show (u : ℝ) = 0 from huval]
            simp
          rw [hseg]
          exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
            change b - (b - a) * (1 + (u : ℝ)) = a
            rw [huval]
            ring))
        · rw [dite_eq_right (show ¬ ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
            Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by
              change ¬ (1 + (u : ℝ) ≤ 1)
              linarith)]
          change (2 - (1 + (u : ℝ))) • γ.val A + ((1 + (u : ℝ)) - 1) • γ.val B =
            Path.segment (γ.val A) (γ.val B) u
          rw [Path.segment_apply, AffineMap.lineMap_apply_module']
          module

private theorem monotoneRoof_area {a b : ℝ} (hab : a < b)
    (γ : ContinuousBVPaths a b) (hk : StrictMono (fun t ↦ γ.val t 0))
    (hh : ∀ t, 0 ≤ γ.val t 1)
    (ha : γ.val ⟨a, le_rfl, hab.le⟩ 1 = 0)
    (hb : γ.val ⟨b, hab.le, le_rfl⟩ 1 = 0) :
    ClassicalResults.area (monotoneRoofRegion hab γ) = -curveAreaFunctional γ ∧
      ClassicalResults.area (monotoneRoofRegion hab γ) =
        ∫ s in γ.val ⟨a, le_rfl, hab.le⟩ 0..γ.val ⟨b, hab.le, le_rfl⟩ 0,
          monotoneRoofHeight hab γ s := by
  classical
  set A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩ with hAdef
  set B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩ with hBdef
  set c : ℝ := γ.val A 0 with hcdef
  set d : ℝ := γ.val B 0 with hddef
  have hAB : A < B := hab
  have hcd : c < d := hk hAB
  -- the horizontal coordinate as a map onto `[c, d]`
  have hγ0 : Continuous fun t : Set.Icc a b ↦ γ.val t 0 :=
    (PiLp.continuous_apply 2 _ 0).comp γ.property.1
  have hγ1 : Continuous fun t : Set.Icc a b ↦ γ.val t 1 :=
    (PiLp.continuous_apply 2 _ 1).comp γ.property.1
  have hmem : ∀ t : Set.Icc a b, γ.val t 0 ∈ Set.Icc c d := fun t ↦
    ⟨hk.monotone (show A ≤ t from t.property.1),
      hk.monotone (show t ≤ B from t.property.2)⟩
  set kmap : Set.Icc a b → Set.Icc c d := fun t ↦ ⟨γ.val t 0, hmem t⟩ with hkmapdef
  have hkc : Continuous kmap := hγ0.subtype_mk _
  have hkinj : Function.Injective kmap := fun x y h ↦ hk.injective (congrArg Subtype.val h)
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hksurj : Function.Surjective kmap := by
    intro s
    obtain ⟨t, ht⟩ := intermediate_value_univ A B hγ0 s.property
    exact ⟨t, Subtype.ext ht⟩
  -- the continuous monotone inverse `φ = k⁻¹`
  set khom : Set.Icc a b ≃ₜ Set.Icc c d :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective kmap ⟨hkinj, hksurj⟩) hkc
    with hkhomdef
  set φ : Set.Icc c d → Set.Icc a b := ⇑khom.symm with hφdef
  have hkhom_apply : ∀ t, khom t = kmap t := fun _ ↦ rfl
  have hφk : ∀ s : Set.Icc c d, γ.val (φ s) 0 = (s : ℝ) := by
    intro s
    have := khom.apply_symm_apply s
    rw [hkhom_apply] at this
    exact congrArg Subtype.val this
  have hφc : Continuous φ := khom.symm.continuous
  have hφs : Function.Surjective φ := khom.symm.surjective
  have hφm : Monotone φ := by
    intro s t hst
    by_contra hcon
    have hlt : φ t < φ s := lt_of_not_ge hcon
    have hlt2 := hk hlt
    simp only [hφk] at hlt2
    exact absurd hst (not_le.mpr hlt2)
  -- the roof height, as a globally continuous function on the line
  set g : ℝ → ℝ := fun s ↦ γ.val (φ (Set.projIcc c d hcd.le s)) 1 with hgdef
  have hgc : Continuous g := hγ1.comp (hφc.comp continuous_projIcc)
  have hgnonneg : ∀ s, 0 ≤ g s := fun s ↦ hh _
  have hheight : ∀ s ∈ Set.Icc c d, monotoneRoofHeight hab γ s = g s := by
    intro s hs
    have hex : ∃ t : Set.Icc a b, γ.val t 0 = s := ⟨φ ⟨s, hs⟩, hφk ⟨s, hs⟩⟩
    have hinv := @Function.invFun_eq _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s hex
    have hpt : @Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s = φ ⟨s, hs⟩ :=
      hk.injective (by simpa using hinv.trans (hφk ⟨s, hs⟩).symm)
    change γ.val (@Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s) 1 = g s
    rw [hpt]
    simp [hgdef, Set.projIcc_of_mem _ hs]
  -- the roof region is the closed subgraph of `g` over `[c, d]`
  have hregion : monotoneRoofRegion hab γ =
      {p : Point | p 0 ∈ Set.Icc c d ∧
        p 1 ∈ Set.Icc ((fun _ : ℝ ↦ (0 : ℝ)) (p 0)) (g (p 0))} := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, by rwa [hheight (p 0) ⟨h1, h2⟩] at h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, by rwa [hheight (p 0) ⟨h1, h2⟩]⟩
  -- the planar volume of a closed vertical subgraph
  have hvolVertical : ∀ (f₀ g₀ : ℝ → ℝ) (S : Set ℝ), Measurable f₀ → Measurable g₀ →
      MeasurableSet S → MeasureTheory.IntegrableOn f₀ S → MeasureTheory.IntegrableOn g₀ S →
      (∀ x ∈ S, f₀ x ≤ g₀ x) →
      MeasureTheory.volume {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        ENNReal.ofReal (∫ x in S, (g₀ - f₀) x) := by
    intro f₀ g₀ S hf hg hS hfi hgi hfg
    have hT : MeasurableSet {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} :=
      measurableSet_region_between_cc hf hg hS
    have hpre : {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        (fun p : Point ↦ (p 0, p 1)) ⁻¹'
          {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} := rfl
    rw [hpre, EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
      hT.nullMeasurableSet]
    rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hS]
    change (MeasureTheory.volume.prod MeasureTheory.volume) (regionBetween f₀ g₀ S) = _
    rw [volume_regionBetween_eq_integral hfi hgi hS hfg]
  have hgint : MeasureTheory.IntegrableOn g (Set.Icc c d) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hIcc : (∫ x in Set.Icc c d, g x) = ∫ s in c..d, g s := by
    rw [intervalIntegral.integral_of_le hcd.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have harea : ClassicalResults.area (monotoneRoofRegion hab γ) = ∫ s in c..d, g s := by
    rw [ClassicalResults.area, hregion,
      hvolVertical (fun _ ↦ 0) g (Set.Icc c d) measurable_const hgc.measurable
        measurableSet_Icc (MeasureTheory.integrableOn_zero) hgint
        (fun x _ ↦ hgnonneg x)]
    rw [ENNReal.toReal_ofReal]
    · simp only [Pi.sub_apply, sub_zero]
      exact hIcc
    · exact MeasureTheory.integral_nonneg (fun x ↦ by simp [hgnonneg x])
  -- the two coordinate Stieltjes drivers
  have hBVext : ∀ {u v : ℝ} (F G : RightContinuousIntervalBV u v),
      F.toFun = G.toFun → F = G := by
    intro u v F G hFG
    cases F
    cases G
    simp only at hFG
    subst hFG
    rfl
  set K := continuousBVCoordinate γ 0 with hKdef
  set H := continuousBVCoordinate γ 1 with hHdef
  have hKcont : Continuous K.toFun := hγ0
  have hHcont : Continuous H.toFun := hγ1
  -- the identity driver on `[c, d]`, with Lebesgue density one
  obtain ⟨Q, hQfun, hQdens⟩ := exists_intervalBV_of_hasDerivAt hcd.le (fun x ↦ x)
    (fun _ ↦ (1 : ℝ)) (fun t ↦ hasDerivAt_id t) continuous_const
  have hstieltjes : intervalStieltjesIntegral K H.toFun Set.univ =
      intervalStieltjesIntegral Q (H.toFun ∘ φ) Set.univ := by
    rw [intervalStieltjesIntegral_comp_monotone_surjective hab.le hcd.le K hKcont
      H.toFun hHcont φ hφc hφm hφs]
    congr 1
    apply hBVext
    funext s
    change γ.val (φ s) 0 = Q.toFun s
    rw [hQfun s, hφk s]
  have hroofint : intervalStieltjesIntegral K H.toFun Set.univ = ∫ s in c..d, g s := by
    rw [hstieltjes, intervalStieltjesIntegral_eq_integral_mul_of_density Q hQdens
      (hHcont.comp hφc) Set.univ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
    have hfun : (fun t : Set.Icc c d ↦ (H.toFun ∘ φ) t * (1 : ℝ)) =
        fun t : Set.Icc c d ↦ g (t : ℝ) := by
      funext t
      simp only [Function.comp_apply, mul_one, hgdef, Set.projIcc_val]
      rfl
    rw [hfun, MeasureTheory.integral_subtype_comap measurableSet_Icc g, hIcc]
  -- integration by parts identifies the curve area with the roof integral
  have hparts := intervalStieltjes_integration_by_parts_of_continuous a b hab.le K H
    hKcont hHcont
  have hends : K.toFun B * H.toFun B - K.toFun A * H.toFun A = 0 := by
    change γ.val B 0 * γ.val B 1 - γ.val A 0 * γ.val A 1 = 0
    rw [ha, hb]
    ring
  have hJγ : curveAreaFunctional γ = -intervalStieltjesIntegral K H.toFun Set.univ := by
    have hform : curveAreaFunctional γ =
        (intervalStieltjesIntegral H K.toFun Set.univ -
          intervalStieltjesIntegral K H.toFun Set.univ) / 2 := rfl
    rw [hform]
    rw [hends] at hparts
    linarith
  have hheightint : (∫ s in c..d, monotoneRoofHeight hab γ s) = ∫ s in c..d, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hheight s (by rwa [Set.uIcc_of_le hcd.le] at hs)
  constructor
  · rw [hJγ, neg_neg, hroofint, harea]
  · exact harea.trans hheightint.symm

theorem monotone_roof_signed_area {a b : ℝ} (hab : a < b)
    (γ : ContinuousBVPaths a b) (hk : StrictMono (fun t ↦ γ.val t 0))
    (hh : ∀ t, 0 ≤ γ.val t 1)
    (ha : γ.val ⟨a, le_rfl, hab.le⟩ 1 = 0)
    (hb : γ.val ⟨b, hab.le, le_rfl⟩ 1 = 0) :
    ∃ Γ : ContinuousBVPaths 0 2, Γ.val = monotoneRoofLoop hab γ ∧
      curveAreaFunctional Γ = ClassicalResults.area (monotoneRoofRegion hab γ) ∧
      ClassicalResults.area (monotoneRoofRegion hab γ) =
        ∫ s in γ.val ⟨a, le_rfl, hab.le⟩ 0..γ.val ⟨b, hab.le, le_rfl⟩ 0,
          monotoneRoofHeight hab γ s := by
  classical
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  obtain ⟨harea, hheight⟩ := monotoneRoof_area hab γ hk hh ha hb
  -- the reversed roof, as a path on `[a, b]`
  have hJrev := curveArea_comp_reverse hab.le γ
  set γrev : ContinuousBVPaths a b :=
    ⟨γ.val ∘ Set.Icc.reverse hab.le,
      γ.property.1.comp (Set.Icc.continuous_reverse hab.le), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i)
          (Set.Icc.antitone_reverse hab.le) (Set.Icc.surjective_reverse hab.le)⟩ with hγrevdef
  change curveAreaFunctional γrev = -curveAreaFunctional γ at hJrev
  -- the antitone reparametrization of `[0, 2]` onto `[a, b]`, pausing on `[1, 2]`
  set revmap : Set.Icc (0 : ℝ) 2 → Set.Icc a b :=
    fun s ↦ Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) with hrevmapdef
  have hrevc : Continuous revmap :=
    continuous_projIcc.comp (by fun_prop)
  have hrevanti : Antitone revmap := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hmul := mul_le_mul_of_nonneg_left hst' (sub_nonneg.mpr hab.le)
    change Set.projIcc a b hab.le (b - (b - a) * (t : ℝ)) ≤
      Set.projIcc a b hab.le (b - (b - a) * (s : ℝ))
    exact Set.monotone_projIcc hab.le (by linarith)
  have hrevsurj : Function.Surjective revmap := by
    intro t
    have hba : (0 : ℝ) < b - a := by linarith
    refine ⟨⟨(b - (t : ℝ)) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [t.property.2]) hba.le
    · rw [div_le_iff₀ hba]
      nlinarith [t.property.1]
    · have hval : b - (b - a) * ((b - (t : ℝ)) / (b - a)) = (t : ℝ) := by
        field_simp
        ring
      change Set.projIcc a b hab.le (b - (b - a) * ((b - (t : ℝ)) / (b - a))) = t
      rw [hval, Set.projIcc_val]
  -- the base segment piece, paused on `[0, 1]`
  set w : Point := γ.val B - γ.val A with hwdef
  set ρ : Set.Icc (0 : ℝ) 2 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) with hρdef
  have hρc : Continuous ρ := continuous_projIcc.comp (by fun_prop)
  have hρm : Monotone ρ := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) ≤
      Set.projIcc 0 1 zero_le_one ((t : ℝ) - 1)
    exact Set.monotone_projIcc zero_le_one (by linarith)
  have hρs : Function.Surjective ρ := by
    intro u
    refine ⟨⟨(u : ℝ) + 1, ?_, ?_⟩, ?_⟩
    · linarith [u.property.1]
    · linarith [u.property.2]
    · change Set.projIcc 0 1 zero_le_one ((u : ℝ) + 1 - 1) = u
      rw [show ((u : ℝ) + 1 - 1) = (u : ℝ) from by ring, Set.projIcc_val]
  obtain ⟨Bpath, hBpathval⟩ := continuousBVPaths_comp_monotone_surjective
    (by norm_num : (0 : ℝ) ≤ 1) (lineSegmentBVPath 0 w) ρ hρc hρm hρs
  set Apath : ContinuousBVPaths 0 2 :=
    ⟨γ.val ∘ revmap, γ.property.1.comp hrevc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i) hrevanti
        hrevsurj⟩ with hApathdef
  set Γ : ContinuousBVPaths 0 2 := Apath + Bpath with hΓdef
  have hΓval : Γ.val = monotoneRoofLoop hab γ := by
    funext s
    have h0 : (0 : ℝ) ≤ (s : ℝ) := s.property.1
    have h2 : (s : ℝ) ≤ 2 := s.property.2
    have hval : Γ.val s = γ.val (revmap s) + Path.segment (0 : Point) w (ρ s) := by
      change Apath.val s + Bpath.val s = _
      rw [hBpathval]
      rfl
    rw [hval]
    unfold monotoneRoofLoop
    split_ifs with hs
    · have hrevs : revmap s = ⟨b - (b - a) * (s : ℝ),
          by constructor <;> nlinarith⟩ := by
        change Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        exact Set.projIcc_of_mem hab.le _
      have hρ0 : ρ s = ⟨0, by norm_num⟩ := by
        change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_le_left zero_le_one (by linarith)
      rw [hrevs, hρ0]
      simp
    · rw [not_le] at hs
      have hrevs : revmap s = A := by
        change Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        rw [Set.projIcc_of_le_left hab.le (by nlinarith)]
      have hρ1 : ρ s = ⟨(s : ℝ) - 1, by constructor <;> linarith⟩ := by
        change Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_mem zero_le_one _
      rw [hrevs, hρ1]
      change γ.val A + AffineMap.lineMap (0 : Point) w ((s : ℝ) - 1) =
        (2 - (s : ℝ)) • γ.val A + ((s : ℝ) - 1) • γ.val B
      rw [AffineMap.lineMap_apply_module', hwdef]
      module
  -- additivity of the curve area along the cut at `s = 1`
  have hΓ2 : (0 : ℝ) ≤ 2 := by norm_num
  have hba : (0 : ℝ) < b - a := by linarith
  have hconcat : IsPathConcatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
      ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
        ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] :=
    monotoneRoofLoop_concatenation hab γ γrev rfl Γ hΓval
  -- the two pieces and the final assembly
  have hsum := curveArea_concatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
    ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
      ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] hconcat
  have hbase : curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) = 0 := by
    rw [curveAreaFunctional_lineSegmentBVPath, segmentArea, planeCrossProduct, ha, hb]
    ring
  have hJΓ : curveAreaFunctional Γ = -curveAreaFunctional γ := by
    have hΓsum : curveAreaFunctional Γ =
        curveAreaFunctional γrev +
          curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) := by
      rw [show curveAreaFunctional Γ =
        curveAreaFunctional (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData).path from rfl, hsum,
        Fin.sum_univ_two]
      rfl
    rw [hΓsum, hbase, hJrev, add_zero]
  exact ⟨Γ, hΓval, hJΓ.trans harea.symm, hheight⟩

/-- Above a parameter's abscissa, a strictly monotone roof has that parameter's ordinate. -/
theorem monotoneRoofHeight_apply {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) (s : Set.Icc a b) :
    monotoneRoofHeight hab γ (γ.val s 0) = γ.val s 1 := by
  classical
  have hne : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  have hinv : @Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0) = s :=
    hk.injective (@Function.invFun_eq _ _ hne (fun t ↦ γ.val t 0) _ ⟨s, rfl⟩)
  change γ.val (@Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0)) 1 = γ.val s 1
  rw [hinv]

/-- Every abscissa between a roof's endpoints is the abscissa of a roof parameter. -/
theorem exists_eq_monotoneRoof_fst {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    {c : ℝ} (hc : c ∈ Set.Icc (γ.val ⟨a, le_rfl, hab.le⟩ 0) (γ.val ⟨b, hab.le, le_rfl⟩ 0)) :
    ∃ s : Set.Icc a b, γ.val s 0 = c := by
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  exact intermediate_value_univ _ _ ((PiLp.continuous_apply 2 _ 0).comp γ.property.1) hc

/-- The closed region under a strictly monotone roof, described parametrically: it consists of the
points on or below the roof on the vertical line through some roof parameter. -/
theorem monotoneRoofRegion_eq_param {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) :
    monotoneRoofRegion hab γ =
      {p : Point | ∃ s : Set.Icc a b, p 0 = γ.val s 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ γ.val s 1} := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs⟩ := exists_eq_monotoneRoof_fst hab γ ⟨h1, h2⟩
    refine ⟨s, hs.symm, h3, ?_⟩
    rwa [← hs, monotoneRoofHeight_apply hab γ hk s] at h4
  · rintro ⟨s, hs0, hs1, hs2⟩
    refine ⟨?_, ?_, hs1, ?_⟩
    · rw [hs0]
      exact hk.monotone (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ≤ s from s.property.1)
    · rw [hs0]
      exact hk.monotone (show s ≤ (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) from s.property.2)
    · rw [hs0, monotoneRoofHeight_apply hab γ hk s]
      exact hs2

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
/-! # Three-piece monotone roofs

A *three-piece roof* over `[r, l]` is the continuous BV path on `[0, 3]` that runs up a straight
segment from a base point `P` to `f l`, traverses an arc `f` backwards from `l` to `r`, and runs
down a straight segment from `f r` to a base point `Q`.  When the arc's first coordinate is
strictly decreasing and `P`, `Q` lie strictly to the left of `f l` resp. to the right of `f r`, the
resulting path has strictly increasing first coordinate, so it is a monotone roof in the sense of
`MovingSofa.monotoneRoofRegion`.

`area_region_under_strictMono_roof` computes the area of the closed region under such a roof, above
the base line `y = -h` carrying `P` and `Q`, as the signed area of the four-piece closed loop that
bounds it, and `area_region_under_roof_le` compares that area with the areas of a base set and of a
set containing the rest of the open region.
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A segment path, read as its base point plus a multiple of its displacement. -/
private theorem segment_eq_add_smul (p q : Point) (u : Set.Icc (0 : ℝ) 1) :
    Path.segment p q u = p + (u : ℝ) • (q - p) := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

/-- Clamping to a nondegenerate interval is strictly monotone away from both clamps. -/
private theorem projIcc_lt_projIcc {a b : ℝ} (hab : a < b) {s t : ℝ} (hst : s < t)
    (hs : s < b) (ht : a < t) :
    Set.projIcc a b hab.le s < Set.projIcc a b hab.le t := by
  change max a (min b s) < max a (min b t)
  rw [min_eq_right hs.le, max_eq_right (le_min hab.le ht.le)]
  exact max_lt (lt_min hab ht) (lt_min hs hst)

/-- A convex combination of two numbers bounded by `c` is bounded by `c`. -/
private theorem affine_le_of_le {A B c s : ℝ} (hA : A ≤ c) (hB : B ≤ c)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : A + s * (B - A) ≤ c := by nlinarith

/-- The middle arc's parameter times run over the arc's own interval. -/
theorem mem_Icc_roofArcTime {r l : ℝ} (hrl : r < l) {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    l + (s - 1) * (r - l) ∈ Set.Icc r l := by
  refine ⟨?_, ?_⟩
  · have h : (0 : ℝ) ≤ (1 - (s - 1)) * (l - r) :=
      mul_nonneg (by linarith only [hs2]) (by linarith only [hrl])
    linarith only [h]
  · have h : (s - 1) * (r - l) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [hs1]) (by linarith only [hrl])
    linarith only [h]

/-- Three pieces — a rising segment into the left end of a strictly decreasing arc, that arc
traversed backwards, and a rising segment out of its right end — assemble into a continuous BV
path on `[0, 3]` whose first coordinate is strictly increasing. -/
theorem exists_strictMono_roof_of_strictAntiOn {r l : ℝ} (hrl : r < l)
    (c : ContinuousBVPaths r l) (f : ℝ → Point) (P Q : Point)
    (hf : ∀ (t : ℝ) (ht : t ∈ Set.Icc r l), c.val ⟨t, ht⟩ = f t)
    (hanti : StrictAntiOn (fun t ↦ f t 0) (Set.Icc r l))
    (hP : P 0 < f l 0) (hQ : f r 0 < Q 0) :
    ∃ γ : ContinuousBVPaths 0 3,
      (∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P)) ∧
        (∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
          γ.val s = f (l + ((s : ℝ) - 1) * (r - l))) ∧
        (∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) →
          γ.val s = f r + ((s : ℝ) - 2) • (Q - f r)) ∧
        StrictMono fun s ↦ γ.val s 0 := by
  have hlr : r - l < 0 := by linarith
  have hcf : ∀ u : Set.Icc r l, c.val u = f (u : ℝ) := fun u ↦ hf u u.property
  have hcanti : ∀ u v : Set.Icc r l, u ≤ v → f (v : ℝ) 0 ≤ f (u : ℝ) 0 := by
    intro u v huv
    rcases eq_or_lt_of_le huv with h | h
    · rw [h]
    · exact (hanti u.property v.property h).le
  -- the antitone reparametrisation of `[0, 3]` onto the arc's domain
  set μ : Set.Icc (0 : ℝ) 3 → Set.Icc r l :=
    fun s ↦ Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) with hμdef
  have hμc : Continuous μ := continuous_projIcc.comp (by fun_prop)
  have hμa : Antitone μ := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := hst
    exact Set.monotone_projIcc hrl.le (by nlinarith)
  have hμs : Function.Surjective μ := by
    intro u
    have hu1 : r ≤ (u : ℝ) := u.property.1
    have hu2 : (u : ℝ) ≤ l := u.property.2
    have hne : l - r ≠ 0 := by linarith
    have hq : 0 ≤ (l - (u : ℝ)) / (l - r) := div_nonneg (by linarith) (by linarith)
    have hq1 : (l - (u : ℝ)) / (l - r) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    refine ⟨⟨1 + (l - (u : ℝ)) / (l - r), by linarith, by linarith⟩, ?_⟩
    change Set.projIcc r l hrl.le (l + (1 + (l - (u : ℝ)) / (l - r) - 1) * (r - l)) = u
    rw [show l + (1 + (l - (u : ℝ)) / (l - r) - 1) * (r - l) = (u : ℝ) by
      field_simp; ring]
    exact Set.projIcc_of_mem hrl.le u.property
  have hμleft : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → μ s = ⟨l, hrl.le, le_rfl⟩ := by
    intro s hs
    change Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) = _
    exact Set.projIcc_of_right_le hrl.le
      (le_add_of_nonneg_right (show (0 : ℝ) ≤ ((s : ℝ) - 1) * (r - l) by nlinarith))
  have hμmid : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      (μ s : ℝ) = l + ((s : ℝ) - 1) * (r - l) := by
    intro s hs1 hs2
    change (Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) : ℝ) = _
    rw [Set.projIcc_of_mem hrl.le ⟨by nlinarith, by nlinarith⟩]
  have hμright : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → μ s = ⟨r, le_rfl, hrl.le⟩ := by
    intro s hs
    change Set.projIcc r l hrl.le (l + ((s : ℝ) - 1) * (r - l)) = _
    exact Set.projIcc_of_le_left hrl.le (by nlinarith)
  have hμstrict : ∀ s t : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) < (t : ℝ) →
      (t : ℝ) ≤ 2 → μ t < μ s := by
    intro s t hs hst ht
    exact projIcc_lt_projIcc hrl (by nlinarith) (by nlinarith) (by nlinarith)
  -- the two clamped affine reparametrisations of the side segments
  set ρ₀ : Set.Icc (0 : ℝ) 3 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one (s : ℝ) with hρ₀def
  set ρ₂ : Set.Icc (0 : ℝ) 3 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) with hρ₂def
  have hρ₀c : Continuous ρ₀ := continuous_projIcc.comp (by fun_prop)
  have hρ₂c : Continuous ρ₂ := continuous_projIcc.comp (by fun_prop)
  have hρ₀m : Monotone ρ₀ := fun s t hst ↦ Set.monotone_projIcc zero_le_one hst
  have hρ₂m : Monotone ρ₂ := fun s t hst ↦
    Set.monotone_projIcc zero_le_one (by linarith [show (s : ℝ) ≤ t from hst])
  have hρ₀s : Function.Surjective ρ₀ := fun u ↦
    ⟨⟨(u : ℝ), u.property.1, le_trans u.property.2 (by norm_num)⟩,
      Set.projIcc_of_mem zero_le_one u.property⟩
  have hρ₂s : Function.Surjective ρ₂ := by
    intro u
    refine ⟨⟨(u : ℝ) + 2, by linarith [u.property.1], by linarith [u.property.2]⟩, ?_⟩
    change Set.projIcc 0 1 zero_le_one ((u : ℝ) + 2 - 2) = u
    rw [show (u : ℝ) + 2 - 2 = (u : ℝ) by ring]
    exact Set.projIcc_of_mem zero_le_one u.property
  have hρ₀left : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → (ρ₀ s : ℝ) = (s : ℝ) := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one (s : ℝ) : ℝ) = _
    rw [Set.projIcc_of_mem zero_le_one ⟨s.property.1, hs⟩]
  have hρ₀right : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (ρ₀ s : ℝ) = 1 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one (s : ℝ) : ℝ) = _
    rw [Set.projIcc_of_right_le zero_le_one hs]
  have hρ₂left : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 2 → (ρ₂ s : ℝ) = 0 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) : ℝ) = _
    rw [Set.projIcc_of_le_left zero_le_one (by linarith)]
  have hρ₂right : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → (ρ₂ s : ℝ) = (s : ℝ) - 2 := by
    intro s hs
    change (Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2) : ℝ) = _
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith, by linarith [s.property.2]⟩]
  -- the three summands of the roof
  obtain ⟨A₀, hA₀⟩ := continuousBVPaths_comp_monotone_surjective zero_le_one
    (lineSegmentBVPath P (f l)) ρ₀ hρ₀c hρ₀m hρ₀s
  obtain ⟨A₂, hA₂⟩ := continuousBVPaths_comp_monotone_surjective zero_le_one
    (lineSegmentBVPath 0 (Q - f r)) ρ₂ hρ₂c hρ₂m hρ₂s
  set A₁ : ContinuousBVPaths 0 3 :=
    ⟨c.val ∘ μ, c.property.1.comp hμc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hrl.le (c.property.2 i) hμa hμs⟩
    with hA₁def
  have hval : ∀ s : Set.Icc (0 : ℝ) 3,
      (A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂).val s =
        (P + (ρ₀ s : ℝ) • (f l - P)) + (f (μ s : ℝ) - f l) +
          (ρ₂ s : ℝ) • (Q - f r) := by
    intro s
    change A₀.val s + (A₁.val s - f l) + A₂.val s = _
    rw [hA₀, hA₂]
    change Path.segment P (f l) (ρ₀ s) + (c.val (μ s) - f l) +
      Path.segment (0 : Point) (Q - f r) (ρ₂ s) = _
    rw [segment_eq_add_smul, segment_eq_add_smul, hcf (μ s)]
    simp
  have hcoord : ∀ s : Set.Icc (0 : ℝ) 3,
      (A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂).val s 0 =
        P 0 + (ρ₀ s : ℝ) * (f l 0 - P 0) + (f (μ s : ℝ) 0 - f l 0) +
          (ρ₂ s : ℝ) * (Q 0 - f r 0) := by
    intro s
    rw [hval s]
    simp
  refine ⟨A₀ + (A₁ - constBVPath 0 3 (f l)) + A₂, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hval s, hρ₀left s hs, hμleft s hs]
    simp [hρ₂left s (by linarith)]
  · intro s hs1 hs2
    rw [hval s, hρ₀right s hs1, hμmid s hs1 hs2, hρ₂left s hs2]
    simp
  · intro s hs
    rw [hval s, hρ₀right s (by linarith), hμright s hs, hρ₂right s hs]
    simp
  · intro s t hst
    have hst' : (s : ℝ) < (t : ℝ) := hst
    have hd0 : (0 : ℝ) < f l 0 - P 0 := by linarith
    have hd2 : (0 : ℝ) < Q 0 - f r 0 := by linarith
    have m0 : (ρ₀ s : ℝ) * (f l 0 - P 0) ≤ (ρ₀ t : ℝ) * (f l 0 - P 0) :=
      mul_le_mul_of_nonneg_right (hρ₀m hst.le) hd0.le
    have m2 : (ρ₂ s : ℝ) * (Q 0 - f r 0) ≤ (ρ₂ t : ℝ) * (Q 0 - f r 0) :=
      mul_le_mul_of_nonneg_right (hρ₂m hst.le) hd2.le
    have m1 : f (μ s : ℝ) 0 ≤ f (μ t : ℝ) 0 := hcanti (μ t) (μ s) (hμa hst.le)
    simp only [hcoord]
    rcases lt_or_ge (s : ℝ) 1 with hc | hc
    · have hs0 : (ρ₀ s : ℝ) < (ρ₀ t : ℝ) :=
        projIcc_lt_projIcc zero_lt_one hst' hc (by linarith [s.property.1])
      have := mul_lt_mul_of_pos_right hs0 hd0
      linarith only [this, m1, m2]
    · rcases le_or_gt (t : ℝ) 2 with hc2 | hc2
      · have hmid : f (μ s : ℝ) 0 < f (μ t : ℝ) 0 :=
          hanti (μ t).property (μ s).property (hμstrict s t hc hst' hc2)
        linarith only [hmid, m0, m2]
      · have hs2 : (ρ₂ s : ℝ) < (ρ₂ t : ℝ) :=
          projIcc_lt_projIcc zero_lt_one (by linarith)
            (by linarith [t.property.2]) (by linarith)
        have := mul_lt_mul_of_pos_right hs2 hd2
        linarith only [this, m0, m1]

/-- A linear functional bounded at the two base corners of a three-piece roof and along its
middle arc is bounded along the whole roof. -/
theorem le_of_threePieceRoof {r l α β cc : ℝ} (hrl : r < l) (f : ℝ → Point) (P Q : Point)
    (γ : ContinuousBVPaths 0 3)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = f (l + ((s : ℝ) - 1) * (r - l)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → γ.val s = f r + ((s : ℝ) - 2) • (Q - f r))
    (hP : α * P 0 + β * P 1 ≤ cc) (hQ : α * Q 0 + β * Q 1 ≤ cc)
    (harc : ∀ t ∈ Set.Icc r l, α * f t 0 + β * f t 1 ≤ cc) (s : Set.Icc (0 : ℝ) 3) :
    α * γ.val s 0 + β * γ.val s 1 ≤ cc := by
  have hcoord : ∀ (p q : Point) (u : ℝ) (i : Fin 2),
      (p + u • (q - p)) i = p i + u * (q i - p i) := fun _ _ _ _ ↦ by simp
  rcases le_or_gt (s : ℝ) 1 with hs | hs
  · rw [hγ0 s hs, hcoord, hcoord]
    have hmid := affine_le_of_le (A := α * P 0 + β * P 1) (B := α * f l 0 + β * f l 1)
      (c := cc) (s := (s : ℝ)) hP (harc l ⟨hrl.le, le_rfl⟩) s.property.1 hs
    calc α * (P 0 + (s : ℝ) * (f l 0 - P 0)) + β * (P 1 + (s : ℝ) * (f l 1 - P 1))
        = (α * P 0 + β * P 1) +
          (s : ℝ) * ((α * f l 0 + β * f l 1) - (α * P 0 + β * P 1)) := by ring
      _ ≤ cc := hmid
  · rcases le_or_gt (s : ℝ) 2 with hs2 | hs2
    · rw [hγ1 s hs.le hs2]
      exact harc _ (mem_Icc_roofArcTime hrl hs.le hs2)
    · rw [hγ2 s hs2.le, hcoord, hcoord]
      have hmid := affine_le_of_le (A := α * f r 0 + β * f r 1) (B := α * Q 0 + β * Q 1)
        (c := cc) (s := (s : ℝ) - 2) (harc r ⟨le_rfl, hrl.le⟩) hQ
        (by linarith only [hs2]) (by linarith only [s.property.2])
      calc α * (f r 0 + ((s : ℝ) - 2) * (Q 0 - f r 0)) +
            β * (f r 1 + ((s : ℝ) - 2) * (Q 1 - f r 1))
          = (α * f r 0 + β * f r 1) +
            ((s : ℝ) - 2) * ((α * Q 0 + β * Q 1) - (α * f r 0 + β * f r 1)) := by ring
        _ ≤ cc := hmid

/-- The closed region under a strictly monotone three-piece roof whose two side segments begin
and end on the line `y = -h` has area equal to the signed area of the four-piece loop that
bounds it: the base segment, the two side segments and the arc. -/
theorem area_region_under_strictMono_roof {r l h : ℝ} (hrl : r < l)
    (c : ContinuousBVPaths r l) (f : ℝ → Point) (P Q : Point) (γ : ContinuousBVPaths 0 3)
    (hf : ∀ (t : ℝ) (ht : t ∈ Set.Icc r l), c.val ⟨t, ht⟩ = f t)
    (hP : P 1 = -h) (hQ : Q 1 = -h)
    (hγ0 : ∀ s : Set.Icc (0 : ℝ) 3, (s : ℝ) ≤ 1 → γ.val s = P + (s : ℝ) • (f l - P))
    (hγ1 : ∀ s : Set.Icc (0 : ℝ) 3, 1 ≤ (s : ℝ) → (s : ℝ) ≤ 2 →
      γ.val s = f (l + ((s : ℝ) - 1) * (r - l)))
    (hγ2 : ∀ s : Set.Icc (0 : ℝ) 3, 2 ≤ (s : ℝ) → γ.val s = f r + ((s : ℝ) - 2) • (Q - f r))
    (hγmono : StrictMono fun s ↦ γ.val s 0)
    (hγlow : ∀ s : Set.Icc (0 : ℝ) 3, -h ≤ γ.val s 1) :
    ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      segmentArea Q (f r) + curveAreaFunctional c + segmentArea (f l) P + segmentArea P Q := by
  have h03 : (0 : ℝ) < 3 := by norm_num
  have h02 : (0 : ℝ) ≤ 2 := by norm_num
  have hadd : ∀ (x y : Point) (i : Fin 2), (x + y) i = x i + y i := fun _ _ _ ↦ by simp
  have hcf : ∀ u : Set.Icc r l, c.val u = f (u : ℝ) := fun u ↦ hf u u.property
  -- the upward shift taking the base line to the horizontal axis
  set v : Point := !₂[0, h] with hvdef
  have hv0 : v 0 = 0 := rfl
  have hv1 : v 1 = h := rfl
  set γ' : ContinuousBVPaths 0 3 := γ + constBVPath 0 3 v with hγ'def
  have hγ'val : ∀ s, γ'.val s = γ.val s + v := fun _ ↦ rfl
  have hγ'coord : ∀ (s : Set.Icc (0 : ℝ) 3) (i : Fin 2), γ'.val s i = γ.val s i + v i := by
    intro s i
    rw [hγ'val s, hadd]
  have hγ'mono : StrictMono fun s ↦ γ'.val s 0 := by
    intro s t hst
    have hm : γ.val s 0 < γ.val t 0 := hγmono hst
    change γ'.val s 0 < γ'.val t 0
    rw [hγ'coord s 0, hγ'coord t 0]
    linarith only [hm]
  have hγstart : γ.val ⟨0, le_rfl, h03.le⟩ = P := by
    rw [hγ0 _ (by norm_num)]
    simp
  have hγend : γ.val ⟨3, h03.le, le_rfl⟩ = Q := by
    rw [hγ2 _ (by norm_num)]
    norm_num
  have hγ'zero : γ'.val ⟨0, le_rfl, h03.le⟩ 1 = 0 := by
    rw [hγ'coord, hγstart, hP, hv1]
    ring
  have hγ'three : γ'.val ⟨3, h03.le, le_rfl⟩ 1 = 0 := by
    rw [hγ'coord, hγend, hQ, hv1]
    ring
  have hγ'nonneg : ∀ s, 0 ≤ γ'.val s 1 := by
    intro s
    rw [hγ'coord, hv1]
    linarith only [hγlow s]
  -- the region is the roof region of the shifted path, translated back down
  have hregion : {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      (fun q : Point ↦ q + v) ⁻¹' monotoneRoofRegion h03 γ' := by
    rw [monotoneRoofRegion_eq_param h03 γ' hγ'mono]
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hadd, hγ'coord, hv0, hv1, add_zero]
    constructor
    · rintro ⟨s, e1, e2, e3⟩
      exact ⟨s, e1, by linarith only [e2], by linarith only [e3]⟩
    · rintro ⟨s, e1, e2, e3⟩
      exact ⟨s, e1, by linarith only [e2], by linarith only [e3]⟩
  have harea : ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} =
      ClassicalResults.area (monotoneRoofRegion h03 γ') := by
    rw [ClassicalResults.area, ClassicalResults.area, hregion,
      MeasureTheory.measure_preimage_add_right]
  obtain ⟨Γ, hΓval, hΓarea, -⟩ :=
    monotone_roof_signed_area h03 γ' hγ'mono hγ'nonneg hγ'zero hγ'three
  -- reading the closed loop on its two branches
  have hloopLow : ∀ (t : Set.Icc (0 : ℝ) 2) (u : Set.Icc (0 : ℝ) 3), (t : ℝ) ≤ 1 →
      (u : ℝ) = 3 - 3 * (t : ℝ) → Γ.val t = γ.val u + v := by
    intro t u ht hu
    rw [hΓval]
    unfold monotoneRoofLoop
    split_ifs with hs
    · rw [hγ'val]
      exact congrArg (fun z : Point ↦ z + v) (congrArg (fun z ↦ γ.val z)
        (Subtype.ext (by rw [hu]; ring)))
    · exact absurd ht hs
  have hloopHigh : ∀ t : Set.Icc (0 : ℝ) 2, 1 ≤ (t : ℝ) →
      Γ.val t = (2 - (t : ℝ)) • (P + v) + ((t : ℝ) - 1) • (Q + v) := by
    intro t ht
    rcases eq_or_lt_of_le ht with heq | hlt
    · rw [hloopLow t ⟨0, le_rfl, h03.le⟩ (le_of_eq heq.symm) (by rw [← heq]; norm_num),
        hγstart, ← heq]
      module
    · rw [hΓval]
      unfold monotoneRoofLoop
      split_ifs with hs
      · exact absurd hs (not_le.mpr hlt)
      · simp only [hγ'val, hγstart, hγend]
  -- the four cuts of the loop's parameter interval
  set e0 : Set.Icc (0 : ℝ) 2 := ⟨0, le_rfl, h02⟩ with he0
  set e1 : Set.Icc (0 : ℝ) 2 := ⟨1 / 3, by norm_num⟩ with he1
  set e2 : Set.Icc (0 : ℝ) 2 := ⟨2 / 3, by norm_num⟩ with he2
  set e3 : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩ with he3
  set e4 : Set.Icc (0 : ℝ) 2 := ⟨2, h02, le_rfl⟩ with he4
  have hle01 : e0 ≤ e1 := by change (0 : ℝ) ≤ 1 / 3; norm_num
  have hle12 : e1 ≤ e2 := by change (1 : ℝ) / 3 ≤ 2 / 3; norm_num
  have hle23 : e2 ≤ e3 := by change (2 : ℝ) / 3 ≤ 1; norm_num
  have hle34 : e3 ≤ e4 := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit : curveAreaFunctional Γ =
      curveAreaFunctional (ContinuousBVPaths.restrict Γ e0 e1 hle01) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e1 e2 hle12) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e2 e3 hle23) +
        curveAreaFunctional (ContinuousBVPaths.restrict Γ e3 e4 hle34) := by
    have hcm : Monotone (![e0, e1, e2, e3, e4] : Fin 5 → Set.Icc (0 : ℝ) 2) := by
      refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
      fin_cases i
      · exact hle01
      · exact hle12
      · exact hle23
      · exact hle34
    have hsum := curveArea_eq_sum_restrict Γ ![e0, e1, e2, e3, e4] hcm rfl rfl
    rw [Fin.sum_univ_four] at hsum
    exact hsum
  -- each restriction, read off through an affine reparametrisation
  have hres : ∀ (u1 u2 : Set.Icc (0 : ℝ) 2) (hu : u1 ≤ u2)
      (t : Set.Icc ((u1 : ℝ)) ((u2 : ℝ))) (wp : Set.Icc (0 : ℝ) 2), (wp : ℝ) = (t : ℝ) →
      (ContinuousBVPaths.restrict Γ u1 u2 hu).val t = Γ.val wp :=
    fun _ _ _ _ _ hw ↦ congrArg (fun z ↦ Γ.val z) (Subtype.ext hw.symm)
  have hseg : ∀ (u1 u2 : Set.Icc (0 : ℝ) 2) (hu : u1 ≤ u2) (p q : Point)
      (φ : Set.Icc ((u1 : ℝ)) ((u2 : ℝ)) → Set.Icc (0 : ℝ) 1), Continuous φ → Monotone φ →
      Function.Surjective φ →
      (ContinuousBVPaths.restrict Γ u1 u2 hu).val = (lineSegmentBVPath p q).val ∘ φ →
      curveAreaFunctional (ContinuousBVPaths.restrict Γ u1 u2 hu) = segmentArea p q := by
    intro u1 u2 hu p q φ hφc hφm hφs hcomp
    rw [curveAreaFunctional_eq_of_comp_monotone_surjective zero_le_one hu
        (lineSegmentBVPath p q) _ φ hφc hφm hφs hcomp,
      curveAreaFunctional_lineSegmentBVPath]
  obtain ⟨φ₁, hφ₁c, hφ₁m, hφ₁s, hφ₁v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e0 : ℝ)) < ((e1 : ℝ)) by
      change (0 : ℝ) < 1 / 3; norm_num) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨φ₂, hφ₂c, hφ₂m, hφ₂s, hφ₂v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e1 : ℝ)) < ((e2 : ℝ)) by
      change (1 : ℝ) / 3 < 2 / 3; norm_num) hrl
  obtain ⟨φ₃, hφ₃c, hφ₃m, hφ₃s, hφ₃v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e2 : ℝ)) < ((e3 : ℝ)) by
      change (2 : ℝ) / 3 < 1; norm_num) (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨φ₄, hφ₄c, hφ₄m, hφ₄s, hφ₄v⟩ :=
    Set.Icc.exists_affine_monotone_surjection (show ((e3 : ℝ)) < ((e4 : ℝ)) by
      change (1 : ℝ) < 2; norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hp1 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e0 e1 hle01) =
      segmentArea (Q + v) (f r + v) := by
    refine hseg e0 e1 hle01 _ _ φ₁ hφ₁c hφ₁m hφ₁s ?_
    funext t
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 / 3 := t.property.2
    rw [hres e0 e1 hle01 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ (by linarith) rfl,
      hγ2 _ (by change (2 : ℝ) ≤ 3 - 3 * (t : ℝ); linarith)]
    change _ = Path.segment (Q + v) (f r + v) (φ₁ t)
    rw [segment_eq_add_smul, hφ₁v t,
      show (0 : ℝ) + ((t : ℝ) - ((e0 : ℝ))) / (((e1 : ℝ)) - ((e0 : ℝ))) * (1 - 0) =
        3 * (t : ℝ) from by change (0 : ℝ) + ((t : ℝ) - 0) / (1 / 3 - 0) * (1 - 0) = _; ring,
      show ((3 : ℝ) - 3 * (t : ℝ)) - 2 = 1 - 3 * (t : ℝ) from by ring]
    module
  have hp2 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e1 e2 hle12) =
      curveAreaFunctional (c + constBVPath r l v) := by
    refine curveAreaFunctional_eq_of_comp_monotone_surjective hrl.le hle12
      (c + constBVPath r l v) _ φ₂ hφ₂c hφ₂m hφ₂s ?_
    funext t
    have ht0 : (1 : ℝ) / 3 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 2 / 3 := t.property.2
    rw [hres e1 e2 hle12 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ (by linarith) rfl,
      hγ1 _ (by change (1 : ℝ) ≤ 3 - 3 * (t : ℝ); linarith)
        (by change (3 : ℝ) - 3 * (t : ℝ) ≤ 2; linarith),
      show l + (((3 : ℝ) - 3 * (t : ℝ)) - 1) * (r - l) = ((φ₂ t : ℝ)) from by
        rw [hφ₂v t]
        change _ = r + ((t : ℝ) - 1 / 3) / (2 / 3 - 1 / 3) * (l - r)
        ring]
    change f ((φ₂ t : ℝ)) + v = c.val (φ₂ t) + v
    rw [hcf (φ₂ t)]
  have hp3 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e2 e3 hle23) =
      segmentArea (f l + v) (P + v) := by
    refine hseg e2 e3 hle23 _ _ φ₃ hφ₃c hφ₃m hφ₃s ?_
    funext t
    have ht0 : (2 : ℝ) / 3 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    rw [hres e2 e3 hle23 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopLow _ ⟨3 - 3 * (t : ℝ), by constructor <;> linarith⟩ ht1 rfl,
      hγ0 _ (by change (3 : ℝ) - 3 * (t : ℝ) ≤ 1; linarith)]
    change _ = Path.segment (f l + v) (P + v) (φ₃ t)
    rw [segment_eq_add_smul, hφ₃v t,
      show (0 : ℝ) + ((t : ℝ) - ((e2 : ℝ))) / (((e3 : ℝ)) - ((e2 : ℝ))) * (1 - 0) =
        3 * (t : ℝ) - 2 from by
          change (0 : ℝ) + ((t : ℝ) - 2 / 3) / (1 - 2 / 3) * (1 - 0) = _
          ring]
    module
  have hp4 : curveAreaFunctional (ContinuousBVPaths.restrict Γ e3 e4 hle34) =
      segmentArea (P + v) (Q + v) := by
    refine hseg e3 e4 hle34 _ _ φ₄ hφ₄c hφ₄m hφ₄s ?_
    funext t
    have ht0 : (1 : ℝ) ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 2 := t.property.2
    rw [hres e3 e4 hle34 t ⟨(t : ℝ), by linarith, by linarith⟩ rfl,
      hloopHigh _ ht0]
    change _ = Path.segment (P + v) (Q + v) (φ₄ t)
    rw [segment_eq_add_smul, hφ₄v t,
      show (0 : ℝ) + ((t : ℝ) - ((e3 : ℝ))) / (((e4 : ℝ)) - ((e3 : ℝ))) * (1 - 0) =
        (t : ℝ) - 1 from by change (0 : ℝ) + ((t : ℝ) - 1) / (2 - 1) * (1 - 0) = _; ring]
    module
  -- assembling the four signed areas and undoing the shift
  rw [harea, ← hΓarea, hsplit, hp1, hp2, hp3, hp4,
    curveAreaFunctional_add_constBVPath hrl.le c v, hcf ⟨l, hrl.le, le_rfl⟩,
    hcf ⟨r, le_rfl, hrl.le⟩]
  simp only [segmentArea_add_right, hv0, hv1]
  ring

/-- Comparing the closed region under a strictly monotone roof with a base set that absorbs the
region's bottom edge and a set that absorbs the rest of the open region: the roof itself is a
null set, so the three areas satisfy the expected inequality. -/
theorem area_region_under_roof_le {h : ℝ} (γ : ContinuousBVPaths 0 3)
    (hγmono : StrictMono fun s ↦ γ.val s 0) (R T : Set Point)
    (hRfin : MeasureTheory.volume R ≠ ⊤) (hTfin : MeasureTheory.volume T ≠ ⊤)
    (hbase : ∀ p : Point, (∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0) → p 1 = -h → p ∈ R)
    (hincl : {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1} \ R ⊆ T) :
    ClassicalResults.area {p : Point | ∃ s : Set.Icc (0 : ℝ) 3,
        p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1} ≤
      ClassicalResults.area R + ClassicalResults.area T := by
  have h03 : (0 : ℝ) < 3 := by norm_num
  set Pu : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h ≤ p 1 ∧ p 1 ≤ γ.val s 1}
    with hPudef
  set Pu' : Set Point :=
    {p : Point | ∃ s : Set.Icc (0 : ℝ) 3, p 0 = γ.val s 0 ∧ -h < p 1 ∧ p 1 < γ.val s 1}
    with hPu'def
  have hsplit : Pu \ R ⊆ (Pu' \ R) ∪ Set.range γ.val := by
    rintro p ⟨hpP, hpR⟩
    obtain ⟨s, hs0, hs1, hs2⟩ := hpP
    rcases eq_or_lt_of_le hs1 with heq | hlt
    · exact absurd (hbase p ⟨s, hs0⟩ heq.symm) hpR
    · rcases eq_or_lt_of_le hs2 with heq2 | hlt2
      · refine Or.inr ⟨s, ?_⟩
        ext i
        fin_cases i
        · exact hs0.symm
        · exact heq2.symm
      · exact Or.inl ⟨⟨s, hs0, hlt, hlt2⟩, hpR⟩
  have hnull : MeasureTheory.volume (Set.range γ.val) = 0 := by
    refine ContinuousBVPaths.volume_range_eq_zero_of_injOn h03.le γ ?_
    intro a _ b _ hab
    exact hγmono.injective (congrArg (fun p : Point ↦ p 0) hab)
  have hkey : MeasureTheory.volume Pu ≤ MeasureTheory.volume R + MeasureTheory.volume T := by
    refine le_trans (MeasureTheory.measure_le_inter_add_sdiff _ _ R) ?_
    refine add_le_add (MeasureTheory.measure_mono Set.inter_subset_right) ?_
    refine le_trans (MeasureTheory.measure_mono hsplit) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    rw [hnull, add_zero]
    exact MeasureTheory.measure_mono hincl
  have hPufin : MeasureTheory.volume Pu ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hRfin, hTfin⟩) hkey
  simp only [ClassicalResults.area]
  rw [← ENNReal.toReal_add hRfin hTfin]
  exact (ENNReal.toReal_le_toReal hPufin (ENNReal.add_ne_top.mpr ⟨hRfin, hTfin⟩)).mpr hkey

end MovingSofa

end

end

end

end

end

end
