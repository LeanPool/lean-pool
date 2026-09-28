/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.ForMathlib.Topology.Foundations.Development001
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.SetSemiring
public import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
/-!
# Moving sofa: related mathematical developments

* `ForMathlib.MeasureTheory.StieltjesTransport`.
* `ForMathlib.MeasureTheory.VectorMeasure.LocallyConstant`.
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
# For Mathlib / Measure Theory / Stieltjes Transport
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

/-- A monotone surjection of compact intervals preserves bounded variation. -/
theorem BoundedVariationOn.comp_monotone_surjective_Icc
    {a b c d : ℝ} (_hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    {φ : Set.Icc c d → Set.Icc a b} (hφ : Monotone φ) (hφs : Function.Surjective φ) :
    BoundedVariationOn (f ∘ φ) Set.univ := by
  let _ : Fact (a ≤ b) := ⟨_hab⟩
  rw [BoundedVariationOn,
    eVariationOn.comp_eq_of_monotoneOn (t := Set.univ) f φ
      (fun _ _ _ _ hxy ↦ hφ hxy)]
  rw [Set.image_univ, hφs.range_eq]
  exact hf

/-- The Stieltjes measure is preserved by continuous monotone surjective reparametrization. -/
theorem BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) {φ : Set.Icc c d → Set.Icc a b} (hφc : Continuous φ)
    (hφ : Monotone φ) (hφs : Function.Surjective φ) :
    (BoundedVariationOn.comp_monotone_surjective_Icc hab hf hφ hφs).vectorMeasure.map φ =
      hf.vectorMeasure := by
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let _ : Fact (c ≤ d) := ⟨hcd⟩
  let hfφ := BoundedVariationOn.comp_monotone_surjective_Icc hab hf hφ hφs
  have fiberGreatest (y : Set.Icc a b) :
      ∃ x, IsGreatest (φ ⁻¹' {y}) x := by
    apply (isClosed_singleton.preimage hφc).isCompact.exists_isGreatest
    rcases hφs y with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  have preimage_Ioc (u v : Set.Icc a b) :
      ∃ x y, φ x = u ∧ φ y = v ∧ (u ≤ v → x ≤ y) ∧
        φ ⁻¹' Ioc u v = Ioc x y := by
    obtain ⟨x, hxmem, hxmax⟩ := fiberGreatest u
    obtain ⟨y, hymem, hymax⟩ := fiberGreatest v
    change φ x = u at hxmem
    change φ y = v at hymem
    have hxy : u ≤ v → x ≤ y := by
      intro huv
      by_contra hxy
      have hyx : y ≤ x := le_of_not_ge hxy
      have huv' : u = v := le_antisymm huv (hxmem ▸ hymem ▸ hφ hyx)
      exact hxy (hymax (by change φ x = v; rw [hxmem, huv']))
    refine ⟨x, y, hxmem, hymem, hxy, Set.ext fun z ↦ ?_⟩
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro hz
    · constructor
      · by_contra hzx
        have hzx' : z ≤ x := le_of_not_gt hzx
        exact (not_le_of_gt hz.1) (hxmem ▸ hφ hzx')
      · by_contra hyz
        have hyz' : y < z := lt_of_not_ge hyz
        have hvz : v ≤ φ z := hymem ▸ hφ hyz'.le
        have : φ z = v := le_antisymm hz.2 hvz
        exact (not_le_of_gt hyz') (hymax this)
    · constructor
      · have hux : u ≤ φ z := hxmem ▸ hφ hz.1.le
        exact hux.lt_of_ne fun hzu ↦ (not_le_of_gt hz.1) (hxmax hzu.symm)
      · exact hymem ▸ hφ hz.2
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hright_comp (x : Set.Icc c d) : (f ∘ φ).rightLim x = (f ∘ φ) x :=
    (hfc.comp hφc).continuousAt.continuousWithinAt.rightLim_eq
  have hinterval (u v : Set.Icc a b) (huv : u ≤ v) :
      (hfφ.vectorMeasure.map φ) (Ioc u v) = hf.vectorMeasure (Ioc u v) := by
    obtain ⟨x, y, hx, hy, hxy, hpre⟩ := preimage_Ioc u v
    rw [VectorMeasure.map_apply _ hφc.measurable measurableSet_Ioc, hpre,
      hfφ.vectorMeasure_Ioc (hxy huv), hf.vectorMeasure_Ioc huv, hright_comp, hright_comp,
      hright, hright, Function.comp_apply, Function.comp_apply, hx, hy]
  apply VectorMeasure.ext_of_generateFrom
      {s | ∃ u v : Set.Icc a b, u ≤ v ∧ s = Ioc u v}
  · rintro s ⟨u, v, huv, rfl⟩
    exact hinterval u v huv
  · exact BorelSpace.measurable_eq.trans <| by
      rw [borel_eq_generateFrom_Ioc_le]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
  · exact IsSetSemiring.isPiSystem IsSetSemiring.Ioc
  · have hφtop : φ ⊤ = ⊤ := by
      obtain ⟨x, hx⟩ := hφs ⊤
      exact top_unique (hx ▸ hφ le_top)
    have hφbot : φ ⊥ = ⊥ := by
      obtain ⟨x, hx⟩ := hφs ⊥
      exact bot_unique (hx ▸ hφ bot_le)
    have htopφ : Filter.atTop.limUnder (f ∘ φ) = (f ∘ φ) ⊤ := by
      apply tendsto_nhds_unique hfφ.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbotφ : Filter.atBot.limUnder (f ∘ φ) = (f ∘ φ) ⊥ := by
      apply tendsto_nhds_unique hfφ.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    have htop : Filter.atTop.limUnder f = f ⊤ := by
      apply tendsto_nhds_unique hf.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbot : Filter.atBot.limUnder f = f ⊥ := by
      apply tendsto_nhds_unique hf.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    rw [VectorMeasure.map_apply _ hφc.measurable MeasurableSet.univ, preimage_univ,
      hfφ.vectorMeasure_univ, hf.vectorMeasure_univ, htopφ, hbotφ, htop, hbot,
      Function.comp_apply, Function.comp_apply, hφtop, hφbot]

/-- The Stieltjes measure of a continuous BV function has no point masses. -/
theorem BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous
    {a b : ℝ} {f : Set.Icc a b → ℝ} (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) (x : Set.Icc a b) : hf.vectorMeasure {x} = 0 := by
  rw [hf.vectorMeasure_singleton,
    hfc.continuousAt.continuousWithinAt.rightLim_eq,
    hfc.continuousAt.continuousWithinAt.leftLim_eq, sub_self]

/-- The Stieltjes measure on a closed subinterval pushes forward to the half-open restriction. -/
theorem BoundedVariationOn.vectorMeasure_map_Icc_inclusion
    {a b : ℝ} {f : Set.Icc a b → ℝ} (hf : BoundedVariationOn f Set.univ)
    (hfc : Continuous f) (l u : Set.Icc a b) (hlu : l ≤ u) :
    let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hfr : BoundedVariationOn (f ∘ ι) Set.univ :=
      ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    hfr.vectorMeasure.map ι = hf.vectorMeasure.restrict (Ioc l u) := by
  dsimp only
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
    ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
  let hfr : BoundedVariationOn (f ∘ ι) Set.univ :=
    ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f ι
      (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
  let _ : Fact ((l : ℝ) ≤ u) := ⟨hlu⟩
  change hfr.vectorMeasure.map ι = hf.vectorMeasure.restrict (Ioc l u)
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hright_comp (x : Set.Icc (l : ℝ) u) : (f ∘ ι).rightLim x = (f ∘ ι) x :=
    (hfc.comp hι).continuousAt.continuousWithinAt.rightLim_eq
  have htop : Filter.atTop.limUnder (f ∘ ι) = (f ∘ ι) ⊤ := by
    apply tendsto_nhds_unique hfr.tendsto_atTop_limUnder
    rw [Filter.atTop_eq_pure_of_isTop isTop_top]
    exact tendsto_pure_nhds _ _
  have hbot : Filter.atBot.limUnder (f ∘ ι) = (f ∘ ι) ⊥ := by
    apply tendsto_nhds_unique hfr.tendsto_atBot_limUnder
    rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
    exact tendsto_pure_nhds _ _
  apply VectorMeasure.ext_of_generateFrom (Set.range Iic)
  · rintro s ⟨x, rfl⟩
    rw [VectorMeasure.map_apply _ hι.measurable measurableSet_Iic,
      VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Iic]
    by_cases hxl : x < l
    · have hp : ι ⁻¹' Iic x = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact (not_le_of_gt hxl) (le_trans y.property.1 hy)
      have hi : Iic x ∩ Ioc l u = ∅ := by ext y; simp; grind
      simp [hp, hi]
    · by_cases hxu : u ≤ x
      · have hp : ι ⁻¹' Iic x = Set.univ := by
          apply eq_univ_of_forall
          intro y
          exact le_trans y.property.2 hxu
        have hi : Iic x ∩ Ioc l u = Ioc l u := by ext y; simp; grind
        rw [hp, hi, hfr.vectorMeasure_univ, hf.vectorMeasure_Ioc hlu]
        rw [htop, hbot, hright, hright]
        rfl
      · have hlx : l ≤ x := le_of_not_gt hxl
        have hxu' : x ≤ u := le_of_not_ge hxu
        let y : Set.Icc (l : ℝ) u := ⟨x, hlx, hxu'⟩
        have hp : ι ⁻¹' Iic x = Iic y := by ext z; rfl
        have hi : Iic x ∩ Ioc l u = Ioc l x := by ext z; simp; grind
        rw [hp, hi, hfr.vectorMeasure_Iic, hf.vectorMeasure_Ioc hlx,
          hright_comp, hbot, hright, hright]
        rfl
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic _)
  · exact isPiSystem_Iic
  · rw [VectorMeasure.map_apply _ hι.measurable MeasurableSet.univ,
      preimage_univ, VectorMeasure.restrict_apply_univ,
      hfr.vectorMeasure_univ, hf.vectorMeasure_Ioc hlu, htop, hbot, hright, hright]
    rfl

/-- An antitone surjection of compact intervals preserves bounded variation. -/
theorem BoundedVariationOn.comp_antitone_surjective_Icc
    {a b c d : ℝ} (_hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ)
    {φ : Set.Icc c d → Set.Icc a b} (hφ : Antitone φ)
    (hφs : Function.Surjective φ) :
    BoundedVariationOn (f ∘ φ) Set.univ := by
  let _ : Fact (a ≤ b) := ⟨_hab⟩
  rw [BoundedVariationOn,
    eVariationOn.comp_eq_of_antitoneOn (t := Set.univ) f φ
      (fun _ _ _ _ hxy ↦ hφ hxy)]
  rw [Set.image_univ, hφs.range_eq]
  exact hf

/-- Reversing a continuous BV function negates its transported Stieltjes measure. -/
theorem BoundedVariationOn.vectorMeasure_map_reverse_Icc
    {a b : ℝ} (hab : a ≤ b) {f : Set.Icc a b → ℝ}
    (hf : BoundedVariationOn f Set.univ) (hfc : Continuous f) :
    let r := Set.Icc.reverse hab
    let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab hf
      (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
    hfr.vectorMeasure.map r = -hf.vectorMeasure := by
  dsimp only
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let r := Set.Icc.reverse hab
  let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab hf
    (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
  have hr : Continuous r := Set.Icc.continuous_reverse hab
  have hleft (x : Set.Icc a b) : f.leftLim x = f x :=
    hfc.continuousAt.continuousWithinAt.leftLim_eq
  have hleft_comp (x : Set.Icc a b) : (f ∘ r).leftLim x = (f ∘ r) x :=
    (hfc.comp hr).continuousAt.continuousWithinAt.leftLim_eq
  have hright (x : Set.Icc a b) : f.rightLim x = f x :=
    hfc.continuousAt.continuousWithinAt.rightLim_eq
  have hpre (u v : Set.Icc a b) :
      r ⁻¹' Ioc u v = Ico (r v) (r u) := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    change (u : ℝ) < a + b - x ∧ a + b - x ≤ v ↔
      a + b - v ≤ x ∧ x < a + b - u
    constructor <;> intro hx <;> constructor <;> linarith
  have hinterval (u v : Set.Icc a b) (huv : u ≤ v) :
      (hfr.vectorMeasure.map r) (Ioc u v) = (-hf.vectorMeasure) (Ioc u v) := by
    rw [MeasureTheory.VectorMeasure.map_apply _ hr.measurable measurableSet_Ioc, hpre,
      hfr.vectorMeasure_Ico ((Set.Icc.antitone_reverse hab) huv)]
    change _ = -(hf.vectorMeasure (Ioc u v))
    rw [hf.vectorMeasure_Ioc huv, hleft_comp, hleft_comp, hright, hright]
    simp [r, Set.Icc.reverse, Function.comp_apply]
  apply MeasureTheory.VectorMeasure.ext_of_generateFrom
      {s | ∃ u v : Set.Icc a b, u ≤ v ∧ s = Ioc u v}
  · rintro s ⟨u, v, huv, rfl⟩
    exact hinterval u v huv
  · exact BorelSpace.measurable_eq.trans <| by
      rw [borel_eq_generateFrom_Ioc_le]
      congr 1
      ext s
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
      · rintro ⟨u, v, huv, rfl⟩
        exact ⟨u, v, huv, rfl⟩
  · exact IsSetSemiring.isPiSystem IsSetSemiring.Ioc
  · rw [MeasureTheory.VectorMeasure.map_apply _ hr.measurable MeasurableSet.univ,
      preimage_univ, hfr.vectorMeasure_univ]
    change _ = -(hf.vectorMeasure Set.univ)
    rw [hf.vectorMeasure_univ]
    have htop : Filter.atTop.limUnder (f ∘ r) = f ⊥ := by
      apply tendsto_nhds_unique hfr.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      convert tendsto_pure_nhds (f ∘ r) ⊤ using 1
      apply congrArg nhds
      apply congrArg f
      apply Subtype.ext
      change a = a + b - b
      ring
    have hbot : Filter.atBot.limUnder (f ∘ r) = f ⊤ := by
      apply tendsto_nhds_unique hfr.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      convert tendsto_pure_nhds (f ∘ r) ⊥ using 1
      apply congrArg nhds
      apply congrArg f
      apply Subtype.ext
      change b = a + b - a
      ring
    have htopf : Filter.atTop.limUnder f = f ⊤ := by
      apply tendsto_nhds_unique hf.tendsto_atTop_limUnder
      rw [Filter.atTop_eq_pure_of_isTop isTop_top]
      exact tendsto_pure_nhds _ _
    have hbotf : Filter.atBot.limUnder f = f ⊥ := by
      apply tendsto_nhds_unique hf.tendsto_atBot_limUnder
      rw [Filter.atBot_eq_pure_of_isBot isBot_bot]
      exact tendsto_pure_nhds _ _
    rw [htop, hbot, htopf, hbotf]
    simp

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
# For Mathlib / Measure Theory / Vector Measure / Locally Constant
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Local constancy away from the initial endpoint gives a variation-null neighborhood. -/
theorem BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    {a b : ℝ} (hab : a < b) {g : Set.Icc a b → ℝ}
    (hg : BoundedVariationOn g Set.univ)
    (hr : ∀ y, ContinuousWithinAt g (Set.Ici y) y) (x : Set.Icc a b)
    (hxbot : a < (x : ℝ))
    (hx : g =ᶠ[𝓝 x] fun _ ↦ g x) :
    ∃ U ∈ 𝓝 x, hg.vectorMeasure.variation U = 0 := by
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hright (y : Set.Icc a b) : Function.rightLim g y = g y :=
    (hr y).rightLim_eq
  by_cases hxtop : x = ⊤
  · subst x
    obtain ⟨c, hc, hsub⟩ := (nhds_top_basis.mem_iff.mp hx)
    refine ⟨Set.Ioi c, nhds_top_basis.mem_iff.mpr ⟨c, hc, subset_rfl⟩, ?_⟩
    rw [hg.variation_vectorMeasure_Ioi]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm
  · have hxlt : x < ⊤ := lt_top_iff_ne_top.mpr hxtop
    have hxgt : ⊥ < x := hxbot
    obtain ⟨c, d, hxcd, hsub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨⊥, hxgt⟩ ⟨⊤, hxlt⟩).mp hx
    refine ⟨Set.Ioo c d, Ioo_mem_nhds hxcd.1 hxcd.2, ?_⟩
    rw [hg.variation_vectorMeasure_Ioo_right]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm

end

end

end
