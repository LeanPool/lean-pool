/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Area.Applications.Development003
public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development003
public import LeanPool.MovingSofa.Area.Foundations.Development004
public import LeanPool.MovingSofa.Cap.Foundations.Development003
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Cap.Applications.Development005
public import LeanPool.MovingSofa.Convex.Foundations.Development004
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
/-!
# Moving sofa: related mathematical developments

* `Cap.InnerCornerVariation`.
* `Cap.CornerModuloLinear`.
* `Cap.Tail.AreaBounds`.
* `Cap.UpperBoundaryTracing`.
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
# The inner-corner variation on the middle window

On the middle window `I = [φᴿ, φᴸ]` the inner corner of a special cap is
`(h_K(t) - 1) • u_t + (h_K(t + π/2) - 1) • v_t`, an affine expression in two support values, so it
depends convex-linearly on the cap. `capInnerCorner_variation` pulls the quadratic curve-area
functional back along that convex-linear map, which gives quadraticity of
`K ↦ 𝒥(x_K|_I)` and reduces its directional derivative to the curve-variation formula.

The remaining work is to recognize the two mixed Stieltjes integrals of that formula as the
pairing of the support increment against the corner measure. The inner corner is `C¹` on the cap
domain by the injectivity condition, so its Stieltjes measure is its classical velocity times
Lebesgue measure; the frame identity `planeCrossProduct_eq_inner_frame` then turns the pointwise
cross product into the corner density against the support increment, on `I` and on `I + π/2`
separately.
-/

/-! ### The middle window -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The two distinguished Gerver angles are positive, ordered, and below `π / 2`, so the middle
window `[φᴿ, φᴸ]` and its quarter turn are disjoint subsets of `[0, π]`. -/
private theorem middleWindow_bounds :
    0 < paperGerverConstants.2.1 ∧ paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 ∧
      paperGerverConstants.2.2 < Real.pi / 2 := by
  obtain ⟨hr, hl, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hle : paperGerverConstants.2.1 ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  exact ⟨hr.1, by linarith only [hle, hsum], hl.2⟩

/-- The middle window lies inside the cap's angular domain. -/
private theorem middleWindow_subset :
    Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ⊆ Set.Icc 0 (Real.pi / 2) := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  exact Set.Icc_subset_Icc hrpos.le hlpi.le

/-! ### Regularity of the inner corner of a special cap -/

/-- The inner corner of a special cap is continuously differentiable on the cap domain. -/
private theorem specialCap_contDiffOn (K : SpecialCapSpace) :
    ContDiffOn ℝ 1 (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1

/-- At an interior time the inner corner of a special cap has an honest derivative. -/
private theorem specialCap_hasDerivAt (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (capInnerCorner K.val)
      (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t :=
  ((specialCap_contDiffOn K).differentiableOn one_ne_zero t
    (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-! ### The corner density on the two middle windows -/

/-- On the right middle window the corner density is the tangent velocity component. -/
private theorem capCornerDensity_eq_right (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    capCornerDensity K s = (capVelocityCoefficients K s).2 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  rw [capCornerDensity, ite_eq_left ⟨lt_of_lt_of_le hrpos hs.1, hs.2.trans hlpi.le⟩]

/-- On the left middle window the corner density is the shifted normal velocity component. -/
private theorem capCornerDensity_eq_left (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2)) :
    capCornerDensity K s = -(capVelocityCoefficients K (s - Real.pi / 2)).1 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have h1 : Real.pi / 2 < s := by linarith [hs.1]
  have h2 : s ≤ Real.pi := by linarith [hs.2]
  rw [capCornerDensity, ite_eq_right (by rintro ⟨-, h⟩; linarith), ite_eq_left ⟨h1, h2⟩]

/-- The corner density is nonnegative on the middle windows, by the injectivity signs. -/
private theorem capCornerDensity_nonneg_middle (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :
    0 ≤ capCornerDensity K s := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have hsign := K.property.1.2.2
  rcases hs with hs | hs
  · rw [capCornerDensity_eq_right K hs]
    exact (hsign s ⟨lt_of_lt_of_le hrpos hs.1, lt_of_le_of_lt hs.2 hlpi⟩).2.le
  · rw [capCornerDensity_eq_left K hs]
    have hmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact neg_nonneg.mpr (hsign _ hmem).1.le

/-- The corner density is continuous on each of the two middle windows. -/
private theorem continuousOn_capCornerDensity_middle (K : SpecialCapSpace) :
    ContinuousOn (capCornerDensity K)
        (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) ∧
      ContinuousOn (capCornerDensity K)
        (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)) := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  refine ⟨(hβ.mono middleWindow_subset).congr fun s hs ↦ capCornerDensity_eq_right K hs, ?_⟩
  have hmaps : Set.MapsTo (fun s : ℝ ↦ s - Real.pi / 2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ContinuousOn.congr ?_ fun s hs ↦ capCornerDensity_eq_left K hs
  exact (((hα.mono middleWindow_subset).comp
    (continuous_id.sub continuous_const).continuousOn hmaps)).neg

/-! ### Integrating against the corner angle measure -/

/-- On a parameter window inside `[0, π]` the corner angle measure integrates a continuous
function against the real corner density. -/
private theorem setIntegral_capCornerAngleMeasure (K : SpecialCapSpace) {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hS : S ⊆ Set.Icc 0 Real.pi)
    (hd : AEMeasurable (capCornerDensity K) (volume.restrict S))
    (hdpos : ∀ s ∈ S, 0 ≤ capCornerDensity K s) {f : Real.Angle → ℝ} (hf : Continuous f) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in S, capCornerDensity K s * f (s : Real.Angle) := by
  have hcoe : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hSIoc : S ⊆ Set.Ioc (-1) Real.pi := fun s hs ↦ ⟨by linarith [(hS hs).1], (hS hs).2⟩
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSmeas hSIoc
  have hApre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) := himg.preimage hcoe
  have hAS : ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) ∩ Set.Icc 0 Real.pi = S := by
    refine Set.Subset.antisymm ?_ fun s hs ↦ ⟨⟨s, hs, rfl⟩, hS hs⟩
    rintro x ⟨⟨s, hs, hxs⟩, hx⟩
    have hxIoc : x ∈ Set.Ioc (-1) Real.pi := ⟨by linarith [hx.1], hx.2⟩
    exact (Real.Angle.injOn_coe_Ioc hturn (hSIoc hs) hxIoc hxs) ▸ hs
  have h1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K := by
    rw [capCornerAngleMeasure]
    exact setIntegral_map himg hf.aestronglyMeasurable hcoe.aemeasurable
  have hrestrict : (volume.restrict (Set.Icc 0 Real.pi)).restrict
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) =
      volume.restrict S := by
    rw [Measure.restrict_restrict hApre, hAS]
  have haem : AEMeasurable (fun s ↦ ENNReal.ofReal (capCornerDensity K s))
      ((volume.restrict (Set.Icc 0 Real.pi)).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S))) := by
    rw [hrestrict]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hd
  have h2 : ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        (ENNReal.ofReal (capCornerDensity K s)).toReal • f (s : Real.Angle)
          ∂volume.restrict (Set.Icc 0 Real.pi) := by
    rw [capCornerMeasure]
    exact setIntegral_withDensity_eq_setIntegral_toReal_smul₀ haem
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _ hApre
  rw [h1, h2]
  change ∫ s, _ ∂((volume.restrict (Set.Icc 0 Real.pi)).restrict _) = _
  rw [hrestrict]
  refine setIntegral_congr_fun hSmeas fun s hs ↦ ?_
  rw [ENNReal.toReal_ofReal (hdpos s hs), smul_eq_mul]

/-! ### The middle Stieltjes integrals as weighted Lebesgue integrals -/

/-- The middle corner path's Stieltjes measure has the inner-corner velocity as density. -/
private theorem capMiddle_stieltjesDensity (K : SpecialCapSpace) (i : Fin 2) :
    HasIntervalStieltjesDensity (continuousBVCoordinate (capMiddleBV K) i)
      (fun t ↦ derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  have hproj : ContDiff ℝ 1 fun p : Point ↦ p i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  refine hasIntervalStieltjesDensity_of_hasDerivAt hrl _
    (fun s ↦ capInnerCorner K.val s i) _ (fun _ ↦ rfl) ?_ ?_ ?_
  · refine ContDiffOn.absolutelyContinuousOnInterval ?_
    rw [Set.uIcc_of_le hrl]
    exact hproj.comp_contDiffOn ((specialCap_contDiffOn K).mono middleWindow_subset)
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hrpos.trans ht.1, ht.2.trans hlpi⟩
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (specialCap_hasDerivAt K ht')
  · exact (((PiLp.continuous_apply 2 _ i).comp_continuousOn
      ((continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset))).integrableOn_compact
        isCompact_Icc

/-- A mixed Stieltjes integral over the middle window is the corresponding weighted Lebesgue
integral of the inner-corner velocity. -/
private theorem capMiddle_stieltjesIntegral_eq (K L : SpecialCapSpace) (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate (capMiddleBV K) i)
        (fun t ↦ (capMiddleBV L).val t j - (capMiddleBV K).val t j) Set.univ =
      ∫ t in Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        (capInnerCorner L.val t j - capInnerCorner K.val t j) *
          derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i := by
  have hq : Continuous fun t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ↦
      (capMiddleBV L).val t j - (capMiddleBV K).val t j :=
    ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV L).property.1).sub
      ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV K).property.1)
  have hval : ∀ (M : SpecialCapSpace)
      (t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (capMiddleBV M).val t = capInnerCorner M.val t.val := fun _ _ ↦ rfl
  rw [intervalStieltjesIntegral_eq_integral_mul_of_density _ (capMiddle_stieltjesDensity K i)
    hq Set.univ MeasurableSet.univ, Measure.restrict_univ]
  simp only [hval]
  have key := MeasureTheory.integral_subtype_preimage (μ := volume)
    (s := Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) measurableSet_Icc
    (MeasurableSet.univ (α := ℝ))
    (fun t : ℝ ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
      derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ] at key
  exact key

/-! ### The variation of the inner corner -/

theorem capInnerCorner_variation :
    IsConvexLinear specialCapCombination bvPathCombination capMiddleBV ∧
    IsQuadraticFunctional specialCapCombination (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ curveAreaFunctional (capMiddleBV M)) K L =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue L.val.val t - supportValue K.val.val t) ∂capCornerAngleMeasure K) +
        (segmentArea (distinguishedCapSides K.val).2.corner
            (distinguishedCapSides L.val).2.corner -
          segmentArea (distinguishedCapSides K.val).1.corner
            (distinguishedCapSides L.val).1.corner) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  -- ### The middle corner path is convex-linear
  have hlinear : IsConvexLinear specialCapCombination bvPathCombination capMiddleBV := by
    intro t K L
    refine Subtype.ext (funext fun s ↦ ?_)
    show capInnerCorner (specialCapCombination t K L).val s.val = _
    rw [capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)]
    rfl
  refine ⟨hlinear, (curveArea_variation _ _ hrl).1.comp_isConvexLinear hlinear, ?_⟩
  intro K L
  rw [convexDirectionalDerivative_comp_isConvexLinear hlinear _ K L,
    (curveArea_variation _ _ hrl).2]
  refine congrArg₂ (· + ·) ?_ rfl
  -- ### The middle window and the corner density on it
  have hSmeas : MeasurableSet (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) := measurableSet_Icc.union measurableSet_Icc
  have hSsub : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2) ⊆ Set.Icc 0 Real.pi := by
    have hpi := Real.pi_pos
    rintro s (hs | hs)
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨hdc1, hdc2⟩ := continuousOn_capCornerDensity_middle K
  have hd : AEMeasurable (capCornerDensity K)
      (volume.restrict (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2))) :=
    (hdc1.union_of_isClosed hdc2 isClosed_Icc isClosed_Icc).aemeasurable hSmeas
  have hcont (M : ConvexBody Point) : Continuous fun u : Real.Angle ↦ supportValue M u :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hfcont : Continuous fun u : Real.Angle ↦ supportValue (L.val.val : Set Point) u -
      supportValue (K.val.val : Set Point) u := (hcont L.val.val).sub (hcont K.val.val)
  have hfreal : Continuous fun s : ℝ ↦ supportValue (L.val.val : Set Point) (s : Real.Angle) -
      supportValue (K.val.val : Set Point) (s : Real.Angle) :=
    hfcont.comp Real.Angle.continuous_coe
  -- ### Continuity of the four Lebesgue integrands on the middle window
  have hXc : ContinuousOn (capInnerCorner K.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn K).mono middleWindow_subset).continuousOn
  have hYc : ContinuousOn (capInnerCorner L.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn L).mono middleWindow_subset).continuousOn
  have hDc : ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset
  have hmixed (i j : Fin 2) : IntegrableOn
      (fun t ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
        derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((((PiLp.continuous_apply 2 _ j).comp_continuousOn hYc).sub
      ((PiLp.continuous_apply 2 _ j).comp_continuousOn hXc)).mul
      ((PiLp.continuous_apply 2 _ i).comp_continuousOn hDc)).integrableOn_compact isCompact_Icc
  have hG1 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (hdc1.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hG2 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    (hdc2.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hmaps : Set.MapsTo (fun t : ℝ ↦ t + Real.pi / 2)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hG2' : IntegrableOn (fun t ↦ capCornerDensity K (t + Real.pi / 2) *
      (supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (((hdc2.mul hfreal.continuousOn).comp
      (continuous_id.add continuous_const).continuousOn hmaps)).integrableOn_compact isCompact_Icc
  -- ### Both sides are Lebesgue integrals over the middle window
  rw [capMiddle_stieltjesIntegral_eq K L 1 0, capMiddle_stieltjesIntegral_eq K L 0 1,
    setIntegral_capCornerAngleMeasure K hSmeas hSsub hd
      (fun s hs ↦ capCornerDensity_nonneg_middle K hs) hfcont,
    setIntegral_union (Set.disjoint_left.mpr fun s hs hs' ↦ by linarith [hs.2, hs'.1])
      measurableSet_Icc hG1 hG2,
    integral_Icc_const_add_eq (Real.pi / 2),
    ← integral_sub (hmixed 1 0) (hmixed 0 1), ← integral_add hG1 hG2']
  -- ### The pointwise cross-product identity
  refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
  have hts : t + Real.pi / 2 ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2) := hmaps ht
  have hdens1 : capCornerDensity K t =
      inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle)) := capCornerDensity_eq_right K ht
  have hdens2 : capCornerDensity K (t + Real.pi / 2) =
      -inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) := by
    rw [capCornerDensity_eq_left K hts]
    simp only [add_sub_cancel_right, capVelocityCoefficients]
  have hu : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (normalVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) (t : Real.Angle) -
        supportValue (K.val.val : Set Point) (t : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_normalVector, inner_capInnerCorner_normalVector]
    ring
  have hv : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (tangentVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_tangentVector, inner_capInnerCorner_tangentVector]
    ring
  have hframe := planeCrossProduct_eq_inner_frame
    (capInnerCorner L.val t - capInnerCorner K.val t)
    (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t
  have hs0 : (capInnerCorner L.val t - capInnerCorner K.val t) 0 =
      capInnerCorner L.val t 0 - capInnerCorner K.val t 0 := by simp
  have hs1 : (capInnerCorner L.val t - capInnerCorner K.val t) 1 =
      capInnerCorner L.val t 1 - capInnerCorner K.val t 1 := by simp
  rw [planeCrossProduct, hs0, hs1] at hframe
  rw [hdens1, hdens2, ← hu, ← hv]
  linear_combination hframe

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
# The outer corner and the two wedge segments, modulo convex-linear functionals

On the middle window `I = [φᴿ, φᴸ]` the outer corner of a cap is its inner corner translated by the
`K`-independent frame sum `c t = u_t + v_t`, so the two curve-area functionals differ by the two
mixed Stieltjes cross integrals, each convex-linear in `K`, plus the constant area of `c`.

The same happens at the two ends of the window: the tangent-line intersection point and the wedge
endpoint differ by a fixed vector, as do the outer and the inner corner, so each of the two
segment-area comparisons differs by a determinant that is affine in the support values and in the
inner corner, hence convex-linear in `K` as well.
-/

/-! ### The outer corner path on the middle window -/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The frame sum `t ↦ u_t + v_t`, as a continuous path of bounded variation. -/
def frameSumBV (a b : ℝ) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn
    (fun t ↦ normalVector (t : Real.Angle) + tangentVector (t : Real.Angle))
    ((contDiff_normalVector.add contDiff_tangentVector).of_le
      (by exact_mod_cast le_top)).contDiffOn

/-- The outer corner of a special cap on the middle window, as a continuous path of bounded
variation: the inner-corner path translated by the frame sum. -/
def capOuterMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capMiddleBV K + frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2

/-- The outer middle path of a special cap traces the outer corner of its body. -/
theorem capOuterMiddleBV_val (K : SpecialCapSpace)
    (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    (capOuterMiddleBV K).val s =
      (rotatingHallwayParts (K.val.val : Set Point) ((s : ℝ) : Real.Angle)).outerCorner :=
  (outerCorner_eq_innerCorner_add K.val.val (s : ℝ)).symm

/-! ### The two end segments -/

/-- At the right Gerver angle the tangent-line intersection point is the right wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_fst (K : RightAngleCapSpace)
    (hcos : Real.cos paperGerverConstants.2.1 ≠ 0) :
    supportingIntersection K.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.1).1 +
        !₂[(1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1, 1] := by
  have hangle : ((Real.pi / 2 : ℝ) : Real.Angle) - (paperGerverConstants.2.1 : Real.Angle) =
      ((Real.pi / 2 - paperGerverConstants.2.1 : ℝ) : Real.Angle) := by rw [Real.Angle.coe_sub]
  have hpyth := Real.sin_sq_add_cos_sq paperGerverConstants.2.1
  obtain ⟨hW0, hW1⟩ := wedgeEndpoints_fst_coords K paperGerverConstants.2.1
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, hW0, hW1]
  · field_simp
    linear_combination (supportValue (K.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)) * hpyth
  · field_simp
    ring

/-- At the left Gerver angle the tangent-line intersection point is the left wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_snd (K : RightAngleCapSpace)
    (hsin : Real.sin paperGerverConstants.2.2 ≠ 0) :
    supportingIntersection K.val ((Real.pi / 2 : ℝ) : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.2).2 +
        !₂[(Real.cos paperGerverConstants.2.2 - 1) /
          Real.sin paperGerverConstants.2.2, 1] := by
  have hangle : ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle) = (paperGerverConstants.2.2 : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show Real.pi / 2 + paperGerverConstants.2.2 - Real.pi / 2 =
      paperGerverConstants.2.2 from by ring]
  obtain ⟨hZ0, hZ1⟩ := wedgeEndpoints_snd_coords K paperGerverConstants.2.2
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hZ0, hZ1] <;>
    field_simp <;> ring_nf

/-- A pair of segment areas whose endpoints are fixed translates of a second pair differs from it
by a determinant, which is convex-linear as soon as the two base points are. -/
private theorem segmentArea_equivalent_of_translations {α : Type*} (cα : I → α → α → α)
    {W X P Q : α → Point} {v w : Point} (hP : ∀ K, P K = W K + w) (hQ : ∀ K, Q K = X K + v)
    (hW : ∀ (t : I) (K L : α), W (cα t K L) = (1 - (t : ℝ)) • W K + (t : ℝ) • W L)
    (hX : ∀ (t : I) (K L : α), X (cα t K L) = (1 - (t : ℝ)) • X K + (t : ℝ) • X L) :
    EquivalentModuloConvexLinear cα (fun K ↦ segmentArea (P K) (Q K))
      (fun K ↦ segmentArea (W K) (X K)) := by
  intro t K L
  simp only [hP, hQ, hW, hX, realCombination, segmentArea, planeCrossProduct, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### The main equivalence -/

theorem cornerArea_equivalent_modulo_linear :
    ∃ F : SpecialCapSpace →
        ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2,
      (∀ K, (F K).val = fun t ↦
        (rotatingHallwayParts (K.val.val : Set Point) (t.val : Real.Angle)).outerCorner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ curveAreaFunctional (F K))
        (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.1 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).1.fanPoint
          (distinguishedCapSides K.val).1.corner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).2.fanPoint
          (distinguishedCapSides K.val).2.corner) := by
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl : paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 :=
    paperGerverConstants_snd_fst_lt_snd_snd.le
  refine ⟨capOuterMiddleBV, fun K ↦ funext (capOuterMiddleBV_val K), ?_, ?_, ?_⟩
  -- ### The middle window: translation by the frame-sum path
  · intro t K L
    show curveAreaFunctional (capMiddleBV (specialCapCombination t K L) +
        frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2) -
      curveAreaFunctional (capMiddleBV (specialCapCombination t K L)) = _
    rw [capInnerCorner_variation.1 t K L]
    exact curveArea_translation_convexLinear hrl _ t (capMiddleBV K) (capMiddleBV L)
  -- ### The right end: both endpoints move by fixed vectors
  · have hcos : 0 < Real.cos paperGerverConstants.2.1 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hr.1], hr.2⟩
    simp only [distinguishedCapSides_fst_fanPoint, distinguishedCapSides_fst_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1, 1])
      (v := normalVector (paperGerverConstants.2.1 : Real.Angle) +
        tangentVector (paperGerverConstants.2.1 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_fst K.val hcos.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.1)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.1).1 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.1
  -- ### The left end: the same, with the complementary trigonometric normalisation
  · have hsin : 0 < Real.sin paperGerverConstants.2.2 :=
      Real.sin_pos_of_pos_of_lt_pi hl.1 (by linarith [Real.pi_pos, hl.2])
    simp only [distinguishedCapSides_snd_fanPoint, distinguishedCapSides_snd_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(Real.cos paperGerverConstants.2.2 - 1) / Real.sin paperGerverConstants.2.2, 1])
      (v := normalVector (paperGerverConstants.2.2 : Real.Angle) +
        tangentVector (paperGerverConstants.2.2 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_snd K.val hsin.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.2)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.2).2 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.2

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
# Cap / Tail / Area Bounds
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A point of a special cap above both the right inner wall at `φᴿ` and the bottom axis that
misses the right canonical tail lies in the niche, on the right side. -/
private theorem mem_capNiche_inter_right_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.1).1)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).1) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane := by
  obtain ⟨hrIoo, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨hmonR, -, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqR : (innerWallUpperHalfPlanes K.val (Real.pi / 2)).1 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    show normalHalfPlane _ (supportValue (K.1.1 : Set Point) _ - 1) true false = _
    rw [K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      q ∉ (innerWallUpperHalfPlanes K.val t).1 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : paperGerverConstants.2.1 < t :=
    ht.1.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hthigh : t < Real.pi / 2 :=
    ht.2.lt_of_ne fun h ↦ hqt (by rw [h, hUpEqR]; exact hup)
  have hmem : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonR t ⟨htlow, ht.2⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨hrIoo.1.trans htlow, hthigh⟩, hmem.2⟩⟩, hwall⟩

/-- A point of a special cap above both the left inner wall at `φᴸ` and the bottom axis that
misses the left canonical tail lies in the niche, on the left side. -/
private theorem mem_capNiche_inter_left_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.2).2)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).2) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane := by
  obtain ⟨-, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨-, hmonL, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqL : (innerWallUpperHalfPlanes K.val 0).2 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    have hzero : ((((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)) =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by rw [zero_add]
    show normalHalfPlane (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (K.1.1 : Set Point) (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle) - 1)
        true false = _
    rw [hzero, K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      q ∉ (innerWallUpperHalfPlanes K.val t).2 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : 0 < t := ht.1.lt_of_ne fun h ↦ hqt (by rw [← h, hUpEqL]; exact hup)
  have hthigh : t < paperGerverConstants.2.2 := ht.2.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hmem : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonL t ⟨ht.1, hthigh⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨htlow, hthigh.trans hlIoo.2⟩, hmem.2⟩⟩, hwall⟩

theorem canonicalTail_niche_area_lower_bounds (K : SpecialCapSpace)
    (B D : ConvexBody Point)
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    segmentArea (rightLeftTailArcs B D).1.startPoint
        (distinguishedCapSides K.val).1.fanPoint -
      convexArcArea B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∧
    segmentArea (distinguishedCapSides K.val).2.fanPoint
        (rightLeftTailArcs B D).2.endPoint -
      convexArcArea D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane) := by
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  obtain ⟨-, -, -, hBsub, -, -, -, hDsub, -, hBeq, -, -, -, hDeq, -, -⟩ :=
    canonicalTailSets_properties K
  -- endpoint support values of the two tails
  have hB1 : supportValue (B : Set Point)
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := hBeq paperGerverConstants.2.1 (by simp)
    rw [hB]
    linarith
  have hB2 : supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hBeq (Real.pi / 2) (by simp)
    rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
    rw [hB]
    linarith
  have hD1 : supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hDeq 0 (by simp)
    rw [hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring),
      hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring), htop] at h
    rw [hD]
    linarith
  have hD2 : supportValue (D : Set Point)
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    have h := hDeq paperGerverConstants.2.2 (by simp)
    rw [hD]
    linarith
  obtain ⟨hOB, hOD, hsegB, hsegD, -, -⟩ :=
    tailFanPoint_identities K.val B D hrIoo hlIoo hB1 hB2 hD1 hD2
  obtain ⟨hWmem, hZmem⟩ := specialCap_wedgeEndpoints_in_bottomEdge K
  have hnichefin : MeasureTheory.volume (capNiche K.val) ≠ ⊤ :=
    ne_of_lt (niche_uniform_bounds.1 _ K.val).2.2.1
  have hRfin : ∀ S : Set Point,
      MeasureTheory.volume (capNiche K.val ∩ S) ≠ ⊤ := fun S ↦
    ne_top_of_le_ne_top hnichefin (MeasureTheory.measure_mono Set.inter_subset_left)
  have hKconv : Convex ℝ (K.1.1 : Set Point) := K.1.1.convex
  have hKclosed : IsClosed (K.1.1 : Set Point) := K.1.1.isCompact.isClosed
  constructor
  · -- right tail
    have hHa : (supportingLineHalfPlane (B : Set Point)
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).1.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show Real.pi + paperGerverConstants.2.1 =
          paperGerverConstants.2.1 + Real.pi by ring), normalVector_add_pi]
      · rw [hB1]; ring
    have hHb : (supportingLineHalfPlane (B : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hB2]; ring
    have hmain := convexArc_tangentRegion_area_le B
      (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)
      (by linarith [hrIoo.2]) (by linarith [hrIoo.1])
      hKconv hKclosed (by rw [hB]; exact hBsub) (by rw [hOB]; exact hWmem.1.1)
      (hRfin _) (fun q hq hqK hqB ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_right_of_notMem_canonicalTail K hq'.1 hq'.2 hqK
          (by rwa [hB] at hqB))
    rw [hOB] at hmain
    rw [show (rightLeftTailArcs B D).1.startPoint =
        (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 from rfl,
      show (distinguishedCapSides K.val).1.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.1).1 from rfl]
    linarith [hmain, hsegB]
  · -- left tail
    have hHa : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hD1]; ring
    have hHb : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).2.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 + paperGerverConstants.2.2 =
          (paperGerverConstants.2.2 + Real.pi / 2) + Real.pi by ring), normalVector_add_pi]
      · rw [hD2, hcast _ _ (show Real.pi / 2 + paperGerverConstants.2.2 =
          paperGerverConstants.2.2 + Real.pi / 2 by ring)]
        ring
    have hmain := convexArc_tangentRegion_area_le D
      (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)
      (by linarith [hlIoo.1]) (by linarith [hlIoo.2])
      hKconv hKclosed (by rw [hD]; exact hDsub) (by rw [hOD]; exact hZmem.1.1)
      (hRfin _) (fun q hq hqK hqD ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_left_of_notMem_canonicalTail K hq'.2 hq'.1 hqK
          (by rwa [hD] at hqD))
    rw [hOD] at hmain
    rw [show (rightLeftTailArcs B D).2.endPoint =
        (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
        from rfl,
      show (distinguishedCapSides K.val).2.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.2).2 from rfl]
    linarith [hmain, hsegD]

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
# Tracing the area of a special cap along its upper boundary

The area of a convex body is half the integral of its support function against its surface area
measure.  For a special cap that measure is carried by the closed upper semicircle of normals,
because the two open quarter arcs of lower normals carry degenerate faces
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`) and the bottom normal carries
support value zero.  The injectivity condition provides angular densities on the two upper quarter
circles, so the four distinguished angles `0`, `φᴿ`, `φᴸ` and `π` are not atoms, and the semicircle
splits — up to a null set — into the four open arcs `(0, φᴿ)`, `(φᴿ, φᴸ)`, `(φᴸ, π / 2)`,
`(π / 2, π)` and the top normal `π / 2`.  Each open arc is shorter than `π`, so the convex arc area
formula applies to it, and the top normal contributes half the mass of a single atom
(`MovingSofa.HasCapDensities.area_eq_upper_arcs_add_top_atom`).  Evaluating the surface area
measure at that fixed angle is convex-linear on the convex domain of special caps, whence the cap
area agrees with the sum of the four arc areas modulo convex-linear functionals
(`MovingSofa.specialCapArea_equivalent_upper_arcs`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MovingSofa

/-- On an open arc shorter than `π` the support-area integral is twice the convex arc area. -/
private theorem setIntegral_image_Ioo_eq_two_mul_convexArcArea (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue (K : Set Point) t ∂surfaceAreaMeasure K =
      2 * convexArcArea K a b := by
  rw [(convexArc_area a b hab hba).2.1 K]
  ring

/-- Up to half the mass of the atom at its top normal, the area of a right-angle cap carrying
angular densities is the sum of the areas of the four upper boundary arcs cut out by the two
distinguished Gerver angles. -/
theorem HasCapDensities.area_eq_upper_arcs_add_top_atom {C : RightAngleCapSpace}
    {dr dl : ℝ → ℝ≥0} (hdens : HasCapDensities C dr dl) :
    ClassicalResults.area (C.val : Set Point) =
      (convexArcArea C.val 0 paperGerverConstants.2.1 +
          convexArcArea C.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea C.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea C.val (Real.pi / 2) Real.pi) +
        (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨⟨hrpos, -⟩, ⟨-, hlT⟩, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  set r := paperGerverConstants.2.1
  set l := paperGerverConstants.2.2
  -- ### The surface measure is finite, so the continuous support function is integrable
  have hfinite : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  have hint : Integrable (fun a : Real.Angle ↦ supportValue (C.val : Set Point) a)
      (surfaceAreaMeasure C.val) :=
    ((compactSet_support_continuity (C.val : Set Point) (C.val : Set Point) C.val.nonempty'
      C.val.isCompact' C.val.nonempty' C.val.isCompact').2.2.1).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  -- ### The five pieces of the closed upper semicircle that carry the surface measure
  set U : Set ℝ := Set.Ioo 0 r ∪ Set.Ioo r l ∪ Set.Ioo l (Real.pi / 2) ∪
    Set.Ioo (Real.pi / 2) Real.pi ∪ {Real.pi / 2} with hUdef
  have hs1 : Set.Ioo (0 : ℝ) r ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨hx.1, by linarith [hx.2]⟩
  have hs2 : Set.Ioo r l ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs3 : Set.Ioo l (Real.pi / 2) ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs4 : Set.Ioo (Real.pi / 2) Real.pi ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs5 : ({Real.pi / 2} : Set ℝ) ⊆ Set.Ioc 0 (2 * Real.pi) := by
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUsub : U ⊆ Set.Ioc 0 (2 * Real.pi) :=
    Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
  have hUIcc : U ⊆ Set.Icc 0 Real.pi := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (fun x hx ↦ ⟨hx.1.le, by linarith [hx.2]⟩)
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩)) ?_
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUmeas : MeasurableSet U :=
    (((measurableSet_Ioo.union measurableSet_Ioo).union measurableSet_Ioo).union
      measurableSet_Ioo).union (measurableSet_singleton _)
  -- ### Angular images of disjoint pieces of one turn are disjoint, and Borel pieces stay Borel
  have hdisj : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y →
      Disjoint ((fun t : ℝ ↦ (t : Real.Angle)) '' X)
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := by
    intro X Y hX hY hXY
    rw [Set.disjoint_left]
    rintro a ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' : y = x :=
      Real.Angle.injOn_coe_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) (hY hy) (hX hx) hyx
    exact Set.disjoint_left.mp hXY hx (hyx' ▸ hy)
  have hmimg : ∀ {Y : Set ℝ}, MeasurableSet Y → Y ⊆ Set.Ioc 0 (2 * Real.pi) →
      MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := fun hY hYs ↦
    Real.Angle.measurableSet_image_of_subset_Ioc (by linarith) hY hYs
  -- ### Splitting the last piece off an angular union
  have hstep : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y → MeasurableSet Y →
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' (X ∪ Y),
          supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
        (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' X,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val) +
          ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Y,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val := by
    intro X Y hX hY hXY hmY
    rw [Set.image_union, setIntegral_union (hdisj hX hY hXY) (hmimg hmY hY)
      hint.integrableOn hint.integrableOn]
  -- ### The four distinguished angles of the upper semicircle are not atoms
  have hatom0 : surfaceAreaMeasure C.val {((0 : ℝ) : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨le_rfl, by positivity⟩
  have hatomr : surfaceAreaMeasure C.val {(r : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨hrpos.le, by linarith⟩
  have hatoml : surfaceAreaMeasure C.val {(l : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨by linarith, hlT⟩
  have hatompi : surfaceAreaMeasure C.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    have h := hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
      (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
    rwa [show (Real.pi / 2 + Real.pi / 2 : ℝ) = Real.pi by ring] at h
  -- ### The five pieces cover the upper semicircle up to those four angles
  have hcover : Set.Icc (0 : ℝ) Real.pi ⊆ U ∪ {0, r, l, Real.pi} := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · exact Or.inr (by simp [← h0])
    rcases lt_trichotomy x r with h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h0, h⟩))))
    · exact Or.inr (by simp [h])
    rcases lt_trichotomy x l with h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, h'⟩))))
    · exact Or.inr (by simp [h'])
    rcases lt_trichotomy x (Real.pi / 2) with h'' | h'' | h''
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h', h''⟩)))
    · exact Or.inl (Or.inr h'')
    rcases eq_or_lt_of_le hx.2 with h₃ | h₃
    · exact Or.inr (by simp [h₃])
    · exact Or.inl (Or.inl (Or.inr ⟨h'', h₃⟩))
  have hnull : surfaceAreaMeasure C.val
      ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi \
        (fun t : ℝ ↦ (t : Real.Angle)) '' U) = 0 := by
    refine measure_mono_null (t := {((0 : ℝ) : Real.Angle), (r : Real.Angle), (l : Real.Angle),
      ((Real.pi : ℝ) : Real.Angle)}) ?_ ?_
    · rw [Set.sdiff_subset_iff]
      refine (Set.image_mono hcover).trans ?_
      rw [Set.image_union]
      exact Set.union_subset_union_right _ (by simp [Set.image_insert_eq])
    · simp only [Set.insert_eq]
      exact measure_union_null hatom0
        (measure_union_null hatomr (measure_union_null hatoml hatompi))
  -- ### The support-area integral is carried by the angular image of the five pieces
  have hSmeas : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have htotal : ∫ a, supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val =
      ∫ a in (fun t : ℝ ↦ (t : Real.Angle)) '' U,
        supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val := by
    rw [← integral_add_compl hSmeas hint,
      C.setIntegral_compl_image_Icc_zero_pi_eq_zero _ C.property.2.2.2.2.2.1, add_zero,
      ← Set.union_sdiff_cancel (Set.image_mono hUIcc),
      setIntegral_union Set.disjoint_sdiff_right (hSmeas.diff (hmimg hUmeas hUsub))
        hint.integrableOn hint.integrableOn,
      setIntegral_measure_zero _ hnull, add_zero]
  -- ### The four short arcs contribute their arc areas and the top normal its atom
  have hI1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (0 : ℝ) r,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val 0 r :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrpos (by linarith)
  have hI2 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo r l,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val r l :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrl (by linarith)
  have hI3 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo l (Real.pi / 2),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val l (Real.pi / 2) :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hlT (by linarith)
  have hI4 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (Real.pi / 2) Real.pi,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val (Real.pi / 2) Real.pi :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val (by linarith) (by linarith)
  have hIT : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' ({Real.pi / 2} : Set ℝ),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    rw [Set.image_singleton, integral_singleton, C.property.2.2.2.1, smul_eq_mul, mul_one,
      measureReal_def]
  -- ### Assembling the support-area identity
  rw [convexBody_area_support_integral.1 C.val, htotal, hUdef,
    hstep (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
      (by rw [Set.disjoint_singleton_right]
          rintro (((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) | ⟨h, -⟩) <;> linarith)
      (measurableSet_singleton _),
    hstep (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4
      (by rw [Set.disjoint_left]
          rintro x ((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep (Set.union_subset hs1 hs2) hs3
      (by rw [Set.disjoint_left]
          rintro x (⟨-, h⟩ | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep hs1 hs2
      (by rw [Set.disjoint_left]
          rintro x ⟨-, h⟩ ⟨h', -⟩
          linarith)
      measurableSet_Ioo,
    hI1, hI2, hI3, hI4, hIT]
  ring

theorem specialCapArea_equivalent_upper_arcs :
    EquivalentModuloConvexLinear specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point))
      (fun K ↦ convexArcArea K.val.val 0 paperGerverConstants.2.1 +
        convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
        convexArcArea K.val.val paperGerverConstants.2.2 (Real.pi / 2) +
        convexArcArea K.val.val (Real.pi / 2) Real.pi) := by
  -- ### The discrepancy is half the mass of the surface measure at the fixed top normal
  have key : ∀ M : SpecialCapSpace,
      ClassicalResults.area (M.val.val : Set Point) -
        (convexArcArea M.val.val 0 paperGerverConstants.2.1 +
          convexArcArea M.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea M.val.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea M.val.val (Real.pi / 2) Real.pi) =
        (surfaceAreaMeasure M.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 :=
    fun M ↦ by
      obtain ⟨dr, dl, hdens, -⟩ := M.property.1.1
      rw [hdens.area_eq_upper_arcs_add_top_atom]
      ring
  intro t K L
  have hKfin : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hLfin : IsFiniteMeasure (surfaceAreaMeasure L.val.val) :=
    (surfaceAreaMeasure_face_union L.val.val).1
  simp only [realCombination, key]
  rw [specialCap_isConvexDomain.1 t K L, surfaceAreaMeasure_convexBodyCombination,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ)),
    ENNReal.toReal_ofReal t.2.1]
  ring

end MovingSofa

end

end

end
