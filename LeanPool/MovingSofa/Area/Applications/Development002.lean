/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Area.Foundations.Development004

/-!
# Moving sofa: related mathematical developments

* `Area.Mamikon.Properties`.
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
# Area / Mamikon / Properties
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The tangential displacement from an exposed-edge endpoint to the path, extended by zero. -/
def mamikonOffset (K : ConvexBody Point) {a b : ℝ} (z : ContinuousBVPaths a b)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc a b then
    inner ℝ (z.val ⟨t, ht⟩ - (edgeVertices K (t : Real.Angle)).1)
      (tangentVector (t : Real.Angle))
  else 0

/-- Half the square integral of a bounded measurable family of integrands that is pointwise
convex-linear in its parameter is a quadratic and convex functional of that parameter. -/
theorem sqIntegral_quadratic_convex {α : Type*} {Ω : Type*} [MeasurableSpace Ω]
    (c : unitInterval → α → α → α) (μ : Measure Ω) [IsFiniteMeasure μ] (g : α → Ω → ℝ)
    (hmeas : ∀ x, Measurable (g x)) (hbdd : ∀ x, ∃ C, ∀ ω, |g x ω| ≤ C)
    (hlin : ∀ (s : unitInterval) (x y : α) (ω : Ω),
      g (c s x y) ω = (1 - (s : ℝ)) * g x ω + (s : ℝ) * g y ω)
    (f : α → ℝ) (hf : ∀ x, f x = (∫ ω, g x ω ^ 2 ∂μ) / 2) :
    IsQuadraticFunctional c f ∧ IsConvexFunctional c f false := by
  have hint : ∀ x y, Integrable (fun ω ↦ g x ω * g y ω) μ := by
    intro x y
    obtain ⟨Cx, hCx⟩ := hbdd x
    obtain ⟨Cy, hCy⟩ := hbdd y
    refine Integrable.mono' (integrable_const (|Cx| * |Cy|))
      ((hmeas x).mul (hmeas y)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hCx ω).trans (le_abs_self _)) ((hCy ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  set B : α → α → ℝ := fun x y ↦ (∫ ω, g x ω * g y ω ∂μ) / 2
  have hBval : ∀ x y, B x y = (∫ ω, g x ω * g y ω ∂μ) / 2 := fun _ _ ↦ rfl
  have hBsymm : ∀ x y, B x y = B y x := fun x y ↦ by
    rw [hBval, hBval, integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)]
  have hBleft : ∀ (s : unitInterval) (x y z : α),
      B (c s x y) z = realCombination s (B x z) (B y z) := by
    intro s x y z
    rw [hBval, hBval, hBval, realCombination,
      integral_congr_ae (Filter.Eventually.of_forall fun ω ↦
        show g (c s x y) ω * g z ω =
            (1 - (s : ℝ)) * (g x ω * g z ω) + (s : ℝ) * (g y ω * g z ω) by
          rw [hlin]; ring),
      integral_add ((hint x z).const_mul _) ((hint y z).const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  have hB : IsConvexBilinear c c realCombination B := by
    refine ⟨fun x s y z ↦ ?_, fun z s x y ↦ hBleft s x y z⟩
    rw [hBsymm x (c s y z), hBleft s y z x, hBsymm y x, hBsymm z x]
  have hfB : ∀ x, f x = B x x := fun x ↦ by
    rw [hf x, hBval, integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ pow_two (g x ω))]
  refine ⟨⟨B, hB, hfB⟩, fun s x y ↦ ?_⟩
  show f (c s x y) ≤ realCombination s (f x) (f y)
  have hnn : 0 ≤ B x x - B x y - B y x + B y y := by
    have i1 : Integrable (fun ω ↦ g x ω * g x ω - g x ω * g y ω) μ := (hint x x).sub (hint x y)
    have i2 : Integrable (fun ω ↦ g x ω * g x ω - g x ω * g y ω - g y ω * g x ω) μ :=
      i1.sub (hint y x)
    have hsplit : (∫ ω, (g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω) ∂μ) =
        (∫ ω, g x ω * g x ω ∂μ) - (∫ ω, g x ω * g y ω ∂μ) - (∫ ω, g y ω * g x ω ∂μ) +
          ∫ ω, g y ω * g y ω ∂μ := by
      rw [integral_add i2 (hint y y), integral_sub i1 (hint y x),
        integral_sub (hint x x) (hint x y)]
    have hpos : 0 ≤ ∫ ω, (g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω) ∂μ :=
      integral_nonneg fun ω ↦ by
        show (0 : ℝ) ≤ g x ω * g x ω - g x ω * g y ω - g y ω * g x ω + g y ω * g y ω
        nlinarith [sq_nonneg (g x ω - g y ω)]
    rw [hsplit] at hpos
    rw [hBval, hBval, hBval, hBval]
    linarith
  have hexp : B (c s x y) (c s x y) = (1 - (s : ℝ)) ^ 2 * B x x +
      (s : ℝ) * (1 - (s : ℝ)) * (B x y + B y x) + (s : ℝ) ^ 2 * B y y := by
    rw [hBleft s x y (c s x y), realCombination, hB.1 x s x y, hB.1 y s x y, realCombination,
      realCombination]
    ring
  rw [hfB, hfB, hfB, realCombination, hexp]
  nlinarith [mul_nonneg (mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2)) hnn]

/-- The Mamikon offset is convex-linear in the body along a convex-linear family of paths. -/
theorem mamikonOffset_convexBodyCombination (s : unitInterval) (K L : ConvexBody Point)
    {a b : ℝ} (zK zL : ContinuousBVPaths a b) (t : ℝ) :
    mamikonOffset (convexBodyCombination s K L) (bvPathCombination s zK zL) t =
      (1 - (s : ℝ)) * mamikonOffset K zK t + (s : ℝ) * mamikonOffset L zL t := by
  by_cases ht : t ∈ Set.Icc a b
  · have hz : (bvPathCombination s zK zL).val ⟨t, ht⟩ =
        (1 - (s : ℝ)) • zK.val ⟨t, ht⟩ + (s : ℝ) • zL.val ⟨t, ht⟩ := rfl
    have hv := ((convexBody_maps_linear s K L).2.1 (t : Real.Angle)).1
    simp only [mamikonOffset, dite_eq_left ht, hz, hv, inner_sub_left, inner_add_left,
      real_inner_smul_left]
    ring
  · simp only [mamikonOffset, dite_eq_right ht]
    ring

private theorem mamikon_frame_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (z : ContinuousBVPaths a b)
    (S : Set (Set.Icc a b)) (hSmeas : MeasurableSet S)
    (hSa : ∀ t ∈ S, a < (t : ℝ))
    (W Z U T D : Fin 2 → RightContinuousIntervalBV a b)
    (hW : ∀ i t, (W i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (hWm : ∀ i (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (W i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hU : ∀ i t, (U i).toFun t = normalVector ((t : ℝ) : Real.Angle) i)
    (hUd : ∀ i, HasIntervalStieltjesDensity (U i)
      (fun t ↦ tangentVector (t : Real.Angle) i))
    (hT : ∀ i t, (T i).toFun t = tangentVector ((t : ℝ) : Real.Angle) i)
    (hUc : ∀ i, Continuous (U i).toFun)
    (hDval : ∀ i t, (D i).toFun t =
      z.val t i - (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (A : RightContinuousIntervalBV a b)
    (hA : ∀ t, A.toFun t = ∑ i, (D i).toFun t * (T i).toFun t)
    (hAmeas : Measurable A.toFun)
    (hzt : ∀ t : Set.Icc a b, inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
      supportValue K ((t : ℝ) : Real.Angle))
    (CA : ℝ) (hCA : ∀ t, ‖A.toFun t‖ ≤ CA) (hCA0 : 0 ≤ CA)
    (hAUb : ∀ i t, ‖A.toFun t * (U i).toFun t‖ ≤ CA)
    (hperpframe : ∀ u : Real.Angle,
      normalVector u 0 * tangentVector u 0 + normalVector u 1 * tangentVector u 1 = 0) :
    intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
      intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S =
    -(∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ)) := by
  -- the integrated product rule against the rotating normal frame
  choose zu hzu hzum using fun i : Fin 2 ↦
    intervalStieltjes_product a b (Z i) (U i) (Or.inr (hUc i))
  choose wu hwu hwum using fun i : Fin 2 ↦
    intervalStieltjes_product a b (W i) (U i) (Or.inr (hUc i))
  obtain ⟨ZU, hZU, hZUm⟩ := intervalStieltjes_linear_combination a b (zu 0) (zu 1) 1 1
  obtain ⟨WU, hWU, hWUm⟩ := intervalStieltjes_linear_combination a b (wu 0) (wu 1) 1 1
  have hZUWU : ZU = WU := by
    refine RightContinuousIntervalBV.toFun_injective (funext fun t ↦ ?_)
    rw [hZU t, hWU t, hzu 0 t, hzu 1 t, hwu 0 t, hwu 1 t, hZ, hZ, hW, hW, hU, hU]
    have h1 := hzt t
    have h2 : inner ℝ (edgeVertices K ((t : ℝ) : Real.Angle)).1
        (normalVector ((t : ℝ) : Real.Angle)) = supportValue K ((t : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem K ((t : ℝ) : Real.Angle)).2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two] at h1 h2
    linear_combination h1 - h2
  have hAint : ∀ F : RightContinuousIntervalBV a b,
      (intervalStieltjesMeasure F).Integrable A.toFun := by
    intro F
    have _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
      BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
    exact A.boundedVariation.integrable
  have hsplitsum : ∀ F G H : RightContinuousIntervalBV a b,
      intervalStieltjesMeasure H =
          (1 : ℝ) • intervalStieltjesMeasure F + (1 : ℝ) • intervalStieltjesMeasure G →
      intervalStieltjesIntegral H A.toFun S =
        intervalStieltjesIntegral F A.toFun S + intervalStieltjesIntegral G A.toFun S := by
    intro F G H hH
    unfold intervalStieltjesIntegral
    rw [hH]
    simp only [one_smul]
    rw [VectorMeasure.restrict_add,
      VectorMeasure.integral_add_vectorMeasure (hAint F).integrableOn (hAint G).integrableOn]
  have hH2 : ∀ (i : Fin 2) (F P : RightContinuousIntervalBV a b),
      (∀ t, P.toFun t = F.toFun t * (U i).toFun t) →
      intervalStieltjesIntegral P A.toFun S =
        intervalStieltjesIntegral F (fun t ↦ A.toFun t * (U i).toFun t) S +
          intervalStieltjesIntegral (U i) (fun t ↦ A.toFun t * F.toFun t) S := fun i F P hP ↦
    intervalStieltjesIntegral_product_of_bounded hab.le F (U i) P (hUc i) hP A.toFun
      hAmeas CA hCA S hSmeas
  have hkey := hsplitsum (zu 0) (zu 1) ZU hZUm
  rw [hZUWU, hsplitsum (wu 0) (wu 1) WU hWUm, hH2 0 (Z 0) (zu 0) (hzu 0),
    hH2 1 (Z 1) (zu 1) (hzu 1), hH2 0 (W 0) (wu 0) (hwu 0), hH2 1 (W 1) (wu 1) (hwu 1)] at hkey
  -- the vertex measure pairs to zero against the rotating normal frame
  have hWzero : intervalStieltjesIntegral (W 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
      intervalStieltjesIntegral (W 1) (fun t ↦ A.toFun t * (U 1).toFun t) S = 0 := by
    have hdot := sum_intervalStieltjesIntegral_positiveVertex_dot K hab hturn W hWm
      (fun i t ↦ A.toFun t * (U i).toFun t) CA hCA0
      (fun i ↦ hAmeas.mul (U i).boundedVariation.measurable) hAUb (fun _ ↦ 0)
      (by
        intro t _
        rw [Fin.sum_univ_two]
        simp only [hU]
        linear_combination (A.toFun t) * hperpframe ((t : ℝ) : Real.Angle))
      S hSmeas hSa
    simpa [Fin.sum_univ_two] using hdot
  -- the Lebesgue density of the rotating frame
  have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := ⟨by
    rw [comap_subtype_coe_apply measurableSet_Icc]
    simp only [Set.image_univ, Subtype.range_val]
    exact measure_Icc_lt_top⟩
  let _ := hfinite
  have hdens : ∀ (i : Fin 2) (F : RightContinuousIntervalBV a b),
      intervalStieltjesIntegral (U i) (fun t ↦ A.toFun t * F.toFun t) S =
        ∫ t in S, A.toFun t * F.toFun t * tangentVector ((t : ℝ) : Real.Angle) i
          ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) := fun i F ↦
    intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (U i) (hUd i)
      (A.boundedVariation.bilinear_comp F.boundedVariation (ContinuousLinearMap.mul ℝ ℝ)) S hSmeas
  have hintd : ∀ (i : Fin 2) (F : RightContinuousIntervalBV a b),
      Integrable (fun t : Set.Icc a b ↦
        A.toFun t * F.toFun t * tangentVector ((t : ℝ) : Real.Angle) i)
        (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := by
    intro i F
    refine (A.boundedVariation.bilinear_comp F.boundedVariation
      (ContinuousLinearMap.mul ℝ ℝ)).integrable.mul_bdd (c := 1) ?_ ?_
    · have h : Continuous fun u : Real.Angle ↦ tangentVector u i := by
        fin_cases i
        · exact Real.Angle.continuous_sin.neg
        · exact Real.Angle.continuous_cos
      exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).aestronglyMeasurable
    · filter_upwards with t
      fin_cases i
      · simpa [tangentVector, frame] using Real.abs_sin_le_one (t : ℝ)
      · simpa [tangentVector, frame] using Real.abs_cos_le_one (t : ℝ)
  have haddZ : Integrable (fun t : Set.Icc a b ↦
      A.toFun t * (Z 0).toFun t * tangentVector ((t : ℝ) : Real.Angle) 0 +
        A.toFun t * (Z 1).toFun t * tangentVector ((t : ℝ) : Real.Angle) 1)
      (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := (hintd 0 (Z 0)).add (hintd 1 (Z 1))
  have haddW : Integrable (fun t : Set.Icc a b ↦
      A.toFun t * (W 0).toFun t * tangentVector ((t : ℝ) : Real.Angle) 0 +
        A.toFun t * (W 1).toFun t * tangentVector ((t : ℝ) : Real.Angle) 1)
      (volume.comap (Subtype.val : Set.Icc a b → ℝ)) := (hintd 0 (W 0)).add (hintd 1 (W 1))
  have hsquare : (intervalStieltjesIntegral (U 0) (fun t ↦ A.toFun t * (Z 0).toFun t) S +
        intervalStieltjesIntegral (U 1) (fun t ↦ A.toFun t * (Z 1).toFun t) S) -
      (intervalStieltjesIntegral (U 0) (fun t ↦ A.toFun t * (W 0).toFun t) S +
        intervalStieltjesIntegral (U 1) (fun t ↦ A.toFun t * (W 1).toFun t) S) =
      ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) := by
    rw [hdens 0 (Z 0), hdens 1 (Z 1), hdens 0 (W 0), hdens 1 (W 1),
      ← integral_add (hintd 0 (Z 0)).integrableOn (hintd 1 (Z 1)).integrableOn,
      ← integral_add (hintd 0 (W 0)).integrableOn (hintd 1 (W 1)).integrableOn,
      ← integral_sub haddZ.integrableOn haddW.integrableOn]
    refine setIntegral_congr_fun hSmeas fun t _ ↦ ?_
    have h := hA t
    rw [Fin.sum_univ_two, hDval, hDval, hT, hT] at h
    simp only [hZ, hW]
    linear_combination (-A.toFun t) * h
  linarith [hkey, hWzero, hsquare]

private theorem mamikon_arc_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hba : b < a + Real.pi) (hturn : b ≤ a + 2 * Real.pi)
    (z : ContinuousBVPaths a b) (S : Set (Set.Icc a b))
    (hSmeas : MeasurableSet S) (hSa : ∀ t ∈ S, a < (t : ℝ))
    (W Z : Fin 2 → RightContinuousIntervalBV a b)
    (hWm : ∀ i (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (W i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hzt : ∀ t : Set.Icc a b, inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
      supportValue K ((t : ℝ) : Real.Angle))
    (himg : (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' S =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioo a b) :
    intervalStieltjesIntegral (W 1) (Z 0).toFun S -
      intervalStieltjesIntegral (W 0) (Z 1).toFun S = 2 * convexArcArea K a b := by
  obtain ⟨C0, hC0⟩ := (Z 0).exists_norm_bound hab.le
  obtain ⟨C1, hC1⟩ := (Z 1).exists_norm_bound hab.le
  have hCz0 : 0 ≤ max C0 C1 := le_trans (norm_nonneg _) ((hC0 ⟨a, le_rfl, hab.le⟩).trans
    (le_max_left _ _))
  have hdot := sum_intervalStieltjesIntegral_positiveVertex_dot K hab hturn W hWm
    ![fun t ↦ -(Z 1).toFun t, (Z 0).toFun] (max C0 C1) hCz0
    (by
      intro i
      fin_cases i
      · exact ((Z 1).boundedVariation.measurable).neg
      · exact (Z 0).boundedVariation.measurable)
    (by
      intro i t
      fin_cases i
      · simpa using (hC1 t).trans (le_max_right _ _)
      · simpa using (hC0 t).trans (le_max_left _ _))
    (fun u ↦ supportValue K u)
    (by
      intro t _
      have h := planeCrossProduct_tangentVector (z.val t) ((t : ℝ) : Real.Angle)
      rw [hzt t] at h
      simp only [planeCrossProduct] at h
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hZ]
      linarith)
    S hSmeas hSa
  rw [Fin.sum_univ_two] at hdot
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hdot
  rw [show intervalStieltjesIntegral (W 0) (fun t ↦ -(Z 1).toFun t) S =
      -intervalStieltjesIntegral (W 0) (Z 1).toFun S from
    VectorMeasure.integral_fun_neg _ _ _] at hdot
  rw [himg] at hdot
  have harea := (convexArc_area a b hab hba).2.1 K
  rw [← hdot] at harea
  linarith

private theorem mamikon_endpoint_identity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (z : ContinuousBVPaths a b)
    (W Z : Fin 2 → RightContinuousIntervalBV a b)
    (hW : ∀ i t, (W i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i)
    (hZ : ∀ i t, (Z i).toFun t = z.val t i)
    (hZc : ∀ i, Continuous (Z i).toFun) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
    let b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
    let S : Set (Set.Icc a b) := Set.Ioo a' b'
    (intervalStieltjesIntegral (W 1) (Z 0).toFun S +
           intervalStieltjesIntegral (Z 0) (W 1).toFun S) -
         (intervalStieltjesIntegral (W 0) (Z 1).toFun S +
           intervalStieltjesIntegral (Z 1) (W 0).toFun S) =
         2 * segmentArea (edgeVertices K ((a : ℝ) : Real.Angle)).1 (z.val a') +
           2 * segmentArea (z.val b') (edgeVertices K ((b : ℝ) : Real.Angle)).2 := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let S : Set (Set.Icc a b) := Set.Ioo a' b'
  have hS : S = Set.Ioo a' b' := rfl
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  -- the product-rule endpoint identity
  obtain ⟨p1, hp1, hp1m⟩ := intervalStieltjes_product a b (W 1) (Z 0) (Or.inr (hZc 0))
  obtain ⟨p0, hp0, hp0m⟩ := intervalStieltjes_product a b (W 0) (Z 1) (Or.inr (hZc 1))
  have hab' : a' < b' := hab
  have hIoo : ∀ P : RightContinuousIntervalBV a b,
      intervalStieltjesMeasure P S = Function.leftLim P.toFun b' - P.toFun a' := by
    intro P
    rw [hS, intervalStieltjesMeasure, P.boundedVariation.vectorMeasure_Ioo hab',
      (P.right_continuous a').rightLim_eq]
  have hleftLimP : ∀ (i j : Fin 2) (P : RightContinuousIntervalBV a b),
      (∀ t, P.toFun t = (W i).toFun t * (Z j).toFun t) →
      Function.leftLim P.toFun b' =
        (edgeVertices K ((b : ℝ) : Real.Angle)).2 i * z.val b' j := by
    intro i j P hP
    have hne : (nhdsWithin b' (Set.Iio b')).NeBot := nhdsLT_neBot_of_exists_lt ⟨a', hab'⟩
    let _ := hne
    refine tendsto_nhds_unique (P.boundedVariation.tendsto_leftLim b') ?_
    have h1 := (W i).boundedVariation.tendsto_leftLim b'
    rw [leftLim_positiveVertex_coordinate K W hW i b' hab] at h1
    have h2 : Filter.Tendsto (Z j).toFun (nhdsWithin b' (Set.Iio b')) (nhds ((Z j).toFun b')) :=
      (hZc j).continuousAt.continuousWithinAt
    rw [hZ j b'] at h2
    exact (h1.mul h2).congr fun t ↦ (hP t).symm
  have hEndpoint : (intervalStieltjesIntegral (W 1) (Z 0).toFun S +
        intervalStieltjesIntegral (Z 0) (W 1).toFun S) -
      (intervalStieltjesIntegral (W 0) (Z 1).toFun S +
        intervalStieltjesIntegral (Z 1) (W 0).toFun S) =
      2 * segmentArea (edgeVertices K ((a : ℝ) : Real.Angle)).1 (z.val a') +
        2 * segmentArea (z.val b') (edgeVertices K ((b : ℝ) : Real.Angle)).2 := by
    rw [← hp1m S hSmeas, ← hp0m S hSmeas, hIoo p1, hIoo p0,
      hleftLimP 1 0 p1 hp1, hleftLimP 0 1 p0 hp0, hp1 a', hp0 a', hW, hW, hZ, hZ]
    simp only [segmentArea, planeCrossProduct]
    ring
  exact hEndpoint

theorem mamikon_integral (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi) (z : ContinuousBVPaths a b)
    (hz : ∀ t : Set.Icc a b,
      z.val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1) :
    Measurable (mamikonOffset K z) ∧
    (∃ C : ℝ, ∀ t, |mamikonOffset K z t| ≤ C) ∧
    (∀ t : Set.Icc a b, z.val t = (edgeVertices K (t.val : Real.Angle)).1 +
      mamikonOffset K z t.val • tangentVector (t.val : Real.Angle)) ∧
    mamikonFunctional K a b hab hba z hz =
      (∫ t in Set.Icc a b, (mamikonOffset K z t) ^ 2) / 2 := by
  have hturn : b ≤ a + 2 * Real.pi := by linarith [Real.pi_pos]
  set a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩ with ha'
  set b' : Set.Icc a b := ⟨b, hab.le, le_rfl⟩ with hb'
  set S : Set (Set.Icc a b) := Set.Ioo a' b' with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  have hSa : ∀ t ∈ S, a < (t : ℝ) := fun t ht ↦ ht.1
  -- the frame data
  obtain ⟨W, hW, hWm⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  set Z : Fin 2 → RightContinuousIntervalBV a b := fun i ↦ continuousBVCoordinate z i with hZdef
  have hZ : ∀ i (t : Set.Icc a b), (Z i).toFun t = z.val t i := fun _ _ ↦ rfl
  have hZc : ∀ i, Continuous (Z i).toFun := fun i ↦
    (PiLp.continuous_apply 2 _ i).comp z.property.1
  choose U hU hUd using fun i : Fin 2 ↦ exists_normalVector_coordinate_intervalBV hab.le i
  choose T hT hTd using fun i : Fin 2 ↦ exists_tangentVector_coordinate_intervalBV hab.le i
  have hUc : ∀ i, Continuous (U i).toFun := by
    intro i
    have h : Continuous fun u : Real.Angle ↦ normalVector u i := by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin
    exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).congr
      fun t ↦ (hU i t).symm
  have hTc : ∀ i, Continuous (T i).toFun := by
    intro i
    have h : Continuous fun u : Real.Angle ↦ tangentVector u i := by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos
    exact (h.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).congr
      fun t ↦ (hT i t).symm
  choose D hD hDm using fun i : Fin 2 ↦
    intervalStieltjes_linear_combination a b (Z i) (W i) 1 (-1)
  have hDval : ∀ i (t : Set.Icc a b),
      (D i).toFun t = z.val t i - (edgeVertices K ((t : ℝ) : Real.Angle)).1 i := by
    intro i t
    rw [hD i t, hZ i t, hW i t]
    ring
  obtain ⟨A, hA, hAm⟩ := intervalStieltjes_inner_fin_two D T hTc
  have hAmeas : Measurable A.toFun := A.boundedVariation.measurable
  -- the offset is the tangent projection of the difference
  have hoffset : ∀ t : Set.Icc a b, mamikonOffset K z (t : ℝ) = A.toFun t := by
    intro t
    rw [hA t]
    simp only [mamikonOffset, dite_eq_left t.property, Subtype.coe_eta, hDval, hT,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, PiLp.sub_apply]
    ring
  have hoffsetval : ∀ t : Set.Icc a b, mamikonOffset K z (t : ℝ) =
      inner ℝ (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1)
        (tangentVector ((t : ℝ) : Real.Angle)) := fun t ↦ by
    simp only [mamikonOffset, dite_eq_left t.property, Subtype.coe_eta]
  have hzt : ∀ t : Set.Icc a b,
      inner ℝ (z.val t) (normalVector ((t : ℝ) : Real.Angle)) =
        supportValue K ((t : ℝ) : Real.Angle) := fun t ↦ hz t
  -- measurability and boundedness of the offset
  have hmeas : Measurable (mamikonOffset K z) := by
    refine measurable_of_restrict_of_restrict_compl (s := Set.Icc a b) measurableSet_Icc ?_ ?_
    · show Measurable fun t : Set.Icc a b ↦ mamikonOffset K z (t : ℝ)
      rw [funext hoffset]
      exact hAmeas
    · show Measurable fun t : ((Set.Icc a b)ᶜ : Set ℝ) ↦ mamikonOffset K z (t : ℝ)
      rw [show (fun t : ((Set.Icc a b)ᶜ : Set ℝ) ↦ mamikonOffset K z (t : ℝ)) = fun _ ↦ 0 from
        funext fun t ↦ dite_eq_right t.property]
      exact measurable_const
  obtain ⟨CA, hCA⟩ := A.exists_norm_bound hab.le
  have hbound : ∀ t : ℝ, |mamikonOffset K z t| ≤ max CA 0 := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · have h := hCA ⟨t, ht⟩
      rw [Real.norm_eq_abs] at h
      rw [hoffset ⟨t, ht⟩]
      exact h.trans (le_max_left _ _)
    · simp only [mamikonOffset, dite_eq_right ht, abs_zero]
      exact le_max_right _ _
  have hrecon : ∀ t : Set.Icc a b, z.val t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 +
      mamikonOffset K z (t : ℝ) • tangentVector ((t : ℝ) : Real.Angle) := by
    intro t
    have hperp : inner ℝ (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1)
        (normalVector ((t : ℝ) : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzt t, (edgeVertices_fst_mem K ((t : ℝ) : Real.Angle)).2, sub_self]
    have hdec := inner_normalVector_smul_add_inner_tangentVector_smul
      (z.val t - (edgeVertices K ((t : ℝ) : Real.Angle)).1) ((t : ℝ) : Real.Angle)
    rw [hperp, zero_smul, zero_add] at hdec
    rw [hoffsetval t, hdec, add_sub_cancel]
  refine ⟨hmeas, ⟨max CA 0, hbound⟩, hrecon, ?_⟩
  have hCA0 : 0 ≤ CA := le_trans (norm_nonneg _) (hCA a')
  have himg : (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' S =
      (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ⟨ht.1, ht.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.le⟩, ⟨hs.1, hs.2⟩, rfl⟩
  have hUb : ∀ (i : Fin 2) (t : Set.Icc a b), ‖(U i).toFun t‖ ≤ 1 := by
    intro i t
    simp only [hU]
    fin_cases i
    · simpa [normalVector, frame] using Real.abs_cos_le_one (t : ℝ)
    · simpa [normalVector, frame] using Real.abs_sin_le_one (t : ℝ)
  have hAUb : ∀ (i : Fin 2) (t : Set.Icc a b), ‖A.toFun t * (U i).toFun t‖ ≤ CA := by
    intro i t
    rw [norm_mul]
    calc ‖A.toFun t‖ * ‖(U i).toFun t‖ ≤ CA * 1 :=
          mul_le_mul (hCA t) (hUb i t) (norm_nonneg _) hCA0
      _ = CA := mul_one CA
  have hperpframe : ∀ u : Real.Angle,
      normalVector u 0 * tangentVector u 0 + normalVector u 1 * tangentVector u 1 = 0 := by
    intro u
    simp only [normalVector, tangentVector, frame, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hTU0 : ∀ t : Set.Icc a b, (T 0).toFun t = -(U 1).toFun t := by
    intro t
    rw [hT, hU]
    simp [normalVector, tangentVector, frame]
  have hTU1 : ∀ t : Set.Icc a b, (T 1).toFun t = (U 0).toFun t := by
    intro t
    rw [hT, hU]
    simp [normalVector, tangentVector, frame]
  have hDA : ∀ (i : Fin 2) (t : Set.Icc a b), (D i).toFun t = A.toFun t * (T i).toFun t := by
    intro i t
    have h := congrArg (fun p : Point ↦ p i) (hrecon t)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h
    rw [hDval i t, hT i t, ← hoffset t]
    linarith [h]
  have hDU0 : ∀ t : Set.Icc a b,
      (Z 0).toFun t - (W 0).toFun t = -(A.toFun t * (U 1).toFun t) := by
    intro t
    have h := hDA 0 t
    rw [hD 0 t, hTU0 t] at h
    rw [show (Z 0).toFun t - (W 0).toFun t = 1 * (Z 0).toFun t + -1 * (W 0).toFun t by ring, h]
    ring
  have hDU1 : ∀ t : Set.Icc a b,
      (Z 1).toFun t - (W 1).toFun t = A.toFun t * (U 0).toFun t := by
    intro t
    have h := hDA 1 t
    rw [hD 1 t, hTU1 t] at h
    rw [show (Z 1).toFun t - (W 1).toFun t = 1 * (Z 1).toFun t + -1 * (W 1).toFun t by ring, h]
  -- integrability of interval-BV integrands
  have hFint : ∀ F G : RightContinuousIntervalBV a b,
      ((intervalStieltjesMeasure G).restrict S).Integrable F.toFun := by
    intro F G
    have _ : IsFiniteMeasure (intervalStieltjesMeasure G).variation :=
      BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure G.boundedVariation
    exact (show (intervalStieltjesMeasure G).Integrable F.toFun from
      F.boundedVariation.integrable).integrableOn
  have hsubint : ∀ F G H : RightContinuousIntervalBV a b,
      intervalStieltjesIntegral H (fun t ↦ F.toFun t - G.toFun t) S =
        intervalStieltjesIntegral H F.toFun S - intervalStieltjesIntegral H G.toFun S :=
    fun F G H ↦ VectorMeasure.integral_fun_sub (hFint F H) (hFint G H)
  -- the curve area functional over the open interval
  have hJ : 2 * curveAreaFunctional z =
      intervalStieltjesIntegral (Z 1) (Z 0).toFun S -
        intervalStieltjesIntegral (Z 0) (Z 1).toFun S := by
    rw [curveAreaFunctional,
      show (fun t : Set.Icc a b ↦ z.val t 0) = (Z 0).toFun from rfl,
      show (fun t : Set.Icc a b ↦ z.val t 1) = (Z 1).toFun from rfl,
      show continuousBVCoordinate z 1 = Z 1 from rfl,
      show continuousBVCoordinate z 0 = Z 0 from rfl,
      intervalStieltjesIntegral_univ_eq_Ioo_of_continuous hab.le (Z 1) (hZc 1) _ (hZc 0),
      intervalStieltjesIntegral_univ_eq_Ioo_of_continuous hab.le (Z 0) (hZc 0) _ (hZc 1)]
    rw [← hS]
    ring
  have hArc := mamikon_arc_identity K hab hba hturn z S hSmeas hSa W Z hWm hZ hzt himg
  have hEndpoint := mamikon_endpoint_identity K hab z W Z hW hZ hZc
  have hframe := mamikon_frame_identity K hab hturn z S hSmeas hSa W Z U T D
    hW hWm hZ hU hUd hT hUc hDval A hA hAmeas hzt CA hCA hCA0 hAUb hperpframe
  -- the offset difference of the two coordinate integrals
  have hGval : (intervalStieltjesIntegral (Z 1) (Z 0).toFun S -
        intervalStieltjesIntegral (Z 1) (W 0).toFun S) -
      (intervalStieltjesIntegral (Z 0) (Z 1).toFun S -
        intervalStieltjesIntegral (Z 0) (W 1).toFun S) =
      -(intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S +
        intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S) := by
    rw [← hsubint (Z 0) (W 0) (Z 1), ← hsubint (Z 1) (W 1) (Z 0),
      show intervalStieltjesIntegral (Z 1) (fun t ↦ (Z 0).toFun t - (W 0).toFun t) S =
        intervalStieltjesIntegral (Z 1) (fun t ↦ -(A.toFun t * (U 1).toFun t)) S from
      VectorMeasure.setIntegral_congr_fun fun t _ ↦ hDU0 t,
      show intervalStieltjesIntegral (Z 0) (fun t ↦ (Z 1).toFun t - (W 1).toFun t) S =
        intervalStieltjesIntegral (Z 0) (fun t ↦ A.toFun t * (U 0).toFun t) S from
      VectorMeasure.setIntegral_congr_fun fun t _ ↦ hDU1 t,
      show intervalStieltjesIntegral (Z 1) (fun t ↦ -(A.toFun t * (U 1).toFun t)) S =
        -intervalStieltjesIntegral (Z 1) (fun t ↦ A.toFun t * (U 1).toFun t) S from
      VectorMeasure.integral_fun_neg _ _ _]
    ring
  -- the open-interval subtype integral is the closed-interval Lebesgue integral
  have hLeb : ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) =
      ∫ t in Set.Icc a b, (mamikonOffset K z t) ^ 2 := by
    have hpre : {x : Set.Icc a b | (x : ℝ) ∈ Set.Ioo a b} = S := by
      ext t
      exact ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
    have hsubtype := integral_subtype_preimage (μ := volume) (s := Set.Icc a b)
      (t := Set.Ioo a b) measurableSet_Icc measurableSet_Ioo
      (fun s : ℝ ↦ (mamikonOffset K z s) ^ 2)
    rw [hpre, Measure.restrict_restrict_of_subset Set.Ioo_subset_Icc_self] at hsubtype
    rw [show ∫ t in S, (A.toFun t) ^ 2 ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) =
        ∫ t in S, (mamikonOffset K z (t : ℝ)) ^ 2
          ∂volume.comap (Subtype.val : Set.Icc a b → ℝ) from
      setIntegral_congr_fun hSmeas fun t _ ↦ by rw [hoffset t], hsubtype]
    exact setIntegral_congr_set Ioo_ae_eq_Icc
  -- assemble
  unfold mamikonFunctional
  rw [← ha', ← hb']
  linarith [hJ, hArc, hEndpoint, hframe, hGval, hLeb]

theorem mamikon_quadratic_convex (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi)
    (F : ConvexBody Point → ContinuousBVPaths a b)
    (hF : ∀ K : ConvexBody Point, ∀ t : Set.Icc a b,
      (F K).val t ∈ (supportingLineHalfPlane K (t.val : Real.Angle)).1)
    (hlinear : IsConvexLinear convexBodyCombination bvPathCombination F) :
    IsQuadraticFunctional convexBodyCombination
        (fun K ↦ mamikonFunctional K a b hab hba (F K) (hF K)) ∧
      IsConvexFunctional convexBodyCombination
        (fun K ↦ mamikonFunctional K a b hab hba (F K) (hF K)) false := by
  have hdata := fun K : ConvexBody Point ↦ mamikon_integral K a b hab hba (F K) (hF K)
  refine sqIntegral_quadratic_convex convexBodyCombination (volume.restrict (Set.Icc a b))
    (fun K ↦ mamikonOffset K (F K)) (fun K ↦ (hdata K).1) (fun K ↦ (hdata K).2.1) ?_ _
    (fun K ↦ (hdata K).2.2.2)
  intro s K L t
  rw [show F (convexBodyCombination s K L) = bvPathCombination s (F K) (F L) from hlinear s K L]
  exact mamikonOffset_convexBodyCombination s K L (F K) (F L) t

end MovingSofa

end

end

end
