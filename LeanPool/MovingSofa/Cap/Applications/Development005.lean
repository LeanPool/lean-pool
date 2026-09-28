/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Cap.Applications.Development002
public import LeanPool.MovingSofa.Cap.Applications.Development004
public import LeanPool.MovingSofa.Cap.Applications.Development003
public import LeanPool.MovingSofa.Cap.Foundations.Development002
public import LeanPool.MovingSofa.Infrastructure.Geometry.Foundations.Development003
public import LeanPool.MovingSofa.Convex.Foundations.Development003
public import LeanPool.MovingSofa.Gerver.Applications.Development001
public import LeanPool.MovingSofa.Gerver.Applications.Development003
public import LeanPool.MovingSofa.Gerver.Applications.Development002
public import LeanPool.MovingSofa.Sofa.Foundations.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.Special.Domain`.
* `Cap.Special.AreaVariation`.
* `Cap.Tail.Interpolation`.
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
# Cap / Special / Domain
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- Choose the special cap representing a convex body combination, with a fallback to the
first cap. -/
def specialCapCombination (t : I) (K L : SpecialCapSpace) : SpecialCapSpace := by
  classical
  exact if h : ∃ M : SpecialCapSpace,
    M.val.val = convexBodyCombination t K.val.val L.val.val then h.choose else K

theorem specialCap_isConvexDomain :
    (∀ t K L, (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val) ∧
    IsConvexDomain.{0, 0} specialCapCombination ∧
    (∀ K : RightAngleCapSpace, IsBalancedMaximumCap K →
      ∃ L : SpecialCapSpace, L.val = K) ∧
    (∃ K : SpecialCapSpace,
      (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) := by
  -- ### The special class is closed under Minkowski interpolation
  have hclosed : ∀ (t : I) (K L : SpecialCapSpace), ∃ M : SpecialCapSpace,
      M.val.val = convexBodyCombination t K.val.val L.val.val := fun t K L ↦
    ⟨⟨⟨convexBodyCombination t K.val.val L.val.val,
        isCap_convexBodyCombination t K.val L.val⟩,
      satisfiesInjectivityCondition_of_eq_convexBodyCombination rfl K.property.1 L.property.1,
      convexBody_area_superlevel _ _ K.property.2 L.property.2 t⟩, rfl⟩
  have h1 : ∀ (t : I) (K L : SpecialCapSpace), (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val := by
    intro t K L
    have h := hclosed t K L
    rw [specialCapCombination, dite_eq_left h]
    exact h.choose_spec
  -- ### The sofa area functional is bounded by the cap area
  have hfunc : ∀ C : RightAngleCapSpace,
      capAreaFunctional C ≤ ClassicalResults.area (C.val : Set Point) := by
    intro C
    have h : (0 : ℝ) ≤ ClassicalResults.area (capNiche C) := ENNReal.toReal_nonneg
    simp only [capAreaFunctional]
    linarith
  -- ### Gerver's cap is a special cap
  obtain ⟨KG, hKGset, hKGinj⟩ := paperGerverCap_injectivity
  have hstd : IsStandardPosition paperGerverSofa (Real.pi / 2) :=
    gerver_capSupport_identification.2.1 ▸ gerver_capSupport_identification.2.2.1
  have hGfunc : capAreaFunctional KG = ClassicalResults.area paperGerverSofa :=
    capAreaFunctional_eq_sofaArea paperGerverSofa (Real.pi / 2)
      ⟨paperGerverSofa, hstd, gerver_paperNiche_identification.2.2.1.symm⟩ KG hKGset
  have hGbound : (11 : ℝ) / 5 ≤ capAreaFunctional KG := by
    rw [hGfunc, ← gerver_canonical_paper_literal.1]
    exact gerver_area_lower_bound.2
  have hGarea : (11 : ℝ) / 5 ≤ ClassicalResults.area (KG.val : Set Point) :=
    hGbound.trans (hfunc KG)
  refine ⟨h1, ?_, ?_, ⟨⟨KG, hKGinj, hGarea⟩, hKGset⟩⟩
  -- ### The convex-domain structure restricts from the ambient body domain
  · obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
    refine ⟨V, fun K ↦ e K.val.val, ?_, ?_, fun t K L ↦
      (congrArg e (h1 t K L)).trans (hcomb t K.val.val L.val.val)⟩
    · intro K L h
      exact Subtype.ext (Subtype.ext (hinj h))
    · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
      have hb1 : b ≤ 1 := by linarith
      refine ⟨specialCapCombination ⟨b, hb, hb1⟩ K L, ?_⟩
      have hba : 1 - b = a := by linarith
      simpa only [hba] using (congrArg e (h1 ⟨b, hb, hb1⟩ K L)).trans
        (hcomb ⟨b, hb, hb1⟩ K.val.val L.val.val)
  -- ### Every balanced maximum cap is special
  · intro K hK
    refine ⟨⟨K, balancedMaximumCap_injectivity K hK, ?_⟩, rfl⟩
    exact hGbound.trans ((balancedMaximumCap_maximizes_area K hK KG).trans (hfunc K))

/-- The extreme face vertices and the intersections of supporting lines of a special cap are
convex-linear along `specialCapCombination`: the underlying bodies interpolate, and both quantities
are convex-linear in the body. -/
theorem specialCap_maps_linear (t : I) (K L : SpecialCapSpace) :
    (∀ a : Real.Angle,
      (edgeVertices (specialCapCombination t K L).val.val a).1 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).1 +
            (t : ℝ) • (edgeVertices L.val.val a).1 ∧
        (edgeVertices (specialCapCombination t K L).val.val a).2 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).2 +
            (t : ℝ) • (edgeVertices L.val.val a).2) ∧
    ∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (specialCapCombination t K L).val.val (a : Real.Angle)
          (b : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) +
          (t : ℝ) • supportingIntersection L.val.val (a : Real.Angle) (b : Real.Angle) := by
  obtain ⟨-, hev, hsi, -⟩ := convexBody_maps_linear t K.val.val L.val.val
  rw [specialCap_isConvexDomain.1 t K L]
  exact ⟨hev, hsi⟩

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
# Cap / Special / Area Variation
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem specialCapArea_variation :
    IsQuadraticFunctional specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue L.val.val t - supportValue K.val.val t) ∂surfaceAreaMeasure K.val.val := by
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcomb := specialCap_isConvexDomain.1
  -- ### Quadraticity is the ambient bilinear form restricted to the special caps
  refine ⟨⟨fun K L ↦ (1 / 2 : ℝ) * ∫ a : Real.Angle,
      supportValue K.val.val a ∂surfaceAreaMeasure L.val.val, ⟨?_, ?_⟩,
    fun K ↦ harea K.val.val⟩, ?_⟩
  · intro K t L M
    show (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K.val.val a
        ∂surfaceAreaMeasure (specialCapCombination t L M).val.val = _
    rw [hcomb t L M]
    exact hbil.1 K.val.val t L.val.val M.val.val
  · intro M t K L
    show (1 / 2 : ℝ) * ∫ a : Real.Angle,
        supportValue (specialCapCombination t K L).val.val a
        ∂surfaceAreaMeasure M.val.val = _
    rw [hcomb t K L]
    exact hbil.2 M.val.val t K.val.val L.val.val
  intro K L
  -- ### The support difference is integrable against the finite surface area measure
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hint : ∀ M : ConvexBody Point,
      Integrable (supportValue M) (surfaceAreaMeasure K.val.val) := by
    intro M
    have hcont : Continuous (supportValue M) :=
      (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
    exact hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hdiff : Integrable (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
      (surfaceAreaMeasure K.val.val) := (hint L.val.val).sub (hint K.val.val)
  -- ### Interpolating special caps is interpolating convex bodies, so the two segment
  -- functionals are equal as functions and the mixed-area derivative transports
  have hseg : segmentFunctional specialCapCombination
        (fun M : SpecialCapSpace ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point))
        K.val.val L.val.val := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · simp only [segmentFunctional, ht, ↓reduceDIte]
      exact congrArg (fun s : Set Point ↦ ClassicalResults.area s)
        (congrArg (fun M : ConvexBody Point ↦ (M : Set Point)) (hcomb ⟨t, ht⟩ K L))
    · simp only [segmentFunctional, ht, ↓reduceDIte]
  -- ### Both caps have vanishing base support value, so the lower normals contribute nothing
  have hzero := K.val.setIntegral_compl_image_Icc_zero_pi_eq_zero
    (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
    (by rw [K.val.property.2.2.2.2.2.1, L.val.property.2.2.2.2.2.1, sub_zero])
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  rw [convexDirectionalDerivative, hseg,
    ((supportMeasure_mixedArea_symmetry K.val.val L.val.val).2).derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num)),
    ← integral_add_compl hS hdiff, hzero, add_zero]

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
# Cap / Tail / Interpolation
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The cap and both tail bodies are the corresponding convex body combinations. -/
def IsCapTailCombination (t : I) (X Y Z : CapTailSpace) : Prop :=
  Z.cap.val.val = convexBodyCombination t X.cap.val.val Y.cap.val.val ∧
    Z.rightBody = convexBodyCombination t X.rightBody Y.rightBody ∧
    Z.leftBody = convexBodyCombination t X.leftBody Y.leftBody

/-- Choose a cap-tail triple representing componentwise convex combination, with a fallback to
`X`. -/
def capTailCombination (t : I) (X Y : CapTailSpace) : CapTailSpace := by
  classical
  exact if h : ∃ Z, IsCapTailCombination t X Y Z then h.choose else X

theorem capTail_isConvexDomain :
    (∀ t X Y, IsCapTailCombination t X Y (capTailCombination t X Y)) ∧
    IsConvexDomain.{0, 0} capTailCombination := by
  -- A cap-tail triple is determined by its three convex bodies.
  have hext : ∀ X Y : CapTailSpace, X.cap = Y.cap → X.rightBody = Y.rightBody →
      X.leftBody = Y.leftBody → X = Y := by
    intro X Y hcap hright hleft
    revert hcap hright hleft
    obtain ⟨c₁, r₁, l₁, -, -, -, -, -, -⟩ := X
    obtain ⟨c₂, r₂, l₂, -, -, -, -, -, -⟩ := Y
    intro hcap hright hleft
    subst hcap; subst hright; subst hleft
    rfl
  -- Minkowski interpolation is monotone in both of its convex-body arguments.
  have hmono : ∀ (t : I) (A B C D : ConvexBody Point), (A : Set Point) ⊆ (C : Set Point) →
      (B : Set Point) ⊆ (D : Set Point) →
      (convexBodyCombination t A B : Set Point) ⊆
        (convexBodyCombination t C D : Set Point) := by
    intro t A B C D hAC hBD z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_convexBodyCombination_iff t A B z).1 hz
    exact (mem_convexBodyCombination_iff t C D _).2 ⟨x, hAC hx, y, hBD hy, rfl⟩
  -- ### The cap-tail conditions are closed under componentwise Minkowski interpolation
  have hclosed : ∀ (t : I) (X Y : CapTailSpace), ∃ Z, IsCapTailCombination t X Y Z := by
    intro t X Y
    have hKval : (specialCapCombination t X.cap Y.cap).val.val =
        convexBodyCombination t X.cap.val.val Y.cap.val.val :=
      specialCap_isConvexDomain.1 t X.cap Y.cap
    have hlin : ∀ (K L : ConvexBody Point) (a : Real.Angle),
        supportValue (convexBodyCombination t K L) a =
          (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a :=
      fun K L ↦ (convexBody_maps_linear t K L).1
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
    have hb : ∀ a b c d : ℝ, a + b ≤ 1 → c + d ≤ 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) ≤ 1 := by
      intro a b c d h₁ h₂
      nlinarith [mul_le_mul_of_nonneg_left h₁ ht1, mul_le_mul_of_nonneg_left h₂ ht0]
    have he : ∀ a b c d : ℝ, a + b = 1 → c + d = 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) = 1 := by
      intro a b c d h₁ h₂
      linear_combination (1 - (t : ℝ)) * h₁ + (t : ℝ) * h₂
    refine ⟨⟨specialCapCombination t X.cap Y.cap,
      convexBodyCombination t X.rightBody Y.rightBody,
      convexBodyCombination t X.leftBody Y.leftBody,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, hKval, rfl, rfl⟩
    · rw [hKval]
      exact hmono t _ _ _ _ X.right_subset Y.right_subset
    · rw [hKval]
      exact hmono t _ _ _ _ X.left_subset Y.left_subset
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.right_bound s hs) (Y.right_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.right_eq s hs) (Y.right_eq s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.left_bound s hs) (Y.left_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.left_eq s hs) (Y.left_eq s hs)
  -- ### The totalized selection therefore always matches
  have h1 : ∀ (t : I) (X Y : CapTailSpace),
      IsCapTailCombination t X Y (capTailCombination t X Y) := by
    intro t X Y
    have h := hclosed t X Y
    rw [capTailCombination, dite_eq_left h]
    exact h.choose_spec
  refine ⟨h1, ?_⟩
  -- ### The convex-domain structure is inherited from three copies of the body domain
  obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
  refine ⟨ModuleCat.of ℝ (V × V × V),
    fun X ↦ (e X.cap.val.val, e X.rightBody, e X.leftBody), ?_, ?_, ?_⟩
  · intro X Y h
    simp only [Prod.mk.injEq] at h
    exact hext X Y (Subtype.ext (Subtype.ext (hinj h.1))) (hinj h.2.1) (hinj h.2.2)
  · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩ a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have hba : 1 - b = a := by linarith
    obtain ⟨hc, hr, hl⟩ := h1 ⟨b, hb, hb1⟩ X Y
    refine ⟨capTailCombination ⟨b, hb, hb1⟩ X Y, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hba] using (congrArg e hc).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hr).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hl).trans (hcomb ⟨b, hb, hb1⟩ _ _)
  · intro t X Y
    obtain ⟨hc, hr, hl⟩ := h1 t X Y
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨(congrArg e hc).trans (hcomb t _ _), (congrArg e hr).trans (hcomb t _ _),
      (congrArg e hl).trans (hcomb t _ _)⟩

end MovingSofa

end

end

end
