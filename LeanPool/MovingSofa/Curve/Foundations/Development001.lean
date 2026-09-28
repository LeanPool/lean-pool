/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Analysis.Foundations.Development002





public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001

public import LeanPool.MovingSofa.ForMathlib.BoundedVariation.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.MeasureTheory.Foundations.Development001
public import LeanPool.MovingSofa.ForMathlib.Topology.Foundations.Development001


public import LeanPool.MovingSofa.Geometry.Foundations.Development001



public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Order.IntermediateValue
/-!
# Moving sofa: related mathematical developments

* `Curve.Area`.
* `Curve.AreaTransport`.
* `Curve.Concatenation`.
* `Curve.AreaAdditivity`.
* `Curve.CyclicRotation`.
* `Curve.Jordan.Basic`.
* `Curve.Jordan.Orientation`.
* `Curve.Jordan.Area`.
* `Curve.Jordan.ArcArea`.
* `Curve.Jordan.Parametrization`.
* `Curve.Jordan.UnitSphere`.
* `Curve.Jordan.Winding`.
* `Curve.Jordan.RadialWinding`.
* `Curve.Jordan.WindingConcatenation`.
* `Curve.Jordan.CyclicRotation`.
* `Curve.Jordan.WindingKernel`.
* `Curve.Jordan.WindingLocalConstancy`.
* `Curve.Jordan.WindingLifts`.
* `Curve.NullRange`.
* `Curve.SegmentArea`.
* `Curve.SegmentArea.Parametrization`.
* `Curve.SmoothIntervalPaths`.
* `Curve.Jordan.RadialLoop`.
* `Curve.StieltjesChainRule`.
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
# Curve / Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The constant planar path, as a continuous path of bounded variation. -/
def constBVPath (a b : ℝ) (p : Point) : ContinuousBVPaths a b :=
  ⟨fun _ ↦ p, continuous_const, fun i ↦ by
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]⟩

/-- View one coordinate of a continuous BV path as a right-continuous BV function. -/
def continuousBVCoordinate {a b : ℝ} (x : ContinuousBVPaths a b) (i : Fin 2) :
    RightContinuousIntervalBV a b where
  toFun t := x.val t i
  boundedVariation := x.property.2 i
  right_continuous _ :=
    ((PiLp.continuous_apply 2 _ i).comp x.property.1).continuousAt.continuousWithinAt

/-- Half the difference of the two coordinate Stieltjes integrals, giving signed area. -/
def curveAreaFunctional {a b : ℝ} (x : ContinuousBVPaths a b) : ℝ :=
  (intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ x.val t 0) Set.univ -
    intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ x.val t 1) Set.univ) / 2

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
# Curve / Area Transport
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- A continuous monotone surjection preserves continuous bounded variation. -/
theorem continuousBVPaths_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  exact ⟨y, rfl⟩

/-- A continuous monotone surjection preserves signed path area. -/
theorem curveArea_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  refine ⟨y, rfl, ?_⟩
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      φ hφc hφm hφs,
    intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      φ hφc hφm hφs]
  rfl

/-- A continuous monotone surjective reparametrisation identifies the signed areas of two given
paths whenever one is the composite of the other with it. -/
theorem curveAreaFunctional_eq_of_comp_monotone_surjective {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφm : Monotone φ)
    (hφs : Function.Surjective φ) (hy : y.val = x.val ∘ φ) :
    curveAreaFunctional y = curveAreaFunctional x := by
  obtain ⟨z, hz, hza⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hφm hφs
  rw [show y = z from Subtype.ext (hy.trans hz.symm)]
  exact hza

/-- Translating a continuous BV path shifts its signed area by the cross product of the
translation vector with the path's total displacement, halved. -/
theorem curveAreaFunctional_add_constBVPath {a b : ℝ} (hab : a ≤ b)
    (x : ContinuousBVPaths a b) (v : Point) :
    curveAreaFunctional (x + constBVPath a b v) =
      curveAreaFunctional x +
        (v 0 * (x.val ⟨b, hab, le_rfl⟩ 1 - x.val ⟨a, le_rfl, hab⟩ 1) -
          v 1 * (x.val ⟨b, hab, le_rfl⟩ 0 - x.val ⟨a, le_rfl, hab⟩ 0)) / 2 := by
  have hcont : ∀ i : Fin 2, Continuous (continuousBVCoordinate x i).toFun :=
    fun i ↦ (PiLp.continuous_apply 2 _ i).comp x.property.1
  have hval : ∀ (i : Fin 2) (t : Set.Icc a b),
      (continuousBVCoordinate (x + constBVPath a b v) i).toFun t =
        (continuousBVCoordinate x i).toFun t + v i := by
    intro i t
    change (x.val t + v) i = x.val t i + v i
    simp
  have hint : ∀ i j : Fin 2,
      intervalStieltjesIntegral (continuousBVCoordinate (x + constBVPath a b v) i)
          (fun t ↦ (x + constBVPath a b v).val t j) univ =
        intervalStieltjesIntegral (continuousBVCoordinate x i) (fun t ↦ x.val t j) univ +
          v j * (x.val ⟨b, hab, le_rfl⟩ i - x.val ⟨a, le_rfl, hab⟩ i) := by
    intro i j
    rw [show (fun t ↦ (x + constBVPath a b v).val t j) =
      fun t ↦ (continuousBVCoordinate x j).toFun t + v j from funext (hval j)]
    exact intervalStieltjesIntegral_add_const hab (continuousBVCoordinate x i) _ (hcont i)
      (v i) (hval i) _ (hcont j) (v j)
  unfold curveAreaFunctional
  rw [hint 1 0, hint 0 1]
  ring

/-- Reversing a continuous BV path negates its signed area. -/
theorem curveArea_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) :
    let r := Set.Icc.reverse hab
    let y : ContinuousBVPaths a b :=
      ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
          (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
    curveAreaFunctional y = -curveAreaFunctional x := by
  dsimp only
  let r := Set.Icc.reverse hab
  let y : ContinuousBVPaths a b :=
    ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
        (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
  have hcoord (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate y p)
          (fun t ↦ y.val t q) Set.univ =
        -intervalStieltjesIntegral (continuousBVCoordinate x p)
          (fun t ↦ x.val t q) Set.univ := by
    have hrev := intervalStieltjesIntegral_comp_reverse hab
      (continuousBVCoordinate x p)
      ((PiLp.continuous_apply 2 _ p).comp x.property.1)
      (fun t ↦ x.val t q) ((PiLp.continuous_apply 2 _ q).comp x.property.1)
    change intervalStieltjesIntegral _ _ Set.univ = -intervalStieltjesIntegral _ _ Set.univ
    exact hrev
  unfold curveAreaFunctional
  rw [hcoord 1 0, hcoord 0 1]
  ring

/-- A continuous antitone surjection negates signed path area. -/
theorem curveArea_comp_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφa : Antitone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = -curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i) hφa hφs⟩
  let r := Set.Icc.reverse hcd
  let ψ : Set.Icc c d → Set.Icc a b := φ ∘ r
  have hψc : Continuous ψ := hφc.comp (Set.Icc.continuous_reverse hcd)
  have hψm : Monotone ψ := fun _ _ hst ↦
    hφa ((Set.Icc.antitone_reverse hcd) hst)
  have hψs : Function.Surjective ψ :=
    hφs.comp (Set.Icc.surjective_reverse hcd)
  obtain ⟨z, hz, hzarea⟩ :=
    curveArea_comp_monotone_surjective hab hcd x ψ hψc hψm hψs
  have hyrev : curveAreaFunctional z = -curveAreaFunctional y := by
    have hz' : z.val = y.val ∘ r := by
      rw [hz]
      rfl
    let yr : ContinuousBVPaths c d :=
      ⟨y.val ∘ r, y.property.1.comp (Set.Icc.continuous_reverse hcd), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hcd (y.property.2 i)
          (Set.Icc.antitone_reverse hcd) (Set.Icc.surjective_reverse hcd)⟩
    have hyr := curveArea_comp_reverse hcd y
    change curveAreaFunctional yr = -curveAreaFunctional y at hyr
    have hzy : z = yr := by
      apply Subtype.ext
      exact hz'
    simpa [hzy] using hyr
  refine ⟨y, rfl, ?_⟩
  linarith

/-- A constant path has zero signed area, including on an empty parameter interval. -/
theorem curveAreaFunctional_eq_zero_of_constant
    {a b : ℝ} (x : ContinuousBVPaths a b) (p : Point)
    (hx : ∀ t, x.val t = p) : curveAreaFunctional x = 0 := by
  have hfun : x.val = fun _ ↦ p := funext hx
  have hcoord (i : Fin 2) : (fun t ↦ x.val t i) = fun _ ↦ p i := by
    funext t
    rw [hx t]
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 0)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 0)
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 1)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 1)
  unfold curveAreaFunctional
  unfold intervalStieltjesIntegral
  rw [MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 0) (g := fun _ ↦ p 0)
      (fun _ _ ↦ congrFun (hcoord 0) _),
    MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 1) (g := fun _ ↦ p 1)
      (fun _ _ ↦ congrFun (hcoord 1) _)]
  rw [MeasureTheory.VectorMeasure.setIntegral_const,
    MeasureTheory.VectorMeasure.setIntegral_const]
  by_cases hab : a ≤ b
  · let _ : Fact (a ≤ b) := ⟨hab⟩
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder,
      Filter.map_const]
  · let _ : IsEmpty (Set.Icc a b) :=
      ⟨fun t ↦ hab (le_trans t.property.1 t.property.2)⟩
    have hfilters : (Filter.atTop : Filter (Set.Icc a b)) = Filter.atBot :=
      Subsingleton.elim _ _
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder, hfilters]

/-- A continuous monotone or antitone surjection transports BV paths and signed area. -/
theorem curveArea_comp_monotone_or_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
      (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
      (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x) := by
  rcases hφ with hm | ha
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    refine ⟨y, hy, fun _ ↦ harea, ?_⟩
    intro ha
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    refine ⟨y, hy, ?_, fun _ ↦ harea⟩
    intro hm
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea

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
# Curve / Concatenation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A continuous path of bounded variation with an ordered real parameter interval. -/
structure RectifiablePathData where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b

/-- An ordered interval partition identifies the path with a nonempty list of parametrized
pieces. -/
def IsPathConcatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) : Prop :=
  0 < n ∧ ∃ cuts : Fin (n + 1) → Set.Icc Γ.a Γ.b,
    Monotone cuts ∧ (cuts 0 : ℝ) = Γ.a ∧ (cuts (Fin.last n) : ℝ) = Γ.b ∧
    ∀ i : Fin n,
      ∃ (φ : Set.Icc (0 : ℝ) 1 →
          Set.Icc (cuts i.castSucc : ℝ) (cuts i.succ : ℝ))
        (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (pieces i).a (pieces i).b),
        Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
        Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
        ∀ s, Γ.path.val ⟨(φ s : ℝ),
          le_trans (cuts i.castSucc).property.1 (φ s).property.1,
          le_trans (φ s).property.2 (cuts i.succ).property.2⟩ = (pieces i).path.val (ψ s)

/-- A concatenated path stays inside the union of the ranges of its pieces. -/
theorem IsPathConcatenation.range_subset_iUnion {Γ : RectifiablePathData} {n : ℕ}
    {pieces : Fin n → RectifiablePathData} (h : IsPathConcatenation Γ pieces) :
    Set.range Γ.path.val ⊆ ⋃ i, Set.range (pieces i).path.val := by
  classical
  obtain ⟨hn, cuts, hmono, hfirst, hlast, hconc⟩ := h
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : Fin n,
      (cuts i.castSucc : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (cuts i.succ : ℝ) := by
    set T := Finset.univ.filter fun i : Fin (n + 1) ↦ (t : ℝ) ≤ (cuts i : ℝ) with hT
    have hmemT : ∀ i, i ∈ T ↔ (t : ℝ) ≤ (cuts i : ℝ) := fun i ↦ by simp [hT]
    have hTne : T.Nonempty :=
      ⟨Fin.last n, (hmemT _).mpr (by rw [hlast]; exact t.property.2)⟩
    have hmin : (t : ℝ) ≤ (cuts (T.min' hTne) : ℝ) := (hmemT _).mp (T.min'_mem hTne)
    rcases Fin.eq_zero_or_eq_succ (T.min' hTne) with hzero | ⟨j, hj⟩
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · rw [show ((⟨0, hn⟩ : Fin n).castSucc) = 0 from rfl, hfirst]
        exact t.property.1
      · exact (hzero ▸ hmin).trans
          (Subtype.coe_le_coe.mpr (hmono (Fin.zero_le ((⟨0, hn⟩ : Fin n).succ))))
    · refine ⟨j, ?_, by rw [← hj]; exact hmin⟩
      by_contra hlt
      have hle := T.min'_le _ ((hmemT j.castSucc).mpr (not_le.mp hlt).le)
      rw [hj] at hle
      exact absurd (lt_of_lt_of_le (Fin.castSucc_lt_succ (i := j)) hle) (lt_irrefl _)
  obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hconc i
  obtain ⟨s, hs⟩ := hφs ⟨(t : ℝ), hi₁, hi₂⟩
  have hval : ((φ s : ℝ)) = (t : ℝ) := congrArg Subtype.val hs
  refine Set.mem_iUnion.mpr ⟨i, ψ s, ?_⟩
  rw [← heq s]
  exact congrArg _ (Subtype.ext hval)

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
# Curve / Area Additivity
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

theorem curveArea_concatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) (h : IsPathConcatenation Γ pieces) :
    curveAreaFunctional Γ.path = ∑ i, curveAreaFunctional (pieces i).path := by
  rcases h with ⟨_, cuts, hcuts, hcuts_zero, hcuts_last, hpieces⟩
  have hcoord (i : Fin n) (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate Γ.path p)
          (fun t ↦ Γ.path.val t q) (Ioc (cuts i.castSucc) (cuts i.succ)) =
        intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
          (fun t ↦ (pieces i).path.val t q) Set.univ := by
    obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hpieces i
    let l := cuts i.castSucc
    let u := cuts i.succ
    let ι : Set.Icc (l : ℝ) u → Set.Icc Γ.a Γ.b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hp : BoundedVariationOn ((continuousBVCoordinate Γ.path p).toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top (continuousBVCoordinate Γ.path p).boundedVariation
        (eVariationOn.comp_le_of_monotoneOn _ ι
          (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    let Fp : RightContinuousIntervalBV (l : ℝ) u :=
      { toFun := (continuousBVCoordinate Γ.path p).toFun ∘ ι
        boundedVariation := hp
        right_continuous := fun _ ↦
          (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
            (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
    rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate Γ.path p)
      ((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t q)
      ((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1) l u
      (hcuts (Fin.castSucc_le_succ i))]
    change intervalStieltjesIntegral Fp
        ((fun t ↦ Γ.path.val t q) ∘ ι) Set.univ =
      intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
        (fun t ↦ (pieces i).path.val t q) Set.univ
    rw [intervalStieltjesIntegral_comp_monotone_surjective
      (show (l : ℝ) ≤ u from hcuts (Fin.castSucc_le_succ i)) (by norm_num) Fp
      (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      ((fun t ↦ Γ.path.val t q) ∘ ι)
      (((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      φ hφc hφm hφs,
      intervalStieltjesIntegral_comp_monotone_surjective
        (pieces i).ordered (by norm_num) (continuousBVCoordinate (pieces i).path p)
        ((PiLp.continuous_apply 2 _ p).comp (pieces i).path.property.1)
        (fun t ↦ (pieces i).path.val t q)
        ((PiLp.continuous_apply 2 _ q).comp (pieces i).path.property.1)
        ψ hψc hψm hψs]
    congr 1
    · congr 1
      funext s
      simpa [Fp, continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z p) (heq s)
    · funext s
      simpa [continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z q) (heq s)
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 1)
      ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 0) ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 0)
      ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 1) ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last]
  simp_rw [hcoord]
  rw [← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

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
# Curve / Cyclic Rotation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Restrict a continuous BV path to a closed subinterval. -/
def ContinuousBVPaths.restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (_hlu : l ≤ u) : ContinuousBVPaths (l : ℝ) u :=
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun t ↦
    ⟨t, le_trans l.property.1 t.property.1, le_trans t.property.2 u.property.2⟩
  ⟨x.val ∘ ι, x.property.1.comp (continuous_subtype_val.subtype_mk _), fun i ↦
    ne_top_of_le_ne_top (x.property.2 i)
      (eVariationOn.comp_le_of_monotoneOn (fun t ↦ x.val t i) ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))⟩

private theorem curveArea_restrict_Ioc
    {a b : ℝ} (x : ContinuousBVPaths a b) (l u : Set.Icc a b) (hlu : l ≤ u) :
    (intervalStieltjesIntegral (continuousBVCoordinate x 1)
        (fun t ↦ x.val t 0) (Ioc l u) -
      intervalStieltjesIntegral (continuousBVCoordinate x 0)
        (fun t ↦ x.val t 1) (Ioc l u)) / 2 =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      l u hlu,
    intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      l u hlu]
  rfl

/-- Signed path area is additive along any monotone chain of cuts of the parameter interval. -/
theorem curveArea_eq_sum_restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    curveAreaFunctional x =
      ∑ i : Fin n, curveAreaFunctional (ContinuousBVPaths.restrict x (cuts i.castSucc)
        (cuts i.succ) (hcuts (Fin.castSucc_le_succ i))) := by
  simp_rw [← curveArea_restrict_Ioc x]
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      cuts hcuts hzero hlast,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      cuts hcuts hzero hlast, ← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

/-- Split the signed area of a continuous BV path at any parameter value. -/
theorem curveArea_eq_restriction_add_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hs1 : a ≤ (s : ℝ) := s.property.1
  have hs2 : (s : ℝ) ≤ b := s.property.2
  change curveAreaFunctional x =
    curveAreaFunctional (ContinuousBVPaths.restrict x a' s hs1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' hs2)
  have hcuts : Monotone (![a', s, b'] : Fin 3 → Set.Icc a b) := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i
    · exact hs1
    · exact hs2
  have hsum := curveArea_eq_sum_restrict x ![a', s, b'] hcuts rfl rfl
  rw [Fin.sum_univ_two] at hsum
  exact hsum

/-- The tail and head restrictions have signed areas summing to the original area. -/
theorem curveArea_cyclic_cut_sum
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) +
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) := by
  rw [curveArea_eq_restriction_add_restriction hab x s, add_comm]

/-- Package a restricted continuous BV path with its interval endpoints. -/
def ContinuousBVPaths.restrictionData {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hlu : l ≤ u) : RectifiablePathData where
  a := l
  b := u
  ordered := hlu
  path := ContinuousBVPaths.restrict x l u hlu

/-- A tail-then-head concatenation preserves the signed area. -/
theorem curveArea_cyclic_rotation
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (rotated : ContinuousBVPaths c d) (hcd : c ≤ d)
    (hrot : IsPathConcatenation
      { a := c, b := d, ordered := hcd, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1]) :
    curveAreaFunctional rotated = curveAreaFunctional x := by
  rw [curveArea_concatenation _ _ hrot]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousBVPaths.restrictionData]
  exact (curveArea_cyclic_cut_sum hab x s).symm

private theorem boundedVariation_concatUnitIntervals_coordinate
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) (i : Fin 2) :
    BoundedVariationOn (fun t ↦ Function.concatUnitIntervals p.val q.val t i) Set.univ := by
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let o : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩
  let w : Set.Icc (0 : ℝ) 2 := ⟨2, by norm_num⟩
  let f := fun t ↦ Function.concatUnitIntervals p.val q.val t i
  have hzo : z ≤ o := by change (0 : ℝ) ≤ 1; norm_num
  have how : o ≤ w := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit := eVariationOn.Icc_add_Icc f hzo how (Set.mem_univ o)
  simp only [Set.univ_inter] at hsplit
  have hwhole : Set.Icc z w = Set.univ := by
    ext t
    change ((0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2) ↔ True
    exact iff_true_intro t.property
  rw [hwhole] at hsplit
  change eVariationOn f Set.univ ≠ ⊤
  rw [← hsplit]
  apply ENNReal.add_ne_top.mpr
  constructor
  · refine ne_top_of_le_ne_top (p.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc z o) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) i)
            (Set.Icc z o) := by
              apply eVariationOn.congr
              intro t ht
              have ht' : (t : ℝ) ≤ 1 := by exact ht.2
              simp [f, Function.concatUnitIntervals, ht']
      _ ≤ eVariationOn (fun t ↦ p.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ p.val t i)
              (t := Set.Icc z o)
              (fun t : Set.Icc (0 : ℝ) 2 ↦ Set.projIcc 0 1 (by norm_num) (t : ℝ))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num) hxy)
              (mapsTo_univ _ _))
  · refine ne_top_of_le_ne_top (q.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc o w) =
          eVariationOn
            (fun t : Set.Icc (0 : ℝ) 2 ↦
              q.val (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1)) i)
            (Set.Icc o w) := by
              apply eVariationOn.congr
              intro t ht
              have hleft : (1 : ℝ) ≤ t := by exact ht.1
              have ht' : ¬(t : ℝ) ≤ 1 ∨ (t : ℝ) = 1 := by
                rcases lt_or_eq_of_le hleft with h | h
                · exact Or.inl (not_le_of_gt h)
                · exact Or.inr h.symm
              rcases ht' with ht' | htEq
              · simp [f, Function.concatUnitIntervals, ht']
              · simpa [f, Function.concatUnitIntervals, htEq] using congrArg (fun z ↦ z i) hjoin
      _ ≤ eVariationOn (fun t ↦ q.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ q.val t i)
              (t := Set.Icc o w)
              (fun t : Set.Icc (0 : ℝ) 2 ↦
                Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num)
                (sub_le_sub_right (show (_ : ℝ) ≤ _ from hxy) 1))
              (mapsTo_univ _ _))

private def concatUnitPaths (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate p q hjoin⟩

private theorem isPathConcatenation_concatUnitPaths
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := concatUnitPaths p q hjoin }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p },
        { a := 0, b := 1, ordered := by norm_num, path := q }] := by
  let cuts : Fin 3 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cuts, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hij ⊢
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨t, by simp [cuts]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk continuous_subtype_val _
    · intro x y hxy
      exact hxy
    · intro y
      exact ⟨⟨y, by simpa [cuts] using y.property⟩, Subtype.ext rfl⟩
    · intro t
      have ht : (t : ℝ) ≤ 1 := t.property.2
      simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, ht]
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(t : ℝ) + 1, by
          change (1 : ℝ) ≤ (t : ℝ) + 1 ∧ (t : ℝ) + 1 ≤ 2
          constructor <;> linarith [t.property.1, t.property.2]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
    · intro x y hxy
      change (x : ℝ) + 1 ≤ (y : ℝ) + 1
      linarith [show (x : ℝ) ≤ y from hxy]
    · intro y
      refine ⟨⟨(y : ℝ) - 1, ?_⟩, Subtype.ext ?_⟩
      · have hy1 : (1 : ℝ) ≤ y := by exact y.property.1
        have hy2 : (y : ℝ) ≤ 2 := by exact y.property.2
        constructor <;> linarith [y.property.1, y.property.2]
      · simp [φ]
    · intro t
      by_cases ht : (t : ℝ) = 0
      · have htSub : t = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext ht
        rw [htSub]
        simpa [φ, ψ, concatUnitPaths, Function.concatUnitIntervals] using hjoin
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, htpos]

private def unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private theorem continuous_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitIntervalParam a b hab) := Set.Icc.continuous_convexComb _ _

private theorem monotone_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitIntervalParam a b hab) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + (s : ℝ) * b ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith

private theorem surjective_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitIntervalParam a b hab) := by
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
    · change (1 - ((x : ℝ) - a) / (b - a)) * a + ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

private theorem unitIntervalParam_zero (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩ := by
  exact Set.Icc.convexComb_zero _ _

private theorem unitIntervalParam_one (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩ := by
  exact Set.Icc.convexComb_one _ _

/-- Rotate a closed continuous BV path by concatenating its tail and head. -/
theorem exists_cyclic_rotation_path {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
  let tail := ContinuousBVPaths.restrict x s ⟨b, hab, le_rfl⟩ s.property.2
  let head := ContinuousBVPaths.restrict x ⟨a, le_rfl, hab⟩ s s.property.1
  obtain ⟨p, hp⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.2 tail
    (unitIntervalParam s b s.property.2) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.1 head
    (unitIntervalParam a s s.property.1) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  have hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩ := by
    rw [hp, hq]
    simp only [Function.comp_apply, unitIntervalParam_one, unitIntervalParam_zero]
    exact hx
  let rotated := concatUnitPaths p q hjoin
  have hrot : IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
    obtain ⟨hn, cuts, hm, hz, ho, hc⟩ := isPathConcatenation_concatUnitPaths p q hjoin
    refine ⟨hn, cuts, hm, hz, ho, ?_⟩
    intro i
    fin_cases i
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 0
      refine ⟨φ, unitIntervalParam s b s.property.2 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = p.val (ψ t) at h
      rw [hp] at h
      exact h
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 1
      refine ⟨φ, unitIntervalParam a s s.property.1 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = q.val (ψ t) at h
      rw [hq] at h
      exact h
  refine ⟨rotated, ?_, hrot⟩
  change Function.concatUnitIntervals p.val q.val = _
  rw [hp, hq]
  rfl

/-- Construct an area-preserving cyclic rotation of a closed continuous BV path. -/
theorem exists_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] ∧
      curveAreaFunctional rotated = curveAreaFunctional x := by
  obtain ⟨rotated, hr, hrot⟩ := exists_cyclic_rotation_path hab x s hx
  exact ⟨rotated, hr, hrot,
    curveArea_cyclic_rotation hab x s rotated (by norm_num) hrot⟩

private theorem mem_range_convexComb {a b : ℝ} (l u z : Set.Icc a b)
    (hlz : l ≤ z) (hzu : z ≤ u) : z ∈ Set.range (Set.Icc.convexComb l u) := by
  obtain ⟨t, ht⟩ := surjective_unitIntervalParam (l : ℝ) u (hlz.trans hzu)
    ⟨z, hlz, hzu⟩
  refine ⟨t, Subtype.ext ?_⟩
  have h := congrArg (fun y : Set.Icc (l : ℝ) u ↦ (y : ℝ)) ht
  exact h

/-- Cutting and rejoining a closed path does not change its carrier. -/
theorem range_cyclic_concat {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s : Set.Icc a b)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩) :
    Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)) = Set.range x := by
  have hjoin : (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩) ⟨1, by norm_num⟩ =
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ⟨0, by norm_num⟩ := by
    simpa using hx.symm
  rw [Function.range_concatUnitIntervals _ _ hjoin]
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.range_comp_subset_range _ _) (Set.range_comp_subset_range _ _)
  · rintro _ ⟨t, rfl⟩
    by_cases hst : s ≤ t
    · obtain ⟨r, hr⟩ := mem_range_convexComb s ⟨b, hab, le_rfl⟩ t hst t.property.2
      exact Or.inl ⟨r, congrArg x hr⟩
    · obtain ⟨r, hr⟩ := mem_range_convexComb ⟨a, le_rfl, hab⟩ s t t.property.1
        (le_of_not_ge hst)
      exact Or.inr ⟨r, congrArg x hr⟩

/-- Every point of a nondegenerate closed path occurs before its terminal parameter. -/
theorem exists_param_lt_top_of_mem_range {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b → Point)
    (hx : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    {p : Point} (hp : p ∈ Set.range x) :
    ∃ s : Set.Icc a b, (s : ℝ) < b ∧ x s = p := by
  obtain ⟨s, hs⟩ := hp
  by_cases hsb : (s : ℝ) < b
  · exact ⟨s, hsb, hs⟩
  · have hst : s = ⟨b, hab.le, le_rfl⟩ :=
      Subtype.ext (le_antisymm s.property.2 (le_of_not_gt hsb))
    exact ⟨⟨a, le_rfl, hab.le⟩, hab, hx.trans (hst ▸ hs)⟩

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
# Curve / Jordan / Basic
-/

@[expose] public section

namespace MovingSofa

/-- The set is the range of an injective continuous map from a closed real interval. -/
def IsJordanArc (Γ : Set Point) : Prop :=
  ∃ (a b : ℝ) (_ : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

/-- The set is the range of an injective continuous map from the circle. -/
def IsJordanCurve (Γ : Set Point) : Prop :=
  ∃ x : Circle → Point, Continuous x ∧ Function.Injective x ∧ Set.range x = Γ

/-- Bundle the predicates for Jordan arcs and Jordan curves. -/
def jordanSets : (Set Point → Prop) × (Set Point → Prop) :=
  (IsJordanArc, IsJordanCurve)

/-- A Jordan arc admits a parametrization with the specified starting and ending points. -/
def IsOrientedJordanArc (Γ : Set Point) (p q : Point) : Prop :=
  ∃ (a b : ℝ) (hab : a ≤ b) (x : Set.Icc a b → Point),
    Continuous x ∧ Function.Injective x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = p ∧ x ⟨b, hab, le_rfl⟩ = q

/-- A Jordan arc equipped with ordered endpoints. -/
structure OrientedJordanArc where
  /-- The point set traced by the arc. -/
  carrier : Set Point
  /-- The initial endpoint of the oriented arc. -/
  startPoint : Point
  /-- The terminal endpoint of the oriented arc. -/
  endPoint : Point
  parametrizable : IsOrientedJordanArc carrier startPoint endPoint

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
# Curve / Jordan / Orientation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Points outside the curve whose connected component in its complement is bounded. -/
def jordanInterior (Γ : Set Point) : Set Point :=
  {p | p ∉ Γ ∧ Bornology.IsBounded (connectedComponentIn Γᶜ p)}

/-- A continuous real angle lifts the normalized displacement from the specified point. -/
def IsCurveAngleLift {a b : ℝ} (x : Set.Icc a b → Point) (p : Point)
    (θ : Set.Icc a b → ℝ) : Prop :=
  Continuous θ ∧ ∀ t,
    Real.cos (θ t) = (x t - p) 0 / ‖x t - p‖ ∧
    Real.sin (θ t) = (x t - p) 1 / ‖x t - p‖

/-- The angle-lift increment divided by `2π`, with value zero if no lift exists. -/
def curveWinding {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point) (p : Point) : ℝ := by
  classical
  exact if h : ∃ θ, IsCurveAngleLift x p θ then
    (h.choose ⟨b, hab, le_rfl⟩ - h.choose ⟨a, le_rfl, hab⟩) / (2 * Real.pi)
  else 0

/-- A simple closed parametrization with the specified winding sign on the interior. -/
def IsOrientedJordanParametrization {a b : ℝ} (hab : a ≤ b)
    (Γ : Set Point) (counterclockwise : Bool) (x : Set.Icc a b → Point) : Prop :=
  a < b ∧ IsJordanCurve Γ ∧ Continuous x ∧ Set.range x = Γ ∧
    x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩ ∧
    Set.InjOn x {t | (t : ℝ) < b} ∧
    ∀ p ∈ jordanInterior Γ, curveWinding hab x p = if counterclockwise then 1 else -1

/-- A Jordan curve together with a choice of clockwise or counterclockwise orientation. -/
structure OrientedJordanCurve where
  /-- The point set traced by the Jordan curve. -/
  carrier : Set Point
  isJordan : IsJordanCurve carrier
  /-- Select positive winding orientation when true and negative orientation when false. -/
  counterclockwise : Bool

/-- Bundle the winding functional and the oriented-parametrization predicate. -/
def jordanCurveOrientation :
    (∀ (a b : ℝ), a ≤ b → (Set.Icc a b → Point) → Point → ℝ) ×
    (∀ (a b : ℝ), a ≤ b → Set Point → Bool → (Set.Icc a b → Point) → Prop) :=
  (fun _ _ hab ↦ curveWinding hab, fun _ _ hab ↦ IsOrientedJordanParametrization hab)

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
# Curve / Jordan / Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- An injective continuous BV parametrization respecting an oriented arc’s endpoints. -/
structure ArcBVParametrization (Γ : OrientedJordanArc) where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b
  injective : Function.Injective path.val
  range_eq : Set.range path.val = Γ.carrier
  start_eq : path.val ⟨a, le_rfl, ordered⟩ = Γ.startPoint
  end_eq : path.val ⟨b, ordered, le_rfl⟩ = Γ.endPoint

/-- A continuous BV parametrization respecting a Jordan curve’s orientation. -/
structure ClosedBVParametrization (Γ : OrientedJordanCurve) where
  /-- The initial real parameter. -/
  a : ℝ
  /-- The terminal real parameter. -/
  b : ℝ
  ordered : a ≤ b
  /-- The continuous parametrization of bounded variation. -/
  path : ContinuousBVPaths a b
  oriented : IsOrientedJordanParametrization ordered Γ.carrier Γ.counterclockwise path.val

/-- Oriented Jordan arcs admitting a continuous BV parametrization. -/
abbrev RectifiableOrientedArc :=
  {Γ : OrientedJordanArc // Nonempty (ArcBVParametrization Γ)}

/-- Oriented Jordan curves admitting a continuous BV parametrization. -/
abbrev RectifiableOrientedCurve :=
  {Γ : OrientedJordanCurve // Nonempty (ClosedBVParametrization Γ)}

/-- The signed Stieltjes area of a chosen BV parametrization of the oriented arc. -/
def jordanArcArea (Γ : RectifiableOrientedArc) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

/-- The signed Stieltjes area of a chosen BV parametrization of the oriented curve. -/
def jordanClosedCurveArea (Γ : RectifiableOrientedCurve) : ℝ :=
  curveAreaFunctional (Classical.choice Γ.property).path

/-- Bundle the signed area functionals for oriented arcs and closed curves. -/
def jordanArea : (RectifiableOrientedArc → ℝ) × (RectifiableOrientedCurve → ℝ) :=
  (jordanArcArea, jordanClosedCurveArea)

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
# Curve / Jordan / Arc Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Same-carrier Jordan arcs have equal or opposite signed areas according to their endpoints. -/
theorem curveArea_arc_same_carrier
    (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
    (y : ArcBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  let _ : Fact (x.a ≤ x.b) := ⟨x.ordered⟩
  let _ : Fact (y.a ≤ y.b) := ⟨y.ordered⟩
  have hxemb : Topology.IsEmbedding x.path.val :=
    (x.path.property.1.isClosedEmbedding x.injective).isEmbedding
  let φ : Set.Icc y.a y.b → Set.Icc x.a x.b := fun t ↦
    hxemb.toHomeomorph.symm ⟨y.path.val t, by
      rw [x.range_eq, hcarrier, ← y.range_eq]
      exact Set.mem_range_self t⟩
  have hφc : Continuous φ :=
    hxemb.toHomeomorph.symm.continuous.comp <|
      y.path.property.1.subtype_mk _
  have hxy (t : Set.Icc y.a y.b) : x.path.val (φ t) = y.path.val t := by
    exact congrArg Subtype.val (hxemb.toHomeomorph.apply_symm_apply
      ⟨y.path.val t, by
        rw [x.range_eq, hcarrier, ← y.range_eq]
        exact Set.mem_range_self t⟩)
  have hφi : Function.Injective φ := fun s t hst ↦
    y.injective <| by rw [← hxy s, ← hxy t, hst]
  have hφs : Function.Surjective φ := by
    intro s
    have hmem : x.path.val s ∈ Set.range y.path.val := by
      rw [y.range_eq, ← hcarrier, ← x.range_eq]
      exact Set.mem_range_self s
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, ?_⟩
    apply x.injective
    rw [hxy t, ht]
  have hxbot : x.path.val (⊥ : Set.Icc x.a x.b) = Γ.startPoint := by
    convert x.start_eq using 1
  have hxtop : x.path.val (⊤ : Set.Icc x.a x.b) = Γ.endPoint := by
    convert x.end_eq using 1
  have hybot : y.path.val (⊥ : Set.Icc y.a y.b) = Δ.startPoint := by
    convert y.start_eq using 1
  have hytop : y.path.val (⊤ : Set.Icc y.a y.b) = Δ.endPoint := by
    convert y.end_eq using 1
  have hmono (hstart : Γ.startPoint = Δ.startPoint)
      (hend : Γ.endPoint = Δ.endPoint) : Monotone φ := by
    apply (hφc.strictMono_of_inj_boundedOrder ?_ hφi).monotone
    have hbot : φ ⊥ = ⊥ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hstart, hxbot]
    have htop : φ ⊤ = ⊤ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hend, hxtop]
    rw [hbot, htop]
    exact bot_le
  have hanti (hstart : Γ.startPoint = Δ.endPoint)
      (hend : Γ.endPoint = Δ.startPoint) : Antitone φ := by
    apply (hφc.strictAnti_of_inj_boundedOrder ?_ hφi).antitone
    have htop : φ ⊤ = ⊥ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hstart, hxbot]
    have hbot : φ ⊥ = ⊤ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hend, hxtop]
    rw [htop, hbot]
    exact bot_le
  constructor
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective
      x.ordered y.ordered x.path φ hφc (hmono hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    simpa [hzy] using hzarea.symm
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective
      x.ordered y.ordered x.path φ hφc (hanti hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    rw [hzy] at hzarea
    linarith

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
# Curve / Jordan / Parametrization
-/

@[expose] public section

noncomputable section

open Set Function

namespace MovingSofa

/-- Identify an open interval with the corresponding subset of the closed interval. -/
def openIntervalToIntervalInterior {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} where
  toFun t := ⟨⟨t, t.property.1.le, t.property.2.le⟩, t.property⟩
  invFun t := ⟨t, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk fun t ↦ ⟨t.property.1.le, t.property.2.le⟩).subtype_mk _
  continuous_invFun := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

/-- Regard a parametrized point as an element of the path’s range. -/
def intervalToRange {a b : ℝ} (x : Set.Icc a b → Point) :
    Set.Icc a b → Set.range x := fun t ↦ ⟨x t, ⟨t, rfl⟩⟩

theorem intervalToRange_continuous {a b : ℝ} (x : Set.Icc a b → Point)
    (hx : Continuous x) : Continuous (intervalToRange x) :=
  hx.subtype_mk fun t ↦ ⟨t, rfl⟩

theorem intervalToRange_surjective {a b : ℝ} (x : Set.Icc a b → Point) :
    Function.Surjective (intervalToRange x) := by
  rintro ⟨p, t, rfl⟩
  exact ⟨t, rfl⟩

/-- The carrier of a closed parametrized loop with its basepoint removed. -/
def puncturedLoopRangeSet {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : Set (Set.range x) :=
  {p | (p : Point) ≠ x ⟨a, le_rfl, hab⟩}

theorem puncturedLoopRangeSet_isOpen {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : IsOpen (puncturedLoopRangeSet hab x) := by
  let p : Set.range x := ⟨x ⟨a, le_rfl, hab⟩, ⟨⟨a, le_rfl, hab⟩, rfl⟩⟩
  rw [show puncturedLoopRangeSet hab x = ({p}ᶜ : Set (Set.range x)) by
    ext q
    change ((q : Point) ≠ (p : Point)) ↔ q ≠ p
    exact not_congr Subtype.ext_iff.symm]
  exact isOpen_compl_singleton

theorem intervalToRange_preimage_punctured {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    intervalToRange x ⁻¹' puncturedLoopRangeSet hab x =
      {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} := by
  ext t
  simp only [Set.mem_preimage, puncturedLoopRangeSet, Set.mem_ofPred_eq, intervalToRange]
  constructor
  · intro ht
    constructor
    · exact lt_of_le_of_ne t.property.1 fun hta ↦ by
        apply ht
        exact congrArg x (Subtype.ext hta.symm)
    · exact lt_of_le_of_ne t.property.2 fun htb ↦ by
        apply ht
        have ht_top : t = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
        rw [ht_top]
        exact hclosed.symm
  · rintro ⟨hat, htb⟩ htx
    have : t = ⟨a, le_rfl, hab⟩ := hinj htb hab' htx
    exact hat.ne (congrArg Subtype.val this).symm

theorem intervalToPuncturedRange_injective {a b : ℝ} (hab : a ≤ b)
    (_hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Function.Injective
      ((puncturedLoopRangeSet hab x).restrictPreimage (intervalToRange x)) := by
  intro s t hst
  apply Subtype.ext
  apply hinj (x₁ := s.val) (x₂ := t.val)
  · have hsne : x s.val ≠ x ⟨a, le_rfl, hab⟩ := s.property
    exact lt_of_le_of_ne s.val.property.2 fun hsb ↦ by
      apply hsne
      have hs_top : s.val = ⟨b, hab, le_rfl⟩ := Subtype.ext hsb
      rw [hs_top]
      exact hclosed.symm
  · have htne : x t.val ≠ x ⟨a, le_rfl, hab⟩ := t.property
    exact lt_of_le_of_ne t.val.property.2 fun htb ↦ by
      apply htne
      have ht_top : t.val = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
      rw [ht_top]
      exact hclosed.symm
  · exact congrArg (fun p : puncturedLoopRangeSet hab x ↦ (p : Point)) hst

/-- Removing the basepoint turns a closed once-traversal into a homeomorphism from the
open parameter interval onto the punctured carrier. -/
noncomputable def openIntervalHomeomorphPuncturedRange {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.Ioo a b ≃ₜ puncturedLoopRangeSet hab x := by
  let f := intervalToRange x
  let s := puncturedLoopRangeSet hab x
  have hfq : Topology.IsQuotientMap f :=
    (intervalToRange_continuous x hx).isClosedMap.isQuotientMap
      (intervalToRange_continuous x hx) (intervalToRange_surjective x)
  have hgq : Topology.IsQuotientMap (s.restrictPreimage f) :=
    hfq.restrictPreimage_isOpen (puncturedLoopRangeSet_isOpen hab x)
  have hgh : IsHomeomorph (s.restrictPreimage f) :=
    isHomeomorph_iff_isQuotientMap_injective.2
      ⟨hgq, intervalToPuncturedRange_injective hab hab' x hclosed hinj⟩
  exact (openIntervalToIntervalInterior hab').trans <|
    (Homeomorph.setCongr
      (intervalToRange_preimage_punctured hab hab' x hclosed hinj).symm).trans
      (hgh.homeomorph _)

/-- The punctured-loop homeomorphism agrees pointwise with the original path. -/
theorem openIntervalHomeomorphPuncturedRange_coe {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) (t : Set.Ioo a b) :
    ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj t :
        puncturedLoopRangeSet hab x) : Point) =
      x ⟨t, t.property.1.le, t.property.2.le⟩ := by
  rfl

private def puncturedLoopRangeHomeomorphOfEq
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    puncturedLoopRangeSet hcd y ≃ₜ puncturedLoopRangeSet hab x where
  toFun q :=
    ⟨⟨q, by rw [hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart)⟩
  invFun q :=
    ⟨⟨q, by rw [← hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _

/-- The transition between two endpoint-matched once-traversals, restricted to their open
parameter intervals. -/
private noncomputable def openIntervalClosedCurveTransition
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    Set.Ioo c d ≃ₜ Set.Ioo a b :=
  (openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj).trans
    ((puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart).trans
      (openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj).symm)

private theorem openIntervalClosedCurveTransition_point
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩)
    (t : Set.Ioo c d) :
    x ⟨openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.1.le,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.2.le⟩ =
      y ⟨t, t.property.1.le, t.property.2.le⟩ := by
  let ex := openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj
  let ey := openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj
  let ec := puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart
  change x ⟨ex.symm (ec (ey t)), (ex.symm (ec (ey t))).property.1.le,
      (ex.symm (ec (ey t))).property.2.le⟩ =
    y ⟨t, t.property.1.le, t.property.2.le⟩
  rw [← openIntervalHomeomorphPuncturedRange_coe hab hab' x hxc hxclosed hxinj
      (ex.symm (ec (ey t))),
    ← openIntervalHomeomorphPuncturedRange_coe hcd hcd' y hyc hyclosed hyinj t]
  exact congrArg (fun q : puncturedLoopRangeSet hab x ↦ (q : Point))
    (ex.apply_symm_apply (ec (ey t)))

private theorem homeomorph_Ioo_strictMono_or_strictAnti
    {a b c d : ℝ} (hcd : c < d) (e : Set.Ioo c d ≃ₜ Set.Ioo a b) :
    StrictMono e ∨ StrictAnti e := by
  let f : ℝ → ℝ := Function.extend ((↑) : Set.Ioo c d → ℝ)
    (fun t ↦ (e t : ℝ)) 0
  have hf_apply (t : Set.Ioo c d) : f t = (e t : ℝ) :=
    Subtype.val_injective.extend_apply _ _ t
  have hfc : ContinuousOn f (Set.Ioo c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    funext t
    exact hf_apply t
  have hfi : Set.InjOn f (Set.Ioo c d) := by
    intro s hs t ht hst
    have heq : e ⟨s, hs⟩ = e ⟨t, ht⟩ := by
      apply Subtype.ext
      calc
        (e ⟨s, hs⟩ : ℝ) = f s := (hf_apply ⟨s, hs⟩).symm
        _ = f t := hst
        _ = (e ⟨t, ht⟩ : ℝ) := hf_apply ⟨t, ht⟩
    exact congrArg Subtype.val (e.injective heq)
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo hcd hfc hfi with hm | ha
  · left
    intro s t hst
    have := hm s.property t.property hst
    change (e s : ℝ) < (e t : ℝ)
    simpa only [hf_apply] using this
  · right
    intro s t hst
    have := ha s.property t.property hst
    change (e t : ℝ) < (e s : ℝ)
    simpa only [hf_apply] using this

private def closedIntervalReverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b ≃ₜ Set.Icc a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem closedIntervalReverse_antitone {a b : ℝ} (_hab : a ≤ b) :
    Antitone (closedIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  change a + b - (t : ℝ) ≤ a + b - (s : ℝ)
  linarith

private theorem closedIntervalReverse_left {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨a, le_rfl, hab⟩ = ⟨b, hab, le_rfl⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private theorem closedIntervalReverse_right {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨b, hab, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private def openIntervalReverse {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ Set.Ioo a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem openIntervalReverse_strictAnti {a b : ℝ} (_hab : a < b) :
    StrictAnti (openIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) < (t : ℝ) := hst
  change a + b - (t : ℝ) < a + b - (s : ℝ)
  linarith

private theorem openIntervalClosedCurveTransition_strictMono_or_strictAnti
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    StrictMono (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) ∨
    StrictAnti (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) :=
  homeomorph_Ioo_strictMono_or_strictAnti hcd'
    (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
      hyclosed hxinj hyinj hrange hstart)

/-- An endpoint-matched pair of continuous once-traversals of the same carrier differ by a
continuous surjective monotone or antitone reparametrization of the closed intervals. -/
private theorem exists_reparametrization_with_endpoints
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧
      ((Monotone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) ∨
        (Antitone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)) ∧
      ∀ t, x (φ t) = y t := by
  let e := openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
    hxclosed hyclosed hxinj hyinj hrange hstart
  rcases openIntervalClosedCurveTransition_strictMono_or_strictAnti hab hab' hcd hcd'
      x y hxc hyc hxclosed hyclosed hxinj hyinj hrange hstart with hm | ha
  · let eo : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse e hm e.symm e.apply_symm_apply
    let φ := OrderIso.extendIoo hab' eo
    refine ⟨φ, OrderIso.continuous_extendIoo hcd' hab' eo,
      OrderIso.surjective_extendIoo hcd' hab' eo, Or.inl ⟨?_, ?_, ?_⟩, ?_⟩
    · exact OrderIso.monotone_extendIoo hcd' hab' eo
    · exact OrderIso.extendIoo_left hcd' hab' eo
    · exact OrderIso.extendIoo_right hcd' hab' eo
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht, show φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' eo]
        exact hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht, show φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' eo]
        exact hxclosed.symm.trans (hstart.trans hyclosed)
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have ht : t = ⟨ti, ti.property.1.le, ti.property.2.le⟩ := Subtype.ext rfl
          rw [ht]
          exact OrderIso.extendIoo_interior hab' eo ti
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti
  · let r := openIntervalReverse hab'
    let g : Set.Ioo c d ≃ₜ Set.Ioo a b := e.trans r
    have hgm : StrictMono g := by
      intro s t hst
      exact openIntervalReverse_strictAnti hab' (ha hst)
    let go : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse g hgm g.symm g.apply_symm_apply
    let ψ := OrderIso.extendIoo hab' go
    let φ : Set.Icc c d → Set.Icc a b := fun t ↦ closedIntervalReverse hab (ψ t)
    refine ⟨φ, (closedIntervalReverse hab).continuous.comp
        (OrderIso.continuous_extendIoo hcd' hab' go),
      (closedIntervalReverse hab).surjective.comp
        (OrderIso.surjective_extendIoo hcd' hab' go), Or.inr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (closedIntervalReverse_antitone hab).comp_monotone
        (OrderIso.monotone_extendIoo hcd' hab' go)
    · rw [show φ ⟨c, le_rfl, hcd⟩ =
          closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩) from rfl,
        show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · rw [show φ ⟨d, hcd, le_rfl⟩ =
          closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩) from rfl,
        show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩)) = _
        rw [show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
        rw [closedIntervalReverse_left hab]
        exact hxclosed.symm.trans hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩)) = _
        rw [show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
        rw [closedIntervalReverse_right hab]
        exact hstart.trans hyclosed
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have hψ := OrderIso.extendIoo_interior hab' go ti
          dsimp [go, g, r] at hψ
          change a + b - (ψ t : ℝ) = (e ti : ℝ)
          rw [hψ]
          change a + b - (a + b - (e ti : ℝ)) = (e ti : ℝ)
          ring
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti

/-- Equal-start simple closed paths with the same range admit a monotone or antitone transition. -/
theorem exists_reparametrization_of_range_eq_of_start_eq
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y = x ∘ φ := by
  rcases exists_reparametrization_with_endpoints hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart with ⟨φ, hφc, hφs, hφo, hφxy⟩
  refine ⟨φ, hφc, hφs, hφo.imp (fun h ↦ h.1) (fun h ↦ h.1), ?_⟩
  funext t
  exact (hφxy t).symm

/-- Equal-start closed Jordan parametrizations admit a monotone or antitone transition. -/
theorem ClosedBVParametrization.exists_reparametrization_of_start_eq
    {Γ Δ : OrientedJordanCurve} (x : ClosedBVParametrization Γ)
    (y : ClosedBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier)
    (hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
    ∃ φ : Set.Icc y.a y.b → Set.Icc x.a x.b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y.path.val = x.path.val ∘ φ := by
  have hrange : Set.range x.path.val = Set.range y.path.val := by
    rw [x.oriented.2.2.2.1, y.oriented.2.2.2.1]
    exact hcarrier
  exact exists_reparametrization_of_range_eq_of_start_eq x.ordered x.oriented.1 y.ordered
    y.oriented.1
    x.path.val y.path.val x.path.property.1 y.path.property.1
    x.oriented.2.2.2.2.1 y.oriented.2.2.2.2.1
    x.oriented.2.2.2.2.2.1 y.oriented.2.2.2.2.2.1 hrange hstart

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
# Curve / Jordan / Unit Sphere
-/

@[expose] public section

noncomputable section
namespace MovingSofa

private def circlePoint (z : Circle) : Point := WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im]

private lemma norm_circlePoint (z : Circle) : ‖circlePoint z‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [circlePoint, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, Real.norm_eq_abs, sq_abs]
  have h := Complex.sq_norm (z : ℂ)
  simp only [Complex.normSq_apply, Circle.norm_coe] at h
  nlinarith

private lemma continuous_circlePoint : Continuous circlePoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val

/-- A planar set homeomorphic to the unit sphere is a Jordan curve. -/
lemma isJordanCurve_of_unitSphere_homeomorph {Γ : Set Point}
    (e : {u : Point | ‖u‖ = 1} ≃ₜ ↥Γ) : IsJordanCurve Γ := by
  let f : Circle → {u : Point | ‖u‖ = 1} := fun z ↦ ⟨circlePoint z, norm_circlePoint z⟩
  refine ⟨fun z ↦ (e (f z) : Point), continuous_subtype_val.comp
    (e.continuous.comp (continuous_circlePoint.subtype_mk _)), ?_, ?_⟩
  · intro z w h
    have he := e.injective (Subtype.ext h)
    have hpoint := congrArg Subtype.val he
    apply Subtype.ext
    apply Complex.ext
    · exact congrFun (congrArg WithLp.ofLp hpoint) 0
    · exact congrFun (congrArg WithLp.ofLp hpoint) 1
  · apply Set.Subset.antisymm
    · rintro p ⟨z, rfl⟩
      exact (e (f z)).property
    · intro p hp
      let u := e.symm ⟨p, hp⟩
      let z : ℂ := ⟨u.val 0, u.val 1⟩
      have hz : ‖z‖ = 1 := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
        rw [Complex.sq_norm]
        have hu : ‖u.val‖ = 1 := u.property
        have hsq := congrArg (fun r : ℝ ↦ r ^ 2) hu
        rw [EuclideanSpace.norm_sq_eq] at hsq
        simpa [z, Fin.sum_univ_two, sq] using hsq
      let ζ : Circle := ⟨z, by
        change z ∈ Metric.sphere 0 1
        simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
      refine ⟨ζ, ?_⟩
      have hf : f ζ = u := by
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl
      change (e (f ζ) : Point) = p
      rw [hf]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)

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
# Curve / Jordan / Winding
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Two continuous angle lifts have the same endpoint increment. -/
theorem IsCurveAngleLift.endpoint_increment_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ ψ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift x p ψ) :
    θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩ =
      ψ ⟨b, hab, le_rfl⟩ - ψ ⟨a, le_rfl, hab⟩ := by
  let _ : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have h := Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin hθ.1 hψ.1
    (fun t ↦ (hθ.2 t).1.trans (hψ.2 t).1.symm)
    (fun t ↦ (hθ.2 t).2.trans (hψ.2 t).2.symm)
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩
  linarith

/-- Compute the winding value from any continuous angle lift. -/
theorem IsCurveAngleLift.curveWinding_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) :
    curveWinding hab x p = (θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩) / (2 * Real.pi) := by
  unfold curveWinding
  rw [dite_eq_left ⟨θ, hθ⟩]
  congr 1
  exact IsCurveAngleLift.endpoint_increment_eq hab (Exists.choose_spec ⟨θ, hθ⟩) hθ

/-- A nonzero winding value provides a continuous angle lift. -/
theorem exists_curveAngleLift_of_curveWinding_ne_zero {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} (h : curveWinding hab x p ≠ 0) :
    ∃ θ, IsCurveAngleLift x p θ := by
  by_contra hn
  apply h
  simp only [curveWinding, dite_eq_right hn]

/-- Pull back an angle lift along a continuous parameter map. -/
theorem IsCurveAngleLift.comp {a b c d : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    IsCurveAngleLift (x ∘ φ) p (θ ∘ φ) :=
  ⟨hθ.1.comp hφ, fun t ↦ hθ.2 (φ t)⟩

/-- Compute winding after continuous reparametrization from lifted endpoint values. -/
theorem IsCurveAngleLift.curveWinding_comp {a b c d : ℝ} (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    curveWinding hcd (x ∘ φ) p =
      (θ (φ ⟨d, hcd, le_rfl⟩) - θ (φ ⟨c, le_rfl, hcd⟩)) / (2 * Real.pi) :=
  (hθ.comp hφ).curveWinding_eq hcd

/-- A continuous reparametrization preserving endpoints preserves winding. -/
theorem curveWinding_comp_of_endpoints {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) :
    curveWinding hcd (x ∘ φ) p = curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]

/-- A continuous reparametrization exchanging endpoints negates winding. -/
theorem curveWinding_comp_of_reversed_endpoints {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩) :
    curveWinding hcd (x ∘ φ) p = -curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]
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
# Curve / Jordan / Radial Winding
-/

@[expose] public section

noncomputable section
namespace MovingSofa

/-- The parameter angle lifts a positive radial loop about its center. -/
lemma isCurveAngleLift_radial {a b : ℝ} (o : Point) (r : Set.Icc a b → ℝ)
    (hr : ∀ t, 0 < r t) :
    IsCurveAngleLift (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o
      (fun t ↦ (t : ℝ)) := by
  refine ⟨continuous_subtype_val, fun t ↦ ?_⟩
  have hn : ‖r t • normalVector ((t : ℝ) : Real.Angle)‖ = r t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr t), norm_normalVector_real, mul_one]
  simp only [add_sub_cancel_left, hn]
  constructor
  · change Real.cos (t : ℝ) = r t * Real.cos (t : ℝ) / r t
    field_simp [(hr t).ne']
  · change Real.sin (t : ℝ) = r t * Real.sin (t : ℝ) / r t
    field_simp [(hr t).ne']

/-- A positive radial loop winds once around its center. -/
lemma curveWinding_radial_center (o : Point) (r : Set.Icc (0 : ℝ) (2 * Real.pi) → ℝ)
    (hr : ∀ t, 0 < r t) :
    curveWinding (by positivity)
      (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o = 1 := by
  rw [(isCurveAngleLift_radial o r hr).curveWinding_eq]
  simp

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
# Curve / Jordan / Winding Concatenation
-/

@[expose] public section

noncomputable section

namespace MovingSofa

private theorem cos_sin_add_sub {α β : ℝ}
    (hc : Real.cos α = Real.cos β) (hs : Real.sin α = Real.sin β) (t : ℝ) :
    Real.cos (t + (α - β)) = Real.cos t ∧
      Real.sin (t + (α - β)) = Real.sin t := by
  have hcd : Real.cos (α - β) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.cos_sq_add_sin_sq β]
  have hsd : Real.sin (α - β) = 0 := by
    rw [Real.sin_sub, hc, hs]
    ring
  simp [Real.cos_add, Real.sin_add, hcd, hsd]

/-- Winding is additive for two paths joined at a common endpoint. -/
theorem curveWinding_concatUnitIntervals
    {x y : Set.Icc (0 : ℝ) 1 → Point} {p : Point}
    {θ ψ : Set.Icc (0 : ℝ) 1 → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift y p ψ)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    curveWinding (by norm_num) (Function.concatUnitIntervals x y) p =
      curveWinding (by norm_num) x p + curveWinding (by norm_num) y p := by
  let δ := θ ⟨1, by norm_num⟩ - ψ ⟨0, by norm_num⟩
  have htrig (t : Set.Icc (0 : ℝ) 1) :
      Real.cos (ψ t + δ) = Real.cos (ψ t) ∧
      Real.sin (ψ t + δ) = Real.sin (ψ t) := by
    apply cos_sin_add_sub
    · rw [(hθ.2 _).1, (hψ.2 _).1, hjoin]
    · rw [(hθ.2 _).2, (hψ.2 _).2, hjoin]
  let η := Function.concatUnitIntervals θ (fun t ↦ ψ t + δ)
  have hη : IsCurveAngleLift (Function.concatUnitIntervals x y) p η := by
    refine ⟨Function.continuous_concatUnitIntervals hθ.1
      (hψ.1.add continuous_const) (by dsimp [δ]; ring), ?_⟩
    intro t
    dsimp [η, Function.concatUnitIntervals]
    split_ifs with ht
    · exact hθ.2 _
    · exact ⟨(htrig _).1.trans (hψ.2 _).1, (htrig _).2.trans (hψ.2 _).2⟩
  rw [hη.curveWinding_eq, hθ.curveWinding_eq, hψ.curveWinding_eq]
  simp only [η, Function.concatUnitIntervals]
  norm_num
  dsimp [δ]
  change (ψ ⟨1, _⟩ + (θ ⟨1, _⟩ - ψ ⟨0, _⟩) - θ ⟨0, _⟩) / (2 * Real.pi) =
    (θ ⟨1, _⟩ - θ ⟨0, _⟩) / (2 * Real.pi) +
      (ψ ⟨1, _⟩ - ψ ⟨0, _⟩) / (2 * Real.pi)
  ring

/-- Moving a closed path's cut point preserves winding. -/
theorem curveWinding_concat_of_cyclic_endpoints {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hφ₁ : φ ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φ) (x ∘ ψ)) p =
      curveWinding hab x p := by
  have hjoin : (x ∘ φ) ⟨1, by norm_num⟩ = (x ∘ ψ) ⟨0, by norm_num⟩ := by
    simp only [Function.comp_apply, hφ₁, hψ₀]
    exact hx.symm
  rw [curveWinding_concatUnitIntervals (hθ.comp hφ) (hθ.comp hψ) hjoin,
    hθ.curveWinding_comp (by norm_num) hφ, hθ.curveWinding_comp (by norm_num) hψ,
    hφ₀, hφ₁, hψ₀, hψ₁, hθ.curveWinding_eq hab]
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
# Curve / Jordan / Cyclic Rotation
-/

@[expose] public section

noncomputable section
namespace MovingSofa

private theorem strictMono_convexComb {a b : ℝ} (l u : Set.Icc a b) (hlu : l < u) :
    StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- Moving an oriented Jordan path's start to an interior parameter preserves area and
orientation. -/
theorem exists_oriented_cyclic_rotation {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val ⟨0, by norm_num⟩ = x.val s ∧
      curveAreaFunctional r = curveAreaFunctional x := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _, harea⟩ := exists_cyclic_rotation_eq_concat hab x s hclosed.symm
  refine ⟨r, ?_, ?_, harea⟩
  · refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
    · rw [hr, range_cyclic_concat hab x.val s hclosed]
      exact hx.2.2.2.1
    · rw [hr]
      simp
    · rw [hr]
      exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
        hx.2.2.2.2.2.1 hclosed s has hsb
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (strictMono_convexComb _ _ hsb) (strictMono_convexComb _ _ has)
        (by simp) (by simp) (by simp)
    · intro p hp
      have hxw := hx.2.2.2.2.2.2 p hp
      have hn : curveWinding hab x.val p ≠ 0 := by
        rw [hxw]
        cases ccw <;> norm_num
      obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
      rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
        (by simp) (by simp) (by simp) (by simp)]
      exact hxw
  · rw [hr]
    simp

/-- A cyclic rotation together with its literal tail-then-head formula. -/
theorem exists_oriented_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _⟩ :=
    exists_cyclic_rotation_path hab x s hclosed.symm
  refine ⟨r, ?_, hr⟩
  refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
  · rw [hr, range_cyclic_concat hab x.val s hclosed]
    exact hx.2.2.2.1
  · rw [hr]
    simp
  · rw [hr]
    exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
      hx.2.2.2.2.2.1 hclosed s has hsb
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (strictMono_convexComb _ _ hsb)
      (strictMono_convexComb _ _ has)
      (by simp) (by simp) (by simp)
  · intro p hp
    have hxw := hx.2.2.2.2.2.2 p hp
    have hn : curveWinding hab x.val p ≠ 0 := by
      rw [hxw]
      cases ccw <;> norm_num
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
    rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
      (by simp) (by simp) (by simp) (by simp)]
    exact hxw

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
# Curve / Jordan / Winding Kernel
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The inverse-distance vector kernel based at `z`. -/
def windingKernel (z p : Point) : Point :=
  (‖z - p‖ ^ 2)⁻¹ • (z - p)

private def pointComplex : Point ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

private theorem pointComplex_windingKernel (z p : Point) :
    pointComplex (windingKernel z p) =
      (starRingEnd ℂ (pointComplex z - pointComplex p))⁻¹ := by
  have hsub : pointComplex (z - p) = pointComplex z - pointComplex p :=
    map_sub pointComplex z p
  rw [windingKernel, map_smul, hsub]
  let v : ℂ := pointComplex z - pointComplex p
  change (‖z - p‖ ^ 2)⁻¹ • v = (starRingEnd ℂ v)⁻¹
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, star_star, Complex.normSq_eq_norm_sq, norm_star]
  have hn : ‖v‖ = ‖z - p‖ := by
    rw [show v = pointComplex (z - p) by simp [v, hsub]]
    exact LinearIsometryEquiv.norm_map pointComplex (z - p)
  rw [hn, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  ring

private theorem norm_windingKernel (z p : Point) :
    ‖windingKernel z p‖ = if p = z then 0 else ‖z - p‖⁻¹ := by
  by_cases hp : p = z
  · subst p
    simp [windingKernel]
  · have hnorm : ‖z - p‖ ≠ 0 := by
      simpa [norm_eq_zero, sub_eq_zero] using Ne.symm hp
    rw [windingKernel, norm_smul, Real.norm_eq_abs]
    simp only [abs_inv, abs_pow, abs_norm]
    simp only [hp, ↓reduceIte]
    field_simp

private theorem ball_zero_subset_ball_two_mul (R : ℝ) (z : Point)
    (hz : ‖z‖ < R) : Metric.ball 0 R ⊆ Metric.ball z (2 * R) := by
  intro p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp ⊢
  have hp' : ‖p‖ < R := by simpa using hp
  calc
    ‖p - z‖ ≤ ‖p‖ + ‖z‖ := norm_sub_le p z
    _ < R + R := add_lt_add hp' hz
    _ = 2 * R := by ring

private theorem measurable_windingKernel (z : Point) : Measurable (windingKernel z) := by
  unfold windingKernel
  exact (((measurable_const.sub measurable_id).norm.pow_const 2).inv.smul
    (measurable_const.sub measurable_id))

private theorem indicator_inv_norm_pointComplex (S : ℝ) (p : Point) :
    (Metric.ball (0 : Point) S).indicator (fun p ↦ ‖p‖⁻¹) p =
      (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) := by
  have hm : pointComplex p ∈ Metric.ball (0 : ℂ) S ↔
      p ∈ Metric.ball (0 : Point) S := by
    simp [Metric.mem_ball, dist_eq_norm]
  by_cases hp : p ∈ Metric.ball (0 : Point) S
  · simp [hp, hm.mpr hp]
  · simp [hp, mt hm.mp hp]

private theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : Point ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  have hf : Integrable ((Metric.ball (0 : ℂ) S).indicator fun q ↦ ‖q‖⁻¹) :=
    (integrable_indicator_iff measurableSet_ball).mpr (Complex.integrableOn_inv_norm_ball S)
  refine (((LinearIsometryEquiv.measurePreserving pointComplex).integrable_comp_emb
    pointComplex.toHomeomorph.measurableEmbedding).mpr hf).congr ?_
  filter_upwards with p
  exact (indicator_inv_norm_pointComplex S p).symm

private theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : Point in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : Point ↦ ‖p‖⁻¹) measurableSet_ball]
  calc
    (∫ p : Point, (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
        ∫ p : Point, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) (pointComplex p) :=
      integral_congr_ae (Filter.Eventually.of_forall (indicator_inv_norm_pointComplex S))
    _ = ∫ q : ℂ, (Metric.ball (0 : ℂ) S).indicator (fun q ↦ ‖q‖⁻¹) q :=
      (LinearIsometryEquiv.measurePreserving pointComplex).integral_comp
        pointComplex.toHomeomorph.measurableEmbedding _
    _ = 2 * Real.pi * S := by
      rw [integral_indicator measurableSet_ball]
      exact Complex.setIntegral_inv_norm_ball S hS

private theorem indicator_centered_inv_norm_eq (z : Point) (S : ℝ) :
    (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) =
      fun p ↦ (Metric.ball 0 S).indicator (fun q ↦ ‖q‖⁻¹) (z - p) := by
  funext p
  have hm : p ∈ Metric.ball z S ↔ z - p ∈ Metric.ball 0 S := by
    simp only [Metric.mem_ball, dist_eq_norm]
    simp [sub_zero, norm_sub_rev]
  by_cases hp : p ∈ Metric.ball z S
  · simp [hp, hm.mp hp]
  · simp [hp, mt hm.mpr hp]

private theorem indicator_centered_inv_norm_nonneg (z : Point) (S : ℝ) (p : Point) :
    0 ≤ (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
  Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem integrable_indicator_centered_inv_norm (z : Point) (S : ℝ) :
    Integrable ((Metric.ball z S).indicator fun p ↦ ‖z - p‖⁻¹) := by
  rw [indicator_centered_inv_norm_eq, MeasureTheory.integrable_comp_sub_left]
  exact (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_norm_ball S)

private theorem integral_indicator_centered_inv_norm (z : Point) (S : ℝ) (hS : 0 < S) :
    (∫ p : Point, (Metric.ball z S).indicator (fun p ↦ ‖z - p‖⁻¹) p) = 2 * Real.pi * S := by
  rw [indicator_centered_inv_norm_eq,
    MeasureTheory.integral_sub_left_eq_self _ volume z, integral_indicator measurableSet_ball]
  exact setIntegral_inv_norm_ball S hS

private theorem norm_windingKernel_le_indicator (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (fun p ↦ ‖windingKernel z p‖) ≤ᵐ[volume.restrict (Metric.ball 0 R)]
      (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  have hpz : p ∈ Metric.ball z (2 * R) := ball_zero_subset_ball_two_mul R z hz hp
  rw [norm_windingKernel]
  by_cases heq : p = z
  · simp only [heq, ↓reduceIte]
    exact indicator_centered_inv_norm_nonneg z (2 * R) z
  · simp [heq, hpz]

/-- The winding kernel is integrable on a disk containing its base point. -/
theorem integrableOn_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    IntegrableOn (windingKernel z) (Metric.ball 0 R) :=
  Integrable.mono' (integrable_indicator_centered_inv_norm z (2 * R)).integrableOn
    (measurable_windingKernel z).aestronglyMeasurable
    (norm_windingKernel_le_indicator R z hz)

/-- The norm of the winding kernel has an integrable uniform majorant on an interior disk. -/
theorem setIntegral_norm_windingKernel_ball_le
    (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R := by
  have hg : Integrable ((Metric.ball z (2 * R)).indicator fun p ↦ ‖z - p‖⁻¹) :=
    integrable_indicator_centered_inv_norm z (2 * R)
  calc
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤
        ∫ p in Metric.ball 0 R, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_mono_ae_restrict (integrableOn_windingKernel_ball R z hz).norm
        hg.integrableOn (norm_windingKernel_le_indicator R z hz)
    _ ≤ ∫ p, (Metric.ball z (2 * R)).indicator (fun p ↦ ‖z - p‖⁻¹) p :=
      setIntegral_le_integral hg
        (Filter.Eventually.of_forall (indicator_centered_inv_norm_nonneg z (2 * R)))
    _ = 2 * Real.pi * (2 * R) :=
      integral_indicator_centered_inv_norm z (2 * R) (by linarith)
    _ = 4 * Real.pi * R := by ring

/-- The integral of the winding kernel over a disk is `π` times its base point. -/
theorem setIntegral_windingKernel_ball (R : ℝ) (z : Point) (hz : ‖z‖ < R) :
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  let T : Point ≃ₗᵢ[ℝ] ℂ := pointComplex.trans Complex.conjLIE
  let a : ℂ := T z
  have ha : ‖a‖ < R := by simpa [a, T] using hz
  have hc := Complex.setIntegral_inv_sub_ball R a ha
  let G : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hpres := (LinearIsometryEquiv.measurePreserving T).integral_comp
    T.toHomeomorph.measurableEmbedding G
  have hfun : ∀ p : Point,
      G (T p) = (Metric.ball 0 R).indicator
        (fun p ↦ pointComplex (windingKernel z p)) p := by
    intro p
    have hm : T p ∈ Metric.ball (0 : ℂ) R ↔ p ∈ Metric.ball (0 : Point) R := by
      simp [Metric.mem_ball, dist_eq_norm, T]
    by_cases hp : p ∈ Metric.ball (0 : Point) R
    · rw [show G (T p) = (a - T p)⁻¹ by simp [G, hm.mpr hp]]
      rw [show (Metric.ball (0 : Point) R).indicator
          (fun p ↦ pointComplex (windingKernel z p)) p =
          pointComplex (windingKernel z p) by simp [hp]]
      rw [pointComplex_windingKernel]
      simp only [a, T, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply,
        map_sub]
    · rw [show G (T p) = 0 by simp [G, mt hm.mp hp]]
      simp [hp]
  have htransport :
      (∫ q in Metric.ball 0 R, (a - q)⁻¹) =
        pointComplex (∫ p in Metric.ball 0 R, windingKernel z p) := by
    rw [← integral_indicator measurableSet_ball]
    change (∫ q, G q) = _
    rw [← hpres]
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    rw [integral_indicator measurableSet_ball]
    simpa using
      (pointComplex.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm hInt)
  apply pointComplex.injective
  rw [← htransport, hc]
  simp [a, T, Complex.real_smul]

/-- Off the range of a continuous interval path, each coordinate of the winding kernel is
a bounded continuous function of the parameter. -/
theorem windingKernel_coord_continuous_bounded
    {a b : ℝ} {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) (i : Fin 2) :
    Continuous (fun t ↦ windingKernel (x t) p i) ∧
      ∃ C : ℝ, ∀ t, |windingKernel (x t) p i| ≤ C := by
  have hsub : Continuous (fun t ↦ x t - p) := hx.sub continuous_const
  have hne : ∀ t, ‖x t - p‖ ^ 2 ≠ 0 := by
    intro t
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    intro h
    exact hp ⟨t, sub_eq_zero.mp h⟩
  have hkernel : Continuous (fun t ↦ windingKernel (x t) p) := by
    unfold windingKernel
    exact ((hsub.norm.pow 2).inv₀ hne).smul hsub
  have hcoord : Continuous (fun t ↦ windingKernel (x t) p i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i).comp hkernel
  refine ⟨hcoord, ?_⟩
  have hbdd : BddAbove ((fun t ↦ |windingKernel (x t) p i|) '' Set.univ) :=
    isCompact_univ.bddAbove_image hcoord.abs.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun t ↦ hC ⟨t, Set.mem_univ t, rfl⟩⟩

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
# Curve / Jordan / Winding Local Constancy
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_m85d0e79 (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_m85d0e79 (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_m85d0e79 (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

/-- The principal relative argument varies continuously while the relative dot product is
positive. This is the branch needed for a small displacement of the basepoint. -/
lemma continuous_arg_conj_mul_of_re_pos {α : Type*} [TopologicalSpace α]
    {z w : α → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (z t) * w t).re) :
    Continuous (fun t ↦ Complex.arg (starRingEnd ℂ (z t) * w t)) := by
  have hf : Continuous (fun u ↦ starRingEnd ℂ (z u) * w u) :=
    (continuous_star.comp hz).mul hw
  change Continuous (Complex.arg ∘ fun u ↦ starRingEnd ℂ (z u) * w u)
  exact Complex.continuousOn_arg.comp_continuous hf (fun t ↦ Or.inl (hpos t))

/-- The principal relative argument rotates the normalized coordinates of `z` to those of `w`. -/
lemma normalized_complex_rotation_by_arg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) :
    Real.cos (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hz, Complex.sin_arg,
    Complex.cos_arg hzw, Complex.sin_arg]
  simp only [Complex.norm_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  rw [Complex.norm_conj]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- Coordinate form of the preceding rotation identity for any chosen real lift of `z`. -/
lemma normalized_complex_rotation_by_relative_arg {z w : ℂ} {θ : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hc : Real.cos θ = z.re / ‖z‖) (hs : Real.sin θ = z.im / ‖z‖) :
    Real.cos (θ + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (θ + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, hc, hs, Complex.cos_arg hzw, Complex.sin_arg,
    Complex.norm_mul, Complex.norm_conj]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- A positive relative dot product supplies the continuous principal correction between two
basepoints. -/
lemma IsCurveAngleLift.add_principal_basepoint_correction {a b : ℝ}
    {x : Set.Icc a b → Point} {p q : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    IsCurveAngleLift x q (fun u ↦ θ u +
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q))) := by
  let z := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - q)
  have hz : Continuous z := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hw : Continuous w := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hδ : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ (z u) * w u)) :=
    continuous_arg_conj_mul_of_re_pos hz hw hpos
  refine ⟨hθ.1.add hδ, fun u ↦ ?_⟩
  have hprod : starRingEnd ℂ (z u) * w u ≠ 0 := by
    intro hzero
    have := hpos u
    rw [hzero] at this
    simp at this
  have hzne : z u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hwne : w u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hc : Real.cos (θ u) = (z u).re / ‖z u‖ := by
    simpa only [z, pointComplex_re_m85d0e79, Complex.orthonormalBasisOneI.repr.symm.norm_map]
      using (hθ.2
        u).1
  have hs : Real.sin (θ u) = (z u).im / ‖z u‖ := by
    simpa only [z, pointComplex_im_m85d0e79, Complex.orthonormalBasisOneI.repr.symm.norm_map]
      using (hθ.2
        u).2
  simpa only [z, w, pointComplex_re_m85d0e79, pointComplex_im_m85d0e79,
      Complex.orthonormalBasisOneI.repr.symm.norm_map] using
    normalized_complex_rotation_by_relative_arg hzne hwne hc hs

/-- Moving the basepoint through the positive-relative-dot neighborhood preserves winding. -/
theorem curveWinding_eq_of_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p q : Point} {θ : Set.Icc a b → ℝ} (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    curveWinding hab x q = curveWinding hab x p := by
  let δ := fun u ↦ Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
    Complex.orthonormalBasisOneI.repr.symm (x u - q))
  have hθδ : IsCurveAngleLift x q (fun u ↦ θ u + δ u) :=
    hθ.add_principal_basepoint_correction hx hpos
  have hδ : δ ⟨a, le_rfl, hab⟩ = δ ⟨b, hab, le_rfl⟩ := by
    simp only [δ, hclosed]
  rw [hθδ.curveWinding_eq hab, hθ.curveWinding_eq hab]
  rw [hδ]
  ring

/-- Off a compact continuous loop, every sufficiently nearby basepoint has positive relative dot
product with the original radial vectors. -/
theorem exists_ball_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) :
    ∃ r > 0, ∀ q, dist q p < r → ∀ u,
      0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q)).re := by
  let _ : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  let f : Set.Icc a b → ℝ := fun u ↦ ‖x u - p‖
  have hf : Continuous f := (hx.sub continuous_const).norm
  obtain ⟨u₀, -, hu₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  have hne (u : Set.Icc a b) : x u - p ≠ 0 := by
    intro hzero
    apply hp
    refine ⟨u, ?_⟩
    exact sub_eq_zero.mp hzero
  have hfu₀ : 0 < f u₀ := norm_pos_iff.mpr (hne u₀)
  refine ⟨f u₀ / 2, half_pos hfu₀, fun q hq u ↦ ?_⟩
  have hmin : f u₀ ≤ f u := hu₀ (Set.mem_univ u)
  have hd : ‖p - q‖ < f u₀ / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hq
  have hd' : ‖p - q‖ < ‖x u - p‖ := lt_of_lt_of_le hd (by linarith)
  rw [conj_pointComplex_mul_re_m85d0e79]
  have hw : x u - q = (x u - p) + (p - q) := by abel
  rw [hw, inner_add_right, real_inner_self_eq_norm_sq]
  have hcs := abs_real_inner_le_norm (x u - p) (p - q)
  have hlower : -(‖x u - p‖ * ‖p - q‖) ≤ inner ℝ (x u - p) (p - q) :=
    (neg_le_of_abs_le hcs)
  nlinarith [norm_pos_iff.mpr (hne u)]

/-- Winding of a continuous closed loop is locally constant away from its range. -/
theorem curveWinding_locally_constant_off_range {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos hab hx hp
  refine ⟨Metric.ball p r, Metric.isOpen_ball, Metric.mem_ball_self hr, fun q hq ↦ ?_⟩
  have hqp : dist q p < r := by simpa [dist_comm] using hq
  have hpos := hdot q hqp
  by_cases hpLift : ∃ θ, IsCurveAngleLift x p θ
  · obtain ⟨θ, hθ⟩ := hpLift
    exact curveWinding_eq_of_relative_dot_pos hab hx hclosed hθ hpos
  · have hqLift : ¬∃ ψ, IsCurveAngleLift x q ψ := by
      rintro ⟨ψ, hψ⟩
      have hrev : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - q)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - p)).re := by
        intro u
        rw [conj_pointComplex_mul_re_m85d0e79, real_inner_comm, ← conj_pointComplex_mul_re_m85d0e79]
        exact hpos u
      exact hpLift ⟨_, hψ.add_principal_basepoint_correction hx hrev⟩
    unfold curveWinding
    rw [dite_eq_right hqLift, dite_eq_right hpLift]

/-- While the relative dot product with the initial radius vector stays positive, the
increment of a continuous angle lift is the principal relative argument, computed as the
arctangent of the ratio of the relative cross product to the relative dot product. -/
theorem IsCurveAngleLift.sub_eq_arctan_of_dot_pos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ) {t u : Set.Icc a b}
    (htu : (t : ℝ) ≤ (u : ℝ))
    (hpos : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
      0 < (x t - p) 0 * (x s - p) 0 + (x t - p) 1 * (x s - p) 1) :
    θ u - θ t = Real.arctan
      (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
        ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
  have hsub : ∀ s : Set.Icc (t : ℝ) (u : ℝ), (s : ℝ) ∈ Set.Icc a b := fun s ↦
    ⟨le_trans t.property.1 s.property.1, le_trans s.property.2 u.property.2⟩
  let ι : Set.Icc (t : ℝ) (u : ℝ) → Set.Icc a b := fun s ↦ ⟨s.val, hsub s⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  set y : Set.Icc (t : ℝ) (u : ℝ) → Point := x ∘ ι with hy
  have hycont : Continuous y := hx.comp hι
  have hιu : ι ⟨(u : ℝ), htu, le_rfl⟩ = u := Subtype.ext rfl
  have hιt : ι ⟨(t : ℝ), le_rfl, htu⟩ = t := Subtype.ext rfl
  set z : ℂ := Complex.orthonormalBasisOneI.repr.symm (x t - p) with hz
  set w : Set.Icc (t : ℝ) (u : ℝ) → ℂ :=
    fun s ↦ Complex.orthonormalBasisOneI.repr.symm (y s - p) with hw
  have hwcont : Continuous w :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hycont.sub continuous_const)
  have hre (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).re =
        (x t - p) 0 * (x (ι s) - p) 0 + (x t - p) 1 * (x (ι s) - p) 1 := by
    simp only [hz, hw, hy, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      pointComplex_re_m85d0e79, pointComplex_im_m85d0e79, Function.comp_apply]
    ring
  have him (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).im =
        (x t - p) 0 * (x (ι s) - p) 1 - (x t - p) 1 * (x (ι s) - p) 0 := by
    simp only [hz, hw, hy, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      pointComplex_re_m85d0e79, pointComplex_im_m85d0e79, Function.comp_apply]
    ring
  have hposC : ∀ s : Set.Icc (t : ℝ) (u : ℝ), 0 < (starRingEnd ℂ z * w s).re := by
    intro s
    rw [hre s]
    exact hpos (ι s) s.property.1 s.property.2
  have hzne : z ≠ 0 := by
    intro h0
    have := hposC ⟨(t : ℝ), le_rfl, htu⟩
    rw [h0] at this
    simp at this
  have hwne : ∀ s, w s ≠ 0 := by
    intro s h0
    have := hposC s
    rw [h0] at this
    simp at this
  have hznorm : ‖z‖ = ‖x t - p‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map _
  have hc : Real.cos (θ t) = z.re / ‖z‖ := by
    rw [hznorm, hz, pointComplex_re_m85d0e79]; exact (hθ.2 t).1
  have hsn : Real.sin (θ t) = z.im / ‖z‖ := by
    rw [hznorm, hz, pointComplex_im_m85d0e79]; exact (hθ.2 t).2
  have hlift1 : IsCurveAngleLift y p (θ ∘ ι) := hθ.comp hι
  have hlift2 : IsCurveAngleLift y p
      (fun s ↦ θ t + Complex.arg (starRingEnd ℂ z * w s)) := by
    refine ⟨continuous_const.add
      (continuous_arg_conj_mul_of_re_pos continuous_const hwcont hposC), fun s ↦ ?_⟩
    have hrot := normalized_complex_rotation_by_relative_arg hzne (hwne s) hc hsn
    have hwnorm : ‖w s‖ = ‖y s - p‖ :=
      Complex.orthonormalBasisOneI.repr.symm.norm_map _
    rw [hwnorm] at hrot
    simpa only [hw, pointComplex_re_m85d0e79, pointComplex_im_m85d0e79] using hrot
  have hincr := IsCurveAngleLift.endpoint_increment_eq htu hlift1 hlift2
  simp only [Function.comp_apply, hιu, hιt] at hincr
  have hwt : w ⟨(t : ℝ), le_rfl, htu⟩ = z := by
    simp only [hw, hy, Function.comp_apply, hιt, hz]
  have hargt : Complex.arg (starRingEnd ℂ z * w ⟨(t : ℝ), le_rfl, htu⟩) = 0 := by
    rw [hwt, mul_comm, Complex.mul_conj]
    exact Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg z)
  rw [hargt] at hincr
  have hre' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).re =
      (x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1 := by
    rw [hre ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have him' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).im =
      (x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0 := by
    rw [him ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have hargu : Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩) =
      Real.arctan
        (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
          ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
    rw [← hre', ← him']
    have hlt : |Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hposC _))
    refine (Real.arctan_eq_of_tan_eq (Complex.tan_arg _) ?_).symm
    exact ⟨neg_lt_of_abs_lt hlt, lt_of_abs_lt hlt⟩
  rw [hargu] at hincr
  linarith [hincr]

/-- Winding is constant on an open neighbourhood of any point off the range of a closed
continuous loop, and that neighbourhood avoids the range. -/
theorem curveWinding_locally_constant_on_compl_range
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      q ∉ Set.range x ∧ curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨U, hU, hpU, heq⟩ := curveWinding_locally_constant_off_range hab hx hclosed hp
  have hclosedRange : IsClosed (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isClosed
  exact ⟨U ∩ (Set.range x)ᶜ, hU.inter hclosedRange.isOpen_compl, ⟨hpU, hp⟩,
    fun q hq ↦ ⟨hq.2, heq q hq.1⟩⟩

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
# Curve / Jordan / Winding Lifts
-/

@[expose] public section

noncomputable section

open scoped unitInterval

namespace MovingSofa

private lemma pointComplex_re_m8588f5d (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma pointComplex_im_m8588f5d (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re_m8588f5d (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

/-- Every continuous interval path avoiding a point admits a continuous angle lift. -/
theorem exists_curveAngleLift_of_avoids {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) : ∃ α, IsCurveAngleLift x p α := by
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let φ : I → Set.Icc a b := Set.Icc.convexComb A B
  let z : I → ℂ := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x (φ u) - p)
  have hz : Continuous z :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp ((hx.comp (Set.Icc.continuous_convexComb
        A B)).sub
      continuous_const)
  have hzne (u : I) : z u ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨φ u, heq⟩
  let ϑ : I → Real.Angle := fun u ↦ (Complex.arg (z u) : Real.Angle)
  have hϑ : Continuous ϑ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuousAt_arg_coe_angle (hzne u)).comp hz.continuousAt
  let ϑ₀ := ϑ 0
  obtain ⟨β, hβ, hβ0, hβϑ⟩ := Real.Angle.exists_continuous_lift_zero
    (fun u ↦ ϑ u - ϑ₀) (hϑ.sub continuous_const) (by simp [ϑ₀])
  let ψ : Set.Icc a b → I := fun u ↦
    ⟨((u : ℝ) - a) / (b - a), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr u.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (by linarith [u.property.2])⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hφψ (u : Set.Icc a b) : φ (ψ u) = u := by
    apply Subtype.ext
    simp [φ, ψ, A, B]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  let c := Complex.arg (z 0)
  refine ⟨fun u ↦ β (ψ u) + c, hβ.comp hψ |>.add continuous_const, fun u ↦ ?_⟩
  have hangle : ((β (ψ u) + c : ℝ) : Real.Angle) = Complex.arg
      (Complex.orthonormalBasisOneI.repr.symm (x u - p)) := by
    rw [Real.Angle.coe_add, hβϑ]
    simp only [ϑ₀, c, ϑ]
    change (Complex.arg (Complex.orthonormalBasisOneI.repr.symm (x (φ (ψ u)) - p)) : Real.Angle) -
        (Complex.arg (z 0) : Real.Angle) + (Complex.arg (z 0) : Real.Angle) = _
    rw [hφψ]
    simp
  have hne : Complex.orthonormalBasisOneI.repr.symm (x u - p) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨u, heq⟩
  constructor
  · have := congrArg Real.Angle.cos hangle
    rw [Real.Angle.cos_coe, Real.Angle.cos_coe, Complex.cos_arg hne] at this
    simpa only [pointComplex_re_m8588f5d, Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      this
  · have := congrArg Real.Angle.sin hangle
    rw [Real.Angle.sin_coe, Real.Angle.sin_coe, Complex.sin_arg] at this
    simpa only [pointComplex_im_m8588f5d, Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      this

/-- A closed path contained in a strict half-plane about a point has winding zero there. -/
theorem curveWinding_eq_zero_of_inner_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (p v : Point) (hv : v ≠ 0) (hpos : ∀ u, 0 < inner ℝ v (x u - p)) :
    curveWinding hab x p = 0 := by
  let z := Complex.orthonormalBasisOneI.repr.symm v
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  have hz : z ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff]
    exact hv
  have hpositive (u : Set.Icc a b) : 0 < (starRingEnd ℂ z * w u).re := by
    rw [conj_pointComplex_mul_re_m8588f5d]
    exact hpos u
  have harg : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ z * w u)) :=
    continuous_arg_conj_mul_of_re_pos continuous_const
      (Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub continuous_const)) hpositive
  let α := fun u ↦ Complex.arg z + Complex.arg (starRingEnd ℂ z * w u)
  have hα : IsCurveAngleLift x p α := by
    refine ⟨continuous_const.add harg, fun u ↦ ?_⟩
    have hw : w u ≠ 0 := by
      intro heq
      simpa [heq] using hpositive u
    simpa only [α, w, pointComplex_re_m8588f5d, pointComplex_im_m8588f5d,
        Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      normalized_complex_rotation_by_arg hz hw
  rw [hα.curveWinding_eq hab]
  have hend : α ⟨b, hab, le_rfl⟩ = α ⟨a, le_rfl, hab⟩ := by
    simp only [α, w, hclosed]
  rw [hend, sub_self, zero_div]

/-- A closed continuous loop has winding zero at every point of an unbounded connected
component of the complement of its range. -/
theorem curveWinding_eq_zero_of_unbounded_component
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x)
    (hunbounded : ¬Bornology.IsBounded (connectedComponentIn (Set.range x)ᶜ p)) :
    curveWinding hab x p = 0 := by
  let V := connectedComponentIn (Set.range x)ᶜ p
  let _ : PreconnectedSpace V :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hlc : IsLocallyConstant (fun z : V ↦ curveWinding hab x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := connectedComponentIn_subset _ _ z.property
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  have hrangeBounded : Bornology.IsBounded (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hrangeBounded
  have hRnonneg : 0 ≤ R := by
    have h := hR (Set.mem_range_self ⟨a, le_rfl, hab⟩)
    have hnorm : ‖x ⟨a, le_rfl, hab⟩‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    exact (norm_nonneg _).trans hnorm
  have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
    by_contra hn
    push Not at hn
    apply hunbounded
    refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
    intro v hv
    simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
  obtain ⟨v, hvV, hvnorm⟩ := hvfar
  have hvzero : curveWinding hab x v = 0 := by
    apply curveWinding_eq_zero_of_inner_pos hab hx hclosed v (-v)
    · exact neg_ne_zero.mpr (by
        intro hv0
        rw [hv0, norm_zero] at hvnorm
        linarith)
    · intro u
      rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [← real_inner_comm v (x u)]
      have hxu := hR (Set.mem_range_self u)
      have hxnorm : ‖x u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hxu
      have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
      have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
      have hinner := abs_real_inner_le_norm (x u) v
      have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
      have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
          (mul_lt_mul_of_pos_right hvlarge hvpos)
      rw [pow_two]
      linarith
  exact (hlc.apply_eq_of_preconnectedSpace ⟨p, mem_connectedComponentIn hp⟩ ⟨v, hvV⟩).trans
    hvzero

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
# The range of an almost injective continuous BV path is null

A continuous planar BV path that is injective on `[a, b)` sweeps a Lebesgue null set: each
compact initial subarc has finite Hausdorff length, hence vanishing Hausdorff `2`-measure,
and a rational exhaustion together with the terminal point covers the whole range.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- The range of a continuous planar BV path injective on `[a, b)` is Lebesgue null. -/
theorem ContinuousBVPaths.volume_range_eq_zero_of_injOn
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) : volume (Set.range x.val) = 0 := by
  let γ : ℝ → Point := x.val ∘ Set.projIcc a b hab
  have hγcont : Continuous γ := x.property.1.comp continuous_projIcc
  have hγBV (q : ℝ) : BoundedVariationOn γ (Icc a q) := by
    apply ne_top_of_le_ne_top x.boundedVariationOn
    exact eVariationOn.comp_le_of_monotoneOn x.val (Set.projIcc a b hab)
      ((Set.monotone_projIcc hab).monotoneOn _) (fun _ _ ↦ mem_univ _)
  have hnull (q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}) :
      volume (γ '' Icc a (q : ℝ)) = 0 := by
    apply volume_image_Icc_eq_zero_of_boundedVariationOn γ q.property.1 hγcont.continuousOn
      _ (hγBV _)
    intro u hu v hv huv
    have huab : u ∈ Icc a b := ⟨hu.1, hu.2.trans q.property.2.le⟩
    have hvab : v ∈ Icc a b := ⟨hv.1, hv.2.trans q.property.2.le⟩
    have heq := hinj (show (Set.projIcc a b hab u : ℝ) < b by
        rw [Set.projIcc_of_mem hab huab]; exact hu.2.trans_lt q.property.2)
      (show (Set.projIcc a b hab v : ℝ) < b by
        rw [Set.projIcc_of_mem hab hvab]; exact hv.2.trans_lt q.property.2) huv
    have hval := congrArg Subtype.val heq
    simpa only [Set.projIcc_of_mem hab huab, Set.projIcc_of_mem hab hvab] using hval
  apply measure_mono_null (t := {x.val ⟨b, hab, le_rfl⟩} ∪
    ⋃ q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}, γ '' Icc a (q : ℝ))
  · rintro y ⟨t, rfl⟩
    by_cases ht : (t : ℝ) = b
    · exact Or.inl (congrArg x.val (show t = ⟨b, hab, le_rfl⟩ from Subtype.ext ht))
    · have htb : (t : ℝ) < b := lt_of_le_of_ne t.property.2 ht
      obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
      apply Or.inr
      apply mem_iUnion.2
      refine ⟨⟨q, t.property.1.trans htq.le, hqb⟩, (t : ℝ), ⟨t.property.1, htq.le⟩, ?_⟩
      dsimp [γ]
      rw [Set.projIcc_of_mem hab t.property]
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null hnull)

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
# Curve / Segment Area
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Half the oriented determinant of the two endpoints. -/
def segmentArea (p q : Point) : ℝ := planeCrossProduct p q / 2

/-- The signed segment area is antisymmetric in its two endpoints. -/
theorem segmentArea_swap (p q : Point) : segmentArea p q = -segmentArea q p := by
  rw [segmentArea, segmentArea, planeCrossProduct_swap p q]
  ring

/-- Translating both endpoints of a segment shifts its signed area by a boundary term. -/
theorem segmentArea_add_right (p q v : Point) :
    segmentArea (p + v) (q + v) =
      segmentArea p q + (v 0 * (q 1 - p 1) - v 1 * (q 0 - p 0)) / 2 := by
  have hadd : ∀ (x y : Point) (i : Fin 2), (x + y) i = x i + y i := fun _ _ _ ↦ by simp
  simp only [segmentArea, planeCrossProduct, hadd]
  ring

/-- The signed area of the segment joining two convex combinations of endpoints is the same
combination of the two signed areas, provided the two endpoints of each pair have a common height:
the mixed terms then cancel. -/
theorem segmentArea_combination_of_apply_one_eq (c : ℝ) {p₁ p₂ q₁ q₂ : Point}
    (hp : p₁ 1 = p₂ 1) (hq : q₁ 1 = q₂ 1) :
    segmentArea ((1 - c) • p₁ + c • p₂) ((1 - c) • q₁ + c • q₂) =
      (1 - c) * segmentArea p₁ q₁ + c * segmentArea p₂ q₂ := by
  simp only [segmentArea, planeCrossProduct, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp, hq]
  ring

/-- Two points on a normal line through the origin span no signed area. -/
theorem segmentArea_eq_zero_of_inner_normalVector_eq_zero {p q : Point} {t : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = 0)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = 0) : segmentArea p q = 0 := by
  rw [segmentArea, planeCrossProduct_eq_inner_frame p q t, hp, hq]
  ring

/-- Collinear additivity of the signed segment area on a common normal line. -/
theorem segmentArea_sub_segmentArea_of_inner_normalVector_eq {p q s : Point} {t c : ℝ}
    (hp : inner ℝ p (normalVector (t : Real.Angle)) = c)
    (hq : inner ℝ q (normalVector (t : Real.Angle)) = c)
    (hs : inner ℝ s (normalVector (t : Real.Angle)) = c) :
    segmentArea p s - segmentArea q s = segmentArea p q := by
  rw [segmentArea, segmentArea, segmentArea, planeCrossProduct_eq_inner_frame p s t,
    planeCrossProduct_eq_inner_frame q s t, planeCrossProduct_eq_inner_frame p q t,
    hp, hq, hs]
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
# Curve / Segment Area / Parametrization
-/

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- The affine segment from `p` to `q`, bundled as a continuous BV path. -/
def lineSegmentBVPath (p q : Point) : ContinuousBVPaths 0 1 where
  val := Path.segment p q
  property := by
    constructor
    · exact (Path.segment p q).continuous
    · intro i
      let C : NNReal := ⟨|q i - p i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦ p i + r * (q i - p i)) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        change |(p i + x * (q i - p i)) - (p i + y * (q i - p i))| ≤
          |q i - p i| * |x - y|
        rw [show (p i + x * (q i - p i)) - (p i + y * (q i - p i)) =
          (x - y) * (q i - p i) by ring, abs_mul, mul_comm]
      have hid : BoundedVariationOn ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) Set.univ := by
        apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
          Set.univ).boundedVariationOn (C := 1)
        intro t _
        rw [abs_of_nonneg t.property.1]
        exact t.property.2
      have hbv := hLip.comp_boundedVariationOn hid
      rw [show (fun t ↦ (Path.segment p q t) i) =
          (fun r : ℝ ↦ p i + r * (q i - p i)) ∘ ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) by
        funext t
        simp only [Path.segment_apply, AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply,
          PiLp.sub_apply, smul_eq_mul, Function.comp_apply]
        change (t : ℝ) * (q i - p i) + p i =
          p i + (t : ℝ) * (q i - p i)
        ring]
      exact hbv

/-- The affine parametrization of an oriented segment, evaluated. -/
theorem lineSegmentBVPath_apply (p q : Point) (s : Set.Icc (0 : ℝ) 1) :
    (lineSegmentBVPath p q).val s = (1 - (s : ℝ)) • p + (s : ℝ) • q := by
  change Path.segment p q s = _
  simp [Path.segment_apply, AffineMap.lineMap_apply_module']
  module

theorem curveAreaFunctional_lineSegmentBVPath (p q : Point) :
    curveAreaFunctional (lineSegmentBVPath p q) = segmentArea p q := by
  have hcoord (i : Fin 2) (t : Set.Icc (0 : ℝ) 1) :
      (continuousBVCoordinate (lineSegmentBVPath p q) i).toFun t =
        p i + (q i - p i) * (t : ℝ) := by
    change (Path.segment p q t) i = _
    simp [Path.segment_apply, AffineMap.lineMap_apply_module']
    ring
  unfold curveAreaFunctional segmentArea
  change
    (intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 1)
        (continuousBVCoordinate (lineSegmentBVPath p q) 0).toFun Set.univ -
      intervalStieltjesIntegral
        (continuousBVCoordinate (lineSegmentBVPath p q) 0)
        (continuousBVCoordinate (lineSegmentBVPath p q) 1).toFun Set.univ) / 2 =
      planeCrossProduct p q / 2
  rw [intervalStieltjesIntegral_affine_cross
    (continuousBVCoordinate (lineSegmentBVPath p q) 0)
    (continuousBVCoordinate (lineSegmentBVPath p q) 1)
    (p 0) (q 0 - p 0) (p 1) (q 1 - p 1) (hcoord 0) (hcoord 1)]
  simp only [planeCrossProduct]
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
# Curve / Smooth Interval Paths
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A continuously differentiable planar path on a compact interval has continuous
bounded-variation coordinates. -/
def continuousBVOfContDiffOn {a b : ℝ} (f : ℝ → Point)
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) : ContinuousBVPaths a b := by
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf.continuousOn, ?_⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath := hC.comp_boundedVariationOn (fun t _ ↦ t.property) hid
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A Lipschitz planar path on a compact interval has continuous bounded-variation coordinates. -/
def continuousBVOfLipschitz {a b : ℝ} (f : Set.Icc a b → Point)
    {C : NNReal} (hf : LipschitzWith C f) : ContinuousBVPaths a b := by
  refine ⟨f, hf.continuous, ?_⟩
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath : BoundedVariationOn f Set.univ := by
    exact hf.comp_boundedVariationOn
      (show BoundedVariationOn (id : Set.Icc a b → Set.Icc a b) Set.univ from hid)
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A coordinate of an interval path has bounded variation on a closed subinterval on which the
path agrees with a continuously differentiable function. -/
theorem boundedVariationOn_coord_Icc_of_contDiffOn {a b : ℝ} (g : Set.Icc a b → Point)
    {l r : ℝ} (hl : a ≤ l) (hlr : l ≤ r) (hr : r ≤ b) {F : ℝ → Point}
    (hF : ContDiffOn ℝ 1 F (Set.Icc l r))
    (hgF : ∀ t : Set.Icc l r, g ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩ = F t.val)
    (i : Fin 2) :
    BoundedVariationOn (fun t : Set.Icc a b ↦ g t i)
      (Set.Icc ⟨l, hl, hlr.trans hr⟩ ⟨r, hl.trans hlr, hr⟩) := by
  set ι : Set.Icc l r → Set.Icc a b := fun t ↦ ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩
  have hmono : MonotoneOn ι Set.univ := fun _ _ _ _ h ↦ h
  have himg : ι '' Set.univ =
      Set.Icc (⟨l, hl, hlr.trans hr⟩ : Set.Icc a b) ⟨r, hl.trans hlr, hr⟩ := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨t.2.1, t.2.2⟩
    · intro hx
      exact ⟨⟨x.val, hx.1, hx.2⟩, Set.mem_univ _, Subtype.ext rfl⟩
  change eVariationOn _ _ ≠ ⊤
  rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ ι hmono]
  have hfun : ((fun t : Set.Icc a b ↦ g t i) ∘ ι) = fun t : Set.Icc l r ↦ F t.val i := by
    funext t
    exact congrArg (fun p : Point ↦ p i) (hgF t)
  rw [hfun]
  exact (continuousBVOfContDiffOn F hF).property.2 i

/-- Gluing two continuously differentiable pieces along a shared endpoint gives a continuous
path of bounded variation. -/
def continuousBVOfContDiffOnIccUnionIcc {a b c : ℝ} (f : ℝ → Point) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : ContDiffOn ℝ 1 f (Set.Icc a b)) (h₂ : ContDiffOn ℝ 1 f (Set.Icc b c)) :
    ContinuousBVPaths a c := by
  have hf : ContinuousOn f (Set.Icc a c) := by
    rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
    exact h₁.continuousOn.union_of_isClosed h₂.continuousOn isClosed_Icc isClosed_Icc
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf, fun i ↦ ?_⟩
  refine BoundedVariationOn.univ_of_Icc_endpoints (hab.trans hbc)
    (BoundedVariationOn.Icc_union_Icc
      (show (⟨a, le_rfl, hab.trans hbc⟩ : Set.Icc a c) ≤ ⟨b, hab, hbc⟩ from hab)
      (show (⟨b, hab, hbc⟩ : Set.Icc a c) ≤ ⟨c, hab.trans hbc, le_rfl⟩ from hbc)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ le_rfl hab hbc h₁ (fun _ ↦ rfl) i)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ hab hbc le_rfl h₂ (fun _ ↦ rfl) i))

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
# Curve / Jordan / Radial Loop
-/

@[expose] public section

noncomputable section
namespace MovingSofa

/-- A Lipschitz map on the unit circle induces a continuous BV loop in increasing angular order. -/
def radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : ContinuousBVPaths 0 (2 * Real.pi) := by
  let n : Set.Icc (0 : ℝ) (2 * Real.pi) → {u : Point | ‖u‖ = 1} :=
    fun t ↦ ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩
  have hn : LipschitzWith 1 n := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    exact lipschitzWith_normalVector_real.dist_le_mul t.val u.val
  exact continuousBVOfLipschitz (f ∘ n) (hf.comp hn)

/-- The radial BV loop evaluates by applying the circle map to the angular normal. -/
lemma radialBVLoop_apply (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (t : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (radialBVLoop f hf).val t =
      f ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩ := rfl

/-- The radial BV loop has equal endpoints. -/
lemma radialBVLoop_closed (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) :
    (radialBVLoop f hf).val ⟨0, le_rfl, by positivity⟩ =
      (radialBVLoop f hf).val ⟨2 * Real.pi, by positivity, le_rfl⟩ := by
  rw [radialBVLoop_apply, radialBVLoop_apply]
  apply congrArg f
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [normalVector, frame]

/-- An injective circle map gives a radial loop injective before its final endpoint. -/
lemma radialBVLoop_injOn (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (hinj : Function.Injective f) :
    Set.InjOn (radialBVLoop f hf).val {t | (t : ℝ) < 2 * Real.pi} := by
  intro t ht u hu h
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [radialBVLoop_apply, radialBVLoop_apply] at h
  have hn := congrArg Subtype.val (hinj h)
  have ha : (t.val : Real.Angle) = (u.val : Real.Angle) := by
    apply Real.Angle.cos_sin_inj
    · exact congrFun (congrArg WithLp.ofLp hn) 0
    · exact congrFun (congrArg WithLp.ofLp hn) 1
  apply Subtype.ext
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show t.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨t.property.1, by simpa using ht⟩)
    (show u.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨u.property.1, by simpa using hu⟩)).mp ha

/-- The radial BV loop has the same range as the underlying unit-circle map. -/
lemma range_radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : Set.range (radialBVLoop f hf).val = Set.range f := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact ⟨_, (radialBVLoop_apply f hf t).symm⟩
  · rintro p ⟨u, rfl⟩
    obtain ⟨θ, hθ⟩ := exists_angle_normalVector_eq u.property
    let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let t := AddCircle.equivIco (2 * Real.pi) 0 θ
    have ht : (t.val : Real.Angle) = θ := AddCircle.coe_equivIco
    refine ⟨⟨t.val, t.property.1, ?_⟩, ?_⟩
    · simpa using t.property.2.le
    · rw [radialBVLoop_apply]
      apply congrArg f
      apply Subtype.ext
      exact (congrArg normalVector ht).trans hθ

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
# A Stieltjes chain rule with a local quadratic remainder

The hypothesis of `ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder`
quantifies the remainder only over parameter pairs closer than a fixed positive threshold.
This is what a locally defined argument branch supplies: no single plane function has to be
named, and no constant is needed across a branch cut.
-/

@[expose] public section

noncomputable section

open Set

namespace MovingSofa

/-- If a real parameter function `A` has increments matching the signed pair
`D₁ dγ₁ - D₀ dγ₀` up to a quadratic remainder on all parameter pairs closer than a fixed
positive threshold, then its endpoint increment is the corresponding difference of
coordinate Stieltjes integrals. -/
theorem ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hBV : BoundedVariationOn x.val univ) (A : Set.Icc a b → ℝ) (D : Point → Fin 2 → ℝ)
    (hD : ∀ i, Continuous (fun t ↦ D (x.val t) i)) {C : ℝ} (hC : 0 ≤ C)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (herror : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
      |A u - A t -
        (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤ C * ‖x.val u - x.val t‖ ^ 2) :
    A ⟨b, hab, le_rfl⟩ - A ⟨a, le_rfl, hab⟩ =
      intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ D (x.val t) 1) univ -
      intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ D (x.val t) 0) univ := by
  obtain ⟨cuts, hcuts, hzero, hlast, hmesh⟩ :=
    Set.Icc.exists_partitions_mesh_tendsto_zero hab
  let N : ℕ → ℕ := fun k ↦ k + 1
  have htaylor := hBV.tendsto_sum_of_local_quadratic_remainder hab x.property.1 A
    (fun t v ↦ D (x.val t) 1 * v 1 - D (x.val t) 0 * v 0) hC hδ₀ herror
    N cuts hcuts hzero hlast hmesh
  have hcoord (i : Fin 2) := tendsto_stieltjesSum_of_mesh_tendsto_zero
    (continuousBVCoordinate x i) ((PiLp.continuous_apply 2 _ i).comp x.property.1)
    (hD i) N cuts hcuts hzero hlast hmesh
  have hsum := (hcoord 1).sub (hcoord 0)
  simp only [← Finset.sum_sub_distrib, continuousBVCoordinate] at hsum
  exact tendsto_nhds_unique htaylor hsum

end MovingSofa

end

end

end
