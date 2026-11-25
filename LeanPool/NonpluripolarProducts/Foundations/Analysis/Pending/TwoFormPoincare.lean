/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentials
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
public import Mathlib.Analysis.Normed.Module.Alternating.Curry

/-!
# A radial Poincaré homotopy for smooth two-forms

This file sets up the real two-form part of the local `ddᶜ` construction.  It
defines contraction with the radial vector field followed by integration along
radial segments and proves both the parameter-integral differentiation theorem
and differentiation of the radial primitive itself.  It also proves the exact
spatial Fréchet-derivative formula, its closed-form alternatization, and the
global smooth closed-form identity `dS = a` by pointwise scalar integration and
the one-variable fundamental theorem of calculus.  The eventual local wrapper
must assume smoothness and closedness only on the chosen star-shaped neighborhood.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff Interval

namespace SGPT.Foundations.Analysis.Pending.LocalPotentials

noncomputable section

/-- Differentiation under a finite interval integral when the integrand and its
parameter derivative are jointly continuous.  Compactness of a closed unit
ball and of the integration interval supplies the domination bound. -/
theorem hasFDerivAt_intervalIntegral_of_jointly_continuous
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : H → ℝ → F} {G' : H → ℝ → H →L[ℝ] F}
    (hG : Continuous G.uncurry) (hG' : Continuous G'.uncurry)
    (hderiv : ∀ x t, HasFDerivAt (fun y ↦ G y t) (G' x t) x)
    (x : H) (a b : ℝ) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, G y t)
      (∫ t in a..b, G' x t) x := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall x 1).prod
      (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn
        hG'.continuousOn
  have hGc (y : H) : Continuous (G y) :=
    hG.comp (continuous_const.prodMk continuous_id)
  have hG'c (y : H) : Continuous (G' y) :=
    hG'.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := G') (bound := fun _ ↦ C) (s := ball x 1)
    (ball_mem_nhds x (by norm_num))
    (Filter.Eventually.of_forall fun y ↦ (hGc y).aestronglyMeasurable)
    ((hGc x).intervalIntegrable _ _)
    (hG'c x).aestronglyMeasurable
    (by
      filter_upwards with t ht y hy
      exact hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ ↦ hderiv y t)

/-- Local form of differentiation under a finite interval integral.  Joint
continuity and the derivative identity are required only on a neighborhood of
the parameter point and on the compact integration interval. -/
theorem hasFDerivAt_intervalIntegral_of_jointly_continuousOn
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : H → ℝ → F} {G' : H → ℝ → H →L[ℝ] F}
    {s : Set H} {x : H} {a b : ℝ} (hs : s ∈ 𝓝 x)
    (hG : ContinuousOn G.uncurry (s ×ˢ uIcc a b))
    (hG' : ContinuousOn G'.uncurry (s ×ˢ uIcc a b))
    (hderiv : ∀ y ∈ s, ∀ t ∈ uIcc a b,
      HasFDerivAt (fun q ↦ G q t) (G' y t) y) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, G y t)
      (∫ t in a..b, G' x t) x := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hs
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδs : closedBall x δ ⊆ s :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεs
  have hK : IsCompact (closedBall x δ ×ˢ uIcc a b) :=
    (isCompact_closedBall x δ).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG'.mono <|
    prod_mono hδs Subset.rfl)
  have hGc (y : H) (hy : y ∈ s) : ContinuousOn (G y) (uIcc a b) :=
    hG.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hy, ht⟩
  have hG'c (y : H) (hy : y ∈ s) : ContinuousOn (G' y) (uIcc a b) :=
    hG'.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hy, ht⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := G') (bound := fun _ ↦ C) (s := ball x δ)
    (ball_mem_nhds x hδ) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds x hδ] with y hy
    exact (hGc y (hδs (ball_subset_closedBall hy))).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc
  · exact (hGc x (hδs (mem_closedBall_self hδ.le))).intervalIntegrable
  · exact (hG'c x (hδs (mem_closedBall_self hδ.le))).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc
  · filter_upwards with t ht y hy
    exact hC (y, t) ⟨ball_subset_closedBall hy, uIoc_subset_uIcc ht⟩
  · filter_upwards with t ht y hy
    exact hderiv y (hδs (ball_subset_closedBall hy)) t (uIoc_subset_uIcc ht)

/-- The integrand in the radial homotopy operator on two-forms. -/
def radialTwoFormIntegrand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (t : ℝ) :
    E → E [⋀^Fin 1]→L[ℝ] ℝ :=
  fun x ↦ t • (a (z + t • (x - z))).curryLeft (x - z)

/-- The radial homotopy operator on two-forms, based at `z`.

At `x`, its value is the one-form
`v ↦ ∫ t in 0..1, t * a (z + t • (x - z)) (x - z, v)`. -/
def radialTwoFormPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) : E → E [⋀^Fin 1]→L[ℝ] ℝ :=
  fun x ↦ ∫ t in (0 : ℝ)..1,
    radialTwoFormIntegrand a z t x

/-- Contraction of a two-form in its first slot is a bounded bilinear
operation. -/
theorem isBoundedBilinearMap_twoForm_curryLeft
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsBoundedBilinearMap ℝ (fun p :
      (E [⋀^Fin 2]→L[ℝ] ℝ) × E ↦ p.1.curryLeft p.2) where
  add_left f g x := by simp
  smul_left c f x := by simp
  add_right f x y := by simp
  smul_right c f x := by simp
  bound := by
    refine ⟨1, zero_lt_one, fun f x ↦ ?_⟩
    simpa using (f.curryLeft).le_opNorm x

/-- A globally smooth two-form has a jointly smooth radial homotopy integrand. -/
theorem contDiff_radialTwoFormIntegrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (Function.uncurry fun x t ↦ radialTwoFormIntegrand a z t x) := by
  have hp : ContDiff ℝ ∞ (fun p : E × ℝ ↦ z + p.2 • (p.1 - z)) := by
    fun_prop
  have hac : ContDiff ℝ ∞ (fun p : E × ℝ ↦ a (z + p.2 • (p.1 - z))) :=
    ha.comp hp
  have hr : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.1 - z) := by
    fun_prop
  have hB : IsBoundedBilinearMap ℝ (fun q :
      (E [⋀^Fin 2]→L[ℝ] ℝ) × E ↦ q.1.curryLeft q.2) :=
    isBoundedBilinearMap_twoForm_curryLeft
  have happ : ContDiff ℝ ∞ (fun p : E × ℝ ↦
      (a (z + p.2 • (p.1 - z))).curryLeft (p.1 - z)) :=
    hB.contDiff.comp (hac.prodMk hr)
  change ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.2 •
    (a (z + p.2 • (p.1 - z))).curryLeft (p.1 - z))
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : E × ℝ ↦ p.2)).smul happ

/-- The Fréchet derivative in the spatial variable of the radial homotopy
integrand.  Bundling this formula separately makes the later
alternatization and parameter integration transparent. -/
noncomputable def radialTwoFormIntegrandFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (t : ℝ) (x : E) :
    E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
  t • (isBoundedBilinearMap_twoForm_curryLeft.deriv
      (a (z + t • (x - z)), x - z)).comp
    (((fderiv ℝ a (z + t • (x - z))).comp
      (t • ContinuousLinearMap.id ℝ E)).prod (ContinuousLinearMap.id ℝ E))

@[simp]
theorem radialTwoFormIntegrandFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (t : ℝ) (x h : E) :
    radialTwoFormIntegrandFDeriv a z t x h =
      t • ((a (z + t • (x - z))).curryLeft h +
        (fderiv ℝ a (z + t • (x - z)) (t • h)).curryLeft (x - z)) := by
  simp [radialTwoFormIntegrandFDeriv,
    IsBoundedBilinearMap.deriv_apply]

/-- Spatial differentiation of the radial integrand. -/
theorem hasFDerivAt_radialTwoFormIntegrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (t : ℝ) (x : E)
    (ha : DifferentiableAt ℝ a (z + t • (x - z))) :
    HasFDerivAt (radialTwoFormIntegrand a z t)
      (radialTwoFormIntegrandFDeriv a z t x) x := by
  have hp : HasFDerivAt (fun y : E ↦ z + t • (y - z))
      (t • ContinuousLinearMap.id ℝ E) x := by
    fun_prop
  have ha' : HasFDerivAt (fun y : E ↦ a (z + t • (y - z)))
      ((fderiv ℝ a (z + t • (x - z))).comp
        (t • ContinuousLinearMap.id ℝ E)) x :=
    ha.hasFDerivAt.comp x hp
  have hr : HasFDerivAt (fun y : E ↦ y - z)
      (ContinuousLinearMap.id ℝ E) x := by
    fun_prop
  have hpair := ha'.prodMk hr
  have happ := (isBoundedBilinearMap_twoForm_curryLeft.hasFDerivAt
      (a (z + t • (x - z)), x - z)).comp x hpair
  change HasFDerivAt (fun y : E ↦
      t • (a (z + t • (y - z))).curryLeft (y - z)) _ x
  exact happ.const_smul t

private theorem continuous_radialTwoFormIntegrandFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (ha : ContDiff ℝ ∞ a) :
    Continuous (Function.uncurry fun y t ↦ radialTwoFormIntegrandFDeriv a z t y) := by
  have hswap : ContDiff ℝ ∞ (fun p : (ℝ × E) × E ↦ (p.2, p.1.1)) := by
    fun_prop
  have hfull : ContDiff ℝ ∞ (fun p : (ℝ × E) × E ↦
      radialTwoFormIntegrand a z p.1.1 p.2) :=
    (contDiff_radialTwoFormIntegrand a z ha).comp hswap
  have hpartial : ContDiff ℝ ∞ (fun p : ℝ × E ↦
      fderiv ℝ (radialTwoFormIntegrand a z p.1) p.2) :=
    hfull.fderiv (by fun_prop) (by simp)
  have hswap2 : Continuous (fun p : E × ℝ ↦ (p.2, p.1)) := by
    fun_prop
  have hc : Continuous (Function.uncurry fun y t ↦
      fderiv ℝ (radialTwoFormIntegrand a z t) y) :=
    hpartial.continuous.comp hswap2
  convert hc using 1
  funext p
  exact (hasFDerivAt_radialTwoFormIntegrand a z p.2 p.1
    ((ha.differentiable (by simp)).differentiableAt)).fderiv.symm

/-- A globally smooth two-form may be differentiated through the radial
homotopy integral. -/
theorem hasFDerivAt_radialTwoFormPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z x : E)
    (ha : ContDiff ℝ ∞ a) :
    HasFDerivAt (radialTwoFormPrimitive a z)
      (∫ t in (0 : ℝ)..1, radialTwoFormIntegrandFDeriv a z t x) x := by
  change HasFDerivAt
    (fun y ↦ ∫ t in (0 : ℝ)..1, radialTwoFormIntegrand a z t y)
    (∫ t in (0 : ℝ)..1, radialTwoFormIntegrandFDeriv a z t x) x
  exact hasFDerivAt_intervalIntegral_of_jointly_continuous
    (H := E) (F := E [⋀^Fin 1]→L[ℝ] ℝ)
    (G := fun y t ↦ radialTwoFormIntegrand a z t y)
    (G' := fun y t ↦ radialTwoFormIntegrandFDeriv a z t y)
    (contDiff_radialTwoFormIntegrand a z ha).continuous
    (continuous_radialTwoFormIntegrandFDeriv a z ha)
    (fun y t ↦ hasFDerivAt_radialTwoFormIntegrand a z t y
      ((ha.differentiable (by simp)).differentiableAt)) x 0 1

/-- Pointwise evaluation of the derivative of the radial primitive commutes
with its parameter integral.  Evaluating the one-form output before applying
the parameter-integral theorem avoids requiring an integration instance on a
nested continuous-linear-map space. -/
theorem radialTwoFormPrimitive_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z x h : E) (w : Fin 1 → E)
    (ha : ContDiff ℝ ∞ a) :
    fderiv ℝ (radialTwoFormPrimitive a z) x h w =
      ∫ t in (0 : ℝ)..1, radialTwoFormIntegrandFDeriv a z t x h w := by
  let ev : (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ (E [⋀^Fin 1]→L[ℝ] ℝ)).flipAlternating w
  let K : E → ℝ → E →L[ℝ] ℝ := fun y t ↦
    ev.comp (radialTwoFormIntegrandFDeriv a z t y)
  have hIjoint : Continuous (Function.uncurry fun y t ↦
      radialTwoFormIntegrand a z t y) :=
    (contDiff_radialTwoFormIntegrand a z ha).continuous
  have hDjoint := continuous_radialTwoFormIntegrandFDeriv a z ha
  have hKjoint : Continuous K.uncurry := by
    exact ((ContinuousLinearMap.compL ℝ E (E [⋀^Fin 1]→L[ℝ] ℝ) ℝ) ev).continuous.comp
      hDjoint
  have hscalar := hasFDerivAt_intervalIntegral_of_jointly_continuous
    (H := E) (F := ℝ)
    (G := fun y t ↦ ev (radialTwoFormIntegrand a z t y))
    (G' := K)
    (ev.continuous.comp hIjoint)
    hKjoint
    (fun y t ↦ ev.hasFDerivAt.comp y
      (hasFDerivAt_radialTwoFormIntegrand a z t y
        ((ha.differentiable (by simp)).differentiableAt))) x 0 1
  have hfun (y : E) :
      ev (radialTwoFormPrimitive a z y) =
        ∫ t in (0 : ℝ)..1, ev (radialTwoFormIntegrand a z t y) := by
    have hIy : Continuous (fun t ↦ radialTwoFormIntegrand a z t y) :=
      hIjoint.comp (continuous_const.prodMk continuous_id)
    exact (ev.intervalIntegral_comp_comm (hIy.intervalIntegrable 0 1)).symm
  have hscalar' : HasFDerivAt
      (fun y ↦ ev (radialTwoFormPrimitive a z y))
      (∫ t in (0 : ℝ)..1, K x t) x :=
    hscalar.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ hfun y)
  have hS := hasFDerivAt_radialTwoFormPrimitive a z x ha
  have hcomp := ev.hasFDerivAt.comp x hS
  have heq := hcomp.unique hscalar'
  calc
    fderiv ℝ (radialTwoFormPrimitive a z) x h w =
        (ev.comp (∫ t in (0 : ℝ)..1,
          radialTwoFormIntegrandFDeriv a z t x)) h := by
      rw [hS.fderiv]
      rfl
    _ = (∫ t in (0 : ℝ)..1, K x t) h := by rw [heq]
    _ = ∫ t in (0 : ℝ)..1, K x t h := by
      have hKx : Continuous (K x) :=
        hKjoint.comp (continuous_const.prodMk continuous_id)
      exact ContinuousLinearMap.intervalIntegral_apply
        (hKx.intervalIntegrable 0 1) h
    _ = ∫ t in (0 : ℝ)..1,
        radialTwoFormIntegrandFDeriv a z t x h w := rfl

/-- The linear map obtained by inserting a fixed radial vector in the
two-form-valued output of a derivative. -/
private noncomputable def radialCurryFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) (r : E) :
    E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ :=
  (isBoundedBilinearMap_twoForm_curryLeft.deriv (0, r)).comp
    (D.prod (0 : E →L[ℝ] E))

@[simp]
private theorem radialCurryFDeriv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) (r h : E) :
    radialCurryFDeriv D r h = (D h).curryLeft r := by
  simp [radialCurryFDeriv, IsBoundedBilinearMap.deriv_apply]

/-- The algebraic heart of the radial homotopy formula: if the
alternatization of a two-form-valued derivative vanishes, alternatizing after
insertion of the radial vector recovers evaluation in that vector. -/
private theorem alternatize_radialCurryFDeriv_of_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : E →L[ℝ] E [⋀^Fin 2]→L[ℝ] ℝ) (r : E)
    (hD : ContinuousAlternatingMap.alternatizeUncurryFin D = 0) :
    ContinuousAlternatingMap.alternatizeUncurryFin
      (radialCurryFDeriv D r) = D r := by
  ext v
  have hz := congrArg (fun A : E [⋀^Fin 3]→L[ℝ] ℝ ↦
    A (Matrix.vecCons r v)) hD
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply] at hz ⊢
  have hremoveOne : Fin.removeNth 1 (Matrix.vecCons r v) =
      Matrix.vecCons r (Fin.tail v) := by
    funext i
    fin_cases i <;> rfl
  have hremoveTwo : Fin.removeNth 2 (Matrix.vecCons r v) =
      Matrix.vecCons r (Fin.removeNth 1 v) := by
    funext i
    fin_cases i <;> rfl
  have hz' : (D r) v + (-(D (v 0)) (Matrix.vecCons r (Fin.tail v)) +
      (D (v 1)) (Matrix.vecCons r (Fin.removeNth 1 v))) = 0 := by
    simpa [Fin.sum_univ_succ, hremoveOne, hremoveTwo] using hz
  simp only [Nat.reduceAdd, Int.reduceNeg, radialCurryFDeriv_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    pow_zero, Fin.removeNth_zero, one_mul, Nat.mod_succ, pow_one, neg_mul]
  linarith

/-- Alternatizing the spatial derivative of the radial integrand gives the
derivative, in the radial parameter, of `t ^ 2 • a (z + t • (x - z))`. -/
theorem alternatize_radialTwoFormIntegrandFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z : E) (t : ℝ) (x : E)
    (hclosed : extDeriv a (z + t • (x - z)) = 0) :
    ContinuousAlternatingMap.alternatizeUncurryFin
        (radialTwoFormIntegrandFDeriv a z t x) =
      t ^ 2 • fderiv ℝ a (z + t • (x - z)) (x - z) +
        (2 * t) • a (z + t • (x - z)) := by
  let p := z + t • (x - z)
  let r := x - z
  let D := fderiv ℝ a p
  have hD : ContinuousAlternatingMap.alternatizeUncurryFin D = 0 := by
    simpa only [extDeriv, p, D] using hclosed
  have hformula : radialTwoFormIntegrandFDeriv a z t x =
      t • ((a p).curryLeft + t • radialCurryFDeriv D r) := by
    ext h v
    simp [radialTwoFormIntegrandFDeriv_apply, radialCurryFDeriv_apply,
      p, r, D, smul_add, smul_smul]
  rw [hformula, ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft,
    alternatize_radialCurryFDeriv_of_closed D r hD]
  simp only [Nat.reduceAdd, p, r, D]
  module

/-- The scalar radial parameter derivative integrates to the value of the
two-form at the endpoint.  This is the one-variable fundamental theorem of
calculus applied after evaluation on a fixed pair of vectors. -/
private theorem integral_radialTwoFormParameterDerivative_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z x : E) (v : Fin 2 → E)
    (ha : ContDiff ℝ ∞ a) :
    (∫ t in (0 : ℝ)..1,
      (t ^ 2 • fderiv ℝ a (z + t • (x - z)) (x - z) +
        (2 * t) • a (z + t • (x - z))) v) = a x v := by
  let ev : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ (E [⋀^Fin 2]→L[ℝ] ℝ)).flipAlternating v
  let B : ℝ → ℝ := fun t ↦ t ^ 2 * ev (a (z + t • (x - z)))
  have hderiv (t : ℝ) : deriv B t =
      ev (t ^ 2 • fderiv ℝ a (z + t • (x - z)) (x - z) +
        (2 * t) • a (z + t • (x - z))) := by
    have hp : HasDerivAt (fun s : ℝ ↦ z + s • (x - z)) (x - z) t := by
      convert ((hasDerivAt_id t).smul_const (x - z)).const_add z using 1 <;> simp
    have haAt : HasFDerivAt a (fderiv ℝ a (z + t • (x - z)))
        (z + t • (x - z)) :=
      ((ha.differentiable (by simp)).differentiableAt).hasFDerivAt
    have hq := ((ev.hasFDerivAt.comp _ haAt).comp t hp.hasFDerivAt).hasDerivAt
    have ht2 := (hasDerivAt_id t).pow 2
    have hprod := ht2.mul hq
    have hprodB := hprod.congr_of_eventuallyEq (f₁ := B)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
    rw [hprodB.deriv]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, id_eq,
      Nat.cast_ofNat, mul_one, Pi.pow_apply]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  have hBcont : ContDiff ℝ ∞ B := by
    have hp : ContDiff ℝ ∞ (fun t : ℝ ↦ z + t • (x - z)) := by fun_prop
    have heva : ContDiff ℝ ∞ (fun t : ℝ ↦ ev (a (z + t • (x - z)))) :=
      ev.contDiff.comp (ha.comp hp)
    exact (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ ↦ t ^ 2)).mul heva
  change (∫ t in (0 : ℝ)..1,
      ev (t ^ 2 • fderiv ℝ a (z + t • (x - z)) (x - z) +
        (2 * t) • a (z + t • (x - z)))) = ev (a x)
  rw [← funext hderiv]
  rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc (f := B) (a := 0) (b := 1)
    (hBcont.of_le (by norm_num)).contDiffOn (by norm_num)]
  simp [B, ev]

/-- The exterior derivative of the radial homotopy primitive of a globally
smooth two-form is the original two-form at `x`, provided the form is closed
along the radial segment from `z` to `x`. -/
theorem extDeriv_radialTwoFormPrimitive_of_closed_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z x : E)
    (ha : ContDiff ℝ ∞ a)
    (hclosed : ∀ t ∈ Icc (0 : ℝ) 1, extDeriv a (z + t • (x - z)) = 0) :
    extDeriv (radialTwoFormPrimitive a z) x = a x := by
  rw [extDeriv]
  ext v
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, ← sub_eq_add_neg]
  simp_rw [radialTwoFormPrimitive_fderiv_apply a z x _ _ ha]
  let f : ℝ → ℝ := fun t ↦
    radialTwoFormIntegrandFDeriv a z t x (v 0) (Fin.removeNth 0 v)
  let g : ℝ → ℝ := fun t ↦
    radialTwoFormIntegrandFDeriv a z t x (v 1) (Fin.removeNth 1 v)
  change (∫ t in (0 : ℝ)..1, f t) - (∫ t in (0 : ℝ)..1, g t) = a x v
  have hDjoint := continuous_radialTwoFormIntegrandFDeriv a z ha
  have hDx : Continuous (fun t ↦ radialTwoFormIntegrandFDeriv a z t x) :=
    hDjoint.comp ((continuous_const (y := x)).prodMk continuous_id)
  let evf : (E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.id ℝ (E [⋀^Fin 1]→L[ℝ] ℝ)).flipAlternating
      (Fin.removeNth 0 v)).comp
        (ContinuousLinearMap.apply ℝ (E [⋀^Fin 1]→L[ℝ] ℝ) (v 0))
  let evg : (E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ((ContinuousLinearMap.id ℝ (E [⋀^Fin 1]→L[ℝ] ℝ)).flipAlternating
      (Fin.removeNth 1 v)).comp
        (ContinuousLinearMap.apply ℝ (E [⋀^Fin 1]→L[ℝ] ℝ) (v 1))
  have hfcont : Continuous f := by
    exact (evf.continuous.comp hDx).congr fun _ ↦ rfl
  have hgcont : Continuous g := by
    exact (evg.continuous.comp hDx).congr fun _ ↦ rfl
  rw [← intervalIntegral.integral_sub (hfcont.intervalIntegrable 0 1)
    (hgcont.intervalIntegrable 0 1)]
  have halt (t : ℝ) : f t - g t =
      ContinuousAlternatingMap.alternatizeUncurryFin
        (radialTwoFormIntegrandFDeriv a z t x) v := by
    rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
      neg_smul, ← sub_eq_add_neg]
    rfl
  rw [intervalIntegral.integral_congr (fun t _ ↦ halt t)]
  rw [intervalIntegral.integral_congr (g := fun t ↦
    (t ^ 2 • fderiv ℝ a (z + t • (x - z)) (x - z) +
      (2 * t) • a (z + t • (x - z))) v) (fun t ht ↦ by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [alternatize_radialTwoFormIntegrandFDeriv a z t x (hclosed t ht)])]
  exact integral_radialTwoFormParameterDerivative_apply a z x v ha

/-- The exterior derivative of the radial homotopy primitive of a globally
smooth closed two-form is the original two-form. -/
theorem extDeriv_radialTwoFormPrimitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : E → E [⋀^Fin 2]→L[ℝ] ℝ) (z x : E)
    (ha : ContDiff ℝ ∞ a)
    (hclosed : ∀ y : E, extDeriv a y = 0) :
    extDeriv (radialTwoFormPrimitive a z) x = a x :=
  extDeriv_radialTwoFormPrimitive_of_closed_segment a z x ha fun _ _ ↦ hclosed _

end

end SGPT.Foundations.Analysis.Pending.LocalPotentials
