/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardBallGrowth
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardAffineGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.WeakGradientTranslation

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardH1sLocTranslate

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local Sobolev membership under a translation by an arbitrary real vector

`MemH1sLoc` is a conjunction of a measurability clause, a weak-gradient clause
on every centred ball, and a smooth-approximation clause in the `H¹_s` norm.
All three transport along `v ↦ v (· + t)` with the coefficient field translating
with them, for an **arbitrary real** vector `t`, and an additive recentring
`v ↦ v - c` is free.

Two facts do the work.

* The weak-gradient clause on `B_R` follows from the clause on
  `B_{R + ‖t‖}` because `B_R + t ⊆ B_{R + ‖t‖}`: the available
  `HasWeakGradientOn.untranslate` moves a pair from a translated set, and
  `hasWeakGradientOn_subset` restricts.  The additive constant needs the
  vanishing of `∫_U ∂_i φ` for a test supported in `U`, which is the constant
  case of `HasWeakPartialDerivOn.of_contDiff`.
* `h1sNormSqOn` is an **unnormalized** integral, so it is monotone in the domain
  with no volume factor; the approximants transport with no constant at all.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Recentring a weak-gradient pair -/

/-- A weak-gradient pair survives subtraction of a constant from its value
field.  The gradient is unchanged.

The proof is the vanishing of `∫_U c ∂_i φ`, which is the constant case of
`HasWeakPartialDerivOn.of_contDiff`, together with a case split on whether
`u ∂_i φ` is integrable on `U`: the definition uses a totalized Bochner
integral, so the split is what keeps the additive step honest. -/
theorem HasWeakGradientOn.sub_const {U : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (h : HasWeakGradientOn U u Du) (c : ℝ) :
    HasWeakGradientOn U (fun x => u x - c) Du := by
  intro i phi hsmooth hcompact hsub
  have hfderivCont : Continuous (fun x : Vec d => (fderiv ℝ phi x) (basisVec i)) := by
    simpa using (hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfderivSupp : HasCompactSupport
      (fun x : Vec d => (fderiv ℝ phi x) (basisVec i)) := by
    simpa using hcompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hcint : IntegrableOn
      (fun x => c * (fderiv ℝ phi x) (basisVec i)) U volume :=
    ((continuous_const.mul hfderivCont).integrable_of_hasCompactSupport
      hfderivSupp.mul_left).integrableOn
  have hzero : ∫ x in U, c * (fderiv ℝ phi x) (basisVec i) ∂volume = 0 := by
    have hconst : HasWeakPartialDerivOn U i (fun _ : Vec d => c)
        (fun x => (fderiv ℝ (fun _ : Vec d => c) x) (basisVec i)) :=
      HCPolySupport.HasWeakPartialDerivOn.of_contDiff contDiff_const
    have hc := hconst phi hsmooth hcompact hsub
    simpa using hc
  have hbase := h i phi hsmooth hcompact hsub
  by_cases hu : IntegrableOn (fun x => u x * (fderiv ℝ phi x) (basisVec i)) U volume
  · show ∫ x in U, (u x - c) * (fderiv ℝ phi x) (basisVec i) ∂volume =
      -∫ x in U, Du x i * phi x ∂volume
    simp_rw [sub_mul]
    rw [integral_sub hu hcint, hzero, sub_zero]
    exact hbase
  · have hnot : ¬ IntegrableOn
        (fun x => u x * (fderiv ℝ phi x) (basisVec i) -
          c * (fderiv ℝ phi x) (basisVec i)) U volume := by
      intro hcon
      refine hu (Integrable.congr (hcon.add hcint) ?_)
      filter_upwards with x
      simp only [Pi.add_apply]
      ring
    rw [integral_undef hu] at hbase
    show ∫ x in U, (u x - c) * (fderiv ℝ phi x) (basisVec i) ∂volume =
      -∫ x in U, Du x i * phi x ∂volume
    simp_rw [sub_mul]
    rw [integral_undef hnot]
    exact hbase

/-! ## Geometry: a ball translated by `t` sits in the ball grown by `‖t‖` -/

/-- The ball of radius `r` centred at `t` sits inside the centred ball of radius
`r + ‖t‖`, the Euclidean length being written through `vecNormSq`. -/
theorem euclideanBallAt_subset_euclideanBall_add (t : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    euclideanBallAt t r ⊆ euclideanBall d (r + Real.sqrt (vecNormSq t)) := by
  intro x hx
  have hx' : vecNormSq (x - t) < r ^ 2 := hx
  have hsub : Real.sqrt (vecNormSq (x - t)) < r := by
    have hlt := Real.sqrt_lt_sqrt (vecNormSq_nonneg (x - t)) hx'
    rwa [Real.sqrt_sq hr] at hlt
  have hxt : (x - t) + t = x := by
    ext i
    simp [sub_eq_add_neg, add_assoc]
  have htri : Real.sqrt (vecNormSq x) ≤
      Real.sqrt (vecNormSq (x - t)) + Real.sqrt (vecNormSq t) := by
    have hh := sqrt_vecNormSq_add_le (x - t) t
    rwa [hxt] at hh
  have hlt : Real.sqrt (vecNormSq x) < r + Real.sqrt (vecNormSq t) := by
    linarith only [htri, hsub]
  show vecNormSq (x - 0) < (r + Real.sqrt (vecNormSq t)) ^ 2
  rw [sub_zero, pow_two]
  have hmm := mul_self_lt_mul_self (Real.sqrt_nonneg (vecNormSq x)) hlt
  rwa [Real.mul_self_sqrt (vecNormSq_nonneg x)] at hmm

/-! ## The `H¹_s` norm is monotone under a translated inclusion -/

/-- Lower Lebesgue integrals transport along a translation and are monotone in
the domain. -/
theorem lintegral_translate_le {U V : Set (Vec d)} (t : Vec d)
    (hUV : translateSet t U ⊆ V) (g : Vec d → ℝ≥0∞) :
    (∫⁻ x in U, g (x + t) ∂volume) ≤ ∫⁻ y in V, g y ∂volume := by
  have h := (HCPolySupport.measurePreserving_addRight_restrict_translateSet t
      U).lintegral_comp_emb (Homeomorph.addRight t).measurableEmbedding g
  calc (∫⁻ x in U, g (x + t) ∂volume)
      = ∫⁻ y in translateSet t U, g y ∂volume := by simpa using h
    _ ≤ ∫⁻ y in V, g y ∂volume :=
        lintegral_mono' (Measure.restrict_mono_set volume hUV) le_rfl

/-- The coefficient-weighted `H¹_s` norm square of a translated pair on `U` is
at most the norm square of the untranslated pair on any set containing the
translate of `U`.  The norm is unnormalized, so there is **no** volume factor. -/
theorem h1sNormSqOn_translate_le (b : CoeffField d) {U V : Set (Vec d)}
    (t : Vec d) (hUV : translateSet t U ⊆ V) (f : Vec d → ℝ) (F : Vec d → Vec d) :
    h1sNormSqOn (fun y => b (y + t)) U (fun y => f (y + t)) (fun y => F (y + t)) ≤
      h1sNormSqOn b V f F := by
  have h1 : (∫⁻ x in U, ENNReal.ofReal |f (x + t)| ∂volume) ≤
      ∫⁻ y in V, ENNReal.ofReal |f y| ∂volume :=
    lintegral_translate_le t hUV (fun y => ENNReal.ofReal |f y|)
  have h2 : (∫⁻ x in U, ENNReal.ofReal
        (vecDot (F (x + t)) (matVecMul (symmPart (b (x + t))) (F (x + t))))
        ∂volume) ≤
      ∫⁻ y in V, ENNReal.ofReal
        (vecDot (F y) (matVecMul (symmPart (b y)) (F y))) ∂volume :=
    lintegral_translate_le t hUV
      (fun y => ENNReal.ofReal (vecDot (F y) (matVecMul (symmPart (b y)) (F y))))
  have hsq : (∫⁻ x in U, ENNReal.ofReal |f (x + t)| ∂volume) ^ 2 ≤
      (∫⁻ y in V, ENNReal.ofReal |f y| ∂volume) ^ 2 := by gcongr
  simp only [h1sNormSqOn, sEnergyOn]
  exact add_le_add hsq h2

/-! ## The coordinate gradient under a translation -/

/-- The coordinate gradient of a translated and recentred smooth function is the
translated coordinate gradient. -/
theorem smoothGrad_comp_addRight_sub_const (f : Vec d → ℝ) (t : Vec d) (c : ℝ)
    (x : Vec d) :
    smoothGrad (fun y => f (y + t) - c) x = smoothGrad f (x + t) := by
  funext i
  simp only [smoothGrad]
  rw [fderiv_sub_const, fderiv_comp_add_right]

/-! ## The `MemH1sLoc` conjunct of the Liouville class, transported -/

/-- **`MemH1sLoc` transports along a translation by an arbitrary real vector**,
the coefficient field translating with the pair, and an arbitrary additive
recentring is free. -/
theorem memH1sLoc_realTranslate_subConst {b : CoeffField d} {v : Vec d → ℝ}
    {Dv : Vec d → Vec d} (h : MemH1sLoc b v Dv) (t : Vec d) (c : ℝ) :
    MemH1sLoc (fun y => b (y + t)) (fun y => v (y + t) - c)
      (fun y => Dv (y + t)) := by
  obtain ⟨⟨hvmeas, hDvmeas⟩, hloc⟩ := h
  have hshift : MeasurePreserving (fun x : Vec d => x + t) volume volume :=
    measurePreserving_add_right volume t
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (hvmeas.comp_quasiMeasurePreserving
      hshift.quasiMeasurePreserving).sub aestronglyMeasurable_const
  · intro i
    exact (hDvmeas i).comp_quasiMeasurePreserving hshift.quasiMeasurePreserving
  · intro R hR
    have hT0 : 0 ≤ Real.sqrt (vecNormSq t) := Real.sqrt_nonneg _
    have hRbig : 0 < R + Real.sqrt (vecNormSq t) := by linarith only [hR, hT0]
    obtain ⟨hweak, w, hwsmooth, hwtend⟩ :=
      hloc (R + Real.sqrt (vecNormSq t)) hRbig
    have hincl : translateSet t (euclideanBall d R) ⊆
        euclideanBall d (R + Real.sqrt (vecNormSq t)) := by
      rw [translateSet_euclideanBall]
      exact euclideanBallAt_subset_euclideanBall_add t hR.le
    have hw2 : HasWeakGradientOn (euclideanBall d R) (fun x => v (x + t))
        (fun x => Dv (x + t)) :=
      HasWeakGradientOn.untranslate t (hasWeakGradientOn_subset hincl hweak)
    refine ⟨HasWeakGradientOn.sub_const hw2 c, fun n y => w n (y + t) - c, ?_, ?_⟩
    · intro n
      have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => w n (y + t)) :=
        (hwsmooth n).comp (contDiff_id.add contDiff_const)
      exact hc.sub contDiff_const
    · refine tendsto_zero_of_le_of_tendsto_zero (fun n => ?_) hwtend
      have hfun : (fun x : Vec d => (w n (x + t) - c) - (v (x + t) - c))
          = fun x : Vec d => (fun y => w n y - v y) (x + t) := by
        funext x
        ring
      have hgrad :
          (fun x : Vec d =>
              smoothGrad (fun y => w n (y + t) - c) x - Dv (x + t))
            = fun x : Vec d => (fun y => smoothGrad (w n) y - Dv y) (x + t) := by
        funext x
        rw [smoothGrad_comp_addRight_sub_const]
      rw [hfun, hgrad]
      exact h1sNormSqOn_translate_le b t hincl (fun y => w n y - v y)
        (fun y => smoothGrad (w n) y - Dv y)

end

end Root
end HighContrast
end HCPolySupport
