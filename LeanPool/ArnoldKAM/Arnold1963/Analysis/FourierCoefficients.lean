/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.FunctionOperations
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierPolynomial
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Fourier coefficients and angle averages from Haar integration on the unit torus, linked to
the physical angle period by scaling. The coefficients have uniform bounds and conjugation laws.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal
namespace KamProject.Arnold1963

/-- Normalized Haar measure for the unit circle used in Fourier coefficient integrals. -/
local instance fourierCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Representatives of unit torus coordinates in the interval `(0, 1]`. -/
def unitTorusRepr {n : ℕ} (t : UnitAddTorus (Fin n)) : RealSpace n :=
  fun j => (AddCircle.equivIoc 1 0 (t j)).1

/-- Real unit-period coordinates embedded as complex angles with period `2π`. -/
def scaledAngle {n : ℕ} (t : RealSpace n) : ComplexSpace n :=
  complexify (fun j => 2 * Real.pi * t j)

theorem continuous_scaledAngle (n : ℕ) : Continuous (scaledAngle (n := n)) := by
  unfold scaledAngle
  exact (continuous_complexify n).comp (by fun_prop)

theorem scaledAngle_mem_strip {n : ℕ} (t : RealSpace n) (ρ : ℝ≥0) :
    scaledAngle t ∈ angleStrip n ρ := complexify_mem_angleStrip _ _

theorem mFourier_eq_fourierMonomial {n : ℕ} (k : FourierIndex n) (t : RealSpace n) :
    UnitAddTorus.mFourier k (fun j => (t j : UnitAddCircle)) =
      fourierMonomial k (scaledAngle t) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  unfold fourierMonomial indexPairing
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [scaledAngle, complexify, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}

/-- Evaluation of a periodic phase function on the unit torus at a fixed action. -/
def torusValue (f : AnalyticPhaseFunction n G ρ) (p : ComplexSpace n)
    (t : UnitAddTorus (Fin n)) : ℂ := f.toFun (p, scaledAngle (unitTorusRepr t))

theorem torusValue_coe (f : AnalyticPhaseFunction n G ρ) {p : ComplexSpace n}
    (hp : p ∈ G) (t : RealSpace n) :
    f.torusValue p (fun j => (t j : UnitAddCircle)) = f.toFun (p, scaledAngle t) := by
  classical
  have hex : ∀ j : Fin n, ∃ k : ℤ,
      (unitTorusRepr (fun j => (t j : UnitAddCircle)) j) = t j + k := by
    intro j
    have he : ((unitTorusRepr (fun j => (t j : UnitAddCircle)) j - t j : ℝ) :
        UnitAddCircle) = 0 := by
      simp [unitTorusRepr, AddCircle.coe_equivIoc]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp he
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose k hk using hex
  have heq : scaledAngle (unitTorusRepr (fun j => (t j : UnitAddCircle))) =
      scaledAngle t + angleShift k := by
    ext j
    simp [scaledAngle, complexify, angleShift, hk, mul_add]
  unfold torusValue
  rw [heq]
  exact f.periodic p hp _ (scaledAngle_mem_strip _ _) k

theorem continuous_torusValue (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) : Continuous (f.torusValue p) := by
  have hquot : IsOpenQuotientMap
      (fun t : RealSpace n => (fun j => (t j : UnitAddCircle))) :=
    IsOpenQuotientMap.piMap (fun _ : Fin n => QuotientAddGroup.isOpenQuotientMap_mk)
  apply hquot.continuous_comp_iff.mp
  have he : f.torusValue p ∘ (fun t : RealSpace n => fun j => (t j : UnitAddCircle)) =
      fun t => f.toFun (p, scaledAngle t) := funext (f.torusValue_coe hp)
  rw [he]
  exact f.analytic.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_scaledAngle n))
    (fun t => ⟨hp, scaledAngle_mem_strip t ρ⟩)

/-- The continuous unit-torus function obtained by fixing an action in the domain. -/
def onUnitTorus (f : AnalyticPhaseFunction n G ρ) (p : G) :
    C(UnitAddTorus (Fin n), ℂ) := ⟨f.torusValue p, f.continuous_torusValue p.property⟩

/-- The normalized torus Fourier coefficient at a fixed complex action. -/
def fourierCoeff (f : AnalyticPhaseFunction n G ρ) (p : ComplexSpace n)
    (k : FourierIndex n) : ℂ := UnitAddTorus.mFourierCoeff (f.torusValue p) k

/-- The zero Fourier coefficient, representing the angle average. -/
def angleAverage (f : AnalyticPhaseFunction n G ρ) (p : ComplexSpace n) : ℂ :=
  f.fourierCoeff p 0

theorem fourierCoeff_eq_integral (f : AnalyticPhaseFunction n G ρ)
    (p : ComplexSpace n) (k : FourierIndex n) :
    f.fourierCoeff p k = UnitAddTorus.mFourierCoeff (f.torusValue p) k := rfl

theorem norm_onUnitTorus_le (f : AnalyticPhaseFunction n G ρ) (p : G) :
    ‖f.onUnitTorus p‖ ≤ f.uniformNorm := by
  apply (ContinuousMap.norm_le _ ((f.norm_le_iff.mp le_rfl).nonneg)).mpr
  intro t
  exact (f.norm_le_iff.mp le_rfl).norm_le ⟨p.property, scaledAngle_mem_strip _ _⟩

theorem norm_fourierCoeff_le (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n) :
    ‖f.fourierCoeff p k‖ ≤ f.uniformNorm := by
  unfold fourierCoeff UnitAddTorus.mFourierCoeff
  have hb : ∀ᵐ t : UnitAddTorus (Fin n),
      ‖UnitAddTorus.mFourier (-k) t • f.torusValue p t‖ ≤ f.uniformNorm := by
    apply Filter.Eventually.of_forall
    intro t
    rw [norm_smul]
    have he : ‖UnitAddTorus.mFourier (-k) t‖ ≤ 1 := by
      simpa only [UnitAddTorus.mFourier_norm] using
        (UnitAddTorus.mFourier (-k)).norm_coe_le_norm t
    have hf : ‖f.torusValue p t‖ ≤ f.uniformNorm :=
      (f.norm_le_iff.mp le_rfl).norm_le ⟨hp, scaledAngle_mem_strip _ _⟩
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa using hf)
  simpa using norm_integral_le_of_norm_le_const hb

theorem norm_angleAverage_le (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) : ‖f.angleAverage p‖ ≤ f.uniformNorm :=
  f.norm_fourierCoeff_le hp 0

theorem angleAverage_eq_integral (f : AnalyticPhaseFunction n G ρ)
    (p : ComplexSpace n) :
    f.angleAverage p = ∫ t : UnitAddTorus (Fin n), f.torusValue p t := by
  simp [angleAverage, fourierCoeff, UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero]

theorem norm_sub_angleAverage_le (f : AnalyticPhaseFunction n G ρ)
    {p q : ComplexSpace n} (hp : p ∈ G) (hq : q ∈ angleStrip n ρ) :
    ‖f.toFun (p, q) - f.angleAverage p‖ ≤ 2 * f.uniformNorm := by
  calc
    _ ≤ ‖f.toFun (p, q)‖ + ‖f.angleAverage p‖ := norm_sub_le _ _
    _ ≤ f.uniformNorm + f.uniformNorm :=
      add_le_add ((f.norm_le_iff.mp le_rfl).norm_le ⟨hp, hq⟩) (f.norm_angleAverage_le hp)
    _ = _ := by ring

theorem fourierCoeff_eq_cubeIntegral (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n) :
    f.fourierCoeff p k =
      ∫ t : RealSpace n in {t | ∀ j, t j ∈ Set.Ioc 0 1},
        UnitAddTorus.mFourier (-k) (fun j => (t j : UnitAddCircle)) *
          f.toFun (p, scaledAngle t) := by
  rw [fourierCoeff, UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : RealSpace n)]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul, f.torusValue_coe hp]

theorem torusValue_conj (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (t : UnitAddTorus (Fin n)) :
    f.torusValue (conjVec p) t = star (f.torusValue p t) := by
  simpa only [torusValue, conjPhase, scaledAngle, conjVec_complexify] using
    f.conj_compatible (p, scaledAngle (unitTorusRepr t))
      ⟨hp, scaledAngle_mem_strip _ _⟩

theorem fourierCoeff_conj (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) (k : FourierIndex n) :
    f.fourierCoeff (conjVec p) (-k) = star (f.fourierCoeff p k) := by
  unfold fourierCoeff UnitAddTorus.mFourierCoeff
  change _ = (starRingEnd ℂ) (∫ t : UnitAddTorus (Fin n),
    UnitAddTorus.mFourier (-k) t • f.torusValue p t)
  rw [← integral_conj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [f.torusValue_conj hp]
  simp [smul_eq_mul, UnitAddTorus.mFourier_neg]

theorem angleAverage_conj (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) :
    f.angleAverage (conjVec p) = star (f.angleAverage p) := by
  simpa only [angleAverage, neg_zero] using f.fourierCoeff_conj hp 0

theorem angleAverage_real_value (f : AnalyticPhaseFunction n G ρ)
    (p : RealSpace n) (hp : complexify p ∈ G) :
    (f.angleAverage (complexify p)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [conjVec_complexify, starRingEnd_apply] using (f.angleAverage_conj hp).symm

@[simp] theorem fourierCoeff_restrict (f : AnalyticPhaseFunction n G ρ)
    {U : Set (ComplexSpace n)} {σ : ℝ≥0} (hUG : U ⊆ G)
    (hσρ : σ ≤ ρ) (hU : ConjInvariant U) (p : ComplexSpace n) (k : FourierIndex n) :
    (f.restrict hUG hσρ hU).fourierCoeff p k = f.fourierCoeff p k := rfl

@[simp] theorem angleAverage_restrict (f : AnalyticPhaseFunction n G ρ)
    {U : Set (ComplexSpace n)} {σ : ℝ≥0} (hUG : U ⊆ G)
    (hσρ : σ ≤ ρ) (hU : ConjInvariant U) (p : ComplexSpace n) :
    (f.restrict hUG hσρ hU).angleAverage p = f.angleAverage p := rfl

theorem integral_centered_eq_zero (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) :
    (∫ t : UnitAddTorus (Fin n), f.torusValue p t - f.angleAverage p) = 0 := by
  rw [integral_sub ((f.continuous_torusValue hp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (integrable_const _)]
  simp [← f.angleAverage_eq_integral]

end AnalyticPhaseFunction
end KamProject.Arnold1963
