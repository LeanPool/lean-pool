/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
Density of nonresonant linear torus flows, proved through Fourier coefficients and closure.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
namespace KamProject.Arnold1963

/-- Normalized Haar measure used in the Fourier proof of orbit density. -/
local instance densityUnitCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance densityUnitCircleHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance densityUnitCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A uniform rotation on the unit-period real torus. -/
def unitTorusLine {n : ℕ} (v : RealSpace n) (t : ℝ) : UnitAddTorus (Fin n) :=
  fun j => (t * v j : ℝ)

theorem unitTorusLine_add {n : ℕ} (v : RealSpace n) (s t : ℝ) :
    unitTorusLine v (s + t) = unitTorusLine v s + unitTorusLine v t := by
  ext j
  simp [unitTorusLine, add_mul]

theorem mFourier_translate {n : ℕ} (k : FourierIndex n)
    (x y : UnitAddTorus (Fin n)) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_unitTorusLine {n : ℕ} (k : FourierIndex n) (v : RealSpace n) (t : ℝ) :
    UnitAddTorus.mFourier k (unitTorusLine v t) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) *
        ((∑ j, (k j : ℝ) * v j : ℝ) : ℂ)) := by
  simp only [UnitAddTorus.mFourier, unitTorusLine, ContinuousMap.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_intCast]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem invariant_under_nonresonant_line_constant {n : ℕ} (v : RealSpace n)
    (hnr : ∀ k : FourierIndex n, k ≠ 0 → ∑ j, (k j : ℝ) * v j ≠ 0)
    (f : C(UnitAddTorus (Fin n), ℂ))
    (hi : ∀ t x, f (unitTorusLine v t + x) = f x) :
    ∀ x y, f x = f y := by
  classical
  have hc : ∀ k : FourierIndex n, k ≠ 0 → UnitAddTorus.mFourierCoeff f k = 0 := by
    intro k hk
    let a : ℝ := ∑ j, ((-k) j : ℝ) * v j
    have ha : a ≠ 0 := hnr (-k) (neg_ne_zero.mpr hk)
    have hm : UnitAddTorus.mFourier (-k) (unitTorusLine v (1 / (2 * a))) = -1 := by
      rw [mFourier_unitTorusLine]
      change Complex.exp (2 * Real.pi * Complex.I * ((1 / (2 * a) : ℝ) : ℂ) * (a : ℂ)) = -1
      have haz : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
      convert Complex.exp_pi_mul_I using 1
      push_cast
      field_simp
    apply integral_eq_zero_of_add_left_eq_neg (g := unitTorusLine v (1 / (2 * a)))
    intro x
    change UnitAddTorus.mFourier (-k) (unitTorusLine v (1 / (2 * a)) + x) *
      f (unitTorusLine v (1 / (2 * a)) + x) = -(UnitAddTorus.mFourier (-k) x * f x)
    rw [mFourier_translate, hi, hm]
    ring
  have hs : Summable (UnitAddTorus.mFourierCoeff f) :=
    summable_of_ne_finset_zero (s := {0}) (by simpa using hc)
  have he (x : UnitAddTorus (Fin n)) : f x = UnitAddTorus.mFourierCoeff f 0 := by
    rw [← (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs x).tsum_eq,
      tsum_eq_single 0]
    · simp [UnitAddTorus.mFourier_zero]
    · intro k hk
      simp [hc k hk]
  exact fun x y => (he x).trans (he y).symm

theorem denseRange_unitTorusLine {n : ℕ} (v : RealSpace n)
    (hnr : ∀ k : FourierIndex n, k ≠ 0 → ∑ j, (k j : ℝ) * v j ≠ 0) :
    DenseRange (unitTorusLine v) := by
  let S := range (unitTorusLine v)
  have hS : S.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  let f : C(UnitAddTorus (Fin n), ℂ) :=
    ⟨fun x => (infDist x S : ℂ), Complex.continuous_ofReal.comp (continuous_infDist_pt S)⟩
  have hi (t : ℝ) (x : UnitAddTorus (Fin n)) : f (unitTorusLine v t + x) = f x := by
    have he : (fun y => unitTorusLine v t + y) '' S = S := by
      ext y
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨t + s, unitTorusLine_add v t s⟩
      · rintro ⟨s, rfl⟩
        refine ⟨unitTorusLine v (s - t), ⟨s - t, rfl⟩, ?_⟩
        change unitTorusLine v t + unitTorusLine v (s - t) = unitTorusLine v s
        rw [← unitTorusLine_add]
        congr 1
        ring
    have hh := infDist_image (isometry_add_left (unitTorusLine v t)) (x := x) (t := S)
    rw [he] at hh
    exact congrArg Complex.ofReal hh
  have he := invariant_under_nonresonant_line_constant v hnr f hi
  intro x
  apply (mem_closure_iff_infDist_zero hS).mpr
  have hh := he x (unitTorusLine v 0)
  change (infDist x S : ℂ) = (infDist (unitTorusLine v 0) S : ℂ) at hh
  rw [infDist_zero_of_mem (show unitTorusLine v 0 ∈ S from ⟨0, rfl⟩)] at hh
  exact Complex.ofReal_eq_zero.mp hh

/-- A real-angle trajectory on the torus with period `2π`. -/
def realTorusLine {n : ℕ} (v q : RealSpace n) (t : ℝ) : RealTorus n :=
  fun j => (q j + t * v j : ℝ)

theorem denseRange_realTorusLine {n : ℕ} (v q : RealSpace n)
    (hnr : ∀ k : FourierIndex n, k ≠ 0 → ∑ j, (k j : ℝ) * v j ≠ 0) :
    DenseRange (realTorusLine v q) := by
  have hT : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  let w : RealSpace n := fun j => v j / (2 * Real.pi)
  have hw : ∀ k : FourierIndex n, k ≠ 0 → ∑ j, (k j : ℝ) * w j ≠ 0 := by
    intro k hk he
    apply hnr k hk
    have hh : (∑ j, (k j : ℝ) * v j) / (2 * Real.pi) = 0 := by
      simpa only [w, ← mul_div_assoc, ← Finset.sum_div] using he
    exact (div_eq_zero_iff.mp hh).resolve_right hT
  let e : UnitAddTorus (Fin n) ≃ₜ RealTorus n := Homeomorph.piCongrRight
    (fun _ => AddCircle.homeomorphAddCircle 1 (2 * Real.pi) one_ne_zero hT)
  have hd := e.surjective.denseRange.comp (denseRange_unitTorusLine w hw) e.continuous
  have he : e ∘ unitTorusLine w = realTorusLine v 0 := by
    funext t
    ext j
    change ((t * (v j / (2 * Real.pi)) * (1⁻¹ * (2 * Real.pi)) : ℝ) :
      AddCircle (2 * Real.pi)) = ((0 + t * v j : ℝ) : AddCircle (2 * Real.pi))
    congr 1
    field_simp
    ring
  rw [he] at hd
  let a : RealTorus n := fun j => (q j : AddCircle (2 * Real.pi))
  have ha : Function.Surjective (fun x : RealTorus n => a + x) := fun y => ⟨y - a, by abel_nf⟩
  have hh := ha.denseRange.comp hd (by fun_prop)
  have he' : (fun x : RealTorus n => a + x) ∘ realTorusLine v 0 = realTorusLine v q := by
    funext t
    ext j
    simp [realTorusLine, a]
  rw [he'] at hh
  exact hh

end KamProject.Arnold1963
