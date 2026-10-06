/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientFiber
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compactness Gradient Projection

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic
open scoped ENNReal
noncomputable section

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Weak convergence in Hilbert-valued `L²` is preserved by a continuous
linear map of the fibers. -/
theorem weak_l2_compLpL
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {μ : Measure α} (L : E →L[ℝ] F)
    (f : ℕ → Lp E 2 μ) (g : Lp E 2 μ)
    (hweak : ∀ w, Tendsto (fun k => inner ℝ (f k) w) atTop
      (nhds (inner ℝ g w))) :
    ∀ w, Tendsto (fun k => inner ℝ (L.compLp (f k)) w) atTop
      (nhds (inner ℝ (L.compLp g) w)) := by
  intro w
  let T : Lp E 2 μ →L[ℝ] Lp F 2 μ := L.compLpL 2 μ
  have h := hweak (T.adjoint w)
  change Tendsto (fun k => inner ℝ (T (f k)) w) atTop
    (nhds (inner ℝ (T g) w))
  simpa only [ContinuousLinearMap.adjoint_inner_right] using h

/-- Applying a scalar functional to a weakly convergent `L²` sequence gives
convergence of its integrals against every scalar `L²` test. -/
theorem weak_l2_scalar_integral_of_fiber_weak
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (L : E →L[ℝ] ℝ)
    (F : ℕ → α → E) (G : Lp E 2 μ)
    (hF : ∀ k, MemLp (F k) 2 μ)
    (hweak : ∀ v, Tendsto
      (fun k => inner ℝ ((hF k).toLp (F k)) v) atTop
      (nhds (inner ℝ G v)))
    (w : α → ℝ) (hw : MemLp w 2 μ) :
    Tendsto (fun k => ∫ x, L (F k x) * w x ∂μ) atTop
      (nhds (∫ x, L (G x) * w x ∂μ)) := by
  let fLp (k : ℕ) : Lp E 2 μ := (hF k).toLp (F k)
  let wLp : Lp ℝ 2 μ := hw.toLp w
  have hmap := weak_l2_compLpL L fLp G hweak wLp
  have hEqF (k : ℕ) :
      inner ℝ (L.compLp (fLp k)) wLp =
        ∫ x, L (F k x) * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLp' (fLp k), (hF k).coeFn_toLp,
      hw.coeFn_toLp] with x hxL hxF hxw
    rw [hxL, hxF, hxw, Real.inner_apply]
  have hEqG : inner ℝ (L.compLp G) wLp =
      ∫ x, L (G x) * w x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [L.coeFn_compLp' G, hw.coeFn_toLp] with x hxL hxw
    rw [hxL, hxw, Real.inner_apply]
  simpa only [fLp, wLp, hEqF, hEqG] using hmap

/-- Evaluation of one matrix entry is continuous on the Euclidean gradient
fiber. -/
@[expose]
def gradientCoordinateCLM (i j : Fin 3) :
    CompactnessGradientFiber →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).comp
    (PiLp.proj 2 (fun _ : Fin 3 => L2Vec3) i)

@[simp] theorem gradientCoordinateCLM_apply
    (i j : Fin 3) (A : CompactnessGradientFiber) :
    gradientCoordinateCLM i j A = A i j := by
  rfl

@[simp] theorem gradientCoordinateCLM_toCompactnessGradientFiber
    (i j : Fin 3) (A : Fin 3 → Vec3) :
    gradientCoordinateCLM i j (toCompactnessGradientFiber A) = A i j := by
  rfl

end CKN.Leray
