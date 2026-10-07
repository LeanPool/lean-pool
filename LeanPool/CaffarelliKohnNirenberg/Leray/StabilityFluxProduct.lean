/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityQuadraticIntegral

/-!
# Stability Flux Product

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

private instance : ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa [CKN.ofReal_threeHalves] using
    hreal.ennrealOfReal

/-- Strong local convergence of an `L^{3/2}` field and an `L³` field passes
their product against a bounded scalar test to the integral limit. -/
theorem stability_flux_product_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F G : ℕ → α → ℝ) (f g φ : α → ℝ)
    (hF : ∀ n, MemLp (F n) (3 / 2 : ℝ≥0∞) μ)
    (hG : ∀ n, MemLp (G n) 3 μ)
    (hf : MemLp f (3 / 2 : ℝ≥0∞) μ) (hg : MemLp g 3 μ)
    (hφ : MemLp φ ∞ μ)
    (hFconv : Tendsto (fun n => eLpNorm (F n - f) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0))
    (hGconv : Tendsto (fun n => eLpNorm (G n - g) 3 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x * φ x ∂μ) atTop
      (nhds (∫ x, f x * g x * φ x ∂μ)) := by
  have hmul (a b : α → ℝ) (ha : AEStronglyMeasurable a μ)
      (hb : AEStronglyMeasurable b μ) :
      eLpNorm (fun x => a x * b x) 1 μ ≤
        eLpNorm a (3 / 2 : ℝ≥0∞) μ * eLpNorm b 3 μ := by
    simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm
      (b := fun x y : ℝ => x * y) (c := (1 : ℝ≥0∞))
      (by fun_prop) ha hb (by filter_upwards with x; simp [enorm_mul]))
  have hsum (n : ℕ) :
      eLpNorm (fun x => F n x * G n x - f x * g x) 1 μ ≤
      eLpNorm (F n - f) (3 / 2 : ℝ≥0∞) μ * eLpNorm (G n) 3 μ +
        eLpNorm f (3 / 2 : ℝ≥0∞) μ * eLpNorm (G n - g) 3 μ := by
    have hdiff : (fun x => F n x * G n x - f x * g x) =
        (fun x => (F n x - f x) * G n x + f x * (G n x - g x)) := by
      funext x
      ring
    rw [hdiff]
    exact (eLpNorm_add_le (by norm_num)).trans
      (add_le_add
        (hmul _ _ ((hF n).sub hf).aestronglyMeasurable
          (hG n).aestronglyMeasurable)
        (hmul _ _ hf.aestronglyMeasurable
          ((hG n).sub hg).aestronglyMeasurable))
  let C := eLpNorm g 3 μ
  have hC : C < ⊤ := hg
  have hC1 : C + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC.ne, ENNReal.one_ne_top⟩
  have hGbound : ∀ᶠ n : ℕ in atTop, eLpNorm (G n) 3 μ ≤ C + 1 := by
    filter_upwards [hGconv.eventually (Iio_mem_nhds
      (by norm_num : (0 : ℝ≥0∞) < 1))] with n hn
    have htriangle := eLpNorm_add_le (μ := μ) (p := (3 : ℝ≥0∞))
      (by norm_num) (f := G n - g) (g := g)
    have hidentity : G n = (fun x => G n x - g x + g x) := by
      funext x
      ring
    calc
      eLpNorm (G n) 3 μ = eLpNorm (fun x => G n x - g x + g x) 3 μ := by
        exact congrArg (fun k => eLpNorm k 3 μ) hidentity
      _ ≤ eLpNorm (G n - g) 3 μ + eLpNorm g 3 μ := htriangle
      _ ≤ 1 + C := add_le_add hn.le le_rfl
      _ = C + 1 := add_comm _ _
  have hfirst : Tendsto (fun n =>
      eLpNorm (F n - f) (3 / 2 : ℝ≥0∞) μ * (C + 1)) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hFconv (Or.inr hC1)
  have hsecond : Tendsto (fun n =>
      eLpNorm f (3 / 2 : ℝ≥0∞) μ * eLpNorm (G n - g) 3 μ)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hGconv (Or.inr hf.ne)
  have hmajor : Tendsto (fun n =>
      eLpNorm (F n - f) (3 / 2 : ℝ≥0∞) μ * (C + 1) +
        eLpNorm f (3 / 2 : ℝ≥0∞) μ * eLpNorm (G n - g) 3 μ)
      atTop (nhds 0) := by
    simpa using hfirst.add hsecond
  have hprod : Tendsto (fun n =>
      eLpNorm (fun x => F n x * G n x - f x * g x) 1 μ)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajor
    · filter_upwards with n
      exact bot_le
    · filter_upwards [hGbound] with n hn
      exact (hsum n).trans (add_le_add (mul_le_mul_right hn _) le_rfl)
  have hprodMem (n : ℕ) : MemLp (fun x => F n x * G n x) 1 μ := by
    have h : MemLp (F n * G n) (1 : ℝ≥0∞) μ :=
      (hF n).mul (hG n)
    convert h using 1
  have hφMem (n : ℕ) : MemLp (fun x => F n x * G n x * φ x) 1 μ := by
    have h : MemLp (φ • fun x => F n x * G n x) (1 : ℝ≥0∞) μ :=
      hφ.smul (hprodMem n)
    convert h using 1
    ext x
    simp [smul_eq_mul, mul_comm, mul_left_comm]
  have hbound (n : ℕ) :
      eLpNorm (fun x => F n x * G n x * φ x - f x * g x * φ x) 1 μ ≤
        eLpNorm φ ∞ μ *
          eLpNorm (fun x => F n x * G n x - f x * g x) 1 μ := by
    have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
      (φ := φ) (f := fun x => F n x * G n x - f x * g x)
      (1 : ℝ≥0∞) hφ.aestronglyMeasurable
    have heq : (fun x => F n x * G n x * φ x - f x * g x * φ x) =
        φ • (fun x => F n x * G n x - f x * g x) := by
      funext x
      change F n x * G n x * φ x - f x * g x * φ x =
        φ x * (F n x * G n x - f x * g x)
      ring
    rwa [heq]
  have hscaled : Tendsto (fun n =>
      eLpNorm (fun x => F n x * G n x * φ x - f x * g x * φ x) 1 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.Tendsto.const_mul hprod (Or.inr hφ.eLpNorm_ne_top))
      (Filter.Eventually.of_forall fun _ => bot_le)
      (Filter.Eventually.of_forall hbound)
  exact tendsto_integral_of_L1' (fun x => f x * g x * φ x)
    (Filter.Eventually.of_forall fun n =>
      memLp_one_iff_integrable.mp (hφMem n)) hscaled

end CKN
