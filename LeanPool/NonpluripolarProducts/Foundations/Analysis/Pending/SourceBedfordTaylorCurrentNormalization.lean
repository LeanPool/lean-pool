/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorForms

/-!
# Rescaling Bedford–Taylor currents

The operator used by `btProduct` has the normalization
`ddᶜ = (i / (2π)) ∂∂bar`, as in Xia's manuscript. This file also
records the conversion to the chosen operator `D = 2π ddᶜ` and
proves that a product of `q` factors is then rescaled by `(2π)^q`.
[Xia's normalization](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_pshfunctions.tex#L121-L124).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.SourceBedfordTaylorCurrentNormalization

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorForms

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Genuine coefficient-measure multiplication is linear in nonnegative current scaling. -/
theorem mulBorel_smul_current {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {c : ℝ} (hc : 0 ≤ c) {u : ComplexModel n → ℝ}
    (hu : Measurable u) (hub : IsLocallyBoundedOn u U) :
    mulBorel (c • T) u = c • mulBorel T u := by
  have hS : IsPositive (c • T) := hT.smul hc
  ext γ φ
  have hd : IsLocalDensity (U := U) hT.traceMeasure
      (fun x => c * hT.density γ x) := by
    refine ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
      (hT.measurable_density γ).const_mul c, ?_⟩
    intro K _ _
    obtain ⟨C, _, hC⟩ := hT.exists_abs_density_le γ
    refine ⟨|c| * C, ?_⟩
    intro x _
    change |c * hT.density γ x| ≤ |c| * C
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)
  have hrep : ∀ ψ : 𝓓(U, ℝ), (c • T) γ ψ =
      ∫ x, ψ x * (c * hT.density γ x) ∂hT.traceMeasure := by
    intro ψ
    change c * T γ ψ = _
    rw [hT.apply_eq_integral_density, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [mulBorel_apply_of_integral_eq hS γ hd hrep hu hub φ]
  change (∫ x, φ x * (u x * (c * hT.density γ x)) ∂hT.traceMeasure) =
    c * mulBorel T u γ φ
  rw [mulBorel_apply hT hu hub, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

private theorem ddcMul_smul_current {q : ℕ} {T : LocalProductCurrent n U (q + 1)}
    (hT : IsPositive T) {c : ℝ} (hc : 0 ≤ c) {u : ComplexModel n → ℝ}
    (hu : IsLocallyBoundedPshOn U u) : ddcMul (c • T) u = c • ddcMul T u := by
  unfold ddcMul
  rw [mulBorel_smul_current hT hc (measurable_indicator_of_isLocallyBoundedPshOn hu)
    (isLocallyBoundedOn_indicator hu), ddc_smul]

private theorem isClosedAny_smul {q : ℕ} {T : LocalProductCurrent n U q}
    (hT : IsClosedAny q T) (c : ℝ) : IsClosedAny q (c • T) := by
  cases q with
  | zero => trivial
  | succ q => exact hT.smul c

/-- The genuine recursive product is linear in nonnegative base-current scaling. -/
theorem btProduct_smul_current : ∀ (q r : ℕ) (u : Fin q → ComplexModel n → ℝ)
    (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    ∀ c : ℝ, 0 ≤ c → btProduct q r u (c • T) = c • btProduct q r u T
  | 0, _, _, _, _, _, _, _, _ => rfl
  | q + 1, r, u, T, hT, hTc, hu, c, hc => by
    rw [btProduct_succ, btProduct_succ, ddcMul_smul_current hT hc (hu (Fin.last q))]
    obtain ⟨hS, hSc⟩ := isPositive_ddcMul hT hTc (hu (Fin.last q))
    exact btProduct_smul_current q r (Fin.init u) _ hS hSc (fun i => hu _) c hc

/-- The rescaled recursive product uses the chosen operator `D(uT) = 2π ddᶜ(uT)`. -/
def sourceDProduct : (q r : ℕ) → (Fin q → ComplexModel n → ℝ) →
    LocalProductCurrent n U (r + q) → LocalProductCurrent n U r
  | 0, _, _, T => T
  | q + 1, r, u, T => sourceDProduct q r (Fin.init u)
      ((2 * Real.pi) • ddcMul T (u (Fin.last q)))

/-- Each recursive step contributes a factor of `2π` to the rescaled current. -/
theorem sourceDProduct_eq : ∀ (q r : ℕ) (u : Fin q → ComplexModel n → ℝ)
    (T : LocalProductCurrent n U (r + q)), IsPositive T → IsClosedAny (r + q) T →
    (∀ i, IsLocallyBoundedPshOn U (u i)) →
    sourceDProduct q r u T = (2 * Real.pi) ^ q • btProduct q r u T
  | 0, _, _, _, _, _, _ => by simp [sourceDProduct]
  | q + 1, r, u, T, hT, hTc, hu => by
    have hc : 0 ≤ (2 * Real.pi) := by positivity
    obtain ⟨hS, hSc⟩ := isPositive_ddcMul hT hTc (hu (Fin.last q))
    rw [sourceDProduct, sourceDProduct_eq q r (Fin.init u) _ (hS.smul hc)
      (isClosedAny_smul hSc _) (fun i => hu _),
      btProduct_smul_current q r (Fin.init u) _ hS hSc (fun i => hu _) _ hc,
      smul_smul, ← pow_succ, ← btProduct_succ]

/-- The rescaled product of locally bounded PSH factors is positive and closed. -/
theorem sourceDProduct_positive_closed (q r : ℕ) (u : Fin q → ComplexModel n → ℝ)
    (T : LocalProductCurrent n U (r + q)) (hT : IsPositive T)
    (hTc : IsClosedAny (r + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    IsPositive (sourceDProduct q r u T) ∧ IsClosedAny r (sourceDProduct q r u T) := by
  rw [sourceDProduct_eq q r u T hT hTc hu]
  obtain ⟨hp, hclosed⟩ := isPositive_btProduct q r u T hT hTc hu
  exact ⟨hp.smul (by positivity), isClosedAny_smul hclosed _⟩

end SGPT.Foundations.Analysis.Pending.SourceBedfordTaylorCurrentNormalization
