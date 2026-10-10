/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Convergence.Limit
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Complex-line analyticity and convergence of angle derivatives for a fixed action label.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

/-- Complex times for which the indicated affine angle line lies in the common open strip. -/
def lineDomain (q v : ComplexSpace n) : Set ℂ :=
  {t | ‖imagPart (q + t • v)‖ < (ρ₀ : ℝ) / 3}

theorem lineDomain_open (q v : ComplexSpace n) : IsOpen (lineDomain (ρ₀ := ρ₀) q v) := by
  apply isOpen_lt _ continuous_const
  unfold imagPart
  fun_prop

theorem line_mem_limitPhase {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q v : ComplexSpace n} {t : ℂ} (ht : t ∈ lineDomain (ρ₀ := ρ₀) q v) :
    (p, q + t • v) ∈ h.limitPhase b := by
  apply h.commonPhase_subset b
  refine ⟨hp, ?_⟩
  exact (show ‖imagPart (q + t • v)‖ < (ρ₀ : ℝ) / 3 from ht).le

theorem line_uniform {p : ComplexSpace n} (hp : p ∈ h.limitDomain b) (q v : ComplexSpace n) :
    TendstoUniformlyOn (fun s t => h.cumulative b s (p, q + t • v))
      (fun t => h.limitMap b (p, q + t • v)) atTop (lineDomain (ρ₀ := ρ₀) q v) :=
  ((h.cumulative_uniform b).comp (fun t => (p, q + t • v))).mono
    (fun _ ht => h.line_mem_limitPhase b hp ht)

theorem line_differentiable {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (q v : ComplexSpace n) (s : ℕ) :
    DifferentiableOn ℂ (fun t => h.cumulative b s (p, q + t • v))
      (lineDomain (ρ₀ := ρ₀) q v) := by
  intro t ht
  have ha : AnalyticAt ℂ (fun u : ℂ => (p, q + u • v)) t :=
    analyticAt_const.prod (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  exact ((h.cumulative_analytic b s _
    (h.limitPhase_subset b s (h.line_mem_limitPhase b hp ht))).comp
      (f := fun u : ℂ => (p, q + u • v)) ha).differentiableAt.differentiableWithinAt

theorem limitMap_line_analytic {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (q v : ComplexSpace n) :
    AnalyticOnNhd ℂ (fun t => h.limitMap b (p, q + t • v)) (lineDomain (ρ₀ := ρ₀) q v) := by
  have hd := (h.line_uniform b hp q v).tendstoLocallyUniformlyOn.differentiableOn
    (Filter.Eventually.of_forall (h.line_differentiable b hp q v)) (lineDomain_open q v)
  exact hd.analyticOnNhd (lineDomain_open q v)

theorem line_derivative_uniform {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    (q v : ComplexSpace n) :
    TendstoLocallyUniformlyOn (fun s => deriv (fun t => h.cumulative b s (p, q + t • v)))
      (deriv (fun t => h.limitMap b (p, q + t • v))) atTop (lineDomain (ρ₀ := ρ₀) q v) :=
  (h.line_uniform b hp q v).tendstoLocallyUniformlyOn.deriv
    (Filter.Eventually.of_forall (h.line_differentiable b hp q v)) (lineDomain_open q v)

theorem line_derivative_eq {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q v : ComplexSpace n} {t : ℂ} (ht : t ∈ lineDomain (ρ₀ := ρ₀) q v) (s : ℕ) :
    deriv (fun t => h.cumulative b s (p, q + t • v)) t =
      fderiv ℂ (h.cumulative b s) (p, q + t • v) (0, v) := by
  have hd : HasDerivAt (fun t : ℂ => (p, q + t • v)) (0, v) t := by
    simpa using (hasDerivAt_const t p).prodMk (((hasDerivAt_id t).smul_const v).const_add q)
  have hf := (h.cumulative_analytic b s _
    (h.limitPhase_subset b s (h.line_mem_limitPhase b hp ht))).differentiableAt.hasFDerivAt
  exact (hf.comp_hasDerivAt t hd).deriv

end KamProject.Arnold1963.Iteration.InitialData
