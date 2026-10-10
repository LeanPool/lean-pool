/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Dynamics.VectorFields
public import LeanPool.ArnoldKAM.Arnold1963.Convergence.ComplexLines
public import Mathlib.Analysis.Complex.RealDeriv

/-!
Pass the conjugacy to the limit and construct solutions of the original Hamiltonian equation
for every real time.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem limit_conjugacy_complex {p : ComplexSpace n} (hp : p ∈ h.limitDomain b)
    {q : ComplexSpace n} {t : ℂ}
    (ht : t ∈ lineDomain (ρ₀ := ρ₀) q (h.limitFrequency b p)) :
    HasDerivAt (fun u : ℂ => h.limitMap b (p, q + u • h.limitFrequency b p))
      (h.vectorField b 0 (h.limitMap b (p, q + t • h.limitFrequency b p))) t := by
  let z : ComplexPhaseSpace n := (p, q + t • h.limitFrequency b p)
  have hz : z ∈ h.limitPhase b := h.line_mem_limitPhase b hp ht
  have hd := (h.line_derivative_uniform b hp q (h.limitFrequency b p)).tendsto_at ht
  have hx := (h.vectorField_analytic b 0 _ (h.limitMap_maps b hz)).continuousAt.tendsto.comp
    ((h.cumulative_uniform b).tendsto_at hz)
  have hl := (hd.sub hx).norm.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto
      (fun s => ‖deriv (fun u : ℂ => h.cumulative b (s + 1)
        (p, q + u • h.limitFrequency b p)) t - h.vectorField b 0 (h.cumulative b (s + 1) z)‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _
      (b.weighted_beta_tendsto_zero.comp (tendsto_add_atTop_nat 1))
    intro s
    rw [h.line_derivative_eq b hp ht (s + 1)]
    exact h.approximate_conjugacy b s hz
  have he := tendsto_nhds_unique hl hzero
  have ha := h.limitMap_line_analytic b hp q (h.limitFrequency b p) t ht
  have hderiv := ha.differentiableAt.hasDerivAt
  rw [sub_eq_zero.mp (norm_eq_zero.mp he)] at hderiv
  exact hderiv

theorem real_time_mem_lineDomain {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) :
    (t : ℂ) ∈ lineDomain (ρ₀ := ρ₀) (complexify q) (h.limitFrequency b (complexify p)) := by
  have he := h.limitFrequency_real_value b hp
  change ‖imagPart (complexify q + (t : ℂ) • h.limitFrequency b (complexify p))‖ < _
  rw [← he]
  have hi : imagPart (complexify q + (t : ℂ) •
      complexify (realPart (h.limitFrequency b (complexify p)))) = 0 := by
    ext j
    simp [imagPart, complexify]
  rw [hi, norm_zero]
  exact div_pos (show (0 : ℝ) < ρ₀ from b.width_pos) (by norm_num)

/-- The limiting phase transformation applied to uniform rotation with the limiting frequency. -/
def orbit (p q : RealSpace n) (t : ℝ) : ComplexPhaseSpace n :=
  h.limitMap b (complexify p, complexify q + (t : ℂ) • h.limitFrequency b (complexify p))

theorem orbit_hasDerivAt {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) :
    HasDerivAt (h.orbit b p q) (h.vectorField b 0 (h.orbit b p q t)) t := by
  have hc := h.limit_conjugacy_complex b (p := complexify p) (q := complexify q)
    hp (h.real_time_mem_lineDomain b hp q t)
  change HasDerivAt (fun u : ℝ => h.limitMap b
    (complexify p, complexify q + (u : ℂ) • h.limitFrequency b (complexify p))) _ t
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul,
    orbit] using! hc.scomp t Complex.ofRealCLM.hasDerivAt

theorem orbit_mem_initial {p : RealSpace n} (hp : p ∈ realSlice (h.limitDomain b))
    (q : RealSpace n) (t : ℝ) : h.orbit b p q t ∈ h.phase b 0 :=
  h.limitMap_maps b (h.line_mem_limitPhase b hp (h.real_time_mem_lineDomain b hp q t))

theorem orbit_initial (p q : RealSpace n) : h.orbit b p q 0 =
    h.limitMap b (complexifyPhase (p, q)) := by simp [orbit, complexifyPhase]

end KamProject.Arnold1963.Iteration.InitialData
