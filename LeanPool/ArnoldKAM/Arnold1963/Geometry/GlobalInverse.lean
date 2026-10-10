/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingLocal

/-!
Injectivity of maps close to identity on possibly nonconvex domains, and consistent analytic
inverses selected on a fixed source domain.
-/

@[expose] public section
noncomputable section
open Set Filter Metric Function
open scoped NNReal Topology
namespace KamProject.Arnold1963

variable {E : Type*} [NormedAddCommGroup E]

theorem injOn_add_of_local_lipschitz {a : E → E} {D : Set E} {r ε : ℝ} {κ : ℝ≥0}
    (hb : ∀ x ∈ D, ‖a x‖ ≤ ε) (hε : 2 * ε ≤ r) (hκ : κ < 1)
    (hlip : ∀ x ∈ D, LipschitzOnWith κ a (closedBall x r)) :
    InjOn (fun x => x + a x) D := by
  intro x hx y hy he
  change x + a x = y + a y at he
  have hxy : x - y = a y - a x := by
    calc
      x - y = (x + a x) - (y + a y) + (a y - a x) := by abel
      _ = a y - a x := by rw [he]; simp
  have hd : dist y x ≤ r := by
    rw [dist_comm, dist_eq_norm, hxy]
    exact (norm_sub_le _ _).trans ((add_le_add (hb y hy) (hb x hx)).trans (by linarith))
  have hr : 0 ≤ r := (dist_nonneg.trans hd)
  have h := (hlip x hx).dist_le_mul y hd x (mem_closedBall_self hr)
  have hh : dist (a y) (a x) = dist x y := by rw [dist_eq_norm, ← hxy, dist_eq_norm]
  rw [hh, dist_comm y x] at h
  have hk : (κ : ℝ) < 1 := hκ
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem erosion_mem_nhds {D : Set E} {r s : ℝ≥0} (hs : 0 < s) {x : E}
    (hx : x ∈ erosion D (r + s)) : erosion D r ∈ 𝓝 x :=
  mem_of_superset (closedBall_mem_nhds x (show (0 : ℝ) < s from hs))
    (fun _ hy => mem_erosion_of_dist_le hx hy)

theorem invFunOn_eventually_eq {f g : E → E} {D : Set E} {x : E}
    (hi : InjOn f D) (hD : D ∈ 𝓝 x) (hg : ContinuousAt g (f x))
    (hgx : g (f x) = x) (he : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    ∀ᶠ y in 𝓝 (f x), invFunOn f D y = g y := by
  have hm : ∀ᶠ y in 𝓝 (f x), g y ∈ D := hg (by simpa only [hgx] using hD)
  filter_upwards [hm, he] with y hy hfy
  have hh := invFunOn_pos ⟨g y, hy, hfy⟩
  exact hi hh.1 hy (hh.2.trans hfy.symm)

theorem analytic_invFunOn [NormedSpace ℂ E] [CompleteSpace E] {f : E → E} {D : Set E} {x : E}
    (hi : InjOn f D) (hD : D ∈ 𝓝 x) (hf : AnalyticAt ℂ f x)
    (hn : ‖fderiv ℂ f x - ContinuousLinearMap.id ℂ E‖ < 1) :
    AnalyticAt ℂ (invFunOn f D) (f x) ∧ invFunOn f D (f x) = x ∧
      ∀ᶠ y in 𝓝 (f x), f (invFunOn f D y) = y := by
  obtain ⟨g, hg, hgx, he⟩ := exists_analytic_local_inverse hf hn
  have heq := invFunOn_eventually_eq hi hD hg.continuousAt hgx he
  refine ⟨hg.congr (heq.mono fun _ h => h.symm), heq.self_of_nhds.trans hgx, ?_⟩
  filter_upwards [heq, he] with y hy hey
  rw [hy]; exact hey

end KamProject.Arnold1963
