/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.DomainBuffer
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.SecondCauchy
public import Mathlib.Analysis.Calculus.MeanValue

/-!
Joint analyticity and operator norm estimates for Hamiltonian gradients in the maximum norm.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal
namespace KamProject.Arnold1963

theorem mem_erosion_of_dist_le {E : Type*} [MetricSpace E] {U : Set E}
    {r s : ℝ≥0} {x y : E} (hx : x ∈ erosion U (r + s)) (hy : dist y x ≤ s) :
    y ∈ erosion U r := by
  intro z hz
  apply hx
  exact (dist_triangle z y x).trans (by exact_mod_cast add_le_add hz hy)

theorem prod_mem_erosion {E F : Type*} [MetricSpace E] [MetricSpace F]
    {G : Set E} {U : Set F} {r : ℝ≥0} {p : E} {q : F}
    (hp : p ∈ erosion G r) (hq : q ∈ erosion U r) : (p, q) ∈ erosion (G ×ˢ U) r := by
  intro z hz
  have h := max_le_iff.mp (show max (dist z.1 p) (dist z.2 q) ≤ (r : ℝ) from hz)
  exact ⟨hp h.1, hq h.2⟩

/-- Evaluation of a phase covector on all action-coordinate basis directions. -/
def pGradientCLM (n : ℕ) :
    (ComplexPhaseSpace n →L[ℂ] ℂ) →L[ℂ] ComplexSpace n :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.apply ℂ ℂ (pDirection j))

/-- Evaluation of a phase covector on all angle-coordinate basis directions. -/
def qGradientCLM (n : ℕ) :
    (ComplexPhaseSpace n →L[ℂ] ℂ) →L[ℂ] ComplexSpace n :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.apply ℂ ℂ (qDirection j))

theorem analyticAt_pGradient {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) : AnalyticAt ℂ (pGradient S) x :=
  ((pGradientCLM n).analyticAt _).comp hS.fderiv

theorem analyticAt_qGradient {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) : AnalyticAt ℂ (qGradient S) x :=
  ((qGradientCLM n).analyticAt _).comp hS.fderiv

theorem fderiv_pGradient_apply {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) (v : ComplexPhaseSpace n) (j : Fin n) :
    fderiv ℂ (pGradient S) x v j = fderiv ℂ (fderiv ℂ S) x v (pDirection j) := by
  exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexSpace n => L v j)
    (((pGradientCLM n).hasFDerivAt.comp x hS.fderiv.differentiableAt.hasFDerivAt).fderiv)

theorem fderiv_qGradient_apply {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) (v : ComplexPhaseSpace n) (j : Fin n) :
    fderiv ℂ (qGradient S) x v j = fderiv ℂ (fderiv ℂ S) x v (qDirection j) := by
  exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexSpace n => L v j)
    (((qGradientCLM n).hasFDerivAt.comp x hS.fderiv.differentiableAt.hasFDerivAt).fderiv)

theorem norm_fderiv_pGradient_le {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hS : AnalyticOnNhd ℂ S U) (hM : NormBoundOn S U M)
    (hx : x ∈ erosion U (r + r)) : ‖fderiv ℂ (pGradient S) x‖ ≤ M / r / r := by
  apply norm_fderiv_le_div_of_mem_erosion hr
    (fun y hy => analyticAt_pGradient (hS y (erosion_subset U r hy)))
    (show NormBoundOn (pGradient S) (erosion U r) (M / r) from
      ⟨div_nonneg hM.nonneg r.coe_nonneg, fun _ hy => norm_pGradient_le_div hr hS hM hy⟩)
  intro y hy
  exact mem_erosion_of_dist_le hx hy

theorem norm_fderiv_qGradient_le {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {U : Set (ComplexPhaseSpace n)} {r : ℝ≥0} {M : ℝ} {x : ComplexPhaseSpace n}
    (hr : 0 < r) (hS : AnalyticOnNhd ℂ S U) (hM : NormBoundOn S U M)
    (hx : x ∈ erosion U (r + r)) : ‖fderiv ℂ (qGradient S) x‖ ≤ M / r / r := by
  apply norm_fderiv_le_div_of_mem_erosion hr
    (fun y hy => analyticAt_qGradient (hS y (erosion_subset U r hy)))
    (show NormBoundOn (qGradient S) (erosion U r) (M / r) from
      ⟨div_nonneg hM.nonneg r.coe_nonneg, fun _ hy => norm_qGradient_le_div hr hS hM hy⟩)
  intro y hy
  exact mem_erosion_of_dist_le hx hy

theorem norm_qGradient_le_on_product {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {G U : Set (ComplexSpace n)} {δ : ℝ≥0} {M : ℝ} {P q : ComplexSpace n}
    (hδ : 0 < δ) (hS : AnalyticOnNhd ℂ S (G ×ˢ U))
    (hM : NormBoundOn S (G ×ˢ U) M) (hP : P ∈ G) (hq : q ∈ erosion U δ) :
    ‖qGradient S (P, q)‖ ≤ M / δ := by
  let f : ComplexSpace n → ℂ := fun t => S (P, t)
  have hf : AnalyticOnNhd ℂ f U := fun t ht =>
    (hS (P, t) ⟨hP, ht⟩).comp (f := fun t => (P, t)) (analyticAt_const.prod analyticAt_id)
  have hb : NormBoundOn f U M := ⟨hM.nonneg, fun t ht => hM.norm_le ⟨hP, ht⟩⟩
  have hd := ((hS (P, q) ⟨hP, erosion_subset _ _ hq⟩).differentiableAt.hasFDerivAt).comp q
    ((hasFDerivAt_const P q).prodMk (hasFDerivAt_id (𝕜 := ℂ) q))
  apply (complex_norm_le_iff _ (div_nonneg hM.nonneg δ.coe_nonneg)).2
  intro j
  have h := norm_fderiv_apply_le_div_of_mem_erosion (f := f) (x := q) hδ hf hb hq
    (show ‖Pi.single j (1 : ℂ)‖ ≤ 1 by rw [Pi.norm_single]; norm_num)
  change ‖fderiv ℂ (S ∘ Prod.mk P) q (Pi.single j 1)‖ ≤ _ at h
  rw [hd.fderiv] at h
  exact h

end KamProject.Arnold1963
