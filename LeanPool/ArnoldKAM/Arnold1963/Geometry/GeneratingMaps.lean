/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GradientBounds

/-!
Mixed-coordinate maps (P, q + S_P) and (P + S_q, q), and the Hessian symplectic identity.
-/

@[expose] public section
noncomputable section
open scoped Topology
namespace KamProject.Arnold1963

/-- The input coordinate map associated with a generating function. -/
def generatingInput {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ComplexPhaseSpace n := (x.1, x.2 + pGradient S x)

/-- The output coordinate map associated with a generating function. -/
def generatingOutput {n : ℕ} (S : ComplexPhaseSpace n → ℂ)
    (x : ComplexPhaseSpace n) : ComplexPhaseSpace n := (x.1 + qGradient S x, x.2)

theorem analyticAt_generatingInput {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) : AnalyticAt ℂ (generatingInput S) x :=
  analyticAt_fst.prod (analyticAt_snd.add (analyticAt_pGradient hS))

theorem analyticAt_generatingOutput {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) : AnalyticAt ℂ (generatingOutput S) x :=
  (analyticAt_fst.add (analyticAt_qGradient hS)).prod analyticAt_snd

theorem fderiv_generatingInput_apply {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) (v : ComplexPhaseSpace n) :
    fderiv ℂ (generatingInput S) x v = (v.1, v.2 + fderiv ℂ (pGradient S) x v) := by
  have hd := (hasFDerivAt_fst (𝕜 := ℂ) (p := x)).prodMk
    ((hasFDerivAt_snd (𝕜 := ℂ) (p := x)).add
      (analyticAt_pGradient hS).differentiableAt.hasFDerivAt)
  exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L v) hd.fderiv

theorem fderiv_generatingOutput_apply {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) (v : ComplexPhaseSpace n) :
    fderiv ℂ (generatingOutput S) x v = (v.1 + fderiv ℂ (qGradient S) x v, v.2) := by
  have hd := ((hasFDerivAt_fst (𝕜 := ℂ) (p := x)).add
    (analyticAt_qGradient hS).differentiableAt.hasFDerivAt).prodMk
      (hasFDerivAt_snd (𝕜 := ℂ) (p := x))
  exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L v) hd.fderiv

theorem norm_fderiv_generatingInput_sub_id_le {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) :
    ‖fderiv ℂ (generatingInput S) x - ContinuousLinearMap.id ℂ _‖ ≤
      ‖fderiv ℂ (pGradient S) x‖ := by
  refine (fderiv ℂ (generatingInput S) x -
    ContinuousLinearMap.id ℂ (ComplexPhaseSpace n)).opNorm_le_bound
    (norm_nonneg (fderiv ℂ (pGradient S) x)) ?_
  intro v
  change ‖fderiv ℂ (generatingInput S) x v - v‖ ≤ _
  rw [fderiv_generatingInput_apply hS]
  simpa [Prod.sub_def] using
    (fderiv ℂ (pGradient S) x).le_opNorm v

theorem norm_fderiv_generatingOutput_sub_id_le {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) :
    ‖fderiv ℂ (generatingOutput S) x - ContinuousLinearMap.id ℂ _‖ ≤
      ‖fderiv ℂ (qGradient S) x‖ := by
  refine (fderiv ℂ (generatingOutput S) x -
    ContinuousLinearMap.id ℂ (ComplexPhaseSpace n)).opNorm_le_bound
    (norm_nonneg (fderiv ℂ (qGradient S) x)) ?_
  intro v
  change ‖fderiv ℂ (generatingOutput S) x v - v‖ ≤ _
  rw [fderiv_generatingOutput_apply hS]
  simpa [Prod.sub_def] using
    (fderiv ℂ (qGradient S) x).le_opNorm v

theorem generating_symplectic_identity {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {x : ComplexPhaseSpace n} (hS : AnalyticAt ℂ S x) (v w : ComplexPhaseSpace n) :
    symplecticForm (fderiv ℂ (generatingOutput S) x v) (fderiv ℂ (generatingOutput S) x w) =
      symplecticForm (fderiv ℂ (generatingInput S) x v) (fderiv ℂ (generatingInput S) x w) := by
  have hsym := hS.contDiffAt.isSymmSndFDerivAt_of_omega v w
  change (fderiv ℂ (fderiv ℂ S) x v).toLinearMap w =
    (fderiv ℂ (fderiv ℂ S) x w).toLinearMap v at hsym
  rw [linearForm_decomposition (fderiv ℂ (fderiv ℂ S) x v).toLinearMap w,
    linearForm_decomposition (fderiv ℂ (fderiv ℂ S) x w).toLinearMap v] at hsym
  simp only [ContinuousLinearMap.coe_coe, ← fderiv_pGradient_apply hS,
    ← fderiv_qGradient_apply hS] at hsym
  rw [fderiv_generatingOutput_apply hS, fderiv_generatingOutput_apply hS,
    fderiv_generatingInput_apply hS, fderiv_generatingInput_apply hS]
  simp only [symplecticForm, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_comm (fderiv ℂ (qGradient S) x v _),
    mul_comm (fderiv ℂ (pGradient S) x v _)]
  linear_combination hsym

theorem canonicalAt_generating_branch {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {g : ComplexPhaseSpace n → ComplexPhaseSpace n} {y : ComplexPhaseSpace n}
    (hS : AnalyticAt ℂ S (g y)) (hg : AnalyticAt ℂ g y)
    (he : ∀ᶠ z in nhds y, generatingInput S (g z) = z) :
    CanonicalAt (generatingOutput S ∘ g) y := by
  have hF := analyticAt_generatingInput hS
  have hH := analyticAt_generatingOutput hS
  have hd : (fderiv ℂ (generatingInput S) (g y)).comp (fderiv ℂ g y) =
      ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp y hF.differentiableAt hg.differentiableAt]
    exact (Filter.EventuallyEq.fderiv_eq he).trans fderiv_id
  refine ⟨hH.differentiableAt.comp y hg.differentiableAt, ?_⟩
  intro v w
  rw [fderiv_comp y hH.differentiableAt hg.differentiableAt]
  change symplecticForm
    (fderiv ℂ (generatingOutput S) (g y) (fderiv ℂ g y v))
    (fderiv ℂ (generatingOutput S) (g y) (fderiv ℂ g y w)) = _
  rw [generating_symplectic_identity hS]
  exact congrArg₂ symplecticForm
    (congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L v) hd)
    (congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L w) hd)

theorem norm_fderiv_generating_branch_le {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {g : ComplexPhaseSpace n → ComplexPhaseSpace n} {y : ComplexPhaseSpace n}
    (hS : AnalyticAt ℂ S (g y)) (hg : AnalyticAt ℂ g y)
    (he : ∀ᶠ z in nhds y, generatingInput S (g z) = z)
    (hp : ‖fderiv ℂ (pGradient S) (g y)‖ ≤ 1 / 4)
    (hq : ‖fderiv ℂ (qGradient S) (g y)‖ ≤ 1 / 4) :
    ‖fderiv ℂ (generatingOutput S ∘ g) y‖ ≤ 5 / 3 := by
  let A := fderiv ℂ (generatingInput S) (g y)
  let D := fderiv ℂ (generatingOutput S) (g y)
  let C := fderiv ℂ g y
  have hA : ‖A - ContinuousLinearMap.id ℂ _‖ ≤ 1 / 4 :=
    (norm_fderiv_generatingInput_sub_id_le hS).trans hp
  have hD : ‖D - ContinuousLinearMap.id ℂ _‖ ≤ 1 / 4 :=
    (norm_fderiv_generatingOutput_sub_id_le hS).trans hq
  have hAC : A.comp C = ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp y (analyticAt_generatingInput hS).differentiableAt hg.differentiableAt]
    exact (Filter.EventuallyEq.fderiv_eq he).trans fderiv_id
  rw [fderiv_comp y (analyticAt_generatingOutput hS).differentiableAt hg.differentiableAt]
  refine (D.comp C).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 5 / 3) ?_
  intro v
  have hav : A (C v) = v :=
    congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ComplexPhaseSpace n => L v) hAC
  have h1 : ‖v - C v‖ ≤ 1 / 4 * ‖C v‖ := by
    have hh := ((A - ContinuousLinearMap.id ℂ _).le_opNorm (C v)).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    simpa only [sub_apply, ContinuousLinearMap.id_apply, hav] using hh
  have h2 : ‖C v‖ ≤ ‖v‖ + ‖v - C v‖ := by
    have := norm_sub_le v (v - C v)
    simpa using this
  have h3 : ‖D (C v) - C v‖ ≤ 1 / 4 * ‖C v‖ :=
    ((D - ContinuousLinearMap.id ℂ _).le_opNorm (C v)).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have h4 : ‖D (C v)‖ ≤ ‖C v‖ + ‖D (C v) - C v‖ := by
    simpa using norm_add_le (C v) (D (C v) - C v)
  change ‖D (C v)‖ ≤ _
  linarith

end KamProject.Arnold1963
