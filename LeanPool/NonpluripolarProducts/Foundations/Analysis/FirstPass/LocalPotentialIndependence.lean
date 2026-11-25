/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PositiveClasses
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshAddition
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Independence of a smooth local potential

The normalized operator `smoothDDC` is computed from the genuine second real
Fréchet derivative.  Its complex diagonal is the Levi form divided by `π`.
Consequently a smooth function with vanishing `smoothDDC` is locally
pluriharmonic.  We use a smooth bump to extend each germ before invoking the
global smooth Levi criterion, so no regularity outside the stated open domain
is assumed.

It follows that two smooth local potentials for the same form give equivalent
PSH correction tests, including at points where the extended-real function is
`⊥`.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

variable {n : ℕ}

/-- Coordinate formula for the actual normalized exterior derivative
`ddᶜu = d(-du ∘ I /(4π))`. -/
theorem smoothDDC_apply_eq_realHessian {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) (v w : ComplexModel n) :
    smoothDDC u z ![v, w] =
      (realHessian u z w (Complex.I • v) -
        realHessian u z v (Complex.I • w)) / (4 * Real.pi) := by
  unfold smoothDDC
  rw [extDeriv_apply]
  · rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Fin.removeNth_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, smoothDc_apply]
    have htail : Fin.tail ![v, w] 0 = w := by rfl
    have hremove : Fin.removeNth 1 ![v, w] 0 = v := by rfl
    rw [htail, hremove]
    norm_num
    have hv : DifferentiableAt ℝ (fun y => fderiv ℝ u y (Complex.I • v)) z := by
      fun_prop
    have hw : DifferentiableAt ℝ (fun y => fderiv ℝ u y (Complex.I • w)) z := by
      fun_prop
    have hfd : DifferentiableAt ℝ (fderiv ℝ u) z :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [fderiv_const_mul hw (-1 / (4 * Real.pi)),
      fderiv_const_mul hv (-1 / (4 * Real.pi))]
    rw [fderiv_clm_apply hfd (differentiableAt_const (c := Complex.I • w)),
      fderiv_clm_apply hfd (differentiableAt_const (c := Complex.I • v))]
    have hcw : fderiv ℝ (fun _ : ComplexModel n ↦ Complex.I • w) z = 0 :=
      fderiv_const_apply (𝕜 := ℝ) (x := z) (Complex.I • w)
    have hcv : fderiv ℝ (fun _ : ComplexModel n ↦ Complex.I • v) z = 0 :=
      fderiv_const_apply (𝕜 := ℝ) (x := z) (Complex.I • v)
    rw [hcw, hcv]
    simp only [ContinuousLinearMap.comp_zero, zero_add, smul_apply,
      ContinuousLinearMap.flip_apply, realHessian_eq_fderiv]
    ring
  · unfold smoothDc
    have houter : ContDiff ℝ 1
        (ContinuousAlternatingMap.ofSubsingletonLIE
          (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ) (0 : Fin 1)) :=
      (ContinuousAlternatingMap.ofSubsingletonLIE
        (𝕜 := ℝ) (E := ComplexModel n) (F := ℝ) (0 : Fin 1)).contDiff
    have hinner : ContDiffAt ℝ 1 (fun y =>
        (-1 / (4 * Real.pi) : ℝ) •
          (fderiv ℝ u y).comp (modelComplexStructure n)) z :=
      ((hu.fderiv_right (m := 1) (by norm_num)).clm_comp contDiffAt_const)
        |>.const_smul (-1 / (4 * Real.pi) : ℝ)
    exact (houter.comp_contDiffAt z hinner).differentiableAt (by norm_num)

/-- A smooth germ on an open subset of the complex model has a globally smooth
representative.  The cutoff is supported strictly inside the open set. -/
theorem exists_contDiff_eventuallyEq_of_contDiffOn
    {W : Set (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hW : IsOpen W) (hh : ContDiffOn ℝ ∞ h W) {x : ComplexModel n} (hx : x ∈ W) :
    ∃ g : ComplexModel n → ℝ, ContDiff ℝ ∞ g ∧ h =ᶠ[𝓝 x] g := by
  classical
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hx
  let b : ContDiffBump x :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let g : ComplexModel n → ℝ := W.piecewise (fun y ↦ b y * h y) 0
  have hbts : tsupport (b : ComplexModel n → ℝ) ⊆ W := by
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεW
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ W
    · apply (b.contDiffAt.mul ((hh y hy).contDiffAt (hW.mem_nhds hy))).congr_of_eventuallyEq
      filter_upwards [hW.mem_nhds hy] with z hz
      simp [g, hz]
    · have hyt : y ∉ tsupport (b : ComplexModel n → ℝ) := fun hyt ↦ hy (hbts hyt)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (b : ComplexModel n → ℝ)).isOpen_compl.mem_nhds hyt]
        with z hz
      have hbz : b z = 0 := by
        apply not_ne_iff.mp
        intro hbzne
        exact hz (subset_tsupport (b : ComplexModel n → ℝ) hbzne)
      by_cases hzW : z ∈ W <;> simp [g, hzW, hbz]
  refine ⟨g, hg, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x b.rIn_pos] with y hy
  have hyW : y ∈ W := hεW (by
    change dist y x < ε
    change dist y x < ε / 4 at hy
    linarith)
  have hby : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  simp [g, hyW, hby]

/-- Nonnegative Levi form on an open set implies plurisubharmonicity there. -/
theorem plurisubharmonicOn_of_contDiffOn_levi_nonneg
    {U : Set (ComplexModel n)} {f : ComplexModel n → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hlevi : ∀ y ∈ U, ∀ v, 0 ≤ leviForm f y v) :
    PlurisubharmonicOn (fun y => (f y : EReal)) U := by
  intro y hy
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn hU hf hy
  have hmem : {x | f x = g x} ∩ U ∈ 𝓝 y := inter_mem heq (hU.mem_nhds hy)
  obtain ⟨W, hWsub, hW, hyW⟩ := _root_.mem_nhds_iff.mp hmem
  have hWU : W ⊆ U := fun x hx ↦ (hWsub hx).2
  have heqW : EqOn f g W := fun x hx ↦ (hWsub hx).1
  have hgLevi : ∀ x ∈ W, ∀ v : ComplexModel n, 0 ≤ leviForm g x v := by
    intro x hx v
    have hlocal : f =ᶠ[𝓝 x] g := by
      filter_upwards [hW.mem_nhds hx] with t ht
      exact heqW ht
    have hsecond : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x :=
      hlocal.fderiv.fderiv_eq
    have hl : leviForm f x v = leviForm g x v := by
      simp only [leviForm, realHessian_eq_fderiv, hsecond]
    rw [← hl]
    exact hlevi x (hWU hx) v
  have hgPsh : PlurisubharmonicOn (fun x ↦ (g x : EReal)) W :=
    plurisubharmonicOn_of_levi_nonneg
      (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hW hgLevi
  apply (hgPsh y hyW).congr
  filter_upwards [hW.mem_nhds hyW] with x hx
  exact congrArg (fun t : ℝ ↦ (t : EReal)) (heqW hx).symm

/-- The complex diagonal of the normalized `ddᶜ` is the Levi form divided by
`π`. -/
theorem smoothDDC_complexDiagonal_eq_leviForm {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) (v : ComplexModel n) :
    smoothDDC u z ![v, Complex.I • v] = leviForm u z v / Real.pi := by
  rw [smoothDDC_apply_eq_realHessian hu]
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp [leviForm, realHessian_eq_fderiv]
  ring

/-- A smooth function with zero `ddᶜ` on an open domain is genuinely PSH there.
The same theorem applied to its negative gives local pluriharmonicity. -/
theorem plurisubharmonicOn_coe_of_smoothDDC_eq_zero
    {W : Set (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hW : IsOpen W) (hh : ContDiffOn ℝ ∞ h W)
    (hzero : ∀ z ∈ W, smoothDDC h z = 0) :
    PlurisubharmonicOn (fun z ↦ (h z : EReal)) W := by
  refine plurisubharmonicOn_of_contDiffOn_levi_nonneg hW hh ?_
  intro y hy v
  have hh2 : ContDiffAt ℝ 2 h y := ((hh y hy).contDiffAt (hW.mem_nhds hy)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hdiag := smoothDDC_complexDiagonal_eq_leviForm hh2 v
  rw [hzero y hy] at hdiag
  exact ((div_eq_zero_iff.mp hdiag.symm).resolve_right Real.pi_ne_zero).ge

/-- Finite corrections cancel without changing either infinity of `EReal`. -/
theorem corrected_add_sub (a : EReal) (r s : ℝ) :
    (a + (r : EReal)) + ((s - r : ℝ) : EReal) = a + (s : EReal) := by
  rw [add_assoc, ← EReal.coe_add]
  congr 2
  ring

/-- Two smooth local potentials of the same form differ by a pluriharmonic
function, so the corrected PSH test is independent of the chosen potential. -/
theorem smoothLocalPotential_psh_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (θ : SmoothRealForm n M 2) (e : ComplexChart n M)
    (W : Set (ComplexModel n)) (ρ σ : ComplexModel n → ℝ)
    (hρ : IsSmoothLocalPotential θ e W ρ) (hσ : IsSmoothLocalPotential θ e W σ)
    (u : ComplexModel n → EReal) :
    PlurisubharmonicOn (fun z => u z + (ρ z : EReal)) W ↔
      PlurisubharmonicOn (fun z => u z + (σ z : EReal)) W := by
  have hsmooth : ContDiffOn ℝ ∞ (fun y ↦ σ y - ρ y) W :=
    hσ.2.2.1.sub hρ.2.2.1
  have hddc : ∀ z ∈ W, smoothDDC (fun y ↦ σ y - ρ y) z = 0 := by
    intro z hz
    rw [PositiveClasses.smoothDDC_sub hρ.1 hσ.2.2.1 hρ.2.2.1 hz,
      hσ.2.2.2 hz, hρ.2.2.2 hz, sub_self]
  have hpsh := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hρ.1 hsmooth hddc
  constructor
  · intro hu
    have hadd := SGPT.Foundations.Analysis.PlurisubharmonicOn.add hu hpsh
    intro x hx
    apply (hadd x hx).congr
    exact Eventually.of_forall fun y ↦ corrected_add_sub (u y) (ρ y) (σ y)
  · intro hu
    have hsmooth' : ContDiffOn ℝ ∞ (fun y ↦ ρ y - σ y) W :=
      hρ.2.2.1.sub hσ.2.2.1
    have hddc' : ∀ z ∈ W, smoothDDC (fun y ↦ ρ y - σ y) z = 0 := by
      intro z hz
      rw [PositiveClasses.smoothDDC_sub hρ.1 hρ.2.2.1 hσ.2.2.1 hz,
        hρ.2.2.2 hz, hσ.2.2.2 hz, sub_self]
    have hpsh' := plurisubharmonicOn_coe_of_smoothDDC_eq_zero hρ.1 hsmooth' hddc'
    have hadd := SGPT.Foundations.Analysis.PlurisubharmonicOn.add hu hpsh'
    intro x hx
    apply (hadd x hx).congr
    exact Eventually.of_forall fun y ↦ corrected_add_sub (u y) (σ y) (ρ y)

end

end SGPT.Foundations.Analysis.FirstPass
