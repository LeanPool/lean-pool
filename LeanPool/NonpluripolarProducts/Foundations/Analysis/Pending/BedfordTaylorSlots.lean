/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorInduction
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.SmoothPlurisubharmonic
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian

/-!
# Slot calculus for the Bedford–Taylor induction

Integration by parts in an arbitrary slot, linearity of a slot, constant
approximations, and the shift of a compactly supported smooth function by a
multiple of `‖z‖²` into a plurisubharmonic function.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem isDecApprox_const {U : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsSmoothPsdOn U f) : IsDecApprox U f (fun _ ↦ f) := by
  refine ⟨fun _ ↦ hf, fun z _ ↦ antitone_const, fun z _ ↦ tendsto_const_nhds,
    fun K hK hKU ↦ ?_⟩
  exact (hK.image_of_continuousOn (hf.1.continuousOn.mono hKU)).bddBelow

/-- A compactly supported smooth function becomes plurisubharmonic after adding a
large multiple of `‖z‖²`. -/
theorem exists_isSmoothPsdOn_add_norm_sq {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ IsSmoothPsdOn ⊤ (fun z ↦ φ z + C * ‖z‖ ^ 2) := by
  have hcont : Continuous (iteratedFDeriv ℝ 2 φ) :=
    hφ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨B, hB⟩ := (hc.iteratedFDeriv 2).exists_bound_of_continuous hcont
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, ?_⟩
  have hψ : ContDiff ℝ ∞ (fun z : ComplexModel n ↦ ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have hsm : ContDiff ℝ ∞ (fun z ↦ φ z + B * ‖z‖ ^ 2) := hφ.add (contDiff_const.mul hψ)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hlevi : ∀ z (v : ComplexModel n), 0 ≤ leviForm (fun z ↦ φ z + B * ‖z‖ ^ 2) z v := by
    intro z v
    have hsplit : (fun z ↦ φ z + B * ‖z‖ ^ 2) = φ + B • fun z : ComplexModel n ↦ ‖z‖ ^ 2 := by
      funext y; simp
    have hψB : ContDiffAt ℝ 2 (B • fun z : ComplexModel n ↦ ‖z‖ ^ 2) z :=
      (hψ.const_smul B).contDiffAt.of_le h2
    rw [hsplit, leviForm_add (hφ.contDiffAt.of_le h2) hψB,
      leviForm_smul (hψ.contDiffAt.of_le h2), leviForm_norm_sq]
    have hbound (w : ComplexModel n) : -(B * ‖w‖ ^ 2) ≤ realHessian φ z w w := by
      have h := (iteratedFDeriv ℝ 2 φ z).le_opNorm ![w, w]
      have hn : ∏ i : Fin 2, ‖(![w, w] : Fin 2 → ComplexModel n) i‖ = ‖w‖ ^ 2 := by
        simp [Fin.prod_univ_two, sq]
      rw [hn] at h
      have h' : |realHessian φ z w w| ≤ B * ‖w‖ ^ 2 :=
        (h.trans (mul_le_mul_of_nonneg_right (hB z) (by positivity)))
      exact (abs_le.mp h').1
    have hIv : ‖Complex.I • v‖ = ‖v‖ := by simp [norm_smul]
    have h1 := hbound v
    have h3 := hbound (Complex.I • v)
    rw [hIv] at h3
    unfold leviForm
    nlinarith [sq_nonneg ‖v‖]
  refine ⟨hsm.contDiffOn, fun z _ ↦ ?_⟩
  exact ((isSmoothPshOn_of_psh (U := ⊤) hsm.contDiffOn
    (plurisubharmonicOn_of_levi_nonneg (hsm.of_le h2) isOpen_univ
      fun z _ v ↦ hlevi z v)).2.2 z trivial)

theorem continuous_mul_of_continuousOn {E F : Type*} [TopologicalSpace E]
    [NormedRing F] {U : Set E} (hU : IsOpen U) {a f : E → F} (ha : Continuous a)
    (hf : ContinuousOn f U) (haU : tsupport a ⊆ U) : Continuous fun z ↦ a z * f z := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ U
  · exact (ha.continuousAt.mul (hf.continuousAt (hU.mem_nhds hz)))
  · have hz' : z ∉ tsupport a := fun h ↦ hz (haU h)
    have hev : (fun z ↦ a z * f z) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hz'] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact continuousAt_const.congr_of_eventuallyEq hev

theorem mixedDensity_cons_eq {m : ℕ} (b : ComplexModel (m + 1) → ℝ)
    (g : Fin m → ComplexModel (m + 1) → ℝ) (z : ComplexModel (m + 1)) :
    mixedDensity (Fin.cons b g : Fin (m + 1) → ComplexModel (m + 1) → ℝ) z =
      (MixedHessian.mixedC b g z).re / Real.pi ^ (m + 1) := by
  unfold mixedDensity MixedHessian.mixedC
  congr 3
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp

theorem continuousOn_mixedC {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    {b : ComplexModel (m + 1) → ℝ} {g : Fin m → ComplexModel (m + 1) → ℝ}
    (hb : ContDiffOn ℝ ∞ b U) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U) :
    ContinuousOn (MixedHessian.mixedC b g) U := by
  have hmat (f : ComplexModel (m + 1) → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
      ContinuousOn (complexHessian f) U :=
    continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦
      MongeAmpere.continuousOn_complexHessian hf j k
  unfold MixedHessian.mixedC mixedCoefficient
  refine continuousOn_finsetSum _ fun σ _ ↦ ?_
  have : ContinuousOn (fun z ↦ (Matrix.of fun j k ↦
      (Fin.cons (complexHessian b z) (fun i ↦ complexHessian (g i) z) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (σ j) j k)) U := by
    refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
    have hslot (i : Fin (m + 1)) : ContinuousOn (fun z ↦
        (Fin.cons (complexHessian b z) (fun i ↦ complexHessian (g i) z) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) i j k) U := by
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simpa using (continuousOn_pi.1 (continuousOn_pi.1 (hmat b hb) j) k)
      · simpa using (continuousOn_pi.1 (continuousOn_pi.1 (hmat (g i) (hg i)) j) k)
    exact hslot (σ j)
  exact continuous_id.matrix_det.comp_continuousOn this

theorem continuous_of_continuousOn_of_eq_zero {E F : Type*} [TopologicalSpace E] [Zero F]
    [TopologicalSpace F] {U K : Set E} (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
    {f : E → F} (hf : ContinuousOn f U) (h0 : ∀ z ∉ K, f z = 0) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ U
  · exact hf.continuousAt (hU.mem_nhds hz)
  · have hz' : z ∉ K := fun h ↦ hz (hKU h)
    have hev : f =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds hz'] with y hy
      exact h0 y hy
    exact continuousAt_const.congr_of_eventuallyEq hev

/-- **Integration by parts in the first slot**, real form. -/
theorem integral_mul_mixedDensity_cons_swap {m : ℕ} {U : Opens (ComplexModel (m + 1))}
    {g : Fin m → ComplexModel (m + 1) → ℝ} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) U)
    {a b : ComplexModel (m + 1) → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    ∫ z, a z * mixedDensity (Fin.cons b g : Fin (m + 1) → ComplexModel (m + 1) → ℝ) z =
      ∫ z, b z * mixedDensity (Fin.cons a g : Fin (m + 1) → ComplexModel (m + 1) → ℝ) z := by
  have hC := MixedHessian.integral_mul_mixedC_swap_of_contDiffOn U.isOpen hg ha hb hac haU
  have hzeroC (k : ComplexModel (m + 1) → ℝ) (f : ComplexModel (m + 1) → ℝ)
      (hk : ∀ z ∉ tsupport a, k z = 0 ∨ MixedHessian.mixedC f g z = 0) :
      ∀ z ∉ tsupport a, (k z : ℂ) * MixedHessian.mixedC f g z = 0 := fun z hz ↦ by
    rcases hk z hz with h | h <;> simp [h]
  have hI (k f : ComplexModel (m + 1) → ℝ) (hk : ContDiffOn ℝ ∞ k U) (hf : ContDiffOn ℝ ∞ f U)
      (h0 : ∀ z ∉ tsupport a, k z = 0 ∨ MixedHessian.mixedC f g z = 0) :
      Integrable fun z ↦ (k z : ℂ) * MixedHessian.mixedC f g z := by
    have hc : Continuous fun z ↦ (k z : ℂ) * MixedHessian.mixedC f g z :=
      continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport a) haU
        ((Complex.continuous_ofReal.comp_continuousOn hk.continuousOn).mul
          (continuousOn_mixedC hf hg)) (hzeroC k f h0)
    exact hc.integrable_of_hasCompactSupport (hac.mono' fun z hz ↦ by
      by_contra h
      exact hz (hzeroC k f h0 z h))
  have hI1 := hI a b ha hb fun z hz ↦ Or.inl (image_eq_zero_of_notMem_tsupport hz)
  have hI2 := hI b a hb ha fun z hz ↦ Or.inr (MixedHessian.mixedC_eq_zero_of_notMem_tsupport hz)
  have hre (k f : ComplexModel (m + 1) → ℝ)
      (hkf : Integrable fun z ↦ (k z : ℂ) * MixedHessian.mixedC f g z) :
      ∫ z, k z * mixedDensity (Fin.cons f g : Fin (m + 1) → ComplexModel (m + 1) → ℝ) z =
        (∫ z, (k z : ℂ) * MixedHessian.mixedC f g z).re / Real.pi ^ (m + 1) := by
    simp only [mixedDensity_cons_eq]
    have h1 := integral_re hkf
    simp only [RCLike.re_to_complex] at h1
    rw [← h1, ← integral_div]
    congr 1
    funext z
    simp [Complex.mul_re, mul_div_assoc]
  rw [hre a b hI1, hre b a hI2, hC]

theorem mixedDensity_update_eq_cons {m : ℕ} (f : Fin (m + 1) → ComplexModel (m + 1) → ℝ)
    (i₀ : Fin (m + 1)) (c : ComplexModel (m + 1) → ℝ) (z : ComplexModel (m + 1)) :
    mixedDensity (Function.update f i₀ c) z =
      mixedDensity (Fin.cons c (fun i ↦ f (Equiv.swap 0 i₀ i.succ)) :
        Fin (m + 1) → ComplexModel (m + 1) → ℝ) z := by
  rw [← mixedDensity_perm (Function.update f i₀ c) (Equiv.swap 0 i₀)]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp
  · have hne : Equiv.swap 0 i₀ i.succ ≠ i₀ := by
      intro h
      have h' := congrArg (Equiv.swap 0 i₀) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
      exact Fin.succ_ne_zero _ h'
    simp [Function.update_of_ne hne]

/-- **Integration by parts in an arbitrary slot.** -/
theorem integral_mul_mixedDensity_update_swap {U : Opens (ComplexModel n)}
    {f : Fin n → ComplexModel n → ℝ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) (i₀ : Fin n)
    {a b : ComplexModel n → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hac : HasCompactSupport a) (haU : tsupport a ⊆ U) :
    ∫ z, a z * mixedDensity (Function.update f i₀ b) z =
      ∫ z, b z * mixedDensity (Function.update f i₀ a) z := by
  cases n with
  | zero => exact i₀.elim0
  | succ m =>
    simp only [mixedDensity_update_eq_cons f i₀]
    exact integral_mul_mixedDensity_cons_swap (fun i ↦ hf _) ha hb hac haU

/-- Linearity of the mixed density in one slot. -/
theorem mixedDensity_update_add_smul {f : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a b : ComplexModel n → ℝ} {z : ComplexModel n} (ha : ContDiffAt ℝ 2 a z)
    (hb : ContDiffAt ℝ 2 b z) (c : ℝ) :
    mixedDensity (Function.update f i₀ (fun y ↦ a y + c * b y)) z =
      mixedDensity (Function.update f i₀ a) z + c * mixedDensity (Function.update f i₀ b) z := by
  cases n with
  | zero => exact i₀.elim0
  | succ m =>
    simp only [mixedDensity_update_eq_cons f i₀, mixedDensity_cons_eq]
    have hsplit : (fun y ↦ a y + c * b y) = a + c • b := by funext y; simp
    rw [hsplit, MixedHessian.mixedC_add_left (b := c • b) ha (hb.const_smul c)]
    have hsm : MixedHessian.mixedC (c • b) (fun i ↦ f (Equiv.swap 0 i₀ i.succ)) z =
        (c : ℂ) * MixedHessian.mixedC b (fun i ↦ f (Equiv.swap 0 i₀ i.succ)) z := by
      simp only [MixedHessian.mixedC, MixedHessian.mixedCoefficient_cons, complexHessian_smul hb,
        Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [hsm, Complex.add_re, Complex.re_ofReal_mul]
    ring

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
