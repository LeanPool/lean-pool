/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FoldExtensionFiniteP
public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.GagliardoNirenbergSobolevFiniteP
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Coarse-graining support: Support.Sobolev.CubeEmbedding.LimitFiniteP

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Finite-`p` coordinate GNS input for cube localization

This module records the coordinate form of the ambient finite-`p`
Gagliardo--Nirenberg--Sobolev theorem.  It is the analytic estimate applied to
compactly supported smooth folded approximants in the cube localization step.
-/

namespace HCPolySupport

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

private theorem tendsto_eLpNorm_mul_of_norm_le_one
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {χ : α → ℝ} {F : ℕ → α → ℝ} {f : α → ℝ} (hχ : ∀ x, ‖χ x‖ ≤ 1)
    (hχm : AEStronglyMeasurable χ μ)
    (htend : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => χ x * F n x - χ x * f x) p μ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ n in Filter.atTop, eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
      ≤ eLpNorm (fun x => F n x - f x) p μ := by
    filter_upwards [htend.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with n hn
    have hd : AEStronglyMeasurable (fun x => F n x - f x) μ :=
      aestronglyMeasurable_of_eLpNorm_ne_top hn.ne
    refine eLpNorm_mono_ae ((hχm.mul hd).congr
      (Filter.Eventually.of_forall fun x => mul_sub _ _ _)) (Filter.Eventually.of_forall fun x
        => ?_)
    rw [show χ x * F n x - χ x * f x = χ x * (F n x - f x) by ring, norm_mul]
    simpa [mul_comm] using
      (mul_le_of_le_one_right (norm_nonneg (F n x - f x)) (hχ x))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htend
    (Filter.Eventually.of_forall fun n => zero_le) hbound

private theorem tendsto_eLpNorm_mul_of_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {χ : α → ℝ} {F : ℕ → α → ℝ} {f : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hχ : ∀ x, ‖χ x‖ ≤ C) (hχm : AEStronglyMeasurable χ μ)
    (htend : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => χ x * F n x - χ x * f x) p μ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ n in Filter.atTop, eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
      ≤ ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ := by
    filter_upwards [htend.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with n hn
    have hd : AEStronglyMeasurable (fun x => F n x - f x) μ :=
      aestronglyMeasurable_of_eLpNorm_ne_top hn.ne
    have hmono : eLpNorm (fun x => χ x * F n x - χ x * f x) p μ
        ≤ eLpNorm (C • fun x => F n x - f x) p μ :=
      eLpNorm_mono_ae ((hχm.mul hd).congr
        (Filter.Eventually.of_forall fun x => mul_sub _ _ _))
        (Filter.Eventually.of_forall fun x => by
        rw [show χ x * F n x - χ x * f x = χ x * (F n x - f x) by ring, norm_mul,
          Pi.smul_apply, smul_eq_mul, norm_mul,
          Real.norm_of_nonneg hC]
        exact mul_le_mul_of_nonneg_right (hχ x) (norm_nonneg _))
    refine hmono.trans ?_
    simpa [Real.enorm_eq_ofReal hC] using
      (eLpNorm_const_smul_le (c := C) (f := fun x => F n x - f x) (p := p) (μ := μ))
  have hscaled : Filter.Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds (ENNReal.ofReal C * 0)) :=
    ENNReal.Tendsto.const_mul htend (Or.inr ENNReal.ofReal_ne_top)
  have hscaled0 : Filter.Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun x => F n x - f x) p μ)
      Filter.atTop (nhds 0) := by
    simpa using hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled0
    (Filter.Eventually.of_forall fun n => zero_le) hbound

private theorem tendsto_eLpNorm_of_tendsto_sub_finiteLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {r : ℝ≥0∞} (hr : 1 ≤ r)
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hfin : eLpNorm f r μ ≠ ⊤)
    (h : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) r μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n) r μ) Filter.atTop (nhds (eLpNorm f r μ)) := by
  have hupper : ∀ n, eLpNorm (F n) r μ ≤
      eLpNorm f r μ + eLpNorm (fun x => F n x - f x) r μ := by
    intro n
    refine (le_of_eq ?_).trans (eLpNorm_add_le hr)
    congr 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hneg : ∀ n, eLpNorm (fun x => f x - F n x) r μ =
      eLpNorm (fun x => F n x - f x) r μ := by
    intro n
    rw [show (fun x => f x - F n x) = -(fun x => F n x - f x) by
      funext x
      simp only [Pi.neg_apply]
      ring, eLpNorm_neg]
  have hlower : ∀ n, eLpNorm f r μ - eLpNorm (fun x => F n x - f x) r μ ≤
      eLpNorm (F n) r μ := by
    intro n
    rw [tsub_le_iff_right]
    calc eLpNorm f r μ = eLpNorm (fun x => F n x + (f x - F n x)) r μ := by
          congr 1
          funext x
          ring
      _ ≤ eLpNorm (F n) r μ + eLpNorm (fun x => f x - F n x) r μ :=
        eLpNorm_add_le hr
      _ = eLpNorm (F n) r μ + eLpNorm (fun x => F n x - f x) r μ := by rw [hneg]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n => eLpNorm f r μ - eLpNorm (fun x => F n x - f x) r μ)
    (h := fun n => eLpNorm f r μ + eLpNorm (fun x => F n x - f x) r μ) ?_ ?_ hlower hupper
  · have ht := ENNReal.Tendsto.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => eLpNorm f r μ) Filter.atTop
        (nhds (eLpNorm f r μ))) h (Or.inl hfin)
    simpa using ht
  · simpa using Filter.Tendsto.const_add (eLpNorm f r μ) h

private theorem eLpNorm_mul_le_of_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f g : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, ‖g x‖ ≤ C) (hgm : AEStronglyMeasurable g μ)
    (hfm : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f x * g x) p μ ≤ ENNReal.ofReal C * eLpNorm f p μ := by
  have hmono : eLpNorm (fun x => f x * g x) p μ ≤
      eLpNorm (C • f) p μ := by
    refine eLpNorm_mono_ae (f := fun x => f x * g x) (g := C • f)
      (hfm.mul hgm) (Filter.Eventually.of_forall fun x => ?_)
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul,
      Real.norm_of_nonneg hC]
    calc
      ‖f x‖ * ‖g x‖ ≤ ‖f x‖ * C :=
        mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
      _ = C * ‖f x‖ := mul_comm _ _
  exact hmono.trans (by
    simpa [Real.enorm_eq_ofReal hC] using
      (eLpNorm_const_smul_le (c := C) (f := f) (p := p) (μ := μ)))

private theorem eLpNorm_cutoffGradient_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {χ f v dχ : α → ℝ} {D U V : ℝ≥0∞} {C : ℝ}
    (hD : D < ⊤) (hU : U < ⊤) (hV : V < ⊤) (hC : 0 ≤ C)
    (hχ : ∀ x, ‖χ x‖ ≤ 1) (hdχ : ∀ x, ‖dχ x‖ ≤ C)
    (hχm : AEStronglyMeasurable χ μ) (hf : AEStronglyMeasurable f μ)
    (hv : AEStronglyMeasurable v μ) (hdχm : AEStronglyMeasurable dχ μ)
    (hv_bound : eLpNorm v p μ ≤ D * V)
    (hf_bound : eLpNorm f p μ ≤ D * U) :
    eLpNorm (fun x => χ x * v x + f x * dχ x) p μ ≤
        D * V + ENNReal.ofReal C * (D * U) ∧
      eLpNorm (fun x => χ x * v x + f x * dχ x) p μ < ⊤ := by
  have hfirst : eLpNorm (fun x => χ x * v x) p μ ≤ D * V := by
    refine (eLpNorm_mono_ae (f := fun x => χ x * v x) (g := v)
      (hχm.mul hv) (Filter.Eventually.of_forall fun x => ?_)).trans hv_bound
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x)
  have hsecond : eLpNorm (fun x => f x * dχ x) p μ ≤
      ENNReal.ofReal C * (D * U) := by
    exact (eLpNorm_mul_le_of_norm_le hC hdχ hdχm hf).trans
      (mul_le_mul_right hf_bound _)
  have hsum : eLpNorm (fun x => χ x * v x + f x * dχ x) p μ ≤
      D * V + ENNReal.ofReal C * (D * U) :=
    (eLpNorm_add_le hp).trans (add_le_add hfirst hsecond)
  refine ⟨hsum, lt_of_le_of_lt hsum ?_⟩
  exact ENNReal.add_lt_top.2
    ⟨ENNReal.mul_lt_top hD hV,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top hD hU)⟩

private theorem tendsto_eLpNorm_cutoffProductRule
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {χ dχ f : α → ℝ} {F G : ℕ → α → ℝ} {g : α → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hχ : ∀ x, ‖χ x‖ ≤ 1)
    (hdχ : ∀ x, ‖dχ x‖ ≤ C)
    (hχm : AEStronglyMeasurable χ μ) (hdχm : AEStronglyMeasurable dχ μ)
    (hF_tend : Filter.Tendsto
      (fun n => eLpNorm (fun x => F n x - f x) p μ) Filter.atTop (nhds 0))
    (hG_tend : Filter.Tendsto
      (fun n => eLpNorm (fun x => G n x - g x) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => χ x * G n x + F n x * dχ x -
          (χ x * g x + f x * dχ x)) p μ)
      Filter.atTop (nhds 0) := by
  have hfirst : Filter.Tendsto
      (fun n => eLpNorm (fun x => χ x * (G n x - g x)) p μ)
      Filter.atTop (nhds 0) := by
    refine (tendsto_eLpNorm_mul_of_norm_le_one hχ hχm hG_tend).congr' ?_
    filter_upwards with n
    congr 1
    funext x
    ring
  have hsecond : Filter.Tendsto
      (fun n => eLpNorm (fun x => (F n x - f x) * dχ x) p μ)
      Filter.atTop (nhds 0) := by
    refine (tendsto_eLpNorm_mul_of_norm_le hC hdχ hdχm hF_tend).congr' ?_
    filter_upwards with n
    congr 1
    funext x
    ring
  have hsum : Filter.Tendsto
      (fun n => eLpNorm
        (fun x => χ x * (G n x - g x) + (F n x - f x) * dχ x) p μ)
      Filter.atTop (nhds 0) := by
    have hbound : ∀ n, eLpNorm
        (fun x => χ x * (G n x - g x) + (F n x - f x) * dχ x) p μ ≤
        eLpNorm (fun x => χ x * (G n x - g x)) p μ +
          eLpNorm (fun x => (F n x - f x) * dχ x) p μ := by
      intro n
      exact eLpNorm_add_le hp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hfirst.add hsecond) (fun n => zero_le) hbound
  refine hsum.congr' ?_
  filter_upwards with n
  apply eLpNorm_congr_ae
  filter_upwards with x
  ring

private theorem eLpNorm_limit_le_of_approximants
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {r s : ℝ≥0∞}
    (hr : 1 < r) {F : ℕ → α → ℝ} {f : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : AEStronglyMeasurable f μ)
    (htend : Filter.Tendsto
      (fun n => eLpNorm (fun x => F n x - f x) r μ) Filter.atTop (nhds 0))
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hbound : ∀ n, eLpNorm (F n) s μ ≤ b n)
    (hb : Filter.Tendsto b Filter.atTop (nhds B)) :
    eLpNorm f s μ ≤ B := by
  have htim : TendstoInMeasure μ F Filter.atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (ne_of_gt (zero_lt_one.trans hr)) htend
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := htim.exists_seq_tendsto_ae
  have hlim : eLpNorm f s μ ≤ Filter.liminf (fun j => eLpNorm (F (σ j)) s μ)
      Filter.atTop :=
    Lp.eLpNorm_lim_le_liminf_eLpNorm (fun j => hF (σ j)) f hf hσ_ae
  have hbσ := hb.comp hσ_mono.tendsto_atTop
  calc
    eLpNorm f s μ ≤ Filter.liminf (fun j => eLpNorm (F (σ j)) s μ) Filter.atTop := hlim
    _ ≤ Filter.liminf (fun j => b (σ j)) Filter.atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j => hbound (σ j))
    _ = B := hbσ.liminf_eq

private theorem boxCutoff_finiteLp_data
    {d : ℕ} (z hi : Vec d) (L : ℝ) (hL : 0 < L)
    (hhi : ∀ k, hi k = z k + L) :
    let χ : Vec d → ℝ := boxCutoff z hi (L / 2)
    ContDiff ℝ (⊤ : ℕ∞) χ ∧
      (∀ x ∈ Box z hi, χ x = 1) ∧ tsupport χ ⊆ Box3 z hi ∧
      (∀ x, ‖χ x‖ ≤ 1) ∧ (∀ x i, |fderiv ℝ χ x (basisVec i)| ≤ 32 / L) := by
  let χ : Vec d → ℝ := boxCutoff z hi (L / 2)
  have hℓ : 0 < L / 2 := by linarith
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := boxCutoff_contDiff
  have hχ_one : ∀ x ∈ Box z hi, χ x = 1 := by
    intro x hx
    exact boxCutoff_eq_one hℓ (Set.mem_Icc.2
      ⟨fun k => (Set.mem_univ_pi.1 hx k).1.le,
        fun k => (Set.mem_univ_pi.1 hx k).2.le⟩)
  have hχ_sub : tsupport χ ⊆ Box3 z hi := by
    have hsupp : Function.support χ ⊆
        Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2) :=
      fun x hx => by by_contra hxn; exact hx (boxCutoff_eq_zero hℓ hxn)
    refine (closure_minimal hsupp isClosed_Icc).trans ?_
    rw [Box3_eq_Box]
    intro x hx
    rw [Set.mem_Icc] at hx
    refine Set.mem_univ_pi.2 fun k => ?_
    exact ⟨by have := hx.1 k; have := hhi k; linarith,
      by have := hx.2 k; have := hhi k; linarith⟩
  have hχ_le1 : ∀ x, ‖χ x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (boxCutoff_nonneg x)]
    exact boxCutoff_le_one x
  have hχ_deriv : ∀ x i, |fderiv ℝ χ x (basisVec i)| ≤ 32 / L := by
    intro x i
    have h := boxCutoff_deriv_bound (lo := z) (hi := hi) hℓ x i
    have h2 : (16 : ℝ) / (L / 2) = 32 / L := by field_simp; ring
    simpa [χ, basisVec, h2] using h
  exact ⟨hχ_smooth, hχ_one, hχ_sub, hχ_le1, hχ_deriv⟩

private theorem tsupport_mul_subset_left
    {α : Type*} [TopologicalSpace α] {f g : α → ℝ} :
    tsupport (fun x => f x * g x) ⊆ tsupport f := by
  intro x hx
  change x ∈ closure (Function.support (fun y => f y * g y)) at hx
  apply closure_minimal ?_ (isClosed_tsupport f) hx
  intro y hy
  apply subset_tsupport f
  rw [Function.mem_support] at hy ⊢
  intro hzero
  apply hy
  simp only [hzero, zero_mul]

private theorem fderiv_support_subset_tsupport
    {d : ℕ} {f : Vec d → ℝ} {K : Set (Vec d)}
    (hsupport : tsupport f ⊆ K) (i : Fin d) :
    Function.support (fun x => fderiv ℝ f x (basisVec i)) ⊆ K := by
  intro x hx
  by_contra hxb
  have hx_nots : x ∉ tsupport f := fun hc => hxb (hsupport hc)
  have hzero : f =ᶠ[nhds x] 0 :=
    (isClosed_tsupport f).isOpen_compl.eventually_mem hx_nots |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  exact (Function.mem_support.1 hx) (by
    rw [Filter.EventuallyEq.fderiv_eq hzero]
    simp)

private theorem finiteLp_cutoffGradient_sum_bound
    {m : ℕ} (Cgns Cd C0 U : ℝ≥0∞) (L : ℝ)
    (Lnorm u : Fin (m + 1) → ℝ≥0∞)
    (hC0 : C0 = Cgns * Cd * ((((m + 1) * 32 : ℕ) : ℝ≥0∞)))
    (hcoordinate : ∀ i : Fin (m + 1),
      Lnorm i ≤ Cd * u i + ENNReal.ofReal (32 / L) * (Cd * U)) :
    Cgns * ∑ i : Fin (m + 1), Lnorm i ≤
      C0 * ((∑ i : Fin (m + 1), u i) + ENNReal.ofReal L⁻¹ * U) := by
  have hsum : ∑ i : Fin (m + 1), Lnorm i ≤
      Cd * (∑ i : Fin (m + 1), u i) +
        ((m + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (32 / L) * (Cd * U)) := by
    refine (Finset.sum_le_sum fun i _ => hcoordinate i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hofReal : ENNReal.ofReal (32 / L) =
      ((32 : ℕ) : ℝ≥0∞) * ENNReal.ofReal L⁻¹ := by
    rw [show (32 : ℝ) / L = 32 * L⁻¹ by ring, ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hN1 : (1 : ℝ≥0∞) ≤ ((((m + 1) * 32 : ℕ)) : ℝ≥0∞) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  refine (mul_le_mul_right hsum Cgns).trans ?_
  rw [hofReal, hC0]
  simp only [mul_add]
  refine add_le_add ?_ (le_of_eq ?_)
  · rw [show Cgns * (Cd * ∑ i : Fin (m + 1), u i) =
        (Cgns * Cd) * ∑ i : Fin (m + 1), u i by ring]
    exact mul_le_mul_left (le_mul_of_one_le_right' hN1) _
  · push_cast
    ring

private theorem finiteLp_cube_constant_data
    {m : ℕ} (p : FiniteLpExponent) :
    ∃ Cgns Cd C0 : ℝ≥0∞,
      Cgns = SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec (m + 1)))
        p.exponent.toNNReal ∧
      Cd = ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal) ∧
      C0 = Cgns * Cd * ((((m + 1) * 32 : ℕ) : ℝ≥0∞)) ∧ C0 < ⊤ := by
  let Cgns : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec (m + 1)))
      p.exponent.toNNReal : ℝ≥0∞)
  let Cd : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ (m + 1)) ^ (1 / p.exponent.toReal)
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
  have hCd_lt : Cd < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp_pos.le)
      (ENNReal.pow_ne_top (by simp))
  have hCgns_lt : Cgns < ⊤ := ENNReal.coe_lt_top
  let C0 : ℝ≥0∞ := Cgns * Cd * ((((m + 1) * 32 : ℕ) : ℝ≥0∞))
  have hC0_lt : C0 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hCgns_lt hCd_lt)
      (ENNReal.natCast_lt_top _)
  exact ⟨Cgns, Cd, C0, rfl, rfl, rfl, hC0_lt⟩

private theorem convexApproxSmoothW1p_smooth_gradient
    {d : ℕ} {Ω : Set (Vec d)} (hV : IsOpenBoundedConvexDomain Ω)
    (p : FiniteLpExponent) (u : W1pFunction Ω p.exponent)
    (x0 : Vec d) (r : ℝ) (hr : 0 < r) :
    (∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (W1pFunction.convexApproxSmoothW1p hV p.one_lt.le u x0 hr n).toFun) ∧
    (∀ n x i,
      (W1pFunction.convexApproxSmoothW1p hV p.one_lt.le u x0 hr n).grad x i =
        fderiv ℝ
          (W1pFunction.convexApproxSmoothW1p hV p.one_lt.le u x0 hr n).toFun x
          (basisVec i)) := by
  constructor
  · intro n
    simp only [W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
    exact contDiff_convexApproxSmoothRepresentative hV.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel) p.one_lt.le u.memLp hr
      (W1pFunction.unitConvexApproxScale_pos n)
  · intro n x i
    simp [W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]

private theorem hasCompactSupport_mul_of_vanishing_outside
    {d : ℕ} (χ g : Vec d → ℝ) (K : Set (Vec d))
    (hK : IsCompact K) (hzero : ∀ x, x ∉ K → χ x = 0) :
    HasCompactSupport (fun x => χ x * g x) := by
  apply HasCompactSupport.intro (K := K) hK
  intro x hx
  rw [hzero x hx, zero_mul]

private theorem midpointQuarterBall_subset_box3
    {d : ℕ} (z hi : Vec d) (L : ℝ) (hL : 0 < L)
    (hhi : ∀ k, hi k = z k + L) :
    Metric.closedBall (fun k => (z k + hi k) / 2) (L / 4) ⊆ Box3 z hi := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith : 0 ≤ L / 4)] at hx
  rw [Box3_eq_Box]
  refine Set.mem_univ_pi.2 fun k => ?_
  have hxk : dist (x k) ((z k + hi k) / 2) ≤ L / 4 := hx k
  rw [Real.dist_eq, abs_le] at hxk
  change 2 * z k - hi k < x k ∧ x k < 2 * hi k - z k
  rw [hhi k] at hxk ⊢
  constructor <;> nlinarith [hxk.1, hxk.2, hL]

private theorem box_subset_box3
    {d : ℕ} (z hi : Vec d) (L : ℝ) (hL : 0 < L)
    (hhi : ∀ k, hi k = z k + L) : Box z hi ⊆ Box3 z hi := by
  rw [Box3_eq_Box]
  intro x hx
  refine Set.mem_univ_pi.2 fun k => ?_
  have h := Set.mem_univ_pi.1 hx k
  change 2 * z k - hi k < x k ∧ x k < 2 * hi k - z k
  rw [hhi k] at h ⊢
  exact ⟨by linarith [h.1, hL], by linarith [h.2, hL]⟩

private theorem eLpNorm_le_of_cutoff_extension
    {d : ℕ} (z hi : Vec d) {p q : ℝ≥0∞}
    (u : W1pFunction (Box z hi) p) (χ f : Vec d → ℝ)
    (hBox : Box z hi ⊆ Box3 z hi)
    (hχ : ∀ x ∈ Box z hi, χ x = 1)
    (hf : f =ᵐ[volume.restrict (Box z hi)] u.toFun) :
    eLpNorm u.toFun q (volume.restrict (Box z hi)) ≤
      eLpNorm (fun x => χ x * f x) q (volume.restrict (Box3 z hi)) := by
  have hcut : (fun x => χ x * f x) =ᵐ[volume.restrict (Box z hi)] u.toFun := by
    filter_upwards [ae_restrict_mem (isOpen_Box z hi).measurableSet, hf] with x hx hfx
    rw [hχ x hx, one_mul, hfx]
  rw [← eLpNorm_congr_ae hcut]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hBox le_rfl)

/-- The operator norm of a scalar functional on `Vec d` is bounded by its
values on the coordinate basis. -/
theorem clm_norm_le_sum_basisVec_finiteLp {d : ℕ} (T : (Vec d) →L[ℝ] ℝ) :
    ‖T‖ ≤ ∑ i, ‖T (basisVec i)‖ := by
  refine T.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  have hx : x = ∑ i, x i • basisVec i := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, basisVec_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ j (fun i => x i)]
    simp
  calc
    ‖T x‖ = ‖T (∑ i, x i • basisVec i)‖ := by rw [← hx]
    _ = ‖∑ i, x i • T (basisVec i)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i, ‖x i • T (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖T (basisVec i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i, ‖x‖ * ‖T (basisVec i)‖ :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i, ‖T (basisVec i)‖) * ‖x‖ := by rw [← Finset.mul_sum]; ring

/-- Coordinate form of the ambient finite-`p` GNS inequality. -/
theorem gns_coord_finiteLp {d : ℕ} (hd : 0 < d) (p q : FiniteLpExponent)
    (hp : p.exponent.toReal < d)
    (hpq : (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcs : HasCompactSupport ψ) :
    eLpNorm ψ q.exponent (volume : Measure (Vec d))
      ≤ SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d)) p.exponent.toNNReal *
        ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) p.exponent
          (volume : Measure (Vec d)) := by
  refine (gns_contDiff_compactSupport_finiteLp hd p q hp hpq hψ hcs).trans
    (mul_le_mul_right ?_ _)
  have hcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hsum_eq : (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖)
      = ∑ i, (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) := by
    funext x
    rw [Finset.sum_apply]
  calc
    eLpNorm (fderiv ℝ ψ) p.exponent (volume : Measure (Vec d))
      ≤ eLpNorm (fun x => ∑ i, ‖fderiv ℝ ψ x (basisVec i)‖) p.exponent volume :=
        eLpNorm_mono hcont.aestronglyMeasurable (fun x =>
          (clm_norm_le_sum_basisVec_finiteLp (fderiv ℝ ψ x)).trans_eq
            (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).symm)
    _ ≤ ∑ i, eLpNorm (fun x => ‖fderiv ℝ ψ x (basisVec i)‖) p.exponent volume := by
        rw [hsum_eq]
        exact eLpNorm_sum_le
          p.one_lt.le
    _ = ∑ i, eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) p.exponent volume :=
        Finset.sum_congr rfl fun i _ =>
          eLpNorm_norm _ (hcont.clm_apply continuous_const).aestronglyMeasurable

private theorem gns_coordinate_bound_on_restricted_domain
    {d : ℕ} (hd : 0 < d) (p q : FiniteLpExponent)
    (hp : p.exponent.toReal < d)
    (hpq : (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcompact : HasCompactSupport ψ)
    {Ω : Set (Vec d)} (hψ_support : tsupport ψ ⊆ Ω)
    (hderiv_support : ∀ i, Function.support (fun x => fderiv ℝ ψ x (basisVec i)) ⊆ Ω)
    (Cgns : ℝ≥0∞)
    (hCgns : Cgns = SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec d))
      p.exponent.toNNReal) :
    eLpNorm ψ q.exponent (volume.restrict Ω) ≤ Cgns * ∑ i,
      eLpNorm (fun x => fderiv ℝ ψ x (basisVec i)) p.exponent
        (volume.restrict Ω) := by
  have hrestrict (f : Vec d → ℝ) (a : ℝ≥0∞)
      (hf : AEStronglyMeasurable f volume) (hsupport : Function.support f ⊆ Ω) :
      eLpNorm f a (volume.restrict Ω) = eLpNorm f a volume :=
    eLpNorm_restrict_eq_of_support_subset (p := a) hf hsupport
  rw [hrestrict _ _ hψ.continuous.aestronglyMeasurable
    ((subset_tsupport ψ).trans hψ_support)]
  rw [hCgns]
  refine (gns_coord_finiteLp hd p q hp hpq
    (hψ.of_le (by exact_mod_cast le_top)) hcompact).trans ?_
  refine mul_le_mul_right (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) _
  exact (hrestrict _ _ ((hψ.continuous_fderiv (by simp)).clm_apply
    continuous_const).aestronglyMeasurable
    (hderiv_support i)).symm

/-! ## The finite-exponent cube embedding -/

/-- The finite-exponent axis-cube Sobolev inequality.  The constant is chosen
before the cube, its scale, and the Sobolev function; its displayed formula
uses only the dimension and the input exponent. -/
theorem cubeSobolevEmbedding_finiteLp {d : ℕ} (hd : 0 < d)
    (p : FiniteLpExponent) (hp : p.exponent.toReal < d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (q : FiniteLpExponent),
        (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
        ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : W1pFunction (axisCube z L) p.exponent,
          eLpNorm u.toFun q.exponent (volumeMeasureOn (axisCube z L))
            ≤ (C : ℝ≥0∞) *
                ((∑ i : Fin d,
                      eLpNorm (fun x => u.grad x i) p.exponent
                        (volumeMeasureOn (axisCube z L)))
                  + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent
                      (volumeMeasureOn (axisCube z L))) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hd' : 0 < m + 1 := hd
  obtain ⟨Cgns, Cd, C0, hCgns, hCd, hC0, hC0_lt⟩ :=
    finiteLp_cube_constant_data (m := m) p
  have hp_pos : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne
  have hCd_lt : Cd < ⊤ := by
    rw [hCd]
    exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp_pos.le)
      (ENNReal.pow_ne_top (by simp))
  have hCgns_lt : Cgns < ⊤ := by
    rw [hCgns]
    exact ENNReal.coe_lt_top
  refine ⟨C0.toNNReal + 1, add_pos_of_nonneg_of_pos (zero_le) one_pos,
    fun q hpq z L hL u => ?_⟩
  set hi : Vec (m + 1) := fun k => z k + L with hhi
  have hlt : ∀ k, z k < hi k := fun k => by simp only [hhi]; linarith
  have hval : ∀ k, hi k = z k + L := fun k => by simp only [hhi]
  change eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤
    (↑(C0.toNNReal + 1) : ℝ≥0∞) *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi)))
  have hV : IsOpenBoundedConvexDomain (Box3 z hi) :=
    isOpenBoundedConvexDomain_Box _ _
  let : IsFiniteMeasure (volume.restrict (Box3 z hi)) :=
    hV.isFiniteMeasure_restrict_volume
  let : IsLocallyFiniteMeasure (volume.restrict (Box3 z hi)) := inferInstance
  set Ext := foldExtensionFiniteP z hi hlt p u
  set Eu : W1pFunction (Box3 z hi) p.exponent := Ext.Eu with hEu
  have hℓ : (0 : ℝ) < L / 2 := by linarith
  set χ : Vec (m + 1) → ℝ := boxCutoff z hi (L / 2) with hχ
  have ⟨hχ_smooth, hχ_one, hχ_sub, hχ_le1, hχ_deriv⟩ :=
    boxCutoff_finiteLp_data z hi L hL hval
  set x0 : Vec (m + 1) := fun k => (z k + hi k) / 2 with hx0
  set r : ℝ := L / 4 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hball : Metric.closedBall x0 r ⊆ Box3 z hi := by
    simpa [x0, r, hrdef] using midpointQuarterBall_subset_box3 z hi L hL hval
  set A : ℕ → W1pFunction (Box3 z hi) p.exponent :=
    W1pFunction.convexApproxSmoothW1p hV p.one_lt.le Eu x0 hr
  have hA_properties := convexApproxSmoothW1p_smooth_gradient hV p Eu x0 r hr
  have hA_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n).toFun := by
    simpa [A] using hA_properties.1
  have hA_grad : ∀ n x i, (A n).grad x i =
      fderiv ℝ ((A n).toFun) x (basisVec i) := by
    simpa [A] using hA_properties.2
  set ψ : ℕ → Vec (m + 1) → ℝ := fun n x => χ x * (A n).toFun x
  have hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) :=
    fun n => hχ_smooth.mul (hA_smooth n)
  have hψ_cptsupp : ∀ n, HasCompactSupport (ψ n) := by
    intro n
    exact hasCompactSupport_mul_of_vanishing_outside χ (A n).toFun
      (Set.Icc (fun k => z k - L / 2) (fun k => hi k + L / 2)) isCompact_Icc
      (fun x hx => by rw [hχ, boxCutoff_eq_zero hℓ hx])
  have hψ_supp : ∀ n, tsupport (ψ n) ⊆ Box3 z hi := by
    intro n
    exact (tsupport_mul_subset_left).trans hχ_sub
  have hψ_dsupp : ∀ n i,
      Function.support (fun x => fderiv ℝ (ψ n) x (basisVec i)) ⊆ Box3 z hi :=
    fun n i => fderiv_support_subset_tsupport (hψ_supp n) i
  set a : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (ψ n) q.exponent (volume.restrict (Box3 z hi))
  set b : ℕ → ℝ≥0∞ := fun n => Cgns * ∑ i,
    eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i)) p.exponent
      (volume.restrict (Box3 z hi))
  have hab : ∀ n, a n ≤ b n := by
    intro n
    change eLpNorm (ψ n) q.exponent (volume.restrict (Box3 z hi)) ≤ b n
    simpa [a, b] using
      gns_coordinate_bound_on_restricted_domain hd' p q hp hpq
        (hψ_smooth n) (hψ_cptsupp n)
        (hψ_supp n) (hψ_dsupp n) Cgns hCgns
  have hA_tend := W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    hV p.one_lt.le p.lt_top.ne Eu hball hr
  have hψ_tend : Filter.Tendsto (fun n =>
      eLpNorm (fun x => ψ n x - χ x * Eu.toFun x) p.exponent
        (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
    simpa [ψ, volumeMeasureOn] using
      tendsto_eLpNorm_mul_of_norm_le_one hχ_le1 hχ_smooth.continuous.aestronglyMeasurable hA_tend
  have hDform : ∀ n x i, fderiv ℝ (ψ n) x (basisVec i) =
      χ x * (A n).grad x i + (A n).toFun x * fderiv ℝ χ x (basisVec i) := by
    intro n x i
    rw [show ψ n = χ * (A n).toFun by rfl,
      fderiv_mul ((hχ_smooth.differentiable (by simp)) x)
        (((hA_smooth n).differentiable (by simp)) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, hA_grad, hχ]
  set G : Fin (m + 1) → Vec (m + 1) → ℝ := fun i x =>
    χ x * Eu.grad x i + Eu.toFun x * fderiv ℝ χ x (basisVec i)
  have hgrad_tend : ∀ i, Filter.Tendsto (fun n =>
      eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i) - G i x) p.exponent
        (volume.restrict (Box3 z hi))) Filter.atTop (nhds 0) := by
    intro i
    have hAgrad := W1pFunction.tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
      hV p.one_lt.le p.lt_top.ne Eu hball hr i
    have hraw := tendsto_eLpNorm_cutoffProductRule p.one_lt.le
      (by positivity : (0 : ℝ) ≤ 32 / L) hχ_le1
      (fun x => by rw [Real.norm_eq_abs]; exact hχ_deriv x i)
      hχ_smooth.continuous.aestronglyMeasurable
      (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable) hA_tend hAgrad
    simpa only [hDform, G] using hraw
  have hG_control : ∀ i,
      eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) ≤
          Cd * eLpNorm (fun x => u.grad x i) p.exponent
            (volume.restrict (Box z hi)) +
            ENNReal.ofReal (32 / L) *
              (Cd * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) ∧
        eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)) < ⊤ := by
    intro i
    change eLpNorm (fun x => χ x * Eu.grad x i +
        Eu.toFun x * fderiv ℝ χ x (basisVec i)) p.exponent
        (volume.restrict (Box3 z hi)) ≤ _ ∧ _
    exact eLpNorm_cutoffGradient_le p.one_lt.le hCd_lt
      u.memLp.eLpNorm_lt_top (u.grad_memLp i).eLpNorm_lt_top
      (by positivity) hχ_le1 (fun x => by
        rw [Real.norm_eq_abs]
        exact hχ_deriv x i)
      hχ_smooth.continuous.aestronglyMeasurable Eu.memLp.aestronglyMeasurable
      (Eu.grad_memLp i).aestronglyMeasurable
      (((hχ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable)
      (by simpa only [hCd] using Ext.grad_eLpNorm_le i)
      (by simpa only [hCd] using Ext.eLpNorm_le)
  set binf : ℝ≥0∞ := Cgns * ∑ i,
    eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi))
  have hb_tend : Filter.Tendsto b Filter.atTop (nhds binf) := by
    change Filter.Tendsto
      (fun n => Cgns * ∑ i, eLpNorm (fun x => fderiv ℝ (ψ n) x (basisVec i))
        p.exponent (volume.restrict (Box3 z hi))) Filter.atTop
      (nhds (Cgns * ∑ i, eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi))))
    refine ENNReal.Tendsto.const_mul (tendsto_finsetSum _ fun i _ => ?_)
      (Or.inr hCgns_lt.ne)
    exact tendsto_eLpNorm_of_tendsto_sub_finiteLp p.one_lt.le
      (hG_control i).2.ne (hgrad_tend i)
  have hBox_sub : Box z hi ⊆ Box3 z hi := box_subset_box3 z hi L hL hval
  have hL1 : eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤
      eLpNorm (fun x => χ x * Eu.toFun x) q.exponent
        (volume.restrict (Box3 z hi)) :=
    eLpNorm_le_of_cutoff_extension z hi u χ Eu.toFun hBox_sub hχ_one Ext.toFun_ae
  have hL2 : eLpNorm (fun x => χ x * Eu.toFun x) q.exponent
      (volume.restrict (Box3 z hi)) ≤ binf :=
    eLpNorm_limit_le_of_approximants p.one_lt
      (fun j => (hψ_smooth j).continuous.aestronglyMeasurable)
      (hχ_smooth.continuous.aestronglyMeasurable.mul Eu.memLp.aestronglyMeasurable)
      hψ_tend (fun n => by simpa [a] using hab n) hb_tend
  have hL4 : binf ≤ C0 *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) := by
    change Cgns * ∑ i, eLpNorm (G i) p.exponent
      (volume.restrict (Box3 z hi)) ≤ _
    exact finiteLp_cutoffGradient_sum_bound Cgns Cd C0
      (eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) L
      (fun i => eLpNorm (G i) p.exponent (volume.restrict (Box3 z hi)))
      (fun i => eLpNorm (fun x => u.grad x i) p.exponent
        (volume.restrict (Box z hi))) hC0
      (fun i => by simpa using (hG_control i).1)
  have hmain : eLpNorm u.toFun q.exponent (volume.restrict (Box z hi)) ≤ C0 *
      ((∑ i, eLpNorm (fun x => u.grad x i) p.exponent (volume.restrict (Box z hi))) +
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun p.exponent (volume.restrict (Box z hi))) :=
    hL1.trans (hL2.trans hL4)
  have hC0le : C0 ≤ (↑(C0.toNNReal + 1) : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hC0_lt.ne, ENNReal.coe_one]
    exact le_self_add
  exact hmain.trans (mul_le_mul_left hC0le _)

end

end HCPolySupport
