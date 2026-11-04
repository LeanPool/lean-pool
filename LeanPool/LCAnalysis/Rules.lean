/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

public import LeanPool.LCAnalysis.Higher

/-!
# Rules of calculus: products and Taylor's formula

Glöckner–Neeb, *Infinite-Dimensional Lie Groups* (arXiv:2602.12362), §1.3–1.4.

* Continuous bilinear maps `β : A × B → F` are smooth, with
  `dβ((a, b), (h, k)) = β(a, k) + β(h, b)`; hence the product rule
  `d(β(f, g))(x)(h) = β(f x, dg(x)(h)) + β(df(x)(h), g x)`.
* Taylor's formula with integral remainder, in weak form (no completeness assumption on `F`):
  for `f` of class `C^{k+1}` and every continuous linear functional `ψ`,
  `ψ (f (x + h)) = ∑_{j ≤ k} ψ (d^(j) f (x, h, …, h)) / j!
    + ∫₀¹ (1 - t)^k / k! · ψ (d^(k+1) f (x + t h, h, …, h)) dt`.
* The second-order chain rule (`dMB_dMB_comp`):
  `d²(g ∘ τ)_y(a, b) = d²g_{τ y}(dτ_y a, dτ_y b) + dg_{τ y}(d²τ_y(a, b))`.
-/

@[expose] public section

open Set Filter Function
open scoped Topology Nat

noncomputable section

namespace LCAnalysis

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-! ### Bilinear maps and the product rule -/

section Bilinear

variable {A B : Type u} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A]
  [AddCommGroup B] [Module ℝ B] [TopologicalSpace B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B] [T2Space B]
  (β : A →ₗ[ℝ] B →ₗ[ℝ] F) (hβ : Continuous fun p : A × B ↦ β p.1 p.2)
include hβ

omit [LocallyConvexSpace ℝ F] [T2Space F] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A] [TopologicalSpace B]
    [IsTopologicalAddGroup B] [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B] [T2Space B] hβ in
theorem hasDirDerivAt_bilin (p q : A × B) :
    HasDirDerivAt (fun p : A × B ↦ β p.1 p.2) p q (β p.1 q.2 + β q.1 p.2) := by
  have key : ∀ t : ℝ, t ≠ 0 → t⁻¹ • (β (p + t • q).1 (p + t • q).2 - β p.1 p.2) =
      β p.1 q.2 + β q.1 p.2 + t • β q.1 q.2 := by
    intro t ht
    have : β (p + t • q).1 (p + t • q).2 - β p.1 p.2 =
        t • (β p.1 q.2 + β q.1 p.2 + t • β q.1 q.2) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply]
      module
    rw [this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hc : Continuous fun t : ℝ ↦ β p.1 q.2 + β q.1 p.2 + t • β q.1 q.2 := by fun_prop
  have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_smul, add_zero] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  exact (key t ht).symm

/-- Continuous bilinear maps are `C^k` for every `k`. -/
theorem contDiffMBOn_bilin (k : ℕ) : ContDiffMBOn k (fun p : A × B ↦ β p.1 p.2) univ := by
  induction k with
  | zero => exact hβ.continuousOn
  | succ k ih =>
    have heq : dMB (fun p : A × B ↦ β p.1 p.2) =
        fun r ↦ β r.1.1 r.2.2 + β r.2.1 r.1.2 :=
      funext fun r ↦ (hasDirDerivAt_bilin β r.1 r.2).dMB_eq
    refine ⟨hβ.continuousOn, fun p _ q ↦ ?_, ?_⟩
    · rw [heq]; exact hasDirDerivAt_bilin β p q
    · rw [heq, univ_prod_univ]
      let L₁ : (A × B) × (A × B) →L[ℝ] A × B :=
        ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.fst ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.snd ℝ _ _))
      let L₂ : (A × B) × (A × B) →L[ℝ] A × B :=
        ((ContinuousLinearMap.fst ℝ A B).comp (ContinuousLinearMap.snd ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ A B).comp (ContinuousLinearMap.fst ℝ _ _))
      have h₁ := ContDiffMBOn.comp_clm L₁ isOpen_univ ih
      have h₂ := ContDiffMBOn.comp_clm L₂ isOpen_univ ih
      rw [preimage_univ] at h₁ h₂
      exact h₁.add isOpen_univ h₂

/-- Product rule: `x ↦ β (f x) (g x)` is `C^k` if `f` and `g` are. -/
theorem ContDiffMBOn.bilin {k : ℕ} {f : E → A} {g : E → B} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) :
    ContDiffMBOn k (fun x ↦ β (f x) (g x)) U :=
  ContDiffMBOn.comp hU isOpen_univ (contDiffMBOn_bilin β hβ k) (hf.prodMk hU hg)
    (mapsTo_univ _ _)

/-- Product rule: `d(β(f, g))(x)(h) = β(f x, dg(x)(h)) + β(df(x)(h), g x)`. -/
theorem ContDiffMBOn.dMB_bilin {f : E → A} {g : E → B} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 1 f U) (hg : ContDiffMBOn 1 g U) {x : E} (hx : x ∈ U) (h : E) :
    dMB (fun x ↦ β (f x) (g x)) (x, h) = β (f x) (dMB g (x, h)) + β (dMB f (x, h)) (g x) := by
  have hc := ContDiffMBOn.dMB_comp (g := fun p : A × B ↦ β p.1 p.2) isOpen_univ
    (contDiffMBOn_bilin β hβ 1) (hf.prodMk hU hg) (mapsTo_univ _ _) hx h
  have hp : dMB (fun x ↦ (f x, g x)) (x, h) = (dMB f (x, h), dMB g (x, h)) :=
    ((hf.2.1 x hx h).prodMk (hg.2.1 x hx h)).dMB_eq
  rw [hp, (hasDirDerivAt_bilin β _ _).dMB_eq] at hc
  exact hc

end Bilinear

/-! ### Taylor's formula -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] [ContinuousSMul ℝ F] in
/-- Along a line, `t ↦ ψ (d^(j) f (x + t h, h, …, h))` has derivative
`ψ (d^(j+1) f (x + t h, h, …, h))`. -/
theorem ContDiffMBOn.hasDerivAt_iteratedDMB_line {k j : ℕ} {f : E → F} {U : Set E}
    (hf : ContDiffMBOn k f U) (hj : j < k) {x h : E} {t : ℝ} (ht : x + t • h ∈ U)
    (ψ : F →L[ℝ] ℝ) :
    HasDerivAt (fun s : ℝ ↦ ψ (iteratedDMB j f (x + s • h, fun _ ↦ h)))
      (ψ (iteratedDMB (j + 1) f (x + t • h, fun _ ↦ h))) t :=
  (hf.hasContIterDerivOn.1 j hj _ ht (fun _ ↦ h)).hasDerivAt_clm ψ

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
    [T2Space F] [ContinuousSMul ℝ F] in
theorem ContDiffMBOn.continuousOn_iteratedDMB_line {k j : ℕ} {f : E → F} {U : Set E}
    (hf : ContDiffMBOn k f U) (hj : j ≤ k) {x h : E} {s : Set ℝ}
    (hs : ∀ t ∈ s, x + t • h ∈ U) (ψ : F →L[ℝ] ℝ) :
    ContinuousOn (fun t : ℝ ↦ ψ (iteratedDMB j f (x + t • h, fun _ ↦ h))) s :=
  ψ.continuous.comp_continuousOn ((hf.hasContIterDerivOn.2 j hj).comp (by fun_prop)
    fun t ht ↦ ⟨hs t ht, mem_univ _⟩)

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
    [T2Space F] [ContinuousSMul ℝ F] in
/-- Taylor's formula with integral remainder, in weak form. -/
theorem ContDiffMBOn.taylor {f : E → F} {U : Set E} {x h : E}
    (hxh : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) (ψ : F →L[ℝ] ℝ) : ∀ (k : ℕ),
    ContDiffMBOn (k + 1) f U →
    ψ (f (x + h)) = ∑ j ∈ Finset.range (k + 1), (j ! : ℝ)⁻¹ * ψ (iteratedDMB j f (x, fun _ ↦ h)) +
      ∫ t in (0 : ℝ)..1, (1 - t) ^ k / k ! * ψ (iteratedDMB (k + 1) f (x + t • h, fun _ ↦ h)) := by
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  intro k
  induction k with
  | zero =>
    intro hf
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ ↦ ψ (iteratedDMB 0 f (x + s • h, fun _ ↦ h)))
      (fun t ht ↦ hf.hasDerivAt_iteratedDMB_line (Nat.zero_lt_one) (hxh t (hI ▸ ht)) ψ)
      ((hf.continuousOn_iteratedDMB_line le_rfl (hI ▸ hxh) ψ).intervalIntegrable)
    simp only [iteratedDMB_zero, one_smul, zero_smul, add_zero] at this
    simp only [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
      pow_zero, div_one, iteratedDMB_zero] at this ⊢
    rw [this]
    abel
  | succ k ih =>
    intro hf
    rw [ih hf.of_succ, Finset.sum_range_succ _ (k + 1), add_assoc]
    congr 1
    have hk : ((k + 1) ! : ℝ) = (k + 1) * k ! := by push_cast [Nat.factorial_succ]; ring
    have hk0 : (k ! : ℝ) ≠ 0 := by positivity
    have hu : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ -((1 - s) ^ (k + 1) / (k + 1) !))
        ((1 - t) ^ k / k !) t := by
      intro t _
      have := (((hasDerivAt_id t).const_sub 1).pow (k + 1)).div_const ((k + 1) ! : ℝ) |>.neg
      refine this.congr_deriv ?_
      simp only [id, hk]
      field_simp
      push_cast
      ring
    have hv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ ψ (iteratedDMB (k + 1) f (x + s • h, fun _ ↦ h)))
          (ψ (iteratedDMB (k + 1 + 1) f (x + t • h, fun _ ↦ h))) t :=
      fun t ht ↦ hf.hasDerivAt_iteratedDMB_line (by omega) (hxh t (hI ▸ ht)) ψ
    have hu' : IntervalIntegrable (fun t : ℝ ↦ (1 - t) ^ k / k !) MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ ↦ (1 - t) ^ k / k !).intervalIntegrable 0 1
    have hv' : IntervalIntegrable
        (fun t : ℝ ↦ ψ (iteratedDMB (k + 1 + 1) f (x + t • h, fun _ ↦ h)))
        MeasureTheory.volume 0 1 :=
      (hf.continuousOn_iteratedDMB_line le_rfl (hI ▸ hxh) ψ).intervalIntegrable
    have := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
    simp only [neg_mul, intervalIntegral.integral_neg, sub_self,
      zero_pow (Nat.succ_ne_zero k), zero_div, neg_zero, zero_mul, zero_sub, one_pow, zero_smul,
      add_zero, sub_zero, one_pow, one_div, neg_neg] at this
    linarith

/-! ### The second-order chain rule -/

section SecondOrder

variable {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']

/-- **Second-order chain rule**:
`d²(g ∘ τ)_y(a, b) = d²g_{τ y}(dτ_y a, dτ_y b) + dg_{τ y}(d²τ_y(a, b))`. -/
theorem dMB_dMB_comp {g : E' → F} {τ : E → E'} {U : Set E} {V : Set E'} (hU : IsOpen U)
    (hV : IsOpen V) (hg : ContDiffMBOn 2 g V) (hτ : ContDiffMBOn 2 τ U) (hUV : MapsTo τ U V)
    {y : E} (hy : y ∈ U) (a b : E) :
    dMB (dMB (g ∘ τ)) ((y, b), (a, 0)) =
      dMB (dMB g) ((τ y, dMB τ (y, b)), (dMB τ (y, a), 0)) +
        dMB g (τ y, dMB (dMB τ) ((y, b), (a, 0))) := by
  have hU2 : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hV2 : IsOpen (V ×ˢ (univ : Set E')) := hV.prod isOpen_univ
  have hτ1 : ContDiffMBOn 1 τ U := hτ.of_le (by norm_num)
  have hg1 : ContDiffMBOn 1 g V := hg.of_le (by norm_num)
  have hdg : ContDiffMBOn 1 (dMB g) (V ×ˢ univ) := hg.2.2
  have hdτ : ContDiffMBOn 1 (dMB τ) (U ×ˢ univ) := hτ.2.2
  have hfst : ContDiffMBOn 1 (τ ∘ ContinuousLinearMap.fst ℝ E E) (U ×ˢ univ) :=
    hτ1.comp hU2 hU ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn 1 _) fun p hp ↦ hp.1
  -- `Φ (y', b') = (τ y', dτ_{y'} b')`
  set Φ : E × E → E' × E' := fun p ↦ ((τ ∘ ContinuousLinearMap.fst ℝ E E) p, dMB τ p)
  have hΦ : ContDiffMBOn 1 Φ (U ×ˢ univ) := ContDiffMBOn.prodMk hU2 hfst hdτ
  have hΦmaps : MapsTo Φ (U ×ˢ univ) (V ×ˢ univ) := fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩
  have hp : (y, b) ∈ U ×ˢ (univ : Set E) := ⟨hy, mem_univ b⟩
  -- first-order chain rule, near `(y, b)`
  have hev : dMB (g ∘ τ) =ᶠ[𝓝 (y, b)] dMB g ∘ Φ :=
    Filter.eventuallyEq_of_mem (hU2.mem_nhds hp) fun q hq ↦
      ContDiffMBOn.dMB_comp hV hg1 hτ1 hUV hq.1 q.2
  rw [dMB_congr_of_eventuallyEq hev, ContDiffMBOn.dMB_comp hV2 hdg hΦ hΦmaps hp]
  -- the derivative of `Φ`
  have hdfst : dMB (τ ∘ ContinuousLinearMap.fst ℝ E E) ((y, b), (a, 0)) = dMB τ (y, a) := by
    rw [ContDiffMBOn.dMB_comp hU hτ1 ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn 1
      (U ×ˢ univ)) (fun p (hp : p ∈ U ×ˢ (univ : Set E)) ↦ hp.1) hp,
      ((ContinuousLinearMap.fst ℝ E E).hasDirDerivAt _ _).dMB_eq]
    rfl
  have hdΦ : dMB Φ ((y, b), (a, 0)) = (dMB τ (y, a), dMB (dMB τ) ((y, b), (a, 0))) := by
    rw [((hfst.hasDirDerivAt hp (a, 0)).prodMk (hdτ.hasDirDerivAt hp (a, 0))).dMB_eq, hdfst]
  have hsplit : (dMB τ (y, a), dMB (dMB τ) ((y, b), (a, 0))) =
      (dMB τ (y, a), (0 : E')) + (0, dMB (dMB τ) ((y, b), (a, 0))) := by simp
  have hΦy : Φ (y, b) = (τ y, dMB τ (y, b)) := rfl
  rw [hdΦ, hsplit, hdg.dMB_add hV2 (hΦmaps hp), hΦy, dMB_slice₂]
  obtain ⟨L, hL⟩ := hg1.exists_clm hV (hUV hy)
  have hfun : (fun w ↦ dMB g (τ y, w)) = ⇑L := funext fun w ↦ (hL w).symm
  rw [hfun, (L.hasDirDerivAt _ _).dMB_eq, hL]

end SecondOrder

end LCAnalysis
