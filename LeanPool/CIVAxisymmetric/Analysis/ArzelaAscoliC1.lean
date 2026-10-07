/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# `C¹` compactness for functions with bounded first and second derivatives

If a sequence of smooth functions on `ℝ × ℝ` and its gradients are uniformly bounded on a
convex compact set `K`, and the second derivatives are also uniformly bounded on `K`, then a
subsequence converges uniformly on `K` together with its gradients, and the limit is
differentiable on the interior of `K` with derivative the limit of the gradients.

The two derivative bounds make both the functions and their gradients uniformly Lipschitz on
`K` (via the mean value inequality), hence equicontinuous; Arzelà–Ascoli then extracts a
uniformly convergent subsequence of the functions, and a further subsequence along which the
gradients also converge uniformly. Identifying the limit of the gradients as the derivative of
the limit function is the content of the uniform-limit differentiation theorem.
-/

public section

open Filter Topology NNReal BoundedContinuousFunction

namespace CIV

/-- A subsequence along which a uniformly `L`-bounded, `C²`-bounded sequence of functions on
`ℝ × ℝ` converges together with its gradients, uniformly on a convex compact set `K`, to a
limit function which is differentiable on the interior of `K` with derivative the limit of the
gradients. -/
theorem exists_subseq_tendstoUniformlyOn_c1 (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKconv : Convex ℝ K)
    (V : ℕ → (ℝ × ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (V n))
    (hV : ∀ n, ∀ y ∈ K, |V n y| ≤ L)
    (hDV : ∀ n, ∀ y ∈ K, ‖fderiv ℝ (V n) y‖ ≤ L)
    (hD2V : ∀ n, ∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ (V n)) y‖ ≤ L) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Vlim : (ℝ × ℝ) → ℝ, ∃ DVlim : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ),
      TendstoUniformlyOn (fun n => V (φ n)) Vlim atTop K ∧
      TendstoUniformlyOn (fun n => fderiv ℝ (V (φ n))) DVlim atTop K ∧
      (∀ y ∈ K, |Vlim y| ≤ L) ∧ (∀ y ∈ K, ‖DVlim y‖ ≤ L) ∧
      (∀ y ∈ interior K, HasFDerivAt Vlim (DVlim y) y) := by
  classical
  have hKcs : CompactSpace (↥K) := isCompact_iff_compactSpace.mp hK
  have hd1 : ∀ n, Differentiable ℝ (V n) ∧ ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (V n)) :=
    fun n => contDiff_infty_iff_fderiv.mp (hsmooth n)
  have hd2 : ∀ n, Differentiable ℝ (fderiv ℝ (V n)) :=
    fun n => (contDiff_infty_iff_fderiv.mp (hd1 n).2).1
  -- Step 1: Arzelà–Ascoli for `V`, giving a subsequence `φ` with `V (φ n) → Vlim` uniformly on `K`.
  obtain ⟨φ, hφmono, Vlim, hVunif⟩ :
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Vlim : (ℝ × ℝ) → ℝ,
        TendstoUniformlyOn (fun n => V (φ n)) Vlim atTop K := by
    have hLip : ∀ n, LipschitzOnWith (Real.toNNReal L) (V n) K :=
      fun n => Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => (hd1 n).1 x)
        (fun x hx => (Real.le_toNNReal_iff_coe_le hL).mpr (by rw [coe_nnnorm]; exact hDV n x hx))
        hKconv
    have hLipK : ∀ n, LipschitzWith (Real.toNNReal L) (K.domRestrict (V n)) :=
      fun n => (hLip n).to_restrict
    set Vc : ℕ → C(↥K, ℝ) := fun n =>
      ⟨K.domRestrict (V n), by
        rw [Set.domRestrict_eq]
        exact (hd1 n).1.continuous.comp continuous_subtype_val⟩ with hVc
    set Vb : ℕ → (↥K →ᵇ ℝ) := fun n => mkOfCompact (Vc n) with hVb
    have hVbcoe : ∀ n, (Vb n : ↥K → ℝ) = K.domRestrict (V n) := fun n => rfl
    have hVbLip : ∀ n, LipschitzWith (Real.toNNReal L) (Vb n : ↥K → ℝ) := by
      intro n; rw [hVbcoe]; exact hLipK n
    have hEquiRange : Equicontinuous ((↑) : Set.range Vb → ↥K → ℝ) := by
      have hstep : ∀ a : Set.range Vb, LipschitzWith (Real.toNNReal L)
          ((a : ↥K →ᵇ ℝ) : ↥K → ℝ) := by
        rintro ⟨f, n, rfl⟩
        exact hVbLip n
      exact (LipschitzWith.uniformEquicontinuous
        (fun a : Set.range Vb => ((a : ↥K →ᵇ ℝ) : ↥K → ℝ)) (Real.toNNReal L)
        hstep).equicontinuous
    have hin_s : ∀ (f : ↥K →ᵇ ℝ) (x : ↥K), f ∈ Set.range Vb →
        f x ∈ Metric.closedBall (0 : ℝ) L := by
      rintro f x ⟨n, rfl⟩
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact hV n x x.2
    have hcompact : IsCompact (closure (Set.range Vb)) :=
      arzela_ascoli (Metric.closedBall (0 : ℝ) L) (isCompact_closedBall _ _) (Set.range Vb)
        hin_s hEquiRange
    have hmemc : ∀ n, Vb n ∈ closure (Set.range Vb) := fun n => subset_closure ⟨n, rfl⟩
    obtain ⟨Vlimb, -, φ, hφmono, hφtendsto⟩ := hcompact.tendsto_subseq hmemc
    refine ⟨φ, hφmono, fun x => if hx : x ∈ K then Vlimb ⟨x, hx⟩ else 0, ?_⟩
    have huniform : TendstoUniformly (fun n => (Vb (φ n) : ↥K → ℝ)) (Vlimb : ↥K → ℝ) atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hφtendsto
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    intro u hu
    filter_upwards [huniform u hu] with n hn x
    simpa [hVbcoe, Set.domRestrict_eq, x.2] using hn x
  -- Step 2: Arzelà–Ascoli for the gradients along the `φ`-subsequence, giving a further
  -- subsequence `ψ` with `fderiv (V (φ (ψ n))) → DVlim` uniformly on `K`.
  obtain ⟨ψ, hψmono, DVlim, hDVunif⟩ :
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ DVlim : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℝ),
        TendstoUniformlyOn (fun n => fderiv ℝ (V (φ (ψ n)))) DVlim atTop K := by
    have hDLip : ∀ n, LipschitzOnWith (Real.toNNReal L) (fderiv ℝ (V (φ n))) K :=
      fun n => Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hd2 (φ n) x)
        (fun x hx => (Real.le_toNNReal_iff_coe_le hL).mpr
          (by rw [coe_nnnorm]; exact hD2V (φ n) x hx))
        hKconv
    have hDLipK : ∀ n, LipschitzWith (Real.toNNReal L) (K.domRestrict (fderiv ℝ (V (φ n)))) :=
      fun n => (hDLip n).to_restrict
    set DVc : ℕ → C(↥K, (ℝ × ℝ) →L[ℝ] ℝ) := fun n =>
      ⟨K.domRestrict (fderiv ℝ (V (φ n))), by
        rw [Set.domRestrict_eq]
        exact (hd1 (φ n)).2.continuous.comp continuous_subtype_val⟩ with hDVc
    set DVb : ℕ → (↥K →ᵇ ((ℝ × ℝ) →L[ℝ] ℝ)) := fun n => mkOfCompact (DVc n) with hDVb
    have hDVbcoe : ∀ n, (DVb n : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)) = K.domRestrict (fderiv ℝ (V (φ n))) :=
      fun n => rfl
    have hDVbLip : ∀ n, LipschitzWith (Real.toNNReal L) (DVb n : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)) := by
      intro n; rw [hDVbcoe]; exact hDLipK n
    have hEquiRange : Equicontinuous ((↑) : Set.range DVb → ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)) := by
      have hstep : ∀ a : Set.range DVb, LipschitzWith (Real.toNNReal L)
          ((a : ↥K →ᵇ ((ℝ × ℝ) →L[ℝ] ℝ)) : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)) := by
        rintro ⟨f, n, rfl⟩
        exact hDVbLip n
      exact (LipschitzWith.uniformEquicontinuous
        (fun a : Set.range DVb => ((a : ↥K →ᵇ ((ℝ × ℝ) →L[ℝ] ℝ)) : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)))
        (Real.toNNReal L) hstep).equicontinuous
    have hin_s : ∀ (f : ↥K →ᵇ ((ℝ × ℝ) →L[ℝ] ℝ)) (x : ↥K), f ∈ Set.range DVb →
        f x ∈ Metric.closedBall (0 : (ℝ × ℝ) →L[ℝ] ℝ) L := by
      rintro f x ⟨n, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hDV (φ n) x x.2
    have hcompact : IsCompact (closure (Set.range DVb)) :=
      arzela_ascoli (Metric.closedBall (0 : (ℝ × ℝ) →L[ℝ] ℝ) L) (isCompact_closedBall _ _)
        (Set.range DVb) hin_s hEquiRange
    have hmemc : ∀ n, DVb n ∈ closure (Set.range DVb) := fun n => subset_closure ⟨n, rfl⟩
    obtain ⟨DVlimb, -, ψ, hψmono, hψtendsto⟩ := hcompact.tendsto_subseq hmemc
    refine ⟨ψ, hψmono, fun x => if hx : x ∈ K then DVlimb ⟨x, hx⟩ else 0, ?_⟩
    have huniform : TendstoUniformly (fun n => (DVb (ψ n) : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)))
        (DVlimb : ↥K → ((ℝ × ℝ) →L[ℝ] ℝ)) atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hψtendsto
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    intro u hu
    filter_upwards [huniform u hu] with n hn x
    simpa [hDVbcoe, Set.domRestrict_eq, x.2] using hn x
  -- Step 3: transfer the `V`-convergence along `ψ`, compose the subsequences, and identify the
  -- gradient limit with the derivative of the limit function.
  have hVunif' : TendstoUniformlyOn (fun n => V (φ (ψ n))) Vlim atTop K := by
    intro u hu
    exact hψmono.tendsto_atTop.eventually (hVunif u hu)
  refine ⟨φ ∘ ψ, hφmono.comp hψmono, Vlim, DVlim, hVunif', hDVunif, ?_, ?_, ?_⟩
  · intro y hy
    have hlim : Tendsto (fun n => V (φ (ψ n)) y) atTop (𝓝 (Vlim y)) := hVunif'.tendsto_at hy
    rw [abs_le]
    exact ⟨ge_of_tendsto' hlim (fun n => (abs_le.mp (hV (φ (ψ n)) y hy)).1),
      le_of_tendsto' hlim (fun n => (abs_le.mp (hV (φ (ψ n)) y hy)).2)⟩
  · intro y hy
    have hlim : Tendsto (fun n => fderiv ℝ (V (φ (ψ n))) y) atTop (𝓝 (DVlim y)) :=
      hDVunif.tendsto_at hy
    exact le_of_tendsto' hlim.norm (fun n => hDV (φ (ψ n)) y hy)
  · intro y hy
    have hf : ∀ n : ℕ, ∀ x : ℝ × ℝ, x ∈ interior K →
        HasFDerivAt (V (φ (ψ n))) (fderiv ℝ (V (φ (ψ n))) x) x :=
      fun n x _ => ((hd1 (φ (ψ n))).1 x).hasFDerivAt
    have hfg : ∀ x : ℝ × ℝ, x ∈ interior K →
        Tendsto (fun n => V (φ (ψ n)) x) atTop (𝓝 (Vlim x)) :=
      fun x hx => hVunif'.tendsto_at (interior_subset hx)
    exact hasFDerivAt_of_tendstoUniformlyOn isOpen_interior (hDVunif.mono interior_subset)
      hf hfg hy

end CIV
