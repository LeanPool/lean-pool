/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import LeanPool.LCAnalysis.Higher

/-!
# Weak integrals of curves and parameter-dependent integrals

For a curve `γ : ℝ → F` in a locally convex space, `y` is a weak integral of `γ` over `[a, b]`
if `φ y = ∫_a^b φ (γ t) dt` for every continuous linear functional `φ` (Glöckner–Neeb, §1.1).
It is unique when it exists (Hahn–Banach), but in general it need not exist in `F`.

* Mean value inclusion: if `γ` takes values in a closed convex set `W ∋ 0`, then
  `y ∈ (b - a + 1) • W`; so weak integrals of uniformly small curves are small.
* Continuity of parameter-dependent weak integrals.
* Differentiation under the integral sign: if `f (x, t)` has jointly continuous partial
  derivatives in `x` and the relevant weak integrals exist, then
  `d(∫_a^b f(·, t) dt)(x)(h) = ∫_a^b d₁f((x, t), h) dt`.

Existence of weak integrals under completeness hypotheses is in `LCAnalysis.IntegralExistence`.
-/

@[expose] public section

open Set Filter Function
open scoped Topology Pointwise

noncomputable section

namespace LCAnalysis

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- `y` is a weak integral of `γ` over `[a, b]`. -/
def HasWeakIntegral (γ : ℝ → F) (a b : ℝ) (y : F) : Prop :=
  ∀ φ : F →L[ℝ] ℝ, φ y = ∫ t in a..b, φ (γ t)

variable {γ η : ℝ → F} {a b : ℝ} {y z : F}

theorem HasWeakIntegral.unique (hy : HasWeakIntegral γ a b y) (hz : HasWeakIntegral γ a b z) :
    y = z :=
  (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr fun φ ↦ by rw [hy φ, hz φ]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasWeakIntegral.sub (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hη : ContinuousOn η (Icc a b)) (hy : HasWeakIntegral γ a b y)
    (hz : HasWeakIntegral η a b z) : HasWeakIntegral (fun t ↦ γ t - η t) a b (y - z) := by
  intro φ
  have i₁ : IntervalIntegrable (fun t ↦ φ (γ t)) MeasureTheory.volume a b :=
    (φ.continuous.comp_continuousOn hγ).intervalIntegrable_of_Icc hab
  have i₂ : IntervalIntegrable (fun t ↦ φ (η t)) MeasureTheory.volume a b :=
    (φ.continuous.comp_continuousOn hη).intervalIntegrable_of_Icc hab
  simp only [map_sub]
  rw [intervalIntegral.integral_sub i₁ i₂, hy φ, hz φ]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem HasWeakIntegral.const_smul (hy : HasWeakIntegral γ a b y) (c : ℝ) :
    HasWeakIntegral (fun t ↦ c • γ t) a b (c • y) := by
  intro φ
  simp only [map_smul, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, hy φ]

omit [T2Space F] in
/-- Mean value inclusion for weak integrals. -/
theorem HasWeakIntegral.mem_smul (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hy : HasWeakIntegral γ a b y) {W : Set F} (hWc : Convex ℝ W) (hWcl : IsClosed W)
    (hW0 : (0 : F) ∈ W) (hγW : ∀ t ∈ Icc a b, γ t ∈ W) : y ∈ (b - a + 1) • W := by
  have hc : (0 : ℝ) < b - a + 1 := by linarith
  by_contra hnot
  obtain ⟨φ, u, hlt, hgt⟩ := geometric_hahn_banach_closed_point (hWc.smul (b - a + 1))
    (hWcl.smul_of_ne_zero hc.ne') hnot
  have hu : 0 < u := by
    simpa using hlt 0 (by simpa using Set.smul_mem_smul_set (a := b - a + 1) hW0)
  have hbound : ∀ t ∈ Icc a b, φ (γ t) ≤ u / (b - a + 1) := by
    intro t ht
    have := hlt _ (Set.smul_mem_smul_set (a := b - a + 1) (hγW t ht))
    rw [map_smul, smul_eq_mul] at this
    rw [le_div_iff₀ hc]
    linarith
  have hle : ∫ t in a..b, φ (γ t) ≤ (b - a) * u / (b - a + 1) := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      ((φ.continuous.comp_continuousOn hγ).intervalIntegrable_of_Icc hab)
      (continuousOn_const.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hab) hbound
    simpa using this
  have hle' : (b - a) * u / (b - a + 1) ≤ u := by
    rw [div_le_iff₀ hc]
    nlinarith
  rw [← hy φ] at hle
  linarith

omit [T2Space F] in
/-- Weak integrals of uniformly small curves are small. -/
theorem exists_nhds_weakIntegral_mem (hab : a ≤ b) {N : Set F} (hN : N ∈ 𝓝 (0 : F)) :
    ∃ W ∈ 𝓝 (0 : F), ∀ (γ : ℝ → F) (y : F), ContinuousOn γ (Icc a b) →
      HasWeakIntegral γ a b y → (∀ t ∈ Icc a b, γ t ∈ W) → y ∈ N := by
  have hc : b - a + 1 ≠ 0 := by linarith
  have hM : (b - a + 1)⁻¹ • N ∈ 𝓝 (0 : F) :=
    (set_smul_mem_nhds_zero_iff (inv_ne_zero hc)).mpr hN
  obtain ⟨W, hW, hWcl, hWc, hWM⟩ := exists_closed_convex_nhds_subset hM
  refine ⟨W, hW, fun γ y hγ hy hγW ↦ ?_⟩
  have h1 := hy.mem_smul hab hγ hWc hWcl (mem_of_mem_nhds hW) hγW
  have h2 := Set.smul_set_mono (a := b - a + 1) hWM h1
  rwa [smul_inv_smul₀ hc] at h2

omit [T2Space F] in
/-- Parameter-dependent weak integrals of continuous maps are continuous. -/
theorem continuousOn_weakIntegral {X : Type*} [TopologicalSpace X] {f : X × ℝ → F}
    {U : Set X} {T : Set ℝ} (hU : IsOpen U) (hT : IsOpen T) (hab : a ≤ b)
    (hTab : Icc a b ⊆ T) (hf : ContinuousOn f (U ×ˢ T)) {I : X → F}
    (hI : ∀ x ∈ U, HasWeakIntegral (fun t ↦ f (x, t)) a b (I x)) : ContinuousOn I U := by
  have hcurve : ∀ x ∈ U, ContinuousOn (fun t ↦ f (x, t)) (Icc a b) := fun x hx ↦
    hf.comp (by fun_prop : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ ⟨hx, hTab ht⟩
  intro x₀ hx₀
  refine ContinuousAt.continuousWithinAt (Filter.tendsto_def.mpr fun N hN ↦ ?_)
  have hN' : (fun z ↦ I x₀ + z) ⁻¹' N ∈ 𝓝 (0 : F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨W, hW, hsmall⟩ := exists_nhds_weakIntegral_mem hab hN'
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc a b, x ∈ U ∧ f (x, t) - f (x₀, t) ∈ W := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t₀ ht₀ ↦ ?_
    have hopen : U ×ˢ T ∈ 𝓝 (x₀, t₀) := prod_mem_nhds (hU.mem_nhds hx₀) (hT.mem_nhds (hTab ht₀))
    have h1 : ContinuousAt f (x₀, t₀) := hf.continuousAt hopen
    have h2 : ContinuousAt (fun z : X × ℝ ↦ f (x₀, z.2)) (x₀, t₀) :=
      ContinuousAt.comp (f := fun z : X × ℝ ↦ (x₀, z.2)) (hf.continuousAt
        (prod_mem_nhds (hU.mem_nhds hx₀) (hT.mem_nhds (hTab ht₀)))) (by fun_prop)
    have h3 : ContinuousAt (fun z : X × ℝ ↦ f z - f (x₀, z.2)) (x₀, t₀) := h1.sub h2
    have h4 : (fun z : X × ℝ ↦ f z - f (x₀, z.2)) (x₀, t₀) = 0 := sub_self _
    have h5 := h3.eventually_mem (h4 ▸ hW : W ∈ 𝓝 ((fun z : X × ℝ ↦ f z - f (x₀, z.2)) (x₀, t₀)))
    filter_upwards [h5, prod_mem_nhds (hU.mem_nhds hx₀) univ_mem] with z hz hzU
    exact ⟨hzU.1, hz⟩
  filter_upwards [htube] with x hx
  have hxU : x ∈ U := (hx a ⟨le_rfl, hab⟩).1
  have := hsmall _ _ ((hcurve x hxU).sub (hcurve x₀ hx₀))
    ((hI x hxU).sub hab (hcurve x hxU) (hcurve x₀ hx₀) (hI x₀ hx₀)) fun t ht ↦ (hx t ht).2
  simpa using this

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Differentiation under the integral sign, for weak integrals. -/
theorem hasDirDerivAt_weakIntegral {f : E × ℝ → F} {U : Set E} {T : Set ℝ} (hU : IsOpen U)
    (hT : IsOpen T) (hab : a ≤ b) (hTab : Icc a b ⊆ T) (hf : ContinuousOn f (U ×ˢ T))
    {D : E × ℝ → E → F} (hd : ∀ p ∈ U ×ˢ T, ∀ h, HasDirDerivAt f p (h, 0) (D p h))
    (hD : ContinuousOn (fun q : (E × ℝ) × E ↦ D q.1 q.2) ((U ×ˢ T) ×ˢ univ)) {I : E → F}
    (hI : ∀ x ∈ U, HasWeakIntegral (fun t ↦ f (x, t)) a b (I x)) {x : E} (hx : x ∈ U) (h : E)
    {J : F} (hJ : HasWeakIntegral (fun t ↦ D (x, t) h) a b J) : HasDirDerivAt I x h J := by
  have hcurve : ∀ x ∈ U, ContinuousOn (fun t ↦ f (x, t)) (Icc a b) := fun x hx ↦
    hf.comp (by fun_prop : Continuous fun t : ℝ ↦ (x, t)).continuousOn
      fun t ht ↦ ⟨hx, hTab ht⟩
  have hDcurve : ContinuousOn (fun t ↦ D (x, t) h) (Icc a b) :=
    hD.comp (by fun_prop : Continuous fun t : ℝ ↦ ((x, t), h)).continuousOn
      fun t ht ↦ ⟨⟨hx, hTab ht⟩, mem_univ _⟩
  refine Filter.tendsto_def.mpr fun N hN ↦ ?_
  have hN' : (fun z ↦ J + z) ⁻¹' N ∈ 𝓝 (0 : F) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨W, hW, hsmall⟩ := exists_nhds_weakIntegral_mem hab hN'
  have hUT : IsOpen (U ×ˢ T) := hU.prod hT
  -- the difference quotients converge to `D`, locally uniformly
  have hloc : ∀ t₀ ∈ Icc a b, ∀ᶠ z : ℝ × ℝ in 𝓝 (0, t₀), z.1 ≠ 0 →
      z.1⁻¹ • (f (x + z.1 • h, z.2) - f (x, z.2)) - D (x, z.2) h ∈ W := by
    intro t₀ ht₀
    have hp : (x, t₀) ∈ U ×ˢ T := ⟨hx, hTab ht₀⟩
    have hq := tendsto_quotient_of_hasDirDerivAt hUT (w := ((h, 0) : E × ℝ))
      (D := fun q ↦ D q h) (fun q hq ↦ hd q hq h)
      (hD.comp (by fun_prop : Continuous fun q : E × ℝ ↦ (q, h)).continuousOn
        fun q hq ↦ ⟨hq, mem_univ _⟩) hp
    have hDc : Tendsto (fun r : (E × ℝ) × ℝ ↦ D r.1 h) (𝓝[{r | r.2 ≠ 0}] ((x, t₀), 0))
        (𝓝 (D (x, t₀) h)) := by
      have : ContinuousAt (fun r : (E × ℝ) × ℝ ↦ D r.1 h) ((x, t₀), 0) :=
        ContinuousAt.comp (f := fun r : (E × ℝ) × ℝ ↦ (r.1, h))
          (hD.continuousAt (prod_mem_nhds (hUT.mem_nhds hp) univ_mem)) (by fun_prop)
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    have hdiff := hq.sub hDc
    rw [sub_self] at hdiff
    have hev := eventually_nhdsWithin_iff.mp (hdiff.eventually (mem_of_superset hW subset_rfl))
    have hmap : Tendsto (fun z : ℝ × ℝ ↦ ((x, z.2), z.1)) (𝓝 (0, t₀)) (𝓝 ((x, t₀), 0)) :=
      (by fun_prop : Continuous fun z : ℝ × ℝ ↦ ((x, z.2), z.1)).tendsto' _ _ rfl
    filter_upwards [hmap.eventually hev] with z hz hz0
    have := hz hz0
    change W _
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using this
  have htube := isCompact_Icc.eventually_forall_of_forall_eventually
    (P := fun s t ↦ s ≠ 0 → s⁻¹ • (f (x + s • h, t) - f (x, t)) - D (x, t) h ∈ W) hloc
  have hxU : ∀ᶠ s : ℝ in 𝓝 0, x + s • h ∈ U := by
    have : Continuous fun s : ℝ ↦ x + s • h := by fun_prop
    exact this.continuousAt.eventually_mem (by simpa using hU.mem_nhds hx)
  filter_upwards [nhdsWithin_le_nhds htube, nhdsWithin_le_nhds hxU, self_mem_nhdsWithin]
    with s hs hsU (hs0 : s ≠ 0)
  have hint : HasWeakIntegral
      (fun t ↦ s⁻¹ • (f (x + s • h, t) - f (x, t)) - D (x, t) h) a b
      (s⁻¹ • (I (x + s • h) - I x) - J) :=
    (((hI _ hsU).sub hab (hcurve _ hsU) (hcurve x hx) (hI x hx)).const_smul s⁻¹).sub hab
      (((hcurve _ hsU).sub (hcurve x hx)).const_smul s⁻¹) hDcurve hJ
  have hcont : ContinuousOn (fun t ↦ s⁻¹ • (f (x + s • h, t) - f (x, t)) - D (x, t) h)
      (Icc a b) := (((hcurve _ hsU).sub (hcurve x hx)).const_smul s⁻¹).sub hDcurve
  have := hsmall _ _ hcont hint fun t ht ↦ hs t ht hs0
  simpa using this

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Parameter-dependent weak integrals of `C^1` maps are `C^1`, provided the weak integrals of the
partial derivatives exist: `d(∫_a^b f(·, t) dt)(x)(h) = ∫_a^b d₁f((x, t), h) dt`. -/
theorem ContDiffMBOn.contDiffMBOn_one_of_hasWeakIntegral {f : E × ℝ → F} {U : Set E}
    {T : Set ℝ} (hU : IsOpen U) (hT : IsOpen T) (hab : a ≤ b) (hTab : Icc a b ⊆ T)
    (hf : ContDiffMBOn 1 f (U ×ˢ T))
    {I : E → F} (hI : ∀ x ∈ U, HasWeakIntegral (fun t ↦ f (x, t)) a b (I x)) {J : E × E → F}
    (hJ : ∀ x ∈ U, ∀ h, HasWeakIntegral (fun t ↦ dMB f ((x, t), (h, 0))) a b (J (x, h))) :
    ContDiffMBOn 1 I U ∧ ∀ x ∈ U, ∀ h, dMB I (x, h) = J (x, h) := by
  have hdf : ContinuousOn (dMB f) ((U ×ˢ T) ×ˢ univ) := hf.2.2
  have hD : ContinuousOn (fun q : (E × ℝ) × E ↦ dMB f (q.1, (q.2, 0))) ((U ×ˢ T) ×ˢ univ) :=
    hdf.comp (by fun_prop) fun q hq ↦ ⟨hq.1, mem_univ _⟩
  have hdir : ∀ x ∈ U, ∀ h, HasDirDerivAt I x h (J (x, h)) := fun x hx h ↦
    hasDirDerivAt_weakIntegral hU hT hab hTab hf.continuousOn
      (D := fun p h ↦ dMB f (p, (h, 0))) (fun p hp h ↦ hf.2.1 p hp (h, 0)) hD hI hx h (hJ x hx h)
  have heq : ∀ x ∈ U, ∀ h, dMB I (x, h) = J (x, h) := fun x hx h ↦ (hdir x hx h).dMB_eq
  have hJc : ContinuousOn J (U ×ˢ univ) :=
    continuousOn_weakIntegral (f := fun r : (E × E) × ℝ ↦ dMB f ((r.1.1, r.2), (r.1.2, 0)))
      (hU.prod isOpen_univ) hT hab hTab
      (hdf.comp (by fun_prop) fun r hr ↦ ⟨⟨hr.1.1, hr.2⟩, mem_univ _⟩)
      fun q hq ↦ hJ q.1 hq.1 q.2
  refine ⟨⟨continuousOn_weakIntegral hU hT hab hTab hf.continuousOn hI,
    fun x hx h ↦ by rw [heq x hx h]; exact hdir x hx h, ?_⟩, heq⟩
  exact hJc.congr fun q hq ↦ heq q.1 hq.1 q.2

end LCAnalysis
