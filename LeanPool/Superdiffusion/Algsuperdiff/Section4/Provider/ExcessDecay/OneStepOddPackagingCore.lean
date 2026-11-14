/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicityTransferFace
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.LocalizedZeroTrace

/-!
# OneStepOddPackagingCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `H¹` packaging of the odd extension: the core atoms

This module builds the three named ingredients that produce it from a
**face-only** zero-trace hypothesis — the honest input identified
in the one-met-face scope note: full `H¹₀`-membership of the competitor would
force it to vanish.

* **The interface eta-cutoff chain.**  The face-only zero trace is rendered by
  CoarseGraining's own `LocalizedZeroTraceFunctionOn Ω V`: every smooth cutoff
  supported in the localization window `V` turns the function into an `H¹₀(Ω)`
  member.  With `Ω` the window half and `V` the reflected window, a cutoff
  supported in `V` vanishes near `∂V` — hence near every part of `∂Ω` *except*
  the interface hyperplane, which is interior to `V`.  This is exactly "zero
  trace on the met face only", with no trace operator.
  `setIntegral_mul_fderiv_of_localizedZeroTrace` is the resulting integration
  by parts: `∫_Ω v ∂ⱼψ = -∫_Ω ∂ⱼv ψ` for smooth `ψ` supported in `V` (not in
  `Ω`! — `ψ` may be nonzero on the interface).  The chain: a smooth bump `η ≡
  1` on a neighbourhood of `tsupport ψ` (`exists_contDiff_eq_one_on_isCompact`,
  the compact-set upgrade of `exists_contDiff_eq_one_nhds`); the `H¹₀` member
  `η·v`; its global zero extension
  (`OddReflectionGlue.hasWeakGradientOn_univ_zeroExtend`); the global test
  identity; and the collapse back to `Ω`.

* **The a.e.-congruence atom.**  The `H¹₀` witness of `η·v` records *some* weak
  gradient; on the open region where `η ≡ 1` it is a weak gradient of `v`
  itself, so by the a.e. uniqueness of weak derivatives on open sets
  (CoarseGraining's `HasWeakPartialDerivOn.ae_eq`) it agrees a.e. with `v.grad`
  there — and the test `ψ` is supported there.
  `hasWeakPartialDerivOn_congr_left` is the value congruence that makes the
  identification legitimate.

## References

* CoarseGraining `Homogenization/Sobolev/H1/LocalizedZeroTrace.lean` (the
  predicate), `Homogenization/Sobolev/W1p/ZeroExtensionGraph.lean` (the zero
  extension).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. A smooth bump identically one on a compact set -/

private theorem tsupport_zeroFun' :
    tsupport (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
  have hsupp : Function.support (fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d)) := by
    ext z
    simp
  change closure (Function.support fun _ : Vec d => (0 : ℝ)) = (∅ : Set (Vec d))
  rw [hsupp, closure_empty]

/-- **A smooth bump identically one on a neighbourhood of a compact set.**  The
compact-set upgrade of `exists_contDiff_eq_one_nhds`, by the same product trick
that drives `exists_smooth_decomposition_of_open_cover`: the defects `1 - g` of
finitely many pointwise bumps annihilate on a neighbourhood of `K`. -/
theorem exists_contDiff_eq_one_on_isCompact {K U : Set (Vec d)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (η : Vec d → ℝ) (N : Set (Vec d)),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
        IsOpen N ∧ K ⊆ N ∧ ∀ y ∈ N, η y = 1 := by
  classical
  have hex : ∀ y : Vec d, ∃ p : (Vec d → ℝ) × Set (Vec d),
      ContDiff ℝ (⊤ : ℕ∞) p.1 ∧ HasCompactSupport p.1 ∧ tsupport p.1 ⊆ U ∧
        IsOpen p.2 ∧ (∀ z ∈ p.2, p.1 z = 1) ∧ (y ∈ K → y ∈ p.2) := by
    intro y
    by_cases hy : y ∈ K
    · obtain ⟨g, W, hg, hgc, hgU, hWopen, hyW, hgW⟩ :=
        exists_contDiff_eq_one_nhds (hU.mem_nhds (hKU hy))
      exact ⟨(g, W), hg, hgc, hgU, hWopen, hgW, fun _ => hyW⟩
    · refine ⟨(fun _ => 0, (∅ : Set (Vec d))), contDiff_const, ?_, ?_,
        isOpen_empty, fun z hz => absurd hz (Set.notMem_empty z),
        fun h => absurd h hy⟩
      · change IsCompact (tsupport fun _ : Vec d => (0 : ℝ))
        rw [tsupport_zeroFun']
        exact isCompact_empty
      · change tsupport (fun _ : Vec d => (0 : ℝ)) ⊆ U
        rw [tsupport_zeroFun']
        exact Set.empty_subset _
  choose p hp1 hp2 hp3 hp4 hp5 hp6 using hex
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y => (p y).2) (fun y => hp4 y)
    (fun y hy => Set.mem_iUnion.2 ⟨y, hp6 y hy⟩)
  have hsupp : tsupport (fun z => 1 - ∏ c ∈ t, (1 - (p c).1 z))
      ⊆ ⋃ c ∈ t, tsupport (p c).1 := by
    refine closure_minimal ?_ (isClosed_biUnion_finset fun c _ => isClosed_tsupport _)
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hcon
    have hall : ∀ c ∈ t, (1 : ℝ) - (p c).1 z = 1 := by
      intro c hc
      have hznot : z ∉ tsupport (p c).1 := fun hmem =>
        hcon (Set.mem_iUnion₂.2 ⟨c, hc, hmem⟩)
      rw [image_eq_zero_of_notMem_tsupport hznot, sub_zero]
    exact hz (by rw [Finset.prod_congr rfl hall, Finset.prod_const_one, sub_self])
  refine ⟨fun z => 1 - ∏ c ∈ t, (1 - (p c).1 z), ⋃ c ∈ t, (p c).2,
    contDiff_const.sub (contDiff_prod fun c _ => contDiff_const.sub (hp1 c)),
    ?_, ?_, isOpen_biUnion fun c _ => hp4 c, ht, ?_⟩
  · exact IsCompact.of_isClosed_subset
      (t.isCompact_biUnion fun c _ => hp2 c) isClosed_closure hsupp
  · exact hsupp.trans (Set.iUnion₂_subset fun c _ => hp3 c)
  · intro y hy
    obtain ⟨c, hct, hyc⟩ : ∃ c ∈ t, y ∈ (p c).2 := by
      simpa only [Set.mem_iUnion, exists_prop] using hy
    have hzero : (1 : ℝ) - (p c).1 y = 0 := by
      rw [hp5 c y hyc, sub_self]
    change 1 - ∏ c ∈ t, (1 - (p c).1 y) = 1
    rw [Finset.prod_eq_zero (f := fun c => 1 - (p c).1 y) hct hzero, sub_zero]

/-! ## 2. `H¹₀` closure facts -/

/-- Shrinking the localization window weakens the localized zero-trace
condition. -/
theorem localizedZeroTraceFunctionOn_mono_window {Ω V V' : Set (Vec d)}
    (hV' : V' ⊆ V) {f : Vec d → ℝ} (h : LocalizedZeroTraceFunctionOn Ω V f) :
    LocalizedZeroTraceFunctionOn Ω V' f :=
  fun η hηs hηc hηV' => h η hηs hηc (hηV'.trans hV')

theorem memH10_zeroExtend_of_subset {A B : Set (Vec d)} (hA : MeasurableSet A)
    (hB : IsOpen B) (hAB : A ⊆ B) {f : Vec d → ℝ} (hf : MemH10 A f) :
    MemH10 B (zeroExtend A f) := by
  obtain ⟨u, hu⟩ := hf
  refine ⟨u.extendByZeroToOpenSuperset hA hB hAB, ?_⟩
  rw [H10Function.extendByZeroToOpenSuperset_toFun]
  change Set.indicator A u.toH1Function.toFun = Set.indicator A f
  rw [hu]

/-- **The restricted reflection transport.**  The weak gradient transports under
pre-composition with the face reflection on any reflection-invariant measurable
set — the `Ω`-restricted twin of
`OddReflectionGlue.hasWeakGradientOn_univ_comp_coordFaceReflection`. -/
theorem hasWeakGradientOn_comp_coordFaceReflection_of_symm {Ω : Set (Vec d)}
    (hΩ : MeasurableSet Ω) (a : ℝ) (i : Fin d)
    (hsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ Ω ↔ y ∈ Ω)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : HasWeakGradientOn Ω w G) :
    HasWeakGradientOn Ω (fun y => w (coordFaceReflection a i y))
      (fun y => coordReflectionLinear i (G (coordFaceReflection a i y))) := by
  intro k φ hφ hφc hφΩ
  set r : Vec d → Vec d := coordFaceReflection a i with hrdef
  set ε : ℝ := if k = i then (-1 : ℝ) else 1 with hεdef
  have hεsq : ε * ε = 1 := by rw [hεdef]; split_ifs <;> norm_num
  have hpre : coordFaceReflection a i ⁻¹' Ω = Ω := Set.ext fun z => hsymm z
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection a i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection a i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection a i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc a i
  have hφrΩ : tsupport (fun z => φ (coordFaceReflection a i z)) ⊆ Ω :=
    tsupport_comp_coordFaceReflection_subset a i hsymm hφΩ
  have hweak := hw k (fun z => φ (coordFaceReflection a i z)) hφr hφrc hφrΩ
  have hchain : ∀ y : Vec d,
      (fderiv ℝ φ (r y)) (basisVec k)
        = ε * (fderiv ℝ (fun z => φ (r z)) y) (basisVec k) := by
    intro y
    have hcd := euclideanCoordDeriv_comp_coordFaceReflection hφ a i k y
    have hcd' : (fderiv ℝ (fun z => φ (r z)) y) (basisVec k)
        = ε * (fderiv ℝ φ (r y)) (basisVec k) := hcd
    rw [hcd', ← mul_assoc, hεsq, one_mul]
  have hcov1 : ∫ y in Ω, w (r y) * (fderiv ℝ φ y) (basisVec k) ∂volume
      = ∫ y in Ω, w y * (fderiv ℝ φ (r y)) (basisVec k) ∂volume := by
    have h := (measurePreserving_coordFaceReflection a i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection a i)
      (fun z => w z * (fderiv ℝ φ (coordFaceReflection a i z)) (basisVec k)) Ω
    rw [hpre] at h
    calc ∫ y in Ω, w (r y) * (fderiv ℝ φ y) (basisVec k) ∂volume
        = ∫ y in Ω, w (r y)
            * (fderiv ℝ φ (coordFaceReflection a i (r y))) (basisVec k) ∂volume := by
          refine setIntegral_congr_fun hΩ fun y _ => ?_
          rw [hrdef, coordFaceReflection_involutive]
      _ = ∫ y in Ω, w y * (fderiv ℝ φ (r y)) (basisVec k) ∂volume := h
  have hcov2 : ∫ y in Ω, G y k * φ (r y) ∂volume
      = ∫ y in Ω, G (r y) k * φ y ∂volume := by
    have h := (measurePreserving_coordFaceReflection a i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection a i)
      (fun z => G (coordFaceReflection a i z) k * φ z) Ω
    rw [hpre] at h
    calc ∫ y in Ω, G y k * φ (r y) ∂volume
        = ∫ y in Ω, G (coordFaceReflection a i (r y)) k * φ (r y) ∂volume := by
          refine setIntegral_congr_fun hΩ fun y _ => ?_
          rw [hrdef, coordFaceReflection_involutive]
      _ = ∫ y in Ω, G (r y) k * φ y ∂volume := h
  calc ∫ y in Ω, w (r y) * (fderiv ℝ φ y) (basisVec k) ∂volume
      = ∫ y in Ω, w y * (fderiv ℝ φ (r y)) (basisVec k) ∂volume := hcov1
    _ = ∫ y in Ω, ε * (w y * (fderiv ℝ (fun z => φ (r z)) y) (basisVec k)) ∂volume := by
        refine setIntegral_congr_fun hΩ fun y _ => ?_
        rw [hchain y]; ring
    _ = ε * ∫ y in Ω, w y * (fderiv ℝ (fun z => φ (r z)) y) (basisVec k) ∂volume :=
        integral_const_mul _ _
    _ = ε * -∫ y in Ω, G y k * φ (r y) ∂volume := by rw [hweak]
    _ = -(ε * ∫ y in Ω, G (r y) k * φ y ∂volume) := by rw [hcov2]; ring
    _ = -∫ y in Ω, coordReflectionLinear i (G (r y)) k * φ y ∂volume := by
        rw [← integral_const_mul]
        refine congrArg Neg.neg (setIntegral_congr_fun hΩ fun y _ => ?_)
        rw [coordReflectionLinear_apply_coord, ← hεdef]
        ring

/-- `eLpNorm` is blind to a `±1` prefactor. -/
private theorem eLpNorm_sign_mul (c : ℝ) (hc : c = -1 ∨ c = 1) (g : Vec d → ℝ)
    (μ : Measure (Vec d)) :
    eLpNorm (fun y => c * g y) 2 μ = eLpNorm g 2 μ := by
  rcases hc with hc | hc
  · have hneg : (fun y => c * g y) = -g := by
      funext y
      rw [hc]
      simp
    rw [hneg]
    exact eLpNorm_neg _ _ _
  · have hone : (fun y => c * g y) = g := by
      funext y
      rw [hc, one_mul]
    rw [hone]

/-- **`H¹₀` is closed under composition with a face reflection** on a
reflection-invariant measurable set. -/
theorem memH10_comp_coordFaceReflection {Ω : Set (Vec d)} (hΩ : MeasurableSet Ω)
    (a : ℝ) (i : Fin d)
    (hsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ Ω ↔ y ∈ Ω)
    {f : Vec d → ℝ} (hf : MemH10 Ω f) :
    MemH10 Ω (fun y => f (coordFaceReflection a i y)) := by
  obtain ⟨u, hu⟩ := hf
  have hpre : coordFaceReflection a i ⁻¹' Ω = Ω := Set.ext fun z => hsymm z
  have mp : MeasurePreserving (coordFaceReflection a i)
      (volume.restrict Ω) (volume.restrict Ω) := by
    have h := (measurePreserving_coordFaceReflection a i).restrict_preimage
      (μa := (volume : Measure (Vec d))) hΩ
    rwa [hpre] at h
  have hmemL2 : MemL2On Ω
      (fun y => u.toH1Function.toFun (coordFaceReflection a i y)) :=
    u.toH1Function.memL2.comp_measurePreserving mp
  have hgradMemL2 : GradMemL2On Ω (fun y =>
      coordReflectionLinear i (u.toH1Function.grad (coordFaceReflection a i y))) := by
    intro k
    have hk : (fun y => coordReflectionLinear i
        (u.toH1Function.grad (coordFaceReflection a i y)) k)
        = fun y => (if k = i then (-1 : ℝ) else 1)
            * u.toH1Function.grad (coordFaceReflection a i y) k := by
      funext y
      rw [coordReflectionLinear_apply_coord]
    change MemLp (fun y => coordReflectionLinear i
      (u.toH1Function.grad (coordFaceReflection a i y)) k) 2 (volume.restrict Ω)
    rw [hk]
    exact ((u.toH1Function.gradMemL2 k).comp_measurePreserving mp).const_mul _
  have hweak : HasWeakGradientOn Ω
      (fun y => u.toH1Function.toFun (coordFaceReflection a i y))
      (fun y => coordReflectionLinear i
        (u.toH1Function.grad (coordFaceReflection a i y))) :=
    hasWeakGradientOn_comp_coordFaceReflection_of_symm hΩ a i hsymm
      u.toH1Function.hasWeakGradient
  have hsm : ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      fun y => u.approx n (coordFaceReflection a i y) := fun n => by
    simpa [Function.comp] using!
      (u.approx_smooth n).comp (contDiff_coordFaceReflection a i)
  have hcs : ∀ n, HasCompactSupport
      fun y => u.approx n (coordFaceReflection a i y) := fun n =>
    hasCompactSupport_comp_coordFaceReflection (u.approx_hasCompactSupport n) a i
  have hss : ∀ n, tsupport (fun y => u.approx n (coordFaceReflection a i y)) ⊆ Ω :=
    fun n => tsupport_comp_coordFaceReflection_subset a i hsymm
      (u.approx_support_subset n)
  have htend : Tendsto (fun n => eLpNorm (fun y =>
      u.approx n (coordFaceReflection a i y)
        - u.toH1Function.toFun (coordFaceReflection a i y)) 2 (volume.restrict Ω))
      atTop (nhds 0) := by
    refine u.tendsto_approx.congr fun n => ?_
    have hae : AEStronglyMeasurable
        (fun y => u.approx n y - u.toH1Function.toFun y) (volume.restrict Ω) :=
      ((u.approx_smooth n).continuous.aestronglyMeasurable).sub
        u.toH1Function.memL2.aestronglyMeasurable
    have hcomp : eLpNorm ((fun y => u.approx n y - u.toH1Function.toFun y)
          ∘ coordFaceReflection a i) 2 (volume.restrict Ω)
        = eLpNorm (fun y => u.approx n y - u.toH1Function.toFun y) 2
            (volume.restrict Ω) :=
      eLpNorm_comp_measurePreserving hae mp
    have hfun : ((fun y => u.approx n y - u.toH1Function.toFun y)
          ∘ coordFaceReflection a i)
        = fun y => u.approx n (coordFaceReflection a i y)
            - u.toH1Function.toFun (coordFaceReflection a i y) := rfl
    rw [← hfun]
    exact hcomp.symm
  have htendg : ∀ k : Fin d, Tendsto (fun n => eLpNorm (fun y =>
      (fderiv ℝ (fun z => u.approx n (coordFaceReflection a i z)) y) (basisVec k)
        - coordReflectionLinear i
            (u.toH1Function.grad (coordFaceReflection a i y)) k) 2
      (volume.restrict Ω)) atTop (nhds 0) := by
    intro k
    refine (u.tendsto_approx_grad k).congr fun n => ?_
    have hae : AEStronglyMeasurable
        (fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
          - u.toH1Function.grad y k) (volume.restrict Ω) := by
      have hcont : Continuous fun y => (fderiv ℝ (u.approx n) y) (basisVec k) :=
        ((u.approx_smooth n).continuous_fderiv (by norm_num)).clm_apply
          continuous_const
      exact hcont.aestronglyMeasurable.sub (u.toH1Function.gradMemL2 k).aestronglyMeasurable
    have hcomp : eLpNorm ((fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
          - u.toH1Function.grad y k) ∘ coordFaceReflection a i) 2 (volume.restrict Ω)
        = eLpNorm (fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
            - u.toH1Function.grad y k) 2 (volume.restrict Ω) :=
      eLpNorm_comp_measurePreserving hae mp
    have hfun0 : ((fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
          - u.toH1Function.grad y k) ∘ coordFaceReflection a i)
        = fun y => (fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k)
            - u.toH1Function.grad (coordFaceReflection a i y) k := rfl
    have hfun : (fun y =>
        (fderiv ℝ (fun z => u.approx n (coordFaceReflection a i z)) y) (basisVec k)
          - coordReflectionLinear i
              (u.toH1Function.grad (coordFaceReflection a i y)) k)
        = fun y => (if k = i then (-1 : ℝ) else 1)
            * ((fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k)
              - u.toH1Function.grad (coordFaceReflection a i y) k) := by
      funext y
      have hcd : (fderiv ℝ (fun z => u.approx n (coordFaceReflection a i z)) y)
          (basisVec k)
          = (if k = i then (-1 : ℝ) else 1)
            * (fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k) :=
        euclideanCoordDeriv_comp_coordFaceReflection (u.approx_smooth n) a i k y
      rw [hcd, coordReflectionLinear_apply_coord]
      ring
    have hsign := eLpNorm_sign_mul (if k = i then (-1 : ℝ) else 1)
      (by split_ifs <;> simp)
      (fun y => (fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k)
        - u.toH1Function.grad (coordFaceReflection a i y) k) (volume.restrict Ω)
    calc eLpNorm (fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
            - u.toH1Function.grad y k) 2 (volume.restrict Ω)
        = eLpNorm ((fun y => (fderiv ℝ (u.approx n) y) (basisVec k)
              - u.toH1Function.grad y k) ∘ coordFaceReflection a i) 2
            (volume.restrict Ω) := hcomp.symm
      _ = eLpNorm (fun y =>
            (fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k)
              - u.toH1Function.grad (coordFaceReflection a i y) k) 2
            (volume.restrict Ω) :=
          congrArg (fun g => eLpNorm g 2 (volume.restrict Ω)) hfun0
      _ = eLpNorm (fun y => (if k = i then (-1 : ℝ) else 1)
            * ((fderiv ℝ (u.approx n) (coordFaceReflection a i y)) (basisVec k)
              - u.toH1Function.grad (coordFaceReflection a i y) k)) 2
            (volume.restrict Ω) := hsign.symm
      _ = eLpNorm (fun y =>
            (fderiv ℝ (fun z => u.approx n (coordFaceReflection a i z)) y) (basisVec k)
              - coordReflectionLinear i
                  (u.toH1Function.grad (coordFaceReflection a i y)) k) 2
            (volume.restrict Ω) :=
          congrArg (fun g => eLpNorm g 2 (volume.restrict Ω)) hfun.symm
  refine ⟨{ toH1Function :=
              { toFun := fun y => u.toH1Function.toFun (coordFaceReflection a i y),
                grad := fun y => coordReflectionLinear i
                  (u.toH1Function.grad (coordFaceReflection a i y)),
                memL2 := hmemL2,
                gradMemL2 := hgradMemL2,
                hasWeakGradient := hweak },
            approx := fun n y => u.approx n (coordFaceReflection a i y),
            approx_smooth := hsm,
            approx_hasCompactSupport := hcs,
            approx_support_subset := hss,
            tendsto_approx := htend,
            tendsto_approx_grad := htendg }, ?_⟩
  change (fun y => u.toH1Function.toFun (coordFaceReflection a i y))
    = fun y => f (coordFaceReflection a i y)
  rw [hu]

/-! ## 3. The a.e.-congruence atom -/

/-- The weak partial derivative predicate depends on the function only through
its values on the window. -/
theorem hasWeakPartialDerivOn_congr_left {W : Set (Vec d)} (hW : MeasurableSet W)
    {j : Fin d} {f f' g : Vec d → ℝ} (h : HasWeakPartialDerivOn W j f g)
    (hff' : ∀ y ∈ W, f y = f' y) : HasWeakPartialDerivOn W j f' g := by
  intro φ hφ hφc hφW
  calc ∫ y in W, f' y * (fderiv ℝ φ y) (basisVec j) ∂volume
      = ∫ y in W, f y * (fderiv ℝ φ y) (basisVec j) ∂volume :=
        setIntegral_congr_fun hW fun y hy => by rw [hff' y hy]
    _ = -∫ y in W, g y * φ y ∂volume := h φ hφ hφc hφW

/-! ## 4. The interface eta-cutoff chain -/

/-- **Integration by parts against a test supported in the localization
window.**  `v ∈ H¹(Ω)` has localized zero trace in `V ⊇` the interface; then for
every smooth compactly supported `ψ` with `tsupport ψ ⊆ V`,

`∫_Ω v ∂ⱼψ = -∫_Ω (∇v)ⱼ ψ`.

The test may be nonzero on the part of `∂Ω` interior to `V` — that is exactly
what the zero-trace hypothesis pays for. -/
theorem setIntegral_mul_fderiv_of_localizedZeroTrace {Ω V : Set (Vec d)}
    (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)] (hV : IsOpen V)
    (v : H1Function Ω) (hzt : LocalizedZeroTraceFunctionOn Ω V v.toFun)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ V) (j : Fin d) :
    ∫ y in Ω, v.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume
      = -∫ y in Ω, v.grad y j * ψ y ∂volume := by
  obtain ⟨η, N, hηs, hηc, hηV, hNopen, hψN, hη1⟩ :=
    exists_contDiff_eq_one_on_isCompact hψc hV hψV
  obtain ⟨u, hu⟩ := hzt η hηs hηc hηV
  have hΩmeas : MeasurableSet Ω := hΩ.measurableSet
  have hglob := hasWeakGradientOn_univ_zeroExtend hΩmeas u
  have hkey := hglob j ψ hψ hψc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hkey
  -- collapse the two global integrals onto `Ω`
  have hL : ∫ y, zeroExtend Ω u.toH1Function.toFun y
        * (fderiv ℝ ψ y) (basisVec j) ∂volume
      = ∫ y in Ω, u.toH1Function.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume := by
    have hfun : (fun y => zeroExtend Ω u.toH1Function.toFun y
        * (fderiv ℝ ψ y) (basisVec j))
        = Set.indicator Ω fun y =>
            u.toH1Function.toFun y * (fderiv ℝ ψ y) (basisVec j) := by
      funext y
      by_cases hy : y ∈ Ω
      · rw [zeroExtend_of_mem _ hy, Set.indicator_of_mem hy]
      · rw [zeroExtend_of_notMem _ hy, Set.indicator_of_notMem hy, zero_mul]
    rw [hfun, integral_indicator hΩmeas]
  have hR : ∫ y, zeroExtendGrad Ω u.toH1Function.grad y j * ψ y ∂volume
      = ∫ y in Ω, u.toH1Function.grad y j * ψ y ∂volume := by
    have hfun : (fun y => zeroExtendGrad Ω u.toH1Function.grad y j * ψ y)
        = Set.indicator Ω fun y => u.toH1Function.grad y j * ψ y := by
      funext y
      by_cases hy : y ∈ Ω
      · rw [zeroExtendGrad_of_mem _ hy, Set.indicator_of_mem hy]
      · rw [zeroExtendGrad_of_notMem _ hy, Set.indicator_of_notMem hy,
          Pi.zero_apply, zero_mul]
    rw [hfun, integral_indicator hΩmeas]
  -- the value side: `η ≡ 1` on the support of `∂ⱼψ`
  have hL2 : ∫ y in Ω, u.toH1Function.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume
      = ∫ y in Ω, v.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume := by
    refine setIntegral_congr_fun hΩmeas fun y _ => ?_
    by_cases hD : (fderiv ℝ ψ y) (basisVec j) = 0
    · rw [hD, mul_zero, mul_zero]
    · have hyψ : y ∈ tsupport ψ := by
        refine support_fderiv_subset ℝ ?_
        simp only [Function.mem_support]
        intro h0
        exact hD (by rw [h0]; simp)
      rw [congrFun hu y, hη1 y (hψN hyψ), one_mul]
  -- the gradient side: split off the support and identify a.e. where `η ≡ 1`
  have hG : ∫ y in Ω, u.toH1Function.grad y j * ψ y ∂volume
      = ∫ y in Ω, v.grad y j * ψ y ∂volume := by
    have hONopen : IsOpen (Ω ∩ N) := hΩ.inter hNopen
    have hONsub : Ω ∩ N ⊆ Ω := Set.inter_subset_left
    have hvanish : ∀ (g : Vec d → ℝ), ∀ y ∈ Ω \ (Ω ∩ N), g y * ψ y = 0 := by
      intro g y hy
      have hyN : y ∉ N := fun hN => hy.2 ⟨hy.1, hN⟩
      rw [image_eq_zero_of_notMem_tsupport fun hmem => hyN (hψN hmem), mul_zero]
    have hwd_u : HasWeakPartialDerivOn (Ω ∩ N) j v.toFun
        (fun y => u.toH1Function.grad y j) := by
      have h1 := (u.toH1Function.hasWeakGradient j).restrict hONopen hONsub
      refine hasWeakPartialDerivOn_congr_left hONopen.measurableSet h1 fun y hy => ?_
      rw [congrFun hu y, hη1 y hy.2, one_mul]
    have hwd_v : HasWeakPartialDerivOn (Ω ∩ N) j v.toFun
        (fun y => v.grad y j) :=
      (v.hasWeakGradient j).restrict hONopen hONsub
    have hu_loc : LocallyIntegrableOn (fun y => u.toH1Function.grad y j)
        (Ω ∩ N) volume := by
      have hint : IntegrableOn (fun y => u.toH1Function.grad y j) Ω volume :=
        (u.toH1Function.gradMemL2 j).integrable (by norm_num)
      exact (hint.mono_set hONsub).locallyIntegrableOn
    have hv_loc : LocallyIntegrableOn (fun y => v.grad y j) (Ω ∩ N) volume := by
      have hint : IntegrableOn (fun y => v.grad y j) Ω volume :=
        (v.gradMemL2 j).integrable (by norm_num)
      exact (hint.mono_set hONsub).locallyIntegrableOn
    have hae := HasWeakPartialDerivOn.ae_eq hONopen hu_loc hv_loc hwd_u hwd_v
    calc ∫ y in Ω, u.toH1Function.grad y j * ψ y ∂volume
        = ∫ y in Ω ∩ N, u.toH1Function.grad y j * ψ y ∂volume :=
          setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩmeas hONsub
            (hvanish _)
      _ = ∫ y in Ω ∩ N, v.grad y j * ψ y ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with y hy
          rw [hy]
      _ = ∫ y in Ω, v.grad y j * ψ y ∂volume :=
          (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩmeas hONsub
            (hvanish _)).symm
  calc ∫ y in Ω, v.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume
      = ∫ y in Ω, u.toH1Function.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume :=
        hL2.symm
    _ = ∫ y, zeroExtend Ω u.toH1Function.toFun y
          * (fderiv ℝ ψ y) (basisVec j) ∂volume := hL.symm
    _ = -∫ y, zeroExtendGrad Ω u.toH1Function.grad y j * ψ y ∂volume := hkey
    _ = -∫ y in Ω, u.toH1Function.grad y j * ψ y ∂volume := by rw [hR]
    _ = -∫ y in Ω, v.grad y j * ψ y ∂volume := by rw [hG]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
