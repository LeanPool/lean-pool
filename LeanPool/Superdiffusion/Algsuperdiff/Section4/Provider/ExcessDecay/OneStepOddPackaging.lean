/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddPackagingCore
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionAssembly

/-!
# OneStepOddPackaging

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `H¹` packaging of the odd extension

* `hasWeakGradientOn_oddFaceExtend_of_localizedZeroTrace` — the analytic core:
  on a reflection-symmetric open `U`, the odd extension
  `W = Z − Z ∘ r` of the zero extension `Z` of `v ∈ H¹(faceHalf U i a σ)` has
  the weak gradient `oddFaceExtendGrad a i (zeroExtendGrad … v.grad)` **on all
  of `U`** — the interface hyperplane contributes nothing, *provided* `v` has
  face-only zero trace (`LocalizedZeroTraceFunctionOn (faceHalf U i a σ) U`).
  Per test `φ` and coordinate `j`, the change of variables folds the test to
  `ψⱼ = φ − εⱼ·(φ ∘ r)` (`εⱼ = −1` exactly at the normal coordinate), and the
  eta-cutoff integration by parts of `OneStepOddPackagingCore` closes the
  identity; for `j = i` the fold is the *even* fold `φ + φ ∘ r`, which does not
  vanish on the interface — that is precisely where the zero trace is spent.

* `exists_h1Function_oddFaceExtend` — the packaged existence: an `H1Function U`
  whose `toFun`/`grad` are **pointwise** the odd extension pair, i.e. verbatim
  the `hwval` (at `c₀ = 0`) and `hwgrad` slots the boundary branch's odd
  producer asks for at one met face, and the `hw` slot of the proved
  transfers.

* `localizedZeroTraceFunctionOn_oddFaceExtend` — the stage-to-stage transport:
  the odd extension inherits face-only zero trace on the larger box, from the
  three `H¹₀` closure facts of the core module.  This is what lets the
  multi-face iteration (`OneStepPartialReflection`) re-fold across the next met
  face.

* `exists_h1_oddFaceReflection_of_meetsUpperFace` / `…_of_meetsLowerFace` — the
  window instances at the manuscript's geometry: `V = (x+□_k) ∩ □_m` meeting
  exactly one face of `∂□_m`, extension to `reflectedWindow x m k`.

## Where the face-vanishing hypothesis lives

The input is `LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
(reflectedWindow x m k) v.toFun` — CoarseGraining's own localized zero-trace
predicate, with the *reflected window* as localization window.  A cutoff
supported there is compactly supported away from `∂(reflectedWindow)`, hence
away from every unmet face of the window; only the met faces (interior to the
reflected window) are constrained.  This is the "face-only zero-trace glue",
stated without a trace operator.  It is a caller-supplied conditional API
obligation: the supplier is the boundary-branch datum reduction (`v − ℓ_h − v₁`
vanishes on the met faces), not this module.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Integrability helpers -/

private theorem holderTwoTwoOne : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
  ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩

private theorem integrable_mul_restrict {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W)) :
    Integrable (fun y => f y * g y) (volume.restrict W) := by
  have := holderTwoTwoOne
  exact hf.integrable_mul hg

/-! ## 2. The weak gradient of the odd extension -/

private theorem oddFaceExtension_weakGradient_assembly :
    ∀ {d : ℕ} {U : Set (Vec d)} {i : Fin d} {a σ : ℝ}
      (v : H1Function (faceHalf U i a σ)) (j : Fin d) (φ : Vec d → ℝ),
      MeasurableSet U →
        let ε : ℝ := if j = i then (-1 : ℝ) else (1 : ℝ);
        (ε = if j = i then (-1 : ℝ) else (1 : ℝ)) →
          (∀ (l : Fin d), MemLp (fun (y : Vec d) => zeroExtendGrad (faceHalf U i a σ) v.grad y l) (2 : ℝ≥0∞) volume) →
            (∀ (l : Fin d),
                MemLp (fun (y : Vec d) => zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y) l) (2 : ℝ≥0∞)
                  volume) →
              MemLp φ (2 : ℝ≥0∞) volume →
                -∫ (y : Vec d) in U, oddFaceExtendGrad a i (zeroExtendGrad (faceHalf U i a σ) v.grad) y j * φ y =
                  (-∫ (y : Vec d) in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j * φ y) +
                    ε * ∫ (y : Vec d) in U, zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y) j * φ y := by
  intro d U i a σ v j φ hUmeas ε hεdef hZG2 hZGr2 hφ2
  have hcoord : ∀ y : Vec d, oddFaceExtendGrad a i
      (zeroExtendGrad (faceHalf U i a σ) v.grad) y j
      = zeroExtendGrad (faceHalf U i a σ) v.grad y j
        - ε * zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i y) j := by
    intro y
    change (zeroExtendGrad (faceHalf U i a σ) v.grad y
      - coordReflectionLinear i (zeroExtendGrad (faceHalf U i a σ) v.grad
          (coordFaceReflection a i y))) j = _
    rw [Pi.sub_apply, coordReflectionLinear_apply_coord, ← hεdef]
  have hsub : ∫ y in U, oddFaceExtendGrad a i
        (zeroExtendGrad (faceHalf U i a σ) v.grad) y j * φ y ∂volume
      = (∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j * φ y ∂volume)
        - ε * ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i y) j * φ y ∂volume := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_restrict ((hZG2 j).restrict U) (hφ2.restrict U))
      ((integrable_mul_restrict ((hZGr2 j).restrict U) (hφ2.restrict U)).const_mul ε)]
    refine setIntegral_congr_fun hUmeas fun y _ => ?_
    rw [hcoord y]
    ring
  rw [hsub]
  ring

private theorem oddFaceExtend_reflectedTestSupport :
    ∀ {d : ℕ} {U : Set (Vec d)} {i : Fin d} {a : ℝ} (j : Fin d)
      (φ : Vec d → ℝ),
      tsupport φ ⊆ U →
        let ε : ℝ := if j = i then (-1 : ℝ) else (1 : ℝ);
        (tsupport fun (z : Vec d) => φ (coordFaceReflection a i z)) ⊆ U →
          let ψ : Vec d → ℝ := fun (z : Vec d) => φ z - ε * φ (coordFaceReflection a i z);
          (ψ = fun (z : Vec d) => φ z - ε * φ (coordFaceReflection a i z)) → tsupport ψ ⊆ U := by
  intro _ U i a _ φ hφU ε hφrU ψ hψdef
  have hsub : Function.support ψ ⊆
      tsupport φ ∪ tsupport (fun z => φ (coordFaceReflection a i z)) := by
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    have h1 : φ z = 0 := image_eq_zero_of_notMem_tsupport hcon.1
    have h2 : φ (coordFaceReflection a i z) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun z => φ (coordFaceReflection a i z)) hcon.2
    refine hz ?_
    rw [hψdef]
    change φ z - ε * φ (coordFaceReflection a i z) = 0
    rw [h1, h2, mul_zero, sub_zero]
  have hclosed : IsClosed
      (tsupport φ ∪ tsupport fun z => φ (coordFaceReflection a i z)) :=
    (isClosed_tsupport φ).union (isClosed_tsupport _)
  exact (closure_minimal hsub hclosed).trans (Set.union_subset hφU hφrU)

/-- **The odd extension is `H¹` across the interface, from face-only zero
trace.**  `U` is open and invariant under the reflection `r` in `{yᵢ = a}`;
`v ∈ H¹(faceHalf U i a σ)` has localized zero trace with localization window
`U`.  Then the odd extension of the zero extension of `v` has the reflected
weak gradient on all of `U`. -/
theorem hasWeakGradientOn_oddFaceExtend_of_localizedZeroTrace {U : Set (Vec d)}
    (hUopen : IsOpen U) {i : Fin d} {a σ : ℝ}
    (hUsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ U ↔ y ∈ U)
    [IsFiniteMeasure (volume.restrict (faceHalf U i a σ))]
    (v : H1Function (faceHalf U i a σ))
    (hzt : LocalizedZeroTraceFunctionOn (faceHalf U i a σ) U v.toFun) :
    HasWeakGradientOn U (oddFaceExtend a i (zeroExtend (faceHalf U i a σ) v.toFun))
      (oddFaceExtendGrad a i (zeroExtendGrad (faceHalf U i a σ) v.grad)) := by
  intro j φ hφ hφc hφU
  have hHopen : IsOpen (faceHalf U i a σ) := isOpen_faceHalf hUopen i a σ
  have hHmeas : MeasurableSet (faceHalf U i a σ) := hHopen.measurableSet
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  have hHsub : faceHalf U i a σ ⊆ U := faceHalf_subset U i a σ
  set ε : ℝ := if j = i then (-1 : ℝ) else 1 with hεdef
  have hpre : coordFaceReflection a i ⁻¹' U = U := Set.ext fun z => hUsymm z
  set Z : Vec d → ℝ := zeroExtend (faceHalf U i a σ) v.toFun with hZdef
  -- global and reflected `L²` data of the zero extensions
  have hZ2 : MemLp Z 2 (volume : Measure (Vec d)) :=
    (memLp_indicator_iff_restrict hHmeas).2 v.memL2
  have hZr2 : MemLp (fun y => Z (coordFaceReflection a i y)) 2
      (volume : Measure (Vec d)) :=
    hZ2.comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  have hZG2 : ∀ l : Fin d, MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y l)
      2 (volume : Measure (Vec d)) := by
    intro l
    rw [zeroExtendGrad_apply_coord]
    exact (memLp_indicator_iff_restrict hHmeas).2 (v.gradMemL2 l)
  have hZGr2 : ∀ l : Fin d,
      MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad
        (coordFaceReflection a i y) l) 2 (volume : Measure (Vec d)) := fun l =>
    (hZG2 l).comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  -- test data
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection a i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection a i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection a i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc a i
  have hφrU : tsupport (fun z => φ (coordFaceReflection a i z)) ⊆ U :=
    tsupport_comp_coordFaceReflection_subset a i hUsymm hφU
  have hDφ2 : MemLp (fun y => (fderiv ℝ φ y) (basisVec j)) 2
      (volume : Measure (Vec d)) := by
    have h := memLp_two_fderiv_apply_restrict (W := (Set.univ : Set (Vec d))) hφ hφc j
    rwa [Measure.restrict_univ] at h
  -- the folded test `ψ = φ - ε·(φ ∘ r)`
  set ψ : Vec d → ℝ := fun z => φ z - ε * φ (coordFaceReflection a i z) with hψdef
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.sub (contDiff_const.mul hφr)
  have hψc : HasCompactSupport ψ := hφc.sub hφrc.mul_left
  have hψU := @oddFaceExtend_reflectedTestSupport (d) (U) (i) (a) (j) (φ) (hφU) (hφrU) (hψdef)
  -- the classical derivative of the fold: `∂ⱼψ = ∂ⱼφ - (∂ⱼφ) ∘ r`
  have hDψ : ∀ y : Vec d, (fderiv ℝ ψ y) (basisVec j)
      = (fderiv ℝ φ y) (basisVec j)
        - (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j) := by
    intro y
    have hdφ : DifferentiableAt ℝ φ y := (hφ.differentiable (by simp)).differentiableAt
    have hdφr : DifferentiableAt ℝ (fun z => φ (coordFaceReflection a i z)) y :=
      (hφr.differentiable (by simp)).differentiableAt
    have hchain : (fderiv ℝ (fun z => φ (coordFaceReflection a i z)) y) (basisVec j)
        = ε * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j) :=
      euclideanCoordDeriv_comp_coordFaceReflection hφ a i j y
    have hεsq : ε * ε = 1 := by rw [hεdef]; split_ifs <;> norm_num
    have hsplit : (fderiv ℝ ψ y) (basisVec j)
        = (fderiv ℝ φ y) (basisVec j)
          - ε * (fderiv ℝ (fun z => φ (coordFaceReflection a i z)) y) (basisVec j) := by
      rw [hψdef]
      rw [fderiv_fun_sub hdφ (hdφr.const_mul ε), fderiv_const_mul hdφr ε]
      simp
    rw [hsplit, hchain, ← mul_assoc, hεsq, one_mul]
  -- collapse of a `U`-integral against a zero-extended field onto the half
  have hcollapse : ∀ (g : Vec d → ℝ) (T : Vec d → ℝ),
      (∀ y, y ∉ faceHalf U i a σ → g y = 0) →
      ∫ y in U, g y * T y ∂volume = ∫ y in faceHalf U i a σ, g y * T y ∂volume := by
    intro g T hg0
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hHsub ?_
    intro y hy
    rw [hg0 y hy.2, zero_mul]
  have hZ0 : ∀ y, y ∉ faceHalf U i a σ → Z y = 0 := fun y hy =>
    zeroExtend_of_notMem _ hy
  have hZG0 : ∀ y, y ∉ faceHalf U i a σ →
      zeroExtendGrad (faceHalf U i a σ) v.grad y j = 0 := by
    intro y hy
    rw [zeroExtendGrad_of_notMem _ hy, Pi.zero_apply]
  -- STEP A: split the left side
  have hsplitL : ∫ y in U,
      oddFaceExtend a i Z y * (fderiv ℝ φ y) (basisVec j) ∂volume
      = (∫ y in U, Z y * (fderiv ℝ φ y) (basisVec j) ∂volume)
        - ∫ y in U, Z (coordFaceReflection a i y)
            * (fderiv ℝ φ y) (basisVec j) ∂volume := by
    rw [← integral_sub (integrable_mul_restrict (hZ2.restrict U) (hDφ2.restrict U))
      (integrable_mul_restrict (hZr2.restrict U) (hDφ2.restrict U))]
    refine setIntegral_congr_fun hUmeas fun y _ => ?_
    show oddFaceExtend a i Z y * (fderiv ℝ φ y) (basisVec j) = _
    rw [oddFaceExtend]
    ring
  -- STEP B: change of variables on the reflected term
  have hcovL : ∫ y in U, Z (coordFaceReflection a i y)
        * (fderiv ℝ φ y) (basisVec j) ∂volume
      = ∫ y in U, Z y * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j) ∂volume := by
    have h := (measurePreserving_coordFaceReflection a i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection a i)
      (fun z => Z z * (fderiv ℝ φ (coordFaceReflection a i z)) (basisVec j)) U
    rw [hpre] at h
    calc ∫ y in U, Z (coordFaceReflection a i y) * (fderiv ℝ φ y) (basisVec j) ∂volume
        = ∫ y in U, Z (coordFaceReflection a i y)
            * (fderiv ℝ φ (coordFaceReflection a i
                (coordFaceReflection a i y))) (basisVec j) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [coordFaceReflection_involutive]
      _ = ∫ y in U, Z y
            * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j) ∂volume := h
  -- STEP C+D: recombine to the folded test, and collapse onto the half
  have hDφr2 : MemLp (fun y => (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j)) 2
      (volume : Measure (Vec d)) :=
    hDφ2.comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  have hfold : (∫ y in U, Z y * (fderiv ℝ φ y) (basisVec j) ∂volume)
      - ∫ y in U, Z y * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j) ∂volume
      = ∫ y in faceHalf U i a σ, v.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume := by
    rw [← integral_sub (integrable_mul_restrict (hZ2.restrict U) (hDφ2.restrict U))
      (integrable_mul_restrict (hZ2.restrict U) (hDφr2.restrict U))]
    have hZfold : ∫ y in U, (Z y * (fderiv ℝ φ y) (basisVec j)
        - Z y * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j)) ∂volume
        = ∫ y in U, Z y * (fderiv ℝ ψ y) (basisVec j) ∂volume := by
      refine setIntegral_congr_fun hUmeas fun y _ => ?_
      rw [hDψ y]
      ring
    rw [hZfold,
      hcollapse Z (fun y => (fderiv ℝ ψ y) (basisVec j)) hZ0]
    refine setIntegral_congr_fun hHmeas fun y hy => ?_
    rw [hZdef, zeroExtend_of_mem _ hy]
  -- STEP E: the eta-cutoff integration by parts on the half
  have hIBP := setIntegral_mul_fderiv_of_localizedZeroTrace hHopen hUopen v hzt
    hψs hψc hψU j
  -- STEP F: expand the folded test on the gradient side
  have hφ2 : MemLp φ 2 (volume : Measure (Vec d)) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  have hφr2 : MemLp (fun y => φ (coordFaceReflection a i y)) 2
      (volume : Measure (Vec d)) :=
    hφ2.comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  have hexpand : ∫ y in faceHalf U i a σ, v.grad y j * ψ y ∂volume
      = (∫ y in faceHalf U i a σ, v.grad y j * φ y ∂volume)
        - ε * ∫ y in faceHalf U i a σ,
            v.grad y j * φ (coordFaceReflection a i y) ∂volume := by
    rw [← integral_const_mul, ← integral_sub
      (integrable_mul_restrict (v.gradMemL2 j) (hφ2.restrict _))
      ((integrable_mul_restrict (v.gradMemL2 j) (hφr2.restrict _)).const_mul ε)]
    refine setIntegral_congr_fun hHmeas fun y _ => ?_
    rw [hψdef]
    change v.grad y j * (φ y - ε * φ (coordFaceReflection a i y)) = _
    ring
  -- STEP G: de-collapse both gradient terms to `U`
  have hdecoll1 : ∫ y in faceHalf U i a σ, v.grad y j * φ y ∂volume
      = ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j * φ y ∂volume := by
    rw [hcollapse (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y j) φ hZG0]
    refine (setIntegral_congr_fun hHmeas fun y hy => ?_).symm
    rw [zeroExtendGrad_of_mem _ hy]
  have hdecoll2 : ∫ y in faceHalf U i a σ,
        v.grad y j * φ (coordFaceReflection a i y) ∂volume
      = ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j
          * φ (coordFaceReflection a i y) ∂volume := by
    rw [hcollapse (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y j)
      (fun y => φ (coordFaceReflection a i y)) hZG0]
    refine (setIntegral_congr_fun hHmeas fun y hy => ?_).symm
    rw [zeroExtendGrad_of_mem _ hy]
  -- STEP H: change of variables back on the second gradient term
  have hcovR : ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j
        * φ (coordFaceReflection a i y) ∂volume
      = ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad
          (coordFaceReflection a i y) j * φ y ∂volume := by
    have h := (measurePreserving_coordFaceReflection a i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection a i)
      (fun z => zeroExtendGrad (faceHalf U i a σ) v.grad
        (coordFaceReflection a i z) j * φ z) U
    rw [hpre] at h
    calc ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j
          * φ (coordFaceReflection a i y) ∂volume
        = ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i (coordFaceReflection a i y)) j
              * φ (coordFaceReflection a i y) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [coordFaceReflection_involutive]
      _ = ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i y) j * φ y ∂volume := h
  -- STEP I: assemble the right side
  have hassemble := @oddFaceExtension_weakGradient_assembly (d) (U) (i) (a) (σ) (v) (j) (φ)
    (hUmeas) (hεdef) (hZG2) (hZGr2) (hφ2)
  -- chain everything
  calc ∫ y in U, oddFaceExtend a i Z y * (fderiv ℝ φ y) (basisVec j) ∂volume
      = (∫ y in U, Z y * (fderiv ℝ φ y) (basisVec j) ∂volume)
        - ∫ y in U, Z (coordFaceReflection a i y)
            * (fderiv ℝ φ y) (basisVec j) ∂volume := hsplitL
    _ = (∫ y in U, Z y * (fderiv ℝ φ y) (basisVec j) ∂volume)
        - ∫ y in U, Z y * (fderiv ℝ φ (coordFaceReflection a i y)) (basisVec j)
            ∂volume := by rw [hcovL]
    _ = ∫ y in faceHalf U i a σ, v.toFun y * (fderiv ℝ ψ y) (basisVec j) ∂volume :=
        hfold
    _ = -∫ y in faceHalf U i a σ, v.grad y j * ψ y ∂volume := hIBP
    _ = -((∫ y in faceHalf U i a σ, v.grad y j * φ y ∂volume)
        - ε * ∫ y in faceHalf U i a σ,
            v.grad y j * φ (coordFaceReflection a i y) ∂volume) := by rw [hexpand]
    _ = -((∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad y j * φ y ∂volume)
        - ε * ∫ y in U, zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i y) j * φ y ∂volume) := by
        rw [hdecoll1, hdecoll2, hcovR]
    _ = -∫ y in U, oddFaceExtendGrad a i
          (zeroExtendGrad (faceHalf U i a σ) v.grad) y j * φ y ∂volume := by
        rw [hassemble]
        ring

/-! ## 3. The packaged `H¹` function -/

/-- ** A, abstract form.**  The odd extension of a face-vanishing `H¹` function of
the half is an `H¹` function of the whole reflection-symmetric domain, with
`toFun` and `grad` pinned **pointwise** to the odd extension pair — verbatim
the `hwval` (at `c₀ = 0`) and `hwgrad` slots of the proved consumers. -/
theorem exists_h1Function_oddFaceExtend {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {i : Fin d} {a σ : ℝ}
    (hUsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ U ↔ y ∈ U)
    (v : H1Function (faceHalf U i a σ))
    (hzt : LocalizedZeroTraceFunctionOn (faceHalf U i a σ) U v.toFun) :
    ∃ w : H1Function U,
      (∀ y, w.toFun y = oddFaceExtend a i (zeroExtend (faceHalf U i a σ) v.toFun) y) ∧
      (∀ y, w.grad y = oddFaceExtendGrad a i
        (zeroExtendGrad (faceHalf U i a σ) v.grad) y) := by
  have : IsFiniteMeasure (volume.restrict (faceHalf U i a σ)) :=
    (isOpenBoundedConvexDomain_faceHalf hU i a σ).isFiniteMeasure_restrict_volume
  have hHmeas : MeasurableSet (faceHalf U i a σ) :=
    (isOpen_faceHalf hU.isOpen i a σ).measurableSet
  have hZ2 : MemLp (zeroExtend (faceHalf U i a σ) v.toFun) 2
      (volume : Measure (Vec d)) :=
    (memLp_indicator_iff_restrict hHmeas).2 v.memL2
  have hZr2 : MemLp (fun y => zeroExtend (faceHalf U i a σ) v.toFun
      (coordFaceReflection a i y)) 2 (volume : Measure (Vec d)) :=
    hZ2.comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  have hZG2 : ∀ l : Fin d,
      MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y l) 2
        (volume : Measure (Vec d)) := by
    intro l
    rw [zeroExtendGrad_apply_coord]
    exact (memLp_indicator_iff_restrict hHmeas).2 (v.gradMemL2 l)
  have hmemL2 : MemL2On U (oddFaceExtend a i (zeroExtend (faceHalf U i a σ) v.toFun)) := by
    have h := (hZ2.restrict U).sub (hZr2.restrict U)
    exact h
  have hgradMemL2 : GradMemL2On U
      (oddFaceExtendGrad a i (zeroExtendGrad (faceHalf U i a σ) v.grad)) := by
    intro l
    have hcoord : (fun y => oddFaceExtendGrad a i
        (zeroExtendGrad (faceHalf U i a σ) v.grad) y l)
        = fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y l
            - (if l = i then (-1 : ℝ) else 1)
              * zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y) l := by
      funext y
      change (zeroExtendGrad (faceHalf U i a σ) v.grad y
        - coordReflectionLinear i (zeroExtendGrad (faceHalf U i a σ) v.grad
            (coordFaceReflection a i y))) l = _
      rw [Pi.sub_apply, coordReflectionLinear_apply_coord]
    change MemLp (fun y => oddFaceExtendGrad a i
      (zeroExtendGrad (faceHalf U i a σ) v.grad) y l) 2 (volume.restrict U)
    rw [hcoord]
    have hr : MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad
        (coordFaceReflection a i y) l) 2 (volume : Measure (Vec d)) :=
      (hZG2 l).comp_measurePreserving (measurePreserving_coordFaceReflection a i)
    exact ((hZG2 l).restrict U).sub ((hr.const_mul _).restrict U)
  exact ⟨{ toFun := oddFaceExtend a i (zeroExtend (faceHalf U i a σ) v.toFun),
           grad := oddFaceExtendGrad a i (zeroExtendGrad (faceHalf U i a σ) v.grad),
           memL2 := hmemL2,
           gradMemL2 := hgradMemL2,
           hasWeakGradient := hasWeakGradientOn_oddFaceExtend_of_localizedZeroTrace
             hU.isOpen hUsymm v hzt },
    fun _ => rfl, fun _ => rfl⟩

/-! ## 4. The stage-to-stage zero-trace transport -/

/-- **The odd extension inherits face-only zero trace on the larger box.**
`H ⊆ B` are the consecutive boxes of the fold, `B` invariant under the
reflection being unfolded, and `V₀` (the common localization window of the
whole chain) is invariant as well.  A cutoff `η` supported in `V₀` splits the
extension as `η·W = zeroExtend H (η·f) − (zeroExtend H ((η∘r)·f)) ∘ r`, and the
three `H¹₀` closure facts of the core module do the rest. -/
theorem localizedZeroTraceFunctionOn_oddFaceExtend {H B V₀ : Set (Vec d)}
    (hHmeas : MeasurableSet H) (hBopen : IsOpen B) (hHB : H ⊆ B) {i : Fin d} {a : ℝ}
    (hBsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ B ↔ y ∈ B)
    (hVsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ V₀ ↔ y ∈ V₀)
    {f : Vec d → ℝ} (hzt : LocalizedZeroTraceFunctionOn H V₀ f) :
    LocalizedZeroTraceFunctionOn B V₀ (oddFaceExtend a i (zeroExtend H f)) := by
  intro η hηs hηc hηV
  have hηr : ContDiff ℝ (⊤ : ℕ∞) fun z => η (coordFaceReflection a i z) := by
    simpa [Function.comp] using! hηs.comp (contDiff_coordFaceReflection a i)
  have hηrc : HasCompactSupport fun z => η (coordFaceReflection a i z) :=
    hasCompactSupport_comp_coordFaceReflection hηc a i
  have hηrV : tsupport (fun z => η (coordFaceReflection a i z)) ⊆ V₀ :=
    tsupport_comp_coordFaceReflection_subset a i hVsymm hηV
  have h1 : MemH10 B (zeroExtend H fun y => η y * f y) :=
    memH10_zeroExtend_of_subset hHmeas hBopen hHB (hzt η hηs hηc hηV)
  have h2' : MemH10 B (zeroExtend H fun y => η (coordFaceReflection a i y) * f y) :=
    memH10_zeroExtend_of_subset hHmeas hBopen hHB
      (hzt (fun z => η (coordFaceReflection a i z)) hηr hηrc hηrV)
  have h2 : MemH10 B (fun y => zeroExtend H
      (fun z => η (coordFaceReflection a i z) * f z) (coordFaceReflection a i y)) :=
    memH10_comp_coordFaceReflection hBopen.measurableSet a i hBsymm h2'
  have hsub := memH10_sub h1 h2
  have hfun : (fun y => η y * oddFaceExtend a i (zeroExtend H f) y)
      = fun y => zeroExtend H (fun z => η z * f z) y
          - zeroExtend H (fun z => η (coordFaceReflection a i z) * f z)
              (coordFaceReflection a i y) := by
    funext y
    have hA : η y * zeroExtend H f y = zeroExtend H (fun z => η z * f z) y := by
      by_cases hy : y ∈ H
      · rw [zeroExtend_of_mem _ hy, zeroExtend_of_mem _ hy]
      · rw [zeroExtend_of_notMem _ hy, zeroExtend_of_notMem _ hy, mul_zero]
    have hB' : η y * zeroExtend H f (coordFaceReflection a i y)
        = zeroExtend H (fun z => η (coordFaceReflection a i z) * f z)
            (coordFaceReflection a i y) := by
      by_cases hy : coordFaceReflection a i y ∈ H
      · rw [zeroExtend_of_mem _ hy, zeroExtend_of_mem _ hy,
          coordFaceReflection_involutive]
      · rw [zeroExtend_of_notMem _ hy, zeroExtend_of_notMem _ hy, mul_zero]
    change η y * (zeroExtend H f y - zeroExtend H f (coordFaceReflection a i y)) = _
    rw [mul_sub, hA, hB']
  rw [hfun]
  exact hsub

/-! ## 5. The window instances (one met face) -/

/-- Transport of the value representative along an equality of `H¹` domains. -/
theorem h1FunctionOfSetEq_toFun {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (h1FunctionOfSetEq h u).toFun = u.toFun := by
  subst h
  rfl

/-- ** A on the windows, upper met face.**  `V = (x+□_k) ∩ □_m` meets exactly the
upper `i`-face of `∂□_m`; a face-vanishing `v ∈ H¹(V)` produces the `H¹` datum
of the reflected window with `toFun`/`grad` pinned pointwise to the odd
extension pair — the exact `hwval` (`c₀ = 0`) and `hwgrad` slots the boundary
branch's odd producer asks for, and the `hw` slot of
`OddReflectionAssembly.isWeaklyHarmonicOn_reflectedWindow_of_meetsUpperFace`. -/
theorem exists_h1_oddFaceReflection_of_meetsUpperFace {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (v : H1Function (truncatedWindow x m k))
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) v.toFun) :
    ∃ w : H1Function (reflectedWindow x m k),
      (∀ y, w.toFun y = oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtend (truncatedWindow x m k) v.toFun) y) ∧
      (∀ y, w.grad y = oddFaceExtendGrad ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtendGrad (truncatedWindow x m k) v.grad) y) := by
  have hset : faceHalf (reflectedWindow x m k) i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1
      = truncatedWindow x m k :=
    faceHalf_reflectedWindow_of_meetsUpperFace hkm hup hother
  obtain ⟨w, hw1, hw2⟩ := exists_h1Function_oddFaceExtend
    (isOpenBoundedConvexDomain_reflectedWindow x m k)
    (mem_reflectedWindow_coordFaceReflection_iff hkm hup)
    (h1FunctionOfSetEq hset.symm v)
    (by rw [h1FunctionOfSetEq_toFun, hset]; exact hzt)
  refine ⟨w, fun y => ?_, fun y => ?_⟩
  · rw [hw1 y, h1FunctionOfSetEq_toFun, hset]
  · rw [hw2 y, h1FunctionOfSetEq_grad, hset]

/-- ** A on the windows, lower met face.** -/
theorem exists_h1_oddFaceReflection_of_meetsLowerFace {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (v : H1Function (truncatedWindow x m k))
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) v.toFun) :
    ∃ w : H1Function (reflectedWindow x m k),
      (∀ y, w.toFun y = oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtend (truncatedWindow x m k) v.toFun) y) ∧
      (∀ y, w.grad y = oddFaceExtendGrad (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtendGrad (truncatedWindow x m k) v.grad) y) := by
  have hset : faceHalf (reflectedWindow x m k) i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1)
      = truncatedWindow x m k :=
    faceHalf_reflectedWindow_of_meetsLowerFace hkm hlow hother
  obtain ⟨w, hw1, hw2⟩ := exists_h1Function_oddFaceExtend
    (isOpenBoundedConvexDomain_reflectedWindow x m k)
    (mem_reflectedWindow_coordFaceReflection_iff_lower hkm hlow)
    (h1FunctionOfSetEq hset.symm v)
    (by rw [h1FunctionOfSetEq_toFun, hset]; exact hzt)
  refine ⟨w, fun y => ?_, fun y => ?_⟩
  · rw [hw1 y, h1FunctionOfSetEq_toFun, hset]
  · rw [hw2 y, h1FunctionOfSetEq_grad, hset]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
