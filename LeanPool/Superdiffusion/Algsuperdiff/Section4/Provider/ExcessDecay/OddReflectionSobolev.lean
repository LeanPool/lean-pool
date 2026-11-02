/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.H10Limit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Profile

/-!
# OddReflectionSobolev

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Sobolev atom of the partial odd reflection

> a smooth compactly supported function that vanishes on the reflection
> hyperplane `{yᵢ = a}` restricts to an `H¹₀` function of the half it cuts out.

This is what turns the *odd* fold `φ - φ ∘ r` of a test function `φ` — the
antisymmetric analogue of CoarseGraining's `foldedCoordFaceTest` — into an
admissible `H¹₀` competitor on the window side of a met face, which is how the
odd extension inherits weak harmonicity.

## The route

Let `H = U ∩ {y : 0 < σ(a - yᵢ)}` be the half (`σ = ±1` selects the side).
Cut off with the smooth profile

```text
  χₙ(y) = θ( σ(a - yᵢ)(n+1) - 1 ) ,     θ = Real.smoothTransition ,
```

so that `χₙ = 0` where `σ(a - yᵢ) ≤ 1/(n+1)` and `χₙ = 1` where
`σ(a - yᵢ) ≥ 2/(n+1)`.  Then `χₙ·ψ` is smooth and compactly supported *inside*
`H` — literally an approximating sequence for `H¹₀(H)` — and the two error
terms

```text
  (1 - χₙ)·ψ ,   (1 - χₙ)·∂ⱼψ ,   ψ·∂ᵢχₙ
```

all vanish outside the strip `Sₙ = H ∩ {σ(a - yᵢ)(n+1) < 2}` and are bounded
there by one `n`-independent constant: the mean value theorem gives
`|ψ(y)| ≤ L·|yᵢ - a|` (because `ψ` vanishes on the face), while
`|∂ᵢχₙ| ≤ derivBound·(n+1)`, and on the support of `∂ᵢχₙ` one has
`σ(a - yᵢ)(n+1) < 2`, so the product is at most `2·L·derivBound`.  Since
`|Sₙ| → 0` (the sets decrease to the empty set inside the bounded `U`), all
three tend to `0` in `L²(H)`, and `memH10_of_tendsto_H1` closes the argument.

## What is not done here

Nothing about the odd extension itself: no gluing, no change of variables, no
harmonicity.

## References

* CoarseGraining `Homogenization.Sobolev.Truncation.H10Limit`
  (`memH10_of_tendsto_H1`), `Homogenization.Sobolev.Foundations.Cutoff.Profile`
  (`smoothTransitionProfile`, `derivBound`),
  `Homogenization.Sobolev.H1.BasicLemmas` (`H1Function.ofContDiff`,
  `memH10_of_contDiff`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The half cut out by a coordinate hyperplane -/

/-- The part of `U` strictly on the `σ`-side of the hyperplane `{yᵢ = a}`.
Taking `σ = 1` gives `U ∩ {yᵢ < a}`, taking `σ = -1` gives `U ∩ {a < yᵢ}`. -/
def faceHalf (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) : Set (Vec d) :=
  U ∩ {y | 0 < σ * (a - y i)}

theorem faceHalf_subset (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) :
    faceHalf U i a σ ⊆ U :=
  Set.inter_subset_left

theorem mem_faceHalf_iff {U : Set (Vec d)} {i : Fin d} {a σ : ℝ} {y : Vec d} :
    y ∈ faceHalf U i a σ ↔ y ∈ U ∧ 0 < σ * (a - y i) :=
  Iff.rfl

theorem isOpen_faceHalf {U : Set (Vec d)} (hU : IsOpen U) (i : Fin d) (a σ : ℝ) :
    IsOpen (faceHalf U i a σ) :=
  hU.inter (isOpen_lt continuous_const
    (continuous_const.mul (continuous_const.sub (continuous_apply i))))

theorem convex_faceHalf {U : Set (Vec d)} (hU : Convex ℝ U) (i : Fin d)
    (a σ : ℝ) : Convex ℝ (faceHalf U i a σ) := by
  have hlin : IsLinearMap ℝ fun y : Vec d => σ * y i :=
    ⟨fun y z => by simp only [Pi.add_apply]; ring,
      fun c y => by simp only [Pi.smul_apply, smul_eq_mul]; ring⟩
  have hset : {y : Vec d | 0 < σ * (a - y i)} =
      {y : Vec d | (fun z : Vec d => σ * z i) y < σ * a} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have : σ * (a - y i) = σ * a - σ * y i := by ring
      linarith only [h, this.symm.le, this.le]
    · intro h
      have : σ * (a - y i) = σ * a - σ * y i := by ring
      linarith only [h, this.symm.le, this.le]
  exact hU.inter (hset ▸ convex_halfSpace_lt hlin (σ * a))

theorem isBoundedDomain_faceHalf {U : Set (Vec d)} (hU : IsBoundedDomain U)
    (i : Fin d) (a σ : ℝ) : IsBoundedDomain (faceHalf U i a σ) := by
  obtain ⟨R, hR, hbd⟩ := hU
  exact ⟨R, hR, fun y hy => hbd y (faceHalf_subset U i a σ hy)⟩

theorem isOpenBoundedConvexDomain_faceHalf {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (i : Fin d) (a σ : ℝ) :
    IsOpenBoundedConvexDomain (faceHalf U i a σ) :=
  ⟨isOpen_faceHalf hU.isOpen i a σ, isBoundedDomain_faceHalf hU.isBoundedDomain i a σ,
    convex_faceHalf hU.convex i a σ⟩

/-! ## 2. The gap to the face, and the Lipschitz bound of a vanishing test -/

/-- Every smooth compactly supported function has a global bound on its
differential. -/
private theorem exists_fderiv_bound {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : Vec d, ‖fderiv ℝ ψ y‖ ≤ L := by
  obtain ⟨L, hL⟩ :=
    (hψc.fderiv ℝ).exists_bound_of_continuous (hψ.continuous_fderiv (by simp))
  exact ⟨max L 0, le_max_right _ _, fun y => (hL y).trans (le_max_left _ _)⟩

/-- **The vanishing-on-the-face Lipschitz bound.**  A `C¹` function vanishing on
`{yᵢ = a}` is bounded by its Lipschitz constant times the distance to that
hyperplane. -/
private theorem abs_le_mul_gap {ψ : Vec d → ℝ} {L : ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hL0 : 0 ≤ L)
    (hL : ∀ y : Vec d, ‖fderiv ℝ ψ y‖ ≤ L) {i : Fin d} {a : ℝ}
    (hψ0 : ∀ y : Vec d, y i = a → ψ y = 0) (y : Vec d) :
    |ψ y| ≤ L * |y i - a| := by
  classical
  set z : Vec d := Function.update y i a with hzdef
  have hzi : z i = a := by rw [hzdef]; simp
  have h0 : ψ z = 0 := hψ0 z hzi
  have hnorm : ‖y - z‖ ≤ |y i - a| := by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
    by_cases hji : j = i
    · subst hji
      rw [Pi.sub_apply, hzdef]
      simp
    · rw [Pi.sub_apply, hzdef, Function.update_of_ne hji]
      simp [abs_nonneg]
  have hmv := (convex_univ (𝕜 := ℝ) (E := Vec d)).norm_image_sub_le_of_norm_fderiv_le
    (f := ψ) (C := L) (fun w _ => (hψ.differentiable (by simp)) w)
    (fun w _ => hL w) (Set.mem_univ z) (Set.mem_univ y)
  rw [h0, sub_zero, Real.norm_eq_abs] at hmv
  exact hmv.trans (by
    have := mul_le_mul_of_nonneg_left hnorm hL0
    linarith only [this])

/-! ## 3. The interface cutoff -/

/-- The `n`-th interface cutoff: `θ(σ(a - yᵢ)(n+1) - 1)`, vanishing within
distance `1/(n+1)` of the face and equal to `1` beyond `2/(n+1)`. -/
def faceCutoff (i : Fin d) (a σ : ℝ) (n : ℕ) : Vec d → ℝ :=
  fun y => HCPolySupport.smoothTransitionProfile (σ * (a - y i) * ((n : ℝ) + 1) - 1)

theorem faceCutoff_nonneg (i : Fin d) (a σ : ℝ) (n : ℕ) (y : Vec d) :
    0 ≤ faceCutoff i a σ n y :=
  HCPolySupport.smoothTransitionProfile.nonneg _

theorem faceCutoff_le_one (i : Fin d) (a σ : ℝ) (n : ℕ) (y : Vec d) :
    faceCutoff i a σ n y ≤ 1 :=
  HCPolySupport.smoothTransitionProfile.le_one _

theorem faceCutoff_eq_zero {i : Fin d} {a σ : ℝ} {n : ℕ} {y : Vec d}
    (h : σ * (a - y i) * ((n : ℝ) + 1) ≤ 1) : faceCutoff i a σ n y = 0 :=
  HCPolySupport.smoothTransitionProfile.zero_of_nonpos (by linarith only [h])

theorem faceCutoff_eq_one {i : Fin d} {a σ : ℝ} {n : ℕ} {y : Vec d}
    (h : 2 ≤ σ * (a - y i) * ((n : ℝ) + 1)) : faceCutoff i a σ n y = 1 :=
  HCPolySupport.smoothTransitionProfile.one_of_one_le (by linarith only [h])

theorem contDiff_faceCutoff (i : Fin d) (a σ : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (faceCutoff i a σ n) := by
  have hinner : ContDiff ℝ (⊤ : ℕ∞)
      fun y : Vec d => σ * (a - y i) * ((n : ℝ) + 1) - 1 :=
    (((contDiff_const.mul (contDiff_const.sub (contDiff_apply ℝ ℝ i))).mul
      contDiff_const).sub contDiff_const)
  exact HCPolySupport.smoothTransitionProfile.smooth.comp hinner

/-- The differential of the interface cutoff: it points along the `i`-th
coordinate and is `θ'` times the chain factor `-σ(n+1)`. -/
private theorem hasFDerivAt_faceCutoff (i : Fin d) (a σ : ℝ) (n : ℕ) (y : Vec d) :
    HasFDerivAt (faceCutoff i a σ n)
      ((deriv HCPolySupport.smoothTransitionProfile
        (σ * (a - y i) * ((n : ℝ) + 1) - 1)) •
          ((-(σ * ((n : ℝ) + 1))) •
            (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) y := by
  set L : (Fin d → ℝ) →L[ℝ] ℝ :=
    (-(σ * ((n : ℝ) + 1))) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)
      with hLdef
  set g : Vec d → ℝ := fun z => σ * (a - z i) * ((n : ℝ) + 1) - 1 with hgdef
  have hgEq : g = fun z : Vec d => (σ * a * ((n : ℝ) + 1) - 1) + L z := by
    funext z
    rw [hgdef, hLdef]
    simp only [smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul]
    ring
  have hg : HasFDerivAt g L y := by
    rw [hgEq]
    exact (L.hasFDerivAt).const_add _
  have hθ : HasDerivAt HCPolySupport.smoothTransitionProfile
      (deriv HCPolySupport.smoothTransitionProfile (g y)) (g y) :=
    (HCPolySupport.smoothTransitionProfile.differentiable (g y)).hasDerivAt
  exact hθ.comp_hasFDerivAt y hg

/-- The `j`-th coordinate derivative of the interface cutoff. -/
private theorem fderiv_faceCutoff_apply (i : Fin d) (a σ : ℝ) (n : ℕ) (y : Vec d)
    (j : Fin d) :
    fderiv ℝ (faceCutoff i a σ n) y (basisVec j) =
      (if i = j then (1 : ℝ) else 0) *
        (deriv HCPolySupport.smoothTransitionProfile
          (σ * (a - y i) * ((n : ℝ) + 1) - 1) * (-(σ * ((n : ℝ) + 1)))) := by
  rw [(hasFDerivAt_faceCutoff i a σ n y).fderiv]
  simp only [smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, basisVec_apply]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-! ## 4. The strip carrying the whole error -/

/-- The vanishing strip: the part of the half within `2/(n+1)` of the face. -/
def faceStrip (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) (n : ℕ) : Set (Vec d) :=
  faceHalf U i a σ ∩ {y | σ * (a - y i) * ((n : ℝ) + 1) < 2}

theorem faceStrip_subset_faceHalf (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) (n : ℕ) :
    faceStrip U i a σ n ⊆ faceHalf U i a σ :=
  Set.inter_subset_left

theorem isOpen_faceStrip {U : Set (Vec d)} (hU : IsOpen U) (i : Fin d)
    (a σ : ℝ) (n : ℕ) : IsOpen (faceStrip U i a σ n) :=
  (isOpen_faceHalf hU i a σ).inter
    (isOpen_lt ((continuous_const.mul (continuous_const.sub (continuous_apply i))).mul
      continuous_const) continuous_const)

theorem antitone_faceStrip (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) :
    Antitone (faceStrip U i a σ) := by
  intro n m hnm y hy
  refine ⟨hy.1, ?_⟩
  have hgap : 0 < σ * (a - y i) := hy.1.2
  have hcast : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
    linarith only [this]
  have := mul_le_mul_of_nonneg_left hcast hgap.le
  exact lt_of_le_of_lt this hy.2

theorem iInter_faceStrip (U : Set (Vec d)) (i : Fin d) (a σ : ℝ) :
    (⋂ n : ℕ, faceStrip U i a σ n) = (∅ : Set (Vec d)) := by
  ext y
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hy
  have hgap : 0 < σ * (a - y i) := (hy 0).1.2
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / (σ * (a - y i)))
  have hlt : σ * (a - y i) * ((n : ℝ) + 1) < 2 := (hy n).2
  have hkey : 2 / (σ * (a - y i)) * (σ * (a - y i)) < ((n : ℝ) + 1) * (σ * (a - y i)) := by
    refine mul_lt_mul_of_pos_right ?_ hgap
    linarith only [hn]
  rw [div_mul_cancel₀ _ (ne_of_gt hgap)] at hkey
  have : σ * (a - y i) * ((n : ℝ) + 1) = ((n : ℝ) + 1) * (σ * (a - y i)) := by ring
  linarith only [hlt, hkey, this.symm.le, this.le]

theorem tendsto_volume_faceStrip {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (i : Fin d) (a σ : ℝ) :
    Tendsto (fun n => volume (faceStrip U i a σ n)) atTop (nhds 0) := by
  have hfin : volume (faceStrip U i a σ 0) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hU.volume_lt_top)
    exact (faceStrip_subset_faceHalf U i a σ 0).trans (faceHalf_subset U i a σ)
  have := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := (volume : Measure (Vec d))) (s := faceStrip U i a σ)
    (fun n => ((isOpen_faceStrip hU.isOpen i a σ n).measurableSet).nullMeasurableSet)
    (antitone_faceStrip U i a σ) ⟨0, hfin⟩
  rw [iInter_faceStrip U i a σ] at this
  simpa using! this

/-! ## 5. An `L²` convergence criterion on a vanishing strip -/

/-- If a sequence of functions is uniformly bounded and supported (inside `H`)
in a sequence of sets of vanishing measure, it tends to `0` in `L²(H)`. -/
private theorem tendsto_eLpNorm_of_strip {H : Set (Vec d)} {S : ℕ → Set (Vec d)}
    {F : ℕ → Vec d → ℝ} {C : ℝ} (hH : MeasurableSet H)
    (hS : ∀ n, MeasurableSet (S n))
    (hzero : ∀ n, ∀ y ∈ H, y ∉ S n → F n y = 0)
    (hbd : ∀ n, ∀ y : Vec d, |F n y| ≤ C)
    (hlim : Tendsto (fun n => volume (S n)) atTop (nhds 0))
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict H)) :
    Tendsto (fun n => eLpNorm (F n) 2 (volume.restrict H)) atTop (nhds 0) := by
  have hkey : ∀ n, eLpNorm (F n) 2 (volume.restrict H) ≤
      volume (S n) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal C := by
    intro n
    have hae : F n =ᵐ[volume.restrict H] (S n).indicator (F n) := by
      refine (MeasureTheory.ae_restrict_iff' hH).2 (Filter.Eventually.of_forall ?_)
      intro y hy
      by_cases hyS : y ∈ S n
      · rw [Set.indicator_of_mem hyS]
      · rw [Set.indicator_of_notMem hyS, hzero n y hy hyS]
    have h1 : eLpNorm (F n) 2 (volume.restrict H) =
        eLpNorm (F n) 2 ((volume.restrict H).restrict (S n)) := by
      rw [MeasureTheory.eLpNorm_congr_ae hae,
        MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict (hS n)]
    have h2 : eLpNorm (F n) 2 ((volume.restrict H).restrict (S n)) ≤
        ((volume.restrict H).restrict (S n)) Set.univ ^ ((2 : ℝ≥0∞).toReal)⁻¹ *
          ENNReal.ofReal C :=
      MeasureTheory.eLpNorm_le_of_ae_bound (hF n).restrict
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hbd n y)
    have h3 : ((volume.restrict H).restrict (S n)) Set.univ ≤ volume (S n) := by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact MeasureTheory.Measure.restrict_le_self (S n)
    refine h1.le.trans (h2.trans ?_)
    exact mul_le_mul' (ENNReal.rpow_le_rpow h3 (by norm_num)) (le_refl _)
  have hrpow : Tendsto
      (fun n => volume (S n) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * ENNReal.ofReal C) atTop
      (nhds 0) := by
    have hr : Tendsto (fun n => volume (S n) ^ ((2 : ℝ≥0∞).toReal)⁻¹) atTop
        (nhds ((0 : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹)) :=
      hlim.ennrpow_const _
    have hz : ((0 : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹) = 0 := by
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
    rw [hz] at hr
    have := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal C) hr
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrpow
    (fun n => zero_le) hkey

/-! ## 6. The cutoff product and its differential -/

private theorem tsupport_faceCutoff_mul_subset {U : Set (Vec d)} {ψ : Vec d → ℝ}
    (hψU : tsupport ψ ⊆ U) (i : Fin d) (a σ : ℝ) (n : ℕ) :
    tsupport (fun y => faceCutoff i a σ n y * ψ y) ⊆ faceHalf U i a σ := by
  have hsub : Function.support (fun y => faceCutoff i a σ n y * ψ y) ⊆
      tsupport ψ ∩ {y : Vec d | 1 ≤ σ * (a - y i) * ((n : ℝ) + 1)} := by
    intro y hy
    have hy0 : faceCutoff i a σ n y * ψ y ≠ 0 := hy
    have hψy : ψ y ≠ 0 := fun h => hy0 (by rw [h, mul_zero])
    have hχy : faceCutoff i a σ n y ≠ 0 := fun h => hy0 (by rw [h, zero_mul])
    refine ⟨subset_closure hψy, ?_⟩
    rcases lt_or_ge (σ * (a - y i) * ((n : ℝ) + 1)) 1 with hlt | hge
    · exact absurd (faceCutoff_eq_zero hlt.le) hχy
    · exact hge
  have hclosed :
      IsClosed (tsupport ψ ∩ {y : Vec d | 1 ≤ σ * (a - y i) * ((n : ℝ) + 1)}) :=
    isClosed_closure.inter (isClosed_le continuous_const
      ((continuous_const.mul (continuous_const.sub (continuous_apply i))).mul
        continuous_const))
  intro y hy
  have hy' := (closure_minimal hsub hclosed) hy
  refine ⟨hψU hy'.1, ?_⟩
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 1 ≤ σ * (a - y i) * ((n : ℝ) + 1) := hy'.2
  rcases le_or_gt (σ * (a - y i)) 0 with hle | hpos
  · have h2 := mul_le_mul_of_nonneg_right hle hN.le
    rw [zero_mul] at h2
    exact absurd h1 (by linarith only [h2])
  · exact hpos

private theorem fderiv_faceCutoff_mul_apply {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) (a σ : ℝ) (n : ℕ) (y : Vec d)
    (j : Fin d) :
    fderiv ℝ (fun z => faceCutoff i a σ n z * ψ z) y (basisVec j) =
      faceCutoff i a σ n y * fderiv ℝ ψ y (basisVec j) +
        ψ y * fderiv ℝ (faceCutoff i a σ n) y (basisVec j) := by
  have hχ := hasFDerivAt_faceCutoff i a σ n y
  have hψat : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
    ((hψ.differentiable (by simp)) y).hasFDerivAt
  have hmul : HasFDerivAt (fun z => faceCutoff i a σ n z * ψ z)
      (faceCutoff i a σ n y • fderiv ℝ ψ y +
        ψ y • fderiv ℝ (faceCutoff i a σ n) y) y := by
    rw [hχ.fderiv]
    exact hχ.mul hψat
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul]

/-- **The key product bound.**  The cutoff derivative blows up like `n`, but the
vanishing of `ψ` on the face makes `ψ` small exactly where that happens; the
product is bounded independently of `n`. -/
private theorem abs_mul_fderiv_faceCutoff_le {ψ : Vec d → ℝ} {L : ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hL0 : 0 ≤ L)
    (hL : ∀ y : Vec d, ‖fderiv ℝ ψ y‖ ≤ L) {i : Fin d} {a σ : ℝ} (hσ : |σ| = 1)
    (hψ0 : ∀ y : Vec d, y i = a → ψ y = 0) (n : ℕ) (y : Vec d) (j : Fin d) :
    |ψ y * fderiv ℝ (faceCutoff i a σ n) y (basisVec j)| ≤
      2 * L * HCPolySupport.smoothTransitionProfile.derivBound := by
  have hDB := HCPolySupport.smoothTransitionProfile.derivBound_nonneg
  have hgoal_nonneg : (0 : ℝ) ≤ 2 * L * HCPolySupport.smoothTransitionProfile.derivBound :=
    by positivity
  rw [fderiv_faceCutoff_apply]
  by_cases hij : i = j
  · rw [ite_eq_left hij, one_mul]
    set N : ℝ := (n : ℝ) + 1 with hNdef
    have hN : (0 : ℝ) < N := by rw [hNdef]; positivity
    set t : ℝ := σ * (a - y i) * N - 1 with htdef
    by_cases ht0 : t ≤ 0
    · rw [HCPolySupport.smoothTransitionProfile.deriv_zero_of_nonpos ht0]
      simpa using hgoal_nonneg
    by_cases ht1 : 1 ≤ t
    · rw [HCPolySupport.smoothTransitionProfile.deriv_zero_of_one_le ht1]
      simpa using hgoal_nonneg
    push Not at ht0 ht1
    -- the transition band: `1 < σ(a - yᵢ)N < 2`
    have hband1 : 1 < σ * (a - y i) * N := by rw [htdef] at ht0; linarith only [ht0]
    have hband2 : σ * (a - y i) * N < 2 := by rw [htdef] at ht1; linarith only [ht1]
    have hgpos : 0 < σ * (a - y i) := by
      by_contra hg
      push Not at hg
      have := mul_le_mul_of_nonneg_right hg hN.le
      rw [zero_mul] at this
      linarith only [hband1, this]
    have habs : |y i - a| = σ * (a - y i) := by
      have h1 : |σ * (a - y i)| = |σ| * |a - y i| := abs_mul _ _
      rw [hσ, one_mul] at h1
      rw [abs_sub_comm, ← h1, abs_of_pos hgpos]
    have hAbound : |ψ y| ≤ L * (σ * (a - y i)) := by
      have := abs_le_mul_gap hψ hL0 hL hψ0 y
      rw [habs] at this
      exact this
    have hBbound : |deriv HCPolySupport.smoothTransitionProfile t| ≤
        HCPolySupport.smoothTransitionProfile.derivBound := by
      have := HCPolySupport.smoothTransitionProfile.norm_deriv_le t
      rwa [Real.norm_eq_abs] at this
    have hsign : |(-(σ * N))| = N := by
      rw [abs_neg, abs_mul, hσ, one_mul, abs_of_pos hN]
    calc |ψ y * (deriv HCPolySupport.smoothTransitionProfile t * (-(σ * N)))|
        = |ψ y| * |deriv HCPolySupport.smoothTransitionProfile t| * N := by
          rw [abs_mul, abs_mul, hsign, mul_assoc]
      _ ≤ (L * (σ * (a - y i))) * |deriv HCPolySupport.smoothTransitionProfile t| * N := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hAbound (abs_nonneg _)) hN.le
      _ ≤ (L * (σ * (a - y i))) * HCPolySupport.smoothTransitionProfile.derivBound * N := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hBbound (by positivity)) hN.le
      _ = L * HCPolySupport.smoothTransitionProfile.derivBound *
            (σ * (a - y i) * N) := by ring
      _ ≤ L * HCPolySupport.smoothTransitionProfile.derivBound * 2 :=
          mul_le_mul_of_nonneg_left hband2.le (by positivity)
      _ = 2 * L * HCPolySupport.smoothTransitionProfile.derivBound := by ring
  · rw [ite_eq_right hij, zero_mul, mul_zero, abs_zero]
    exact hgoal_nonneg

private theorem abs_fderiv_apply_le {ψ : Vec d → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ y : Vec d, ‖fderiv ℝ ψ y‖ ≤ L) (y : Vec d) (j : Fin d) :
    |fderiv ℝ ψ y (basisVec j)| ≤ L := by
  have hb : ‖basisVec (d := d) j‖ ≤ (1 : ℝ) := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
    rw [basisVec_apply, Real.norm_eq_abs]
    split_ifs <;> simp
  have hop := (fderiv ℝ ψ y).le_opNorm (basisVec j)
  rw [Real.norm_eq_abs] at hop
  calc |fderiv ℝ ψ y (basisVec j)| ≤ ‖fderiv ℝ ψ y‖ * ‖basisVec (d := d) j‖ := hop
    _ ≤ L * 1 := mul_le_mul (hL y) hb (norm_nonneg _) hL0
    _ = L := mul_one L

/-! ## 7. The atom -/

/-- **: the Sobolev atom of the partial odd reflection.**

A smooth compactly supported function on the domain `U` that *vanishes on the
hyperplane* `{yᵢ = a}` restricts to an `H¹₀` function of the half of `U` on
either side of that hyperplane (`σ = 1` the side `yᵢ < a`, `σ = -1` the side
`a < yᵢ`).

This is the one new Sobolev fact behind the draft's odd reflection: applied to
the *odd fold* `φ - φ ∘ r` of a test function `φ`, it makes the fold an
admissible `H¹₀` competitor on the window side of a met face. -/
theorem memH10_faceHalf_of_contDiff_of_vanishing_on_face
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {i : Fin d} {a σ : ℝ}
    (hσ : |σ| = 1) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hψ0 : ∀ y : Vec d, y i = a → ψ y = 0) :
    MemH10 (faceHalf U i a σ) ψ := by
  classical
  have hHdom : IsOpenBoundedConvexDomain (faceHalf U i a σ) :=
    isOpenBoundedConvexDomain_faceHalf hU i a σ
  obtain ⟨L, hL0, hL⟩ := exists_fderiv_bound hψ hψc
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hDB := HCPolySupport.smoothTransitionProfile.derivBound_nonneg
  set C : ℝ := M + L + 2 * L * HCPolySupport.smoothTransitionProfile.derivBound
    with hCdef
  set g : ℕ → Vec d → ℝ := fun n y => faceCutoff i a σ n y * ψ y with hgdef
  have hgsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n) := fun n =>
    (contDiff_faceCutoff i a σ n).mul hψ
  have hgcompact : ∀ n, HasCompactSupport (g n) := fun _ => hψc.mul_left
  have hgsub : ∀ n, tsupport (g n) ⊆ faceHalf U i a σ := fun n =>
    tsupport_faceCutoff_mul_subset hψU i a σ n
  set f : H1Function (faceHalf U i a σ) :=
    H1Function.ofContDiff hHdom.isOpen (hψ.of_le (by simp)) hψc with hfdef
  set F : ℕ → H1Function (faceHalf U i a σ) := fun n =>
    H1Function.ofContDiff hHdom.isOpen ((hgsmooth n).of_le (by simp)) (hgcompact n)
    with hFdef
  have hftoFun : f.toFun = ψ := by rw [hfdef]; rfl
  have hfgrad : ∀ (x : Vec d) (j : Fin d),
      f.grad x j = fderiv ℝ ψ x (basisVec j) := by
    intro x j; rw [hfdef]; rfl
  have hFtoFun : ∀ (n : ℕ) (x : Vec d),
      (F n).toFun x = faceCutoff i a σ n x * ψ x := by
    intro n x; rw [hFdef]; rfl
  have hFgrad : ∀ (n : ℕ) (x : Vec d) (j : Fin d),
      (F n).grad x j = fderiv ℝ (g n) x (basisVec j) := by
    intro n x j; rw [hFdef]; rfl
  -- outside the strip the cutoff is `1` and its derivative vanishes
  have houtside : ∀ (n : ℕ) (y : Vec d), y ∈ faceHalf U i a σ →
      y ∉ faceStrip U i a σ n → 2 ≤ σ * (a - y i) * ((n : ℝ) + 1) := by
    intro n y hy hyS
    rcases lt_or_ge (σ * (a - y i) * ((n : ℝ) + 1)) 2 with h | h
    · exact absurd (Set.mem_inter hy h) hyS
    · exact h
  have hcut_one_abs : ∀ (n : ℕ) (y : Vec d),
      |1 - faceCutoff i a σ n y| ≤ 1 := by
    intro n y
    rw [abs_le]
    exact ⟨by linarith only [faceCutoff_le_one i a σ n y],
      by linarith only [faceCutoff_nonneg i a σ n y]⟩
  have hmem : ∀ n, MemH10 (faceHalf U i a σ) (F n).toFun := by
    intro n
    have := memH10_of_contDiff hHdom.isOpen (hgsmooth n) (hgcompact n) (hgsub n)
    exact this
  have hfun : Tendsto (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x) 2
      (volumeMeasureOn (faceHalf U i a σ))) atTop (nhds 0) := by
    refine tendsto_eLpNorm_of_strip (C := C)
      (isOpen_faceHalf hU.isOpen i a σ).measurableSet
      (fun n => (isOpen_faceStrip hU.isOpen i a σ n).measurableSet) ?_ ?_
      (tendsto_volume_faceStrip hU i a σ)
      (fun n => (f.memL2.sub (F n).memL2).aestronglyMeasurable)
    · intro n y hy hyS
      rw [hftoFun, hFtoFun n y, faceCutoff_eq_one (houtside n y hy hyS), one_mul,
        sub_self]
    · intro n y
      rw [hftoFun, hFtoFun n y, hCdef]
      have hrw : ψ y - faceCutoff i a σ n y * ψ y =
          (1 - faceCutoff i a σ n y) * ψ y := by ring
      have hMy : |ψ y| ≤ M := by
        have := hM y; rwa [Real.norm_eq_abs] at this
      rw [hrw, abs_mul]
      have hstep : |1 - faceCutoff i a σ n y| * |ψ y| ≤ 1 * M :=
        mul_le_mul (hcut_one_abs n y) hMy (abs_nonneg _) zero_le_one
      have : (0 : ℝ) ≤ L + 2 * L * HCPolySupport.smoothTransitionProfile.derivBound := by
        positivity
      linarith only [hstep, this]
  have hgrad : ∀ j : Fin d, Tendsto (fun n => eLpNorm
      (fun x => f.grad x j - (F n).grad x j) 2
        (volumeMeasureOn (faceHalf U i a σ))) atTop (nhds 0) := by
    intro j
    refine tendsto_eLpNorm_of_strip (C := C)
      (isOpen_faceHalf hU.isOpen i a σ).measurableSet
      (fun n => (isOpen_faceStrip hU.isOpen i a σ n).measurableSet) ?_ ?_
      (tendsto_volume_faceStrip hU i a σ)
      (fun n => ((f.gradMemL2 j).sub ((F n).gradMemL2 j)).aestronglyMeasurable)
    · intro n y hy hyS
      have h2 := houtside n y hy hyS
      have hzero : fderiv ℝ (faceCutoff i a σ n) y (basisVec j) = 0 := by
        rw [fderiv_faceCutoff_apply,
          HCPolySupport.smoothTransitionProfile.deriv_zero_of_one_le
            (by linarith only [h2])]
        ring
      rw [hfgrad y j, hFgrad n y j, hgdef,
        fderiv_faceCutoff_mul_apply hψ i a σ n y j, faceCutoff_eq_one h2, hzero]
      ring
    · intro n y
      rw [hfgrad y j, hFgrad n y j, hgdef,
        fderiv_faceCutoff_mul_apply hψ i a σ n y j, hCdef]
      have hrw : fderiv ℝ ψ y (basisVec j) -
          (faceCutoff i a σ n y * fderiv ℝ ψ y (basisVec j) +
            ψ y * fderiv ℝ (faceCutoff i a σ n) y (basisVec j)) =
          (1 - faceCutoff i a σ n y) * fderiv ℝ ψ y (basisVec j) -
            ψ y * fderiv ℝ (faceCutoff i a σ n) y (basisVec j) := by ring
      rw [hrw]
      have h1 : |(1 - faceCutoff i a σ n y) * fderiv ℝ ψ y (basisVec j)| ≤ L := by
        rw [abs_mul]
        have := mul_le_mul (hcut_one_abs n y) (abs_fderiv_apply_le hL0 hL y j)
          (abs_nonneg _) zero_le_one
        linarith only [this]
      have h2 := abs_mul_fderiv_faceCutoff_le hψ hL0 hL hσ hψ0 n y j
      have h3 := abs_sub ((1 - faceCutoff i a σ n y) * fderiv ℝ ψ y (basisVec j))
        (ψ y * fderiv ℝ (faceCutoff i a σ n) y (basisVec j))
      linarith only [h1, h2, h3, hM0]
  have hres := memH10_of_tendsto_H1 hHdom f F hmem hfun hgrad
  rwa [hftoFun] at hres

end

end Algsuperdiff.Section4.Provider.ExcessDecay
