/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicityTransferTests
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionGlue

/-!
# HarmonicityTransferFace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The single-face harmonicity transfer

Let `U` be an open bounded convex domain symmetric under the reflection `r` in
the hyperplane `{yᵢ = a}`, and let `H = faceHalf U i a σ` be one of the two open
halves it cuts.  If `v` is weakly harmonic on `H`, then its **odd extension**
across the face — `w = v - v ∘ r` after zero extension off `H` — is weakly
harmonic on all of `U`.

## Scope

The `H¹(U)` *packaging* of the odd extension is an **input** here: the theorem
takes an `H1Function U` whose recorded gradient is the odd extension of the
zero-extended gradient of `v`, and proves that it is weakly harmonic.  Producing
that packaging from a *localized* zero-trace hypothesis on the met face is the
separate job of the weak-gradient locality lemma
(`WeakGradientLocality.lean`) — the harmonicity proved here never uses the
zero-trace hypothesis, only the harmonicity of `v` on the half.

## References

* CoarseGraining, `Homogenization/Sobolev/Foundations/CubeReflection/` (the
  reflection, its measure preservation, and the *even* fold
  `foldedCoordFaceTest`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory Filter Topology

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Reflection algebra -/

/-- The coordinate reflection is self-adjoint for the coordinate dot product. -/
theorem vecDot_coordReflectionLinear_left (i : Fin d) (A B : Vec d) :
    vecDot (coordReflectionLinear i A) B = vecDot A (coordReflectionLinear i B) := by
  simp only [vecDot]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordReflectionLinear_apply_coord, coordReflectionLinear_apply_coord]
  ring

private theorem vecDot_sub_left (A B C : Vec d) :
    vecDot (A - B) C = vecDot A C - vecDot B C := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem vecDot_sub_right (A B C : Vec d) :
    vecDot A (B - C) = vecDot A B - vecDot A C := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The coordinates of the face reflection: the normal coordinate is flipped
about `a`, the tangential ones are untouched. -/
theorem coordFaceReflection_apply (a : ℝ) (i : Fin d) (y : Vec d) (j : Fin d) :
    coordFaceReflection a i y j = if j = i then 2 * a - y j else y j := by
  have hsplit : coordFaceReflection a i y j =
      coordReflectionLinear i y j + coordFaceReflectionOffset a i j := rfl
  rw [hsplit]
  by_cases hj : j = i
  · subst hj
    have h2 : coordReflectionLinear j y j = -(y j) := by simp [coordReflectionLinear]
    have h3 : coordFaceReflectionOffset a j j = 2 * a := by simp [coordFaceReflectionOffset]
    rw [h2, h3, ite_eq_left rfl]
    ring
  · have h2 : coordReflectionLinear i y j = y j := by simp [coordReflectionLinear, hj]
    have h3 : coordFaceReflectionOffset a i j = 0 := by simp [coordFaceReflectionOffset, hj]
    rw [h2, h3, ite_eq_right hj, add_zero]

/-- A point of the reflecting hyperplane is fixed. -/
theorem coordFaceReflection_eq_self {a : ℝ} {i : Fin d} {y : Vec d} (hy : y i = a) :
    coordFaceReflection a i y = y := by
  funext j
  rw [coordFaceReflection_apply]
  by_cases hj : j = i
  · subst hj
    rw [ite_eq_left rfl]
    linarith only [hy]
  · rw [ite_eq_right hj]

/-- If `U` is invariant under the reflection, so is the closed support of any
test function supported in `U` — hence the reflected test is again supported in
`U`. -/
theorem tsupport_comp_coordFaceReflection_subset {U : Set (Vec d)} (a : ℝ) (i : Fin d)
    (hUsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ U ↔ y ∈ U)
    {φ : Vec d → ℝ} (hφU : tsupport φ ⊆ U) :
    tsupport (fun z => φ (coordFaceReflection a i z)) ⊆ U := by
  have hpre : Function.support (fun z => φ (coordFaceReflection a i z)) =
      coordFaceReflection a i ⁻¹' Function.support φ := rfl
  have hclos : coordFaceReflection a i ⁻¹' closure (Function.support φ) =
      closure (coordFaceReflection a i ⁻¹' Function.support φ) :=
    (coordFaceReflectionHomeomorph a i).preimage_closure (Function.support φ)
  change closure (Function.support fun z => φ (coordFaceReflection a i z)) ⊆ U
  rw [hpre, ← hclos]
  intro z hz
  exact (hUsymm z).1 (hφU hz)

/-! ## 2. Integrability of the tested pairing -/

private theorem integrableOn_vecDot {W : Set (Vec d)} {A B : Vec d → Vec d}
    (hA : ∀ j, MemLp (fun y => A y j) 2 (volume.restrict W))
    (hB : ∀ j, MemLp (fun y => B y j) 2 (volume.restrict W)) :
    IntegrableOn (fun y => vecDot (A y) (B y)) W volume := by
  have hsum : (fun y => vecDot (A y) (B y)) = fun y => ∑ j : Fin d, A y j * B y j := by
    funext y
    rw [vecDot]
  rw [IntegrableOn, hsum]
  exact integrable_finsetSum _ fun j _ => (hA j).integrable_mul (hB j)

/-! ## 3. The transfer -/

/-- **The single-face harmonicity transfer.**

`U` is an open bounded convex domain invariant under the reflection `r` in
`{yᵢ = a}`; `H = faceHalf U i a σ` is the open half on the `σ`-side; `v` is
weakly harmonic on `H`; and `w` is an `H¹(U)` function whose gradient is the
*odd extension* of `v`'s gradient, zero-extended off `H`.  Then `w` is weakly
harmonic on `U`.

The proof folds the test function oddly, `ψ = φ - φ ∘ r`, uses to make `ψ` an
admissible `H¹₀(H)` competitor, and reduces the reflected half of the integral
to `H` by the measure-preserving change of variables. -/
theorem isWeaklyHarmonicOn_of_oddFaceExtendGrad {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {i : Fin d} {a σ : ℝ} (hσ : |σ| = 1)
    (hUsymm : ∀ y : Vec d, coordFaceReflection a i y ∈ U ↔ y ∈ U)
    (v : H1Function (faceHalf U i a σ))
    (hv : IsWeaklyHarmonicOn (faceHalf U i a σ) v)
    (w : H1Function U)
    (hw : ∀ y, w.grad y =
      oddFaceExtendGrad a i (zeroExtendGrad (faceHalf U i a σ) v.grad) y) :
    IsWeaklyHarmonicOn U w := by
  have hHopen : IsOpen (faceHalf U i a σ) := isOpen_faceHalf hU.isOpen i a σ
  have hHmeas : MeasurableSet (faceHalf U i a σ) := hHopen.measurableSet
  have hHsub : faceHalf U i a σ ⊆ U := faceHalf_subset U i a σ
  have hUmeas : MeasurableSet U := hU.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (faceHalf U i a σ)) :=
    (isOpenBoundedConvexDomain_faceHalf hU i a σ).isFiniteMeasure_restrict_volume
  -- the zero-extended gradient is globally `L²`
  have hGL2 : ∀ j : Fin d,
      MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad y j) 2
        (volume : Measure (Vec d)) := by
    intro j
    rw [zeroExtendGrad_apply_coord]
    exact (memLp_indicator_iff_restrict hHmeas).2 (v.gradMemL2 j)
  have hGrL2 : ∀ j : Fin d,
      MemLp (fun y => zeroExtendGrad (faceHalf U i a σ) v.grad
        (coordFaceReflection a i y) j) 2 (volume : Measure (Vec d)) := fun j =>
    (hGL2 j).comp_measurePreserving (measurePreserving_coordFaceReflection a i)
  refine isWeaklyHarmonicOn_of_contDiff_tests w ?_
  intro φ hφ hφc hφU
  -- the reflected test and the odd fold
  have hφr : ContDiff ℝ (⊤ : ℕ∞) fun z => φ (coordFaceReflection a i z) := by
    simpa [Function.comp] using! hφ.comp (contDiff_coordFaceReflection a i)
  have hφrc : HasCompactSupport fun z => φ (coordFaceReflection a i z) :=
    hasCompactSupport_comp_coordFaceReflection hφc a i
  have hφrU : tsupport (fun z => φ (coordFaceReflection a i z)) ⊆ U :=
    tsupport_comp_coordFaceReflection_subset a i hUsymm hφU
  have hψ : ContDiff ℝ (⊤ : ℕ∞) fun z => φ z - φ (coordFaceReflection a i z) :=
    hφ.sub hφr
  have hψc : HasCompactSupport fun z => φ z - φ (coordFaceReflection a i z) :=
    hφc.sub hφrc
  have hψU : tsupport (fun z => φ z - φ (coordFaceReflection a i z)) ⊆ U := by
    have hsub : Function.support (fun z => φ z - φ (coordFaceReflection a i z)) ⊆
        tsupport φ ∪ tsupport (fun z => φ (coordFaceReflection a i z)) := by
      intro z hz
      simp only [Function.mem_support] at hz
      by_contra hcon
      simp only [Set.mem_union, not_or] at hcon
      have h1 : φ z = 0 := image_eq_zero_of_notMem_tsupport hcon.1
      have h2 : φ (coordFaceReflection a i z) = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z => φ (coordFaceReflection a i z)) hcon.2
      exact hz (by rw [h1, h2, sub_self])
    have hclosed : IsClosed
        (tsupport φ ∪ tsupport (fun z => φ (coordFaceReflection a i z))) :=
      (isClosed_tsupport φ).union (isClosed_tsupport _)
    exact (closure_minimal hsub hclosed).trans (Set.union_subset hφU hφrU)
  have hψ0 : ∀ y : Vec d, y i = a → φ y - φ (coordFaceReflection a i y) = 0 := by
    intro y hy
    rw [coordFaceReflection_eq_self hy, sub_self]
  have hmem : MemH10 (faceHalf U i a σ) (fun z => φ z - φ (coordFaceReflection a i z)) :=
    memH10_faceHalf_of_contDiff_of_vanishing_on_face hU hσ hψ hψc hψU hψ0
  have hzero := integral_vecDot_euclideanGradient_eq_zero hHopen hv hψ hmem
  -- the gradient of the odd fold
  have hgradcomp : ∀ y : Vec d,
      euclideanGradient (fun z => φ (coordFaceReflection a i z)) y =
        coordReflectionLinear i (euclideanGradient φ (coordFaceReflection a i y)) :=
    fun y => euclideanGradient_comp_coordFaceReflection hφ a i y
  have hgradψ : ∀ y : Vec d,
      euclideanGradient (fun z => φ z - φ (coordFaceReflection a i z)) y =
        euclideanGradient φ y -
          euclideanGradient (fun z => φ (coordFaceReflection a i z)) y := by
    intro y
    funext j
    change (fderiv ℝ (fun z => φ z - φ (coordFaceReflection a i z)) y) (basisVec j) =
      (fderiv ℝ φ y) (basisVec j) -
        (fderiv ℝ (fun z => φ (coordFaceReflection a i z)) y) (basisVec j)
    rw [fderiv_fun_sub (hφ.differentiable (by simp) y) (hφr.differentiable (by simp) y)]
    simp
  -- `L²` data of the two test gradients
  have hDφL2 : ∀ j : Fin d,
      MemLp (fun y => euclideanGradient φ y j) 2 (volume : Measure (Vec d)) := by
    intro j
    have h := memLp_two_fderiv_apply_restrict (W := (Set.univ : Set (Vec d))) hφ hφc j
    rwa [Measure.restrict_univ] at h
  have hDφrL2 : ∀ j : Fin d,
      MemLp (fun y => euclideanGradient (fun z => φ (coordFaceReflection a i z)) y j) 2
        (volume : Measure (Vec d)) := by
    intro j
    have h := memLp_two_fderiv_apply_restrict (W := (Set.univ : Set (Vec d))) hφr hφrc j
    rwa [Measure.restrict_univ] at h
  -- collapsing an integral over `U` against the zero-extended gradient onto `H`
  have hcollapse : ∀ K : Vec d → Vec d,
      (∀ j, MemLp (fun y => K y j) 2 (volume : Measure (Vec d))) →
      ∫ y in U, vecDot (zeroExtendGrad (faceHalf U i a σ) v.grad y) (K y) ∂volume =
        ∫ y in faceHalf U i a σ, vecDot (v.grad y) (K y) ∂volume := by
    intro K _hK
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hHsub ?_]
    · refine setIntegral_congr_fun hHmeas fun y hy => ?_
      rw [zeroExtendGrad_of_mem _ hy]
    · intro y hy
      rw [zeroExtendGrad_of_notMem _ hy.2]
      simp [vecDot]
  -- the two `U`-integrands are integrable
  have hK1int : IntegrableOn
      (fun y => vecDot (zeroExtendGrad (faceHalf U i a σ) v.grad y)
        (euclideanGradient φ y)) U volume :=
    integrableOn_vecDot (fun j => (hGL2 j).restrict U) (fun j => (hDφL2 j).restrict U)
  have hK2int : IntegrableOn
      (fun y => vecDot (coordReflectionLinear i
        (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)))
        (euclideanGradient φ y)) U volume := by
    refine integrableOn_vecDot (fun j => ?_) (fun j => (hDφL2 j).restrict U)
    have hj : (fun y => coordReflectionLinear i
        (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)) j) =
        fun y => (if j = i then (-1 : ℝ) else 1) *
          zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y) j := by
      funext y
      rw [coordReflectionLinear_apply_coord]
    rw [hj]
    exact ((hGrL2 j).const_mul _).restrict U
  -- split the tested integral
  have hsplit : ∫ y in U, vecDot (w.grad y) (euclideanGradient φ y) ∂volume =
      (∫ y in U, vecDot (zeroExtendGrad (faceHalf U i a σ) v.grad y)
        (euclideanGradient φ y) ∂volume) -
      ∫ y in U, vecDot (coordReflectionLinear i
        (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)))
        (euclideanGradient φ y) ∂volume := by
    rw [← integral_sub hK1int hK2int]
    refine setIntegral_congr_fun hUmeas fun y _ => ?_
    rw [hw y]
    exact vecDot_sub_left _ _ _
  -- the change of variables on the reflected term
  have hpre : coordFaceReflection a i ⁻¹' U = U := by
    ext z
    exact hUsymm z
  have hcov : ∫ y in U, vecDot (coordReflectionLinear i
      (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)))
      (euclideanGradient φ y) ∂volume =
      ∫ y in U, vecDot (zeroExtendGrad (faceHalf U i a σ) v.grad y)
        (euclideanGradient (fun z => φ (coordFaceReflection a i z)) y) ∂volume := by
    have h := (measurePreserving_coordFaceReflection a i).setIntegral_preimage_emb
      (measurableEmbedding_coordFaceReflection a i)
      (fun y => vecDot (coordReflectionLinear i
        (zeroExtendGrad (faceHalf U i a σ) v.grad y))
        (euclideanGradient φ (coordFaceReflection a i y))) U
    rw [hpre] at h
    calc ∫ y in U, vecDot (coordReflectionLinear i
          (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)))
          (euclideanGradient φ y) ∂volume
        = ∫ y in U, vecDot (coordReflectionLinear i
            (zeroExtendGrad (faceHalf U i a σ) v.grad (coordFaceReflection a i y)))
            (euclideanGradient φ (coordFaceReflection a i
              (coordFaceReflection a i y))) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [coordFaceReflection_involutive]
      _ = ∫ y in U, vecDot (coordReflectionLinear i
            (zeroExtendGrad (faceHalf U i a σ) v.grad y))
            (euclideanGradient φ (coordFaceReflection a i y)) ∂volume := h
      _ = ∫ y in U, vecDot (zeroExtendGrad (faceHalf U i a σ) v.grad y)
            (euclideanGradient (fun z => φ (coordFaceReflection a i z)) y) ∂volume := by
          refine setIntegral_congr_fun hUmeas fun y _ => ?_
          rw [vecDot_coordReflectionLinear_left, ← hgradcomp y]
  -- recombine on the half
  have hHint1 : IntegrableOn
      (fun y => vecDot (v.grad y) (euclideanGradient φ y)) (faceHalf U i a σ) volume :=
    integrableOn_vecDot v.gradMemL2 (fun j => (hDφL2 j).restrict _)
  have hHint2 : IntegrableOn
      (fun y => vecDot (v.grad y)
        (euclideanGradient (fun z => φ (coordFaceReflection a i z)) y))
      (faceHalf U i a σ) volume :=
    integrableOn_vecDot v.gradMemL2 (fun j => (hDφrL2 j).restrict _)
  have hfold : (∫ y in faceHalf U i a σ, vecDot (v.grad y) (euclideanGradient φ y) ∂volume) -
      ∫ y in faceHalf U i a σ, vecDot (v.grad y)
        (euclideanGradient (fun z => φ (coordFaceReflection a i z)) y) ∂volume =
      ∫ y in faceHalf U i a σ, vecDot (v.grad y)
        (euclideanGradient (fun z => φ z - φ (coordFaceReflection a i z)) y) ∂volume := by
    rw [← integral_sub hHint1 hHint2]
    refine setIntegral_congr_fun hHmeas fun y _ => ?_
    rw [hgradψ y, vecDot_sub_right]
  rw [hsplit, hcov, hcollapse _ hDφL2, hcollapse _ hDφrL2, hfold]
  exact hzero

end

end Algsuperdiff.Section4.Provider.ExcessDecay
