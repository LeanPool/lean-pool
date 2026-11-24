/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalNonPluripolar
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothBedfordTaylorMeasure

/-!
# Smooth density of the non-pluripolar product away from poles

On a relatively compact coordinate open set contained in one common strict
truncation locus, the mixed non-pluripolar limit stabilizes at that truncation.
If the underlying finite potentials are smooth there, this stabilized measure
is precisely the smooth mixed Bedford--Taylor density measure.  The argument
uses the actual truncation limit and canonical Bedford--Taylor measure; it does
not assume a comparison with a separately defined mass.

For the diagonal global product, this is the local measure-theoretic half of
the comparison with `acTopMass`.  The remaining bridge is the separate
finite-dimensional identity between the genuine exterior-power density
`actualTopPowerDensity` and the determinant density `smoothDensity`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
open FirstPass.MixedNonPluripolar MixedNonPluripolar MixedMongeAmpere BedfordTaylor

variable {n : ℕ}

/-- Germ equality of real potentials identifies their complex Hessians. -/
theorem complexHessian_congr_of_eventuallyEq
    {a b : ComplexModel n → ℝ} {z : ComplexModel n}
    (hab : a =ᶠ[𝓝 z] b) :
    complexHessian a z = complexHessian b z := by
  have hsecond : fderiv ℝ (fderiv ℝ a) z = fderiv ℝ (fderiv ℝ b) z :=
    hab.fderiv.fderiv_eq
  ext j k
  simp only [complexHessian, realHessian_eq_fderiv, hsecond]

/-- Smooth mixed PSH certificates transport across equality on an open set.
The mixed-density nonnegativity is transported through the Hessian equality,
rather than being assumed again. -/
theorem isSmoothMixedPshOn_of_eqOn
    {W : Opens (ComplexModel n)} {a b : Fin n → ComplexModel n → ℝ}
    (hb : IsSmoothMixedPshOn W b) (hab : ∀ i, EqOn (a i) (b i) W) :
    IsSmoothMixedPshOn W a := by
  refine ⟨?_, ?_⟩
  · intro i
    apply isSmoothPshOn_of_psh
    · exact (hb.component i).1.congr fun z hz => hab i hz
    · intro z hz
      apply ((hb.component i).2.1 z hz).congr
      filter_upwards [W.isOpen.mem_nhds hz] with y hy
      exact congrArg (fun r : ℝ => (r : EReal)) (hab i hy).symm
  · intro z hz
    have hnear (i : Fin n) : a i =ᶠ[𝓝 z] b i := by
      filter_upwards [W.isOpen.mem_nhds hz] with y hy
      exact hab i hy
    have hH : (fun i => complexHessian (a i) z) =
        (fun i => complexHessian (b i) z) := by
      funext i
      exact complexHessian_congr_of_eventuallyEq (hnear i)
    rw [mixedDensity, hH]
    exact hb.density_nonneg z hz

/-- On a common strict truncation locus, smoothness of the original finite
potentials supplies smoothness of the real truncations. -/
theorem mixedTruncationReal_isSmoothMixedPshOn_of_eqOn
    {Ω W : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (k : ℕ) (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Ω u k)
    (hu : IsSmoothMixedPshOn W (fun i z => (u i z).toReal)) :
    IsSmoothMixedPshOn W (mixedTruncationReal u k) :=
  isSmoothMixedPshOn_of_eqOn hu fun i _ hz =>
    mixedTruncationReal_eq_on_commonStrictLocus k i (hWk hz)

/-- Smooth mixed density measures are invariant under equality on their open
coordinate domain. -/
theorem smoothMixedMeasure_eq_of_eqOn
    {W : Opens (ComplexModel n)} {a b : Fin n → ComplexModel n → ℝ}
    (ha : IsSmoothMixedPshOn W a) (hb : IsSmoothMixedPshOn W b)
    (hab : ∀ i, EqOn (a i) (b i) W) :
    smoothMixedMeasure W a ha = smoothMixedMeasure W b hb := by
  unfold smoothMixedMeasure
  apply withDensity_congr_ae
  apply ae_restrict_of_forall_mem W.isOpen.measurableSet
  intro z hz
  have hnear (i : Fin n) : a i =ᶠ[𝓝 z] b i := by
    filter_upwards [W.isOpen.mem_nhds hz] with y hy
    exact hab i hy
  have hH : (fun i => complexHessian (a i) z) =
      (fun i => complexHessian (b i) z) := by
    funext i
    exact complexHessian_congr_of_eventuallyEq (hnear i)
  change ENNReal.ofReal ((mixedCoefficient (fun i => complexHessian (a i) z)).re / Real.pi ^ n) =
    ENNReal.ofReal (mixedDensity b z)
  rw [hH]
  rfl

/-- The non-pluripolar truncation limit has its literal smooth density on a
relatively compact open set inside one common strict locus. -/
theorem mixedTruncationLimitMeasure_restrict_smooth
    {Ω W : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ)
    (hW : RelativelyCompactIn W Ω)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Ω u k)
    (hsm : IsSmoothMixedPshOn W (mixedTruncationReal u k)) :
    (mixedTruncationLimitMeasure Ω u hu).restrict (W : Set (ComplexModel n)) =
      smoothMixedMeasure W (mixedTruncationReal u k) hsm := by
  calc
    (mixedTruncationLimitMeasure Ω u hu).restrict (W : Set (ComplexModel n)) =
        ((mixedTruncationLimitMeasure Ω u hu).restrict (commonStrictLocus Ω u k)).restrict
          (W : Set (ComplexModel n)) :=
      (Measure.restrict_restrict_of_subset hWk).symm
    _ = (mixedTruncationMeasure Ω u hu k).restrict (W : Set (ComplexModel n)) := by
      rw [mixedTruncationLimitMeasure_restrict_commonStrictLocus hu k]
    _ = (canonicalMixedBedfordTaylorMeasure Ω (mixedTruncationReal u k)
        (mixedTruncationReal_isLocallyBounded hu k)).restrict (W : Set (ComplexModel n)) := by
      unfold mixedTruncationMeasure
      rw [Measure.restrict_restrict_of_subset hWk]
    _ = smoothMixedMeasure W (mixedTruncationReal u k) hsm :=
      canonicalMixedBedfordTaylorMeasure_restrict_smooth
        (mixedTruncationReal_isLocallyBounded hu k) hW hsm

/-- The preceding local equality can be expressed with the original finite
potentials, since real truncations agree with them on the strict locus. -/
theorem mixedTruncationLimitMeasure_restrict_smooth_of_original
    {Ω W : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → EReal}
    (hu : ∀ i, PlurisubharmonicOn (u i) Ω) (k : ℕ)
    (hW : RelativelyCompactIn W Ω)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Ω u k)
    (hsm : IsSmoothMixedPshOn W (fun i z => (u i z).toReal)) :
    (mixedTruncationLimitMeasure Ω u hu).restrict (W : Set (ComplexModel n)) =
      smoothMixedMeasure W (fun i z => (u i z).toReal) hsm := by
  let htrunc := mixedTruncationReal_isSmoothMixedPshOn_of_eqOn k hWk hsm
  calc
    (mixedTruncationLimitMeasure Ω u hu).restrict (W : Set (ComplexModel n)) =
        smoothMixedMeasure W (mixedTruncationReal u k) htrunc :=
      mixedTruncationLimitMeasure_restrict_smooth hu k hW hWk htrunc
    _ = smoothMixedMeasure W (fun i z => (u i z).toReal) hsm :=
      smoothMixedMeasure_eq_of_eqOn htrunc hsm fun i z hz =>
        mixedTruncationReal_eq_on_commonStrictLocus k i (hWk hz)

open FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches GlobalNonPluripolar

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Restricting the global measure to one concrete patch, followed by the
literal `Patch.pushMeasure` evaluation, identifies an inverse-chart image with
the smooth mixed measure obtained from the stabilized truncation limit. -/
theorem globalMixedMeasure_coordinate_inverse_image_eq_smoothMixedMeasure
    {theta : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (theta i).val (u i))
    (Q : Patch theta u) (W : Opens (ComplexModel n)) (hWQ : W ≤ Q.domain)
    (k : ℕ) (hW : RelativelyCompactIn W Q.domain)
    (hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k)
    (hsm : IsSmoothMixedPshOn W (fun i z => (Q.corrected i z).toReal))
    {S : Set (ComplexModel n)} (hSW : S ⊆ W) :
    globalMixedMeasure theta u hu (Q.chart.val.symm '' S) =
      smoothMixedMeasure W (fun i z => (Q.corrected i z).toReal) hsm S := by
  have hSQ : S ⊆ Q.domain := hSW.trans hWQ
  have hsource : Q.chart.val.symm '' S ⊆ (Q.source : Set M) := by
    rintro x ⟨z, hz, rfl⟩
    exact Q.map_target (hSQ hz)
  have hpreimage : (Q.domain : Set (ComplexModel n)) ∩
      Q.chart.val.symm ⁻¹' (Q.chart.val.symm '' S) = S := by
    ext z
    constructor
    · rintro ⟨hzD, y, hyS, hy⟩
      have hyD : y ∈ Q.domain := hSQ hyS
      have hzy : z = y := by
        calc
          z = Q.chart.val (Q.chart.val.symm z) :=
            (Q.chart.val.right_inv (Q.domain_le_target hzD)).symm
          _ = Q.chart.val (Q.chart.val.symm y) := congrArg Q.chart.val hy.symm
          _ = y := Q.chart.val.right_inv (Q.domain_le_target hyD)
      exact hzy.symm ▸ hyS
    · intro hz
      exact ⟨hSQ hz, ⟨z, hz, rfl⟩⟩
  have hpatch : patchMeasure Q (Q.chart.val.symm '' S) =
      mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S := by
    rw [patchMeasure, Q.pushMeasure_apply, hpreimage]
  have hrestrict :
      mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S =
        (mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
          (W : Set (ComplexModel n)) S := by
    symm
    rw [Measure.restrict_apply' W.isOpen.measurableSet,
      inter_eq_self_of_subset_left hSW]
  have hlocal := mixedTruncationLimitMeasure_restrict_smooth_of_original
    Q.plurisubharmonic k hW hWk hsm
  calc
    globalMixedMeasure theta u hu (Q.chart.val.symm '' S) =
        (globalMixedMeasure theta u hu).restrict (Q.source : Set M)
          (Q.chart.val.symm '' S) := by
      symm
      rw [Measure.restrict_apply' Q.source.isOpen.measurableSet,
        inter_eq_self_of_subset_left hsource]
    _ = patchMeasure Q (Q.chart.val.symm '' S) :=
      congrArg (fun mu : Measure M => mu (Q.chart.val.symm '' S))
        (globalMixedMeasure_restrict_patch hu Q)
    _ = mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic S := hpatch
    _ = (mixedTruncationLimitMeasure Q.domain Q.corrected Q.plurisubharmonic).restrict
          (W : Set (ComplexModel n)) S := hrestrict
    _ = smoothMixedMeasure W (fun i z => (Q.corrected i z).toReal) hsm S :=
      congrArg (fun mu : Measure (ComplexModel n) => mu S) hlocal

end SGPT.Foundations.Analysis.Pending.LocalNonPluripolarDensity
