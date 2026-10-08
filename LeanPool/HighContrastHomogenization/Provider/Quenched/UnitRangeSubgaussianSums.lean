/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellSeparation
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.ColourIndependence
public import Mathlib.Probability.Moments.SubGaussian

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeSubgaussianSums

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Sub-Gaussian sums of bounded local observables under unit range

Unit range of dependence makes a family of observables carried by pairwise
`ℓ^∞`-separated regions jointly independent.  Bounded centred random variables
have sub-Gaussian moment-generating functions by Hoeffding's lemma, and the
moment-generating function of a sum of independent sub-Gaussian variables is the
product of theirs, so a sum over a separated family is sub-Gaussian with
parameter the number of its members.

The family the concentration-for-sums condition is stated for is not separated:
neighbouring standard aligned cubes touch.  It becomes separated after a triadic
colouring, and the moment-generating function of the whole sum is bounded by the
product of the colour-class ones without any independence between the colours.
The Cauchy–Schwarz inequality turns the resulting sum of square roots into the
dimensional parameter `3^d N` for a family of `N` cubes.

Every constant produced here is a power of three in the dimension: nothing in
this file sees a law, a reference block, a source scale or an exponent.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory ProbabilityTheory

open scoped NNReal

noncomputable section

variable {d : ℕ}

/-! ## Two facts about sub-Gaussian moment-generating functions -/

/-- The sub-Gaussian parameter may be enlarged. -/
theorem hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c c' : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') :
    HasSubgaussianMGF X c' μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := by
    refine (h.mgf_le t).trans (Real.exp_le_exp.2 ?_)
    have hcc : (c : ℝ) ≤ (c' : ℝ) := NNReal.coe_le_coe.2 hc
    have hmul := mul_le_mul_of_nonneg_right hcc (sq_nonneg t)
    linarith only [hmul]

/-- A finite sum of sub-Gaussian variables, with no independence assumed, is
sub-Gaussian with the square of the sum of the square roots of the parameters. -/
theorem hasSubgaussianMGF_finset_sum {Ω κ : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : κ → Ω → ℝ} {n : κ → ℝ≥0}
    (T : Finset κ) (h : ∀ c ∈ T, HasSubgaussianMGF (Y c) (n c) μ) :
    HasSubgaussianMGF (fun a => ∑ c ∈ T, Y c a) ((∑ c ∈ T, NNReal.sqrt (n c)) ^ 2) μ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert c T hc ih =>
      have hstep := ih fun e he => h e (Finset.mem_insert_of_mem he)
      have hhead := h c (Finset.mem_insert_self c T)
      have hadd := hhead.add hstep
      rw [NNReal.sqrt_sq] at hadd
      have hfun : (fun a => ∑ e ∈ insert c T, Y e a)
          = fun a => Y c a + ∑ e ∈ T, Y e a := by
        funext a
        rw [Finset.sum_insert hc]
      rw [hfun, Finset.sum_insert hc]
      exact hadd

/-! ## Bounded centred observables -/

/-- Hoeffding's lemma on the coefficient space: a centred observable bounded by
one has a sub-Gaussian moment-generating function with parameter one. -/
theorem hasSubgaussianMGF_of_abs_le_one {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {X : CoeffSpace d → ℝ} (hm : AEMeasurable X P)
    (hbd : ∀ᵐ a ∂P, |X a| ≤ 1) (hmean : ∫ a, X a ∂P = 0) :
    HasSubgaussianMGF X 1 P := by
  have hIcc : ∀ᵐ a ∂P, X a ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hbd] with a ha
    exact Set.mem_Icc.2 (abs_le.1 ha)
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hIcc hmean
  have hpar : (‖(1 : ℝ) - (-1 : ℝ)‖₊ / 2) ^ 2 = 1 := by norm_num
  rwa [hpar] at h

/-! ## Sums over a separated family -/

/-- **A sum of centred observables bounded by one, each measurable for the local
sigma-field of its own region, over a pairwise unit-separated family of regions,
is sub-Gaussian with parameter the number of summands.** -/
theorem hasSubgaussianMGF_sum_of_pairwise_unitSeparated {ι : Type*}
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {U : ι → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j => UnitSeparated (U i) (U j))
    {X : ι → CoeffSpace d → ℝ}
    (hXloc : ∀ i, @Measurable (CoeffSpace d) ℝ (coeffSigma d (U i)) _ (X i))
    (hXbd : ∀ i, ∀ᵐ a ∂P, |X i a| ≤ 1)
    (hXmean : ∀ i, ∫ a, X i a ∂P = 0) (s : Finset ι) :
    HasSubgaussianMGF (fun a => ∑ i ∈ s, X i a) (s.card : ℝ≥0) P := by
  have hindep : iIndepFun X P :=
    Recurrence.iIndepFun_of_measurable_coeffSigma P hP hU hXloc hsep
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) 1 P := fun i _ =>
    hasSubgaussianMGF_of_abs_le_one
      (Recurrence.measurable_of_measurable_coeffSigma (hXloc i)).aemeasurable (hXbd i) (hXmean i)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hindep (c := fun _ => (1 : ℝ≥0)) hsub
  simpa using h

/-! ## Sums over one colour class of standard aligned cubes -/

/-- A sum of centred observables bounded by one, each local to its own standard
aligned cube, over a family of cubes of one colour, is sub-Gaussian with
parameter the number of cubes. -/
theorem hasSubgaussianMGF_sum_standardCell_colour
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _ (X w))
    (hXbd : ∀ w, ∀ᵐ a ∂P, |X w a| ≤ 1)
    (hXmean : ∀ w, ∫ a, X w a ∂P = 0)
    (c : Fin d → ZMod 3) (Zc : Finset (Fin d → ℤ))
    (hZc : ∀ w ∈ Zc, (fun i => ((w i : ZMod 3))) = c) :
    HasSubgaussianMGF (fun a => ∑ w ∈ Zc, X w a) (Zc.card : ℝ≥0) P := by
  classical
  set col : (Fin d → ℤ) → Fin d → ZMod 3 := fun w i => ((w i : ZMod 3)) with hcol
  set U : (Fin d → ℤ) → Set (Vec d) :=
    fun w => if col w = c then standardCell d k w else ∅ with hU
  set Y : (Fin d → ℤ) → CoeffSpace d → ℝ :=
    fun w => if col w = c then X w else 0 with hY
  have hUmeas : ∀ w, MeasurableSet (U w) := by
    intro w
    by_cases hw : col w = c
    · simpa [hU, hw] using measurableSet_standardCell d k w
    · simp [hU, hw]
  have hsep : Pairwise fun w w' => UnitSeparated (U w) (U w') := by
    intro w w' hww
    by_cases hw : col w = c
    · by_cases hw' : col w' = c
      · have hcolour : (fun i => ((w i : ZMod 3))) = fun i => ((w' i : ZMod 3)) := by
          rw [show (fun i => ((w i : ZMod 3))) = col w from rfl,
            show (fun i => ((w' i : ZMod 3))) = col w' from rfl, hw, hw']
        simpa [hU, hw, hw'] using
          unitSeparated_standardCell_of_intCast_eq hk hww hcolour
      · simp only [hU, ite_eq_right hw']
        intro x y _ hy
        exact absurd hy (Set.notMem_empty y)
    · simp only [hU, ite_eq_right hw]
      intro x y hx _
      exact absurd hx (Set.notMem_empty x)
  have hYloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (U w)) _ (Y w) := by
    intro w
    by_cases hw : col w = c
    · have hUw : U w = standardCell d k w := by simp [hU, hw]
      rw [hUw]
      simpa [hY, hw] using hXloc w
    · simp only [hY, ite_eq_right hw]
      exact measurable_const
  have hYbd : ∀ w, ∀ᵐ a ∂P, |Y w a| ≤ 1 := by
    intro w
    by_cases hw : col w = c
    · simpa [hY, hw] using! hXbd w
    · simp [hY, hw]
  have hYmean : ∀ w, ∫ a, Y w a ∂P = 0 := by
    intro w
    by_cases hw : col w = c
    · simpa [hY, hw] using hXmean w
    · simp [hY, hw]
  have hmain := hasSubgaussianMGF_sum_of_pairwise_unitSeparated hP hUmeas hsep hYloc
    hYbd hYmean Zc
  have hfun : (fun a => ∑ w ∈ Zc, Y w a) = fun a => ∑ w ∈ Zc, X w a := by
    funext a
    refine Finset.sum_congr rfl fun w hw => ?_
    have hwc : col w = c := hZc w hw
    simp [hY, hwc]
  rwa [hfun] at hmain

/-! ## Sums over the whole family -/

/-- **The concentration-for-sums moment bound.**  A sum of centred observables
bounded by one, each local to its own standard aligned cube of a common
nonnegative scale, is sub-Gaussian with the dimensional parameter `3^d N`, where
`N` is the number of cubes.  The colour classes carry independence; the sum over
the at most `3^d` colours costs the Cauchy–Schwarz factor. -/
theorem hasSubgaussianMGF_sum_standardCell
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ w, @Measurable (CoeffSpace d) ℝ (coeffSigma d (standardCell d k w)) _ (X w))
    (hXbd : ∀ w, ∀ᵐ a ∂P, |X w a| ≤ 1)
    (hXmean : ∀ w, ∫ a, X w a ∂P = 0) (Z : Finset (Fin d → ℤ)) :
    HasSubgaussianMGF (fun a => ∑ w ∈ Z, X w a) (((3 ^ d * Z.card : ℕ) : ℝ≥0)) P := by
  classical
  set col : (Fin d → ℤ) → Fin d → ZMod 3 := fun w i => ((w i : ZMod 3)) with hcoldef
  set T : Finset (Fin d → ZMod 3) := Z.image col with hTdef
  set part : (Fin d → ZMod 3) → Finset (Fin d → ℤ) :=
    fun c => Z.filter fun w => col w = c with hpartdef
  have hdisj : (↑T : Set (Fin d → ZMod 3)).PairwiseDisjoint part :=
    Recurrence.pairwiseDisjoint_filter_intCast Z
  have hunion : T.biUnion part = Z := Recurrence.biUnion_filter_intCast_eq Z
  have hsumsplit : (fun a => ∑ w ∈ Z, X w a)
      = fun a => ∑ c ∈ T, ∑ w ∈ part c, X w a := by
    funext a
    rw [← hunion, Finset.sum_biUnion hdisj]
  have hcolour : ∀ c ∈ T,
      HasSubgaussianMGF (fun a => ∑ w ∈ part c, X w a) (((part c).card : ℝ≥0)) P := by
    intro c _
    refine hasSubgaussianMGF_sum_standardCell_colour hP hk hXloc hXbd hXmean c (part c) ?_
    intro w hw
    exact (Finset.mem_filter.1 hw).2
  have hagg := hasSubgaussianMGF_finset_sum (μ := P) T hcolour
  rw [← hsumsplit] at hagg
  refine hasSubgaussianMGF_mono hagg ?_
  have hcs : (∑ c ∈ T, NNReal.sqrt (((part c).card : ℝ≥0))) ^ 2
      ≤ (T.card : ℝ≥0) * ∑ c ∈ T, NNReal.sqrt (((part c).card : ℝ≥0)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsq : ∀ c, NNReal.sqrt (((part c).card : ℝ≥0)) ^ 2 = ((part c).card : ℝ≥0) :=
    fun c => NNReal.sq_sqrt _
  have hcard : ∑ c ∈ T, ((part c).card : ℝ≥0) = (Z.card : ℝ≥0) := by
    have hnat : ∑ c ∈ T, (part c).card = Z.card := by
      rw [← hunion, Finset.card_biUnion hdisj]
    calc ∑ c ∈ T, ((part c).card : ℝ≥0)
        = ((∑ c ∈ T, (part c).card : ℕ) : ℝ≥0) := by push_cast; ring
      _ = (Z.card : ℝ≥0) := by rw [hnat]
  have hTcard : (T.card : ℝ≥0) ≤ ((3 ^ d : ℕ) : ℝ≥0) := by
    exact_mod_cast Recurrence.card_image_intCast_le Z
  calc (∑ c ∈ T, NNReal.sqrt (((part c).card : ℝ≥0))) ^ 2
      ≤ (T.card : ℝ≥0) * ∑ c ∈ T, NNReal.sqrt (((part c).card : ℝ≥0)) ^ 2 := hcs
    _ = (T.card : ℝ≥0) * (Z.card : ℝ≥0) := by
        simp only [hsq]
        rw [hcard]
    _ ≤ ((3 ^ d : ℕ) : ℝ≥0) * (Z.card : ℝ≥0) := by gcongr
    _ = ((3 ^ d * Z.card : ℕ) : ℝ≥0) := by push_cast; ring

end

end Quenched
end HighContrast
end HCPolySupport
