/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Basic

/-!
# Local Sobolev Calculus

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open Filter
open scoped ENNReal Topology InnerProductSpace
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Appending a final letter to a derivative word applies that derivative last. -/
theorem wordDeriv_append (α : List (Fin 3)) (j : Fin 3) (g : Vec3 → ℝ) :
    wordDeriv (α ++ [j]) g = spatialDeriv (wordDeriv α g) j := by
  induction α generalizing g with
  | nil => rfl
  | cons i α ih =>
      simp only [List.cons_append, wordDeriv]
      exact ih (spatialDeriv g i)

/-- Every ordered derivative of a smooth function is smooth. -/
theorem contDiff_wordDeriv {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (α : List (Fin 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (wordDeriv α g) := by
  induction α generalizing g with
  | nil => simpa [wordDeriv] using hg
  | cons j α ih =>
      have hderiv : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g j) := by
        have hfderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) :=
          hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        exact hfderiv.clm_apply contDiff_const
      exact ih hderiv

/-- A smooth function with square-integrable derivatives gives its classical
ordered derivatives as a Sobolev family. -/
theorem isSobolevFamilyOn_wordDeriv {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ m →
      MemLp (wordDeriv α g) 2 (volume.restrict U)) :
    IsSobolevFamilyOn m U g (fun α => wordDeriv α g) := by
  refine ⟨?_, hL2, ?_⟩
  · exact Filter.EventuallyEq.rfl
  · intro α j hα
    rw [wordDeriv_append]
    exact (HasWeakPartialDerivOn.of_contDiff
      ((contDiff_wordDeriv hg α).of_le (by simp))).restrict hU (Set.subset_univ U)

/-- A family through order `m + 1` consists of its order-zero family, its
first derivatives, and the shifted families through order `m`. -/
theorem isSobolevFamilyOn_succ_iff {m : ℕ} {U : Set Vec3} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} :
    IsSobolevFamilyOn (m + 1) U f D ↔
      IsSobolevFamilyOn 0 U f D ∧ ∀ j : Fin 3,
        HasWeakPartialDerivOn U j (D []) (D [j]) ∧
          IsSobolevFamilyOn m U (D [j]) (fun α => D (j :: α)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ⟨h.zero, fun α hα => h.memL2 α (by omega), fun α j hα =>
        h.weak α j (by omega)⟩
    · intro j
      refine ⟨h.weak [] j (by simp), ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · rfl
      · intro α hα
        exact h.memL2 (j :: α) (by simp only [List.length_cons]; omega)
      · intro α k hα
        simpa only [List.cons_append] using
          h.weak (j :: α) k (by simp only [List.length_cons]; omega)
  · rintro ⟨hzero, hj⟩
    refine ⟨hzero.zero, ?_, ?_⟩
    · intro α hα
      by_cases hnil : α = []
      · subst α
        exact hzero.memL2 [] (by simp)
      · obtain ⟨j, β, rfl⟩ := List.exists_cons_of_ne_nil hnil
        exact (hj j).2.memL2 β (by simp only [List.length_cons] at hα; omega)
    · intro α j hα
      by_cases hnil : α = []
      · subst α
        exact (hj j).1
      · obtain ⟨i, β, rfl⟩ := List.exists_cons_of_ne_nil hnil
        have hα' : β.length < m := by simp only [List.length_cons] at hα; omega
        exact (hj i).2.weak β j hα'

/-- A Sobolev family restricts to every lower derivative order. -/
theorem IsSobolevFamilyOn.of_le {m m' : ℕ} {U : Set Vec3} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn m U f D) (hm : m' ≤ m) :
    IsSobolevFamilyOn m' U f D := by
  refine ⟨h.zero, ?_, ?_⟩
  · intro α hα
    exact h.memL2 α (hα.trans hm)
  · intro α j hα
    exact h.weak α j (lt_of_lt_of_le hα hm)

/-- A Sobolev family restricts to an open subset of its domain. -/
theorem IsSobolevFamilyOn.mono_set {m : ℕ} {U V : Set Vec3} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn m U f D)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsSobolevFamilyOn m V f D := by
  refine ⟨?_, ?_, ?_⟩
  · exact h.zero.filter_mono
      (ae_mono (Measure.restrict_mono hVU le_rfl))
  · intro α hα
    exact (h.memL2 α hα).mono_measure (Measure.restrict_mono hVU le_rfl)
  · intro α j hα
    exact (h.weak α j hα).restrict hV hVU

private theorem localSobolev_memLp_test {U : Set Vec3} {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    MemLp φ 2 (volume.restrict U) := by
  exact (hφ.continuous.memLp_of_hasCompactSupport (p := 2) hφc).mono_measure
    Measure.restrict_le_self

private theorem localSobolev_memLp_test_deriv {U : Set Vec3} {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (j : Fin 3) :
    MemLp (spatialDeriv φ j) 2 (volume.restrict U) := by
  have hcont : Continuous (spatialDeriv φ j) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (spatialDeriv φ j) := by
    change HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec j))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact (hcont.memLp_of_hasCompactSupport (p := 2) hcompact).mono_measure
    Measure.restrict_le_self

private theorem localSobolev_memLp_restrict_open {U : Set Vec3} (hU : IsOpen U)
    {f : Vec3 → ℝ} (hf : MemLp f 2 volume) : MemLp f 2 (volume.restrict U) := by
  have hsingle : MemLp f 2 (volume.restrict U) := hf.mono_measure Measure.restrict_le_self
  have hdouble : volume.restrict U = (volume.restrict U).restrict U := by
    rw [Measure.restrict_restrict hU.measurableSet]
    simp
  have hdoubleLp : MemLp f 2 ((volume.restrict U).restrict U) :=
    hsingle.mono_measure Measure.restrict_le_self
  rw [← hdouble] at hdoubleLp
  exact hdoubleLp

private theorem localSobolev_memLp_test_open {U : Set Vec3} (hU : IsOpen U)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    MemLp φ 2 (volume.restrict U) := by
  exact localSobolev_memLp_restrict_open hU
    (hφ.continuous.memLp_of_hasCompactSupport (p := 2) hφc)

private theorem localSobolev_memLp_test_deriv_open {U : Set Vec3} (hU : IsOpen U)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (j : Fin 3) : MemLp (spatialDeriv φ j) 2 (volume.restrict U) := by
  have hcont : Continuous (spatialDeriv φ j) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (spatialDeriv φ j) := by
    change HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec j))
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact localSobolev_memLp_restrict_open hU
    (hcont.memLp_of_hasCompactSupport (p := 2) hcompact)

private theorem weakPartial_add_of_memLp {U : Set Vec3} {i : Fin 3}
    {f g df dg : Vec3 → ℝ}
    (hf : HasWeakPartialDerivOn U i f df) (hg : HasWeakPartialDerivOn U i g dg)
    (hfL2 : MemLp f 2 (volume.restrict U)) (hgL2 : MemLp g 2 (volume.restrict U))
    (hdfL2 : MemLp df 2 (volume.restrict U)) (hdgL2 : MemLp dg 2 (volume.restrict U)) :
    HasWeakPartialDerivOn U i (fun x => f x + g x) (fun x => df x + dg x) := by
  intro φ hφ hφc hφU
  let μ := volume.restrict U
  have hφL2 := localSobolev_memLp_test hφ hφc (U := U)
  have hφiL2 := localSobolev_memLp_test_deriv hφ hφc i (U := U)
  have h1 : Integrable (fun x => f x * spatialDeriv φ i x) μ := hfL2.integrable_mul hφiL2
  have h2 : Integrable (fun x => g x * spatialDeriv φ i x) μ := hgL2.integrable_mul hφiL2
  have h3 : Integrable (fun x => df x * φ x) μ := hdfL2.integrable_mul hφL2
  have h4 : Integrable (fun x => dg x * φ x) μ := hdgL2.integrable_mul hφL2
  have hweakf := hf φ hφ hφc hφU
  have hweakg := hg φ hφ hφc hφU
  have hweakf' : (∫ x in U, f x * spatialDeriv φ i x) =
      -(∫ x in U, df x * φ x) := by simpa [spatialDeriv] using hweakf
  have hweakg' : (∫ x in U, g x * spatialDeriv φ i x) =
      -(∫ x in U, dg x * φ x) := by simpa [spatialDeriv] using hweakg
  change (∫ x, (f x + g x) * spatialDeriv φ i x ∂μ) =
    -(∫ x, (df x + dg x) * φ x ∂μ)
  calc
    (∫ x, (f x + g x) * spatialDeriv φ i x ∂μ) =
        ∫ x, (f x * spatialDeriv φ i x + g x * spatialDeriv φ i x) ∂μ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
    _ = (∫ x, f x * spatialDeriv φ i x ∂μ) +
          ∫ x, g x * spatialDeriv φ i x ∂μ := integral_add h1 h2
    _ = -(∫ x, df x * φ x ∂μ) - ∫ x, dg x * φ x ∂μ := by
          rw [hweakf', hweakg']
          ring
    _ = -(∫ x, (df x + dg x) * φ x ∂μ) := by
          have hsum : (∫ x, df x * φ x ∂μ) + ∫ x, dg x * φ x ∂μ =
              ∫ x, (df x + dg x) * φ x ∂μ := by
            calc
              (∫ x, df x * φ x ∂μ) + ∫ x, dg x * φ x ∂μ =
                  ∫ x, (df x * φ x + dg x * φ x) ∂μ := (integral_add h3 h4).symm
              _ = ∫ x, (df x + dg x) * φ x ∂μ := by
                  apply integral_congr_ae
                  exact Eventually.of_forall fun x => by ring
          rw [← hsum]
          ring

private theorem weakPartial_const_mul_of_memLp {U : Set Vec3} {i : Fin 3}
    {f df : Vec3 → ℝ} (hf : HasWeakPartialDerivOn U i f df)
    (hfL2 : MemLp f 2 (volume.restrict U)) (hdfL2 : MemLp df 2 (volume.restrict U))
    (c : ℝ) :
    HasWeakPartialDerivOn U i (fun x => c * f x) (fun x => c * df x) := by
  intro φ hφ hφc hφU
  let μ := volume.restrict U
  have hφL2 := localSobolev_memLp_test hφ hφc (U := U)
  have hφiL2 := localSobolev_memLp_test_deriv hφ hφc i (U := U)
  have h1 : Integrable (fun x => f x * spatialDeriv φ i x) μ := hfL2.integrable_mul hφiL2
  have h2 : Integrable (fun x => df x * φ x) μ := hdfL2.integrable_mul hφL2
  have hweak := hf φ hφ hφc hφU
  have hweak' : (∫ x in U, f x * spatialDeriv φ i x) =
      -(∫ x in U, df x * φ x) := by simpa [spatialDeriv] using hweak
  change (∫ x, (c * f x) * spatialDeriv φ i x ∂μ) =
    -(∫ x, (c * df x) * φ x ∂μ)
  calc
    (∫ x, (c * f x) * spatialDeriv φ i x ∂μ) =
        c * ∫ x, f x * spatialDeriv φ i x ∂μ := by
          calc
            (∫ x, (c * f x) * spatialDeriv φ i x ∂μ) =
                ∫ x, c * (f x * spatialDeriv φ i x) ∂μ := by
                  apply integral_congr_ae
                  exact Eventually.of_forall fun x => by ring
            _ = c * ∫ x, f x * spatialDeriv φ i x ∂μ := integral_const_mul c _
    _ = c * (-(∫ x, df x * φ x ∂μ)) := by rw [hweak']
    _ = -(c * ∫ x, df x * φ x ∂μ) := by ring
    _ = -(∫ x, (c * df x) * φ x ∂μ) := by
          congr 1
          calc
            c * ∫ x, df x * φ x ∂μ = ∫ x, c * (df x * φ x) ∂μ :=
                (integral_const_mul c _).symm
            _ = ∫ x, (c * df x) * φ x ∂μ := by
                apply integral_congr_ae
                exact Eventually.of_forall fun x => by ring

private theorem weakPartial_congr_ae {U : Set Vec3} {i : Fin 3}
    {f f' df df' : Vec3 → ℝ} (hf : HasWeakPartialDerivOn U i f df)
    (hf' : f =ᵐ[volume.restrict U] f') (hdf' : df =ᵐ[volume.restrict U] df') :
    HasWeakPartialDerivOn U i f' df' := by
  intro φ hφ hφc hφU
  have hweak := hf φ hφ hφc hφU
  have hweak' : (∫ x in U, f x * spatialDeriv φ i x) =
      -(∫ x in U, df x * φ x) := by simpa [spatialDeriv] using hweak
  calc
    (∫ x in U, f' x * spatialDeriv φ i x) =
        ∫ x in U, f x * spatialDeriv φ i x := by
          apply integral_congr_ae
          filter_upwards [hf'] with x hx
          simp [hx]
    _ = -(∫ x in U, df x * φ x) := hweak'
    _ = -(∫ x in U, df' x * φ x) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hdf'] with x hx
          simp [hx]

/-- Sums of Sobolev families are Sobolev families. -/
theorem IsSobolevFamilyOn.add {m : ℕ} {U : Set Vec3} {f g : Vec3 → ℝ}
    {D E : List (Fin 3) → Vec3 → ℝ} (hf : IsSobolevFamilyOn m U f D)
    (hg : IsSobolevFamilyOn m U g E) :
    IsSobolevFamilyOn m U (fun x => f x + g x) (fun α x => D α x + E α x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hf.zero.add hg.zero
  · intro α hα
    exact (hf.memL2 α hα).add (hg.memL2 α hα)
  · intro α j hα
    exact weakPartial_add_of_memLp (hf.weak α j hα) (hg.weak α j hα)
      (hf.memL2 α (by omega)) (hg.memL2 α (by omega))
      (hf.memL2 (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))
      (hg.memL2 (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))

/-- Scalar multiples of Sobolev families are Sobolev families. -/
theorem IsSobolevFamilyOn.const_mul {m : ℕ} {U : Set Vec3} {f : Vec3 → ℝ}
    {D : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn m U f D) (c : ℝ) :
    IsSobolevFamilyOn m U (fun x => c * f x) (fun α x => c * D α x) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [h.zero] with x hx
    exact congrArg (fun y : ℝ => c * y) hx
  · intro α hα
    exact (h.memL2 α hα).const_mul c
  · intro α j hα
    exact weakPartial_const_mul_of_memLp (h.weak α j hα)
      (h.memL2 α (by omega))
      (h.memL2 (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)) c

/-- Replacing a Sobolev family by almost-everywhere equal representatives
preserves its properties. -/
theorem IsSobolevFamilyOn.congr_ae {m : ℕ} {U : Set Vec3} {f f' : Vec3 → ℝ}
    {D D' : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn m U f D)
    (hf : f =ᵐ[volume.restrict U] f')
    (hD : ∀ α : List (Fin 3), α.length ≤ m → D α =ᵐ[volume.restrict U] D' α) :
    IsSobolevFamilyOn m U f' D' := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hD [] (by simp)).symm.trans (h.zero.trans hf)
  · intro α hα
    exact (memLp_congr_ae (hD α hα)).mp (h.memL2 α hα)
  · intro α j hα
    exact weakPartial_congr_ae (h.weak α j hα) (hD α (by omega))
      (hD (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))

private theorem weakPartial_l2_limit {U : Set Vec3} (hU : IsOpen U) {i : Fin 3}
    {f g : Vec3 → ℝ} {fn gn : ℕ → Vec3 → ℝ}
    (hweak : ∀ n, HasWeakPartialDerivOn U i (fn n) (gn n))
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hfn : ∀ n, MemLp (fn n) 2 (volume.restrict U))
    (hgn : ∀ n, MemLp (gn n) 2 (volume.restrict U))
    (hconvf : Tendsto (fun n => eLpNorm (fn n - f) 2 (volume.restrict U)) atTop (𝓝 0))
    (hconvg : Tendsto (fun n => eLpNorm (gn n - g) 2 (volume.restrict U)) atTop (𝓝 0)) :
    HasWeakPartialDerivOn U i f g := by
  intro φ hφ hφc hφU
  let μ := volume.restrict U
  have hφL2 := localSobolev_memLp_test_open hU hφ hφc
  have hφiL2 := localSobolev_memLp_test_deriv_open hU hφ hφc i
  let qφ : Lp ℝ 2 μ := hφL2.toLp φ
  let qφi : Lp ℝ 2 μ := hφiL2.toLp (spatialDeriv φ i)
  have hconvf' : Tendsto
      (fun n => eLpNorm (((hfn n).toLp (fn n) : Vec3 → ℝ) - f) 2 μ) atTop (𝓝 0) := by
    have heq (n : ℕ) :
        eLpNorm (((hfn n).toLp (fn n) : Vec3 → ℝ) - f) 2 μ =
          eLpNorm (fn n - f) 2 μ :=
      eLpNorm_congr_ae ((hfn n).coeFn_toLp.sub Filter.EventuallyEq.rfl)
    have heqfun :
        (fun n => eLpNorm (fn n - f) 2 μ) =ᶠ[atTop]
          (fun n => eLpNorm (((hfn n).toLp (fn n) : Vec3 → ℝ) - f) 2 μ) := by
      filter_upwards [] with n
      exact (heq n).symm
    exact hconvf.congr' heqfun
  have hconvg' : Tendsto
      (fun n => eLpNorm (((hgn n).toLp (gn n) : Vec3 → ℝ) - g) 2 μ) atTop (𝓝 0) := by
    have heq (n : ℕ) :
        eLpNorm (((hgn n).toLp (gn n) : Vec3 → ℝ) - g) 2 μ =
          eLpNorm (gn n - g) 2 μ :=
      eLpNorm_congr_ae ((hgn n).coeFn_toLp.sub Filter.EventuallyEq.rfl)
    have heqfun :
        (fun n => eLpNorm (gn n - g) 2 μ) =ᶠ[atTop]
          (fun n => eLpNorm (((hgn n).toLp (gn n) : Vec3 → ℝ) - g) 2 μ) := by
      filter_upwards [] with n
      exact (heq n).symm
    exact hconvg.congr' heqfun
  have hfnLp : Tendsto (fun n => (hfn n).toLp (fn n)) atTop
      (𝓝 (hf.toLp f)) := by
    exact Lp.tendsto_Lp_of_tendsto_eLpNorm f hf hconvf'
  have hgnLp : Tendsto (fun n => (hgn n).toLp (gn n)) atTop
      (𝓝 (hg.toLp g)) := by
    exact Lp.tendsto_Lp_of_tendsto_eLpNorm g hg hconvg'
  have hcontφi : Continuous (fun q : Lp ℝ 2 μ => inner ℝ q qφi) := by
    exact continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hcontφ : Continuous (fun q : Lp ℝ 2 μ => inner ℝ q qφ) := by
    exact continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hpairfn (n : ℕ) :
      inner ℝ ((hfn n).toLp (fn n)) qφi =
        ∫ x, fn n x * spatialDeriv φ i x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hfn n).coeFn_toLp, hφiL2.coeFn_toLp] with x hfnx hφx
    calc
      inner ℝ ((hfn n).toLp (fn n) x) (qφi x) =
          inner ℝ (fn n x) (spatialDeriv φ i x) := by rw [hfnx, hφx]
      _ = fn n x * spatialDeriv φ i x := Real.inner_apply _ _
  have hpairf :
      inner ℝ (hf.toLp f) qφi = ∫ x, f x * spatialDeriv φ i x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hφiL2.coeFn_toLp] with x hfx hφx
    calc
      inner ℝ (hf.toLp f x) (qφi x) = inner ℝ (f x) (spatialDeriv φ i x) := by
        rw [hfx, hφx]
      _ = f x * spatialDeriv φ i x := Real.inner_apply _ _
  have hpairgn (n : ℕ) :
      inner ℝ ((hgn n).toLp (gn n)) qφ = ∫ x, gn n x * φ x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hgn n).coeFn_toLp, hφL2.coeFn_toLp] with x hgnx hφx
    calc
      inner ℝ ((hgn n).toLp (gn n) x) (qφ x) = inner ℝ (gn n x) (φ x) := by
        rw [hgnx, hφx]
      _ = gn n x * φ x := Real.inner_apply _ _
  have hpairg : inner ℝ (hg.toLp g) qφ = ∫ x, g x * φ x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, hφL2.coeFn_toLp] with x hgx hφx
    calc
      inner ℝ (hg.toLp g x) (qφ x) = inner ℝ (g x) (φ x) := by rw [hgx, hφx]
      _ = g x * φ x := Real.inner_apply _ _
  have hpairfnEvent :
      (fun n => inner ℝ ((hfn n).toLp (fn n)) qφi) =ᶠ[atTop]
        (fun n => ∫ x, fn n x * spatialDeriv φ i x ∂μ) :=
    by
      filter_upwards [] with n
      exact hpairfn n
  have hpairgnEvent :
      (fun n => inner ℝ ((hgn n).toLp (gn n)) qφ) =ᶠ[atTop]
        (fun n => ∫ x, gn n x * φ x ∂μ) :=
    by
      filter_upwards [] with n
      exact hpairgn n
  have hfnIntegral : Tendsto (fun n => ∫ x, fn n x * spatialDeriv φ i x ∂μ)
      atTop (𝓝 (∫ x, f x * spatialDeriv φ i x ∂μ)) := by
    rw [← hpairf]
    exact (hcontφi.continuousAt.tendsto.comp hfnLp).congr' hpairfnEvent
  have hgnIntegral : Tendsto (fun n => ∫ x, gn n x * φ x ∂μ)
      atTop (𝓝 (∫ x, g x * φ x ∂μ)) := by
    rw [← hpairg]
    exact (hcontφ.continuousAt.tendsto.comp hgnLp).congr' hpairgnEvent
  have hEq (n : ℕ) :
      (∫ x, fn n x * spatialDeriv φ i x ∂μ) =
        -(∫ x, gn n x * φ x ∂μ) := by
    simpa [μ, spatialDeriv] using hweak n φ hφ hφc hφU
  have hgnNeg := hgnIntegral.neg
  have hfnAlt : Tendsto (fun n => ∫ x, fn n x * spatialDeriv φ i x ∂μ)
      atTop (𝓝 (-(∫ x, g x * φ x ∂μ))) :=
    hgnNeg.congr' (show (fun n => -(∫ x, gn n x * φ x ∂μ)) =ᶠ[atTop]
        (fun n => ∫ x, fn n x * spatialDeriv φ i x ∂μ) from by
          filter_upwards [] with n
          exact (hEq n).symm)
  have hlim := tendsto_nhds_unique hfnIntegral hfnAlt
  simpa [μ, spatialDeriv] using hlim

/-- Weak derivative families of one function agree almost everywhere on an
open set. -/
theorem IsSobolevFamilyOn.ae_eq {m : ℕ} {U : Set Vec3} (hU : IsOpen U) {f : Vec3 → ℝ}
    {D D' : List (Fin 3) → Vec3 → ℝ} (h : IsSobolevFamilyOn m U f D)
    (h' : IsSobolevFamilyOn m U f D') :
    ∀ α : List (Fin 3), α.length ≤ m → D α =ᵐ[volume.restrict U] D' α := by
  have hlocD (α : List (Fin 3)) (hα : α.length ≤ m) :
      LocallyIntegrableOn (D α) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((h.memL2 α hα).locallyIntegrable (by norm_num))
  have hlocD' (α : List (Fin 3)) (hα : α.length ≤ m) :
      LocallyIntegrableOn (D' α) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((h'.memL2 α hα).locallyIntegrable (by norm_num))
  intro α
  induction α using List.reverseRecOn with
  | nil =>
      intro _
      exact h.zero.trans h'.zero.symm
  | append_singleton β j ih =>
      intro hα
      have hβ : β.length < m := by
        simp only [List.length_append, List.length_singleton] at hα
        omega
      have hweak' : HasWeakPartialDerivOn U j (D β) (D' (β ++ [j])) :=
        weakPartial_congr_ae (h'.weak β j hβ) (ih (by omega)).symm Filter.EventuallyEq.rfl
      exact HasWeakPartialDerivOn.ae_eq hU
        (hlocD (β ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))
        (hlocD' (β ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))
        (h.weak β j hβ) hweak'

/-- Limits in `L²` of Sobolev families remain Sobolev families. -/
theorem IsSobolevFamilyOn.of_tendsto {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {Dn : ℕ → List (Fin 3) → Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (h : ∀ n, IsSobolevFamilyOn m U (Dn n []) (Dn n))
    (hD : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 (volume.restrict U))
    (hconv : ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun n => eLpNorm (Dn n α - D α) 2 (volume.restrict U)) atTop (𝓝 0)) :
    IsSobolevFamilyOn m U (D []) D := by
  refine ⟨Filter.EventuallyEq.rfl, hD, ?_⟩
  intro α j hα
  exact weakPartial_l2_limit hU
    (fun n => (h n).weak α j hα)
    (hD α (by omega))
    (hD (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega))
    (fun n => (h n).memL2 α (by omega))
    (fun n => (h n).memL2 (α ++ [j])
      (by simp only [List.length_append, List.length_singleton]; omega))
    (hconv α (by omega))
    (hconv (α ++ [j])
      (by simp only [List.length_append, List.length_singleton]; omega))

/-- The intrinsic Sobolev norm is bounded by the value from any chosen
Sobolev family. -/
theorem hNormOn_le {ι : Type*} [Fintype ι] {m : ℕ} {U : Set Vec3} {f : ι → Vec3 → ℝ}
    {D : ι → List (Fin 3) → Vec3 → ℝ} (h : ∀ i, IsSobolevFamilyOn m U (f i) (D i)) :
  hNormOn m U f ≤ ENNReal.ofReal (Real.sqrt (∑ i, sobolevNormSqOn m U (D i))) := by
  unfold hNormOn
  exact iInf_le_of_le D (iInf_le_of_le h le_rfl)

private theorem sobolevNormSqOn_eq_of_family_ae {ι : Type*} [Fintype ι]
    {m : ℕ} {U : Set Vec3} (hU : IsOpen U) {f : ι → Vec3 → ℝ}
    {D E : ι → List (Fin 3) → Vec3 → ℝ}
    (hD : ∀ i, IsSobolevFamilyOn m U (f i) (D i))
    (hE : ∀ i, IsSobolevFamilyOn m U (f i) (E i)) :
    (∑ i, sobolevNormSqOn m U (D i)) = ∑ i, sobolevNormSqOn m U (E i) := by
  apply Finset.sum_congr rfl
  intro i hi
  unfold sobolevNormSqOn
  apply Finset.sum_congr rfl
  intro α hα
  have hae := IsSobolevFamilyOn.ae_eq hU (hD i) (hE i) α (mem_sobolevWords.mp hα)
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

/-- The intrinsic Sobolev norm is computed by any representing family on an
open set. -/
theorem hNormOn_eq {ι : Type*} [Fintype ι] {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {f : ι → Vec3 → ℝ} {D : ι → List (Fin 3) → Vec3 → ℝ}
    (h : ∀ i, IsSobolevFamilyOn m U (f i) (D i)) :
    hNormOn m U f = ENNReal.ofReal (Real.sqrt (∑ i, sobolevNormSqOn m U (D i))) := by
  apply le_antisymm
  · exact hNormOn_le h
  · unfold hNormOn
    apply le_iInf
    intro E
    apply le_iInf
    intro hE
    rw [sobolevNormSqOn_eq_of_family_ae hU h hE]

/-- A finite Sobolev norm is equivalent to componentwise membership in the
Sobolev space. -/
theorem hNormOn_lt_top_iff {ι : Type*} [Fintype ι] {m : ℕ} {U : Set Vec3}
    {f : ι → Vec3 → ℝ} : hNormOn m U f < ⊤ ↔ ∀ i, MemSobolevOn m U (f i) := by
  constructor
  · intro hfinite i
    unfold hNormOn at hfinite
    obtain ⟨D, hDfinite⟩ := iInf_lt_top.mp hfinite
    obtain ⟨hD, _⟩ := iInf_lt_top.mp hDfinite
    exact ⟨D i, hD i⟩
  · intro hmem
    classical
    choose D hD using hmem
    exact (lt_of_le_of_lt (hNormOn_le hD) ENNReal.ofReal_lt_top)

end CKN
