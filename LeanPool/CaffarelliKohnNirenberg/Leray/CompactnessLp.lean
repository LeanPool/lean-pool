/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.UnifTight
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Compactness Lp

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace CKN.Leray

/-- On a finite measure space, convergence in measure and a uniform bound in a
strictly higher finite exponent imply convergence in every intermediate
`Lᵖ` seminorm. This is the interpolation step in `cor:compactness-Lq`. -/
theorem tendsto_eLpNorm_of_tendstoInMeasure_of_uniform_high
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {p r : ℝ≥0∞} {f : ℕ → α → E}
    (hp : 1 ≤ p) (hpr : p < r) (hr : r ≠ ⊤)
    (hf : ∀ n, MemLp (f n) r μ)
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n, eLpNorm (f n) r μ ≤ B)
    (hmeasure : TendstoInMeasure μ f atTop (fun _ => (0 : E))) :
    Tendsto (fun n => eLpNorm (f n) p μ) atTop (nhds 0) := by
  have hpTop : p ≠ ⊤ := ne_of_lt (lt_trans hpr (lt_top_iff_ne_top.mpr hr))
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpPos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hprReal : p.toReal < r.toReal := (ENNReal.toReal_lt_toReal hpTop hr).mpr hpr
  have hAlpha : 0 < 1 / p.toReal - 1 / r.toReal := by
    have hInv := one_div_lt_one_div_of_lt hpReal hprReal
    exact sub_pos.mpr (by simpa only [one_div] using hInv)
  let theta : ℝ := 1 / p.toReal - 1 / r.toReal
  obtain ⟨B, hB, hBbound⟩ := hbound
  have hUi : UnifIntegrable f p μ := by
    rw [unifIntegrable_iff]
    intro ε hε
    have hsmall : Tendsto (fun δ : ℝ≥0∞ => B * δ ^ theta) (nhds 0) (nhds 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hB.ne hAlpha
    have hev : ∀ᶠ δ in nhds (0 : ℝ≥0∞), B * δ ^ theta ≤ ε :=
      (ENNReal.tendsto_nhds_zero.mp hsmall) ε hε
    obtain ⟨δ, hδpos, hδsmall⟩ :=
      ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hev
    refine ⟨δ, hδpos, fun n s hs => ?_⟩
    have hrestrict : (μ.restrict s) Set.univ = μ s :=
      Measure.restrict_apply_univ (μ := μ) (s := s)
    calc
      eLpNorm (f n) p (μ.restrict s) ≤
          eLpNorm (f n) r (μ.restrict s) *
            (μ.restrict s Set.univ) ^ (1 / p.toReal - 1 / r.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hpr.le hpPos
      _ ≤ B * (μ s) ^ theta := by
        rw [hrestrict]
        gcongr
        exact (eLpNorm_mono_measure (f n) Measure.restrict_le_self).trans (hBbound n)
      _ ≤ ε := by
        have hs' : μ s ∈ Set.Iic δ := hs
        exact hδsmall hs'
  have hTight : UnifTight f p μ := by
    intro ε hε
    refine ⟨Set.univ, measure_ne_top μ Set.univ, ?_⟩
    intro n
    simp
  have hfP : ∀ n, MemLp (f n) p μ := fun n => (hf n).mono_exponent hpr.le
  have hzero : MemLp (fun _ : α => (0 : E)) p μ := by simp
  have hLp := (tendstoInMeasure_iff_tendsto_Lp hp hpTop hfP hzero).mp
    ⟨hmeasure, hUi, hTight⟩
  have heq : (fun n => eLpNorm (f n - (fun _ : α => (0 : E))) p μ) =
      fun n => eLpNorm (f n) p μ := by
    funext n
    congr 1
    funext x
    simp
  rw [← heq]
  exact hLp

/-- Strong local `L²` convergence and a uniform bound in a higher finite
exponent imply convergence in every intermediate exponent. This is the
upgrade used in `cor:compactness-Lq`. -/
theorem tendsto_eLpNorm_sub_of_tendsto_eLpNorm_two_of_uniform_high
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {p r : ℝ≥0∞} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hpr : p < r) (hr : r ≠ ⊤)
    (hf : ∀ n, MemLp (f n) r μ) (hg : MemLp g r μ)
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n, eLpNorm (f n) r μ ≤ B)
    (h2 : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0) := by
  have hr1 : 1 ≤ r := le_trans hp hpr.le
  have hmeasure :
    TendstoInMeasure μ (fun n => f n - g) atTop (fun _ => (0 : E)) := by
    have hseqEq :
        (fun n => eLpNorm ((f n - g) - (fun _ => (0 : E))) 2 μ) =
          (fun n => eLpNorm (f n - g) 2 μ) := by
      funext n
      congr 1
      funext x
      simp
    have h2' :
        Tendsto (fun n => eLpNorm ((f n - g) - (fun _ => (0 : E))) 2 μ)
          atTop (nhds 0) := hseqEq ▸ h2
    have h' := tendstoInMeasure_of_tendsto_eLpNorm
      (μ := μ) (p := (2 : ℝ≥0∞)) (f := fun n => f n - g)
      (g := fun _ => (0 : E)) (l := atTop) (by norm_num) h2'
    simpa [Pi.sub_apply] using h'
  obtain ⟨B, hB, hBbound⟩ := hbound
  let B' : ℝ≥0∞ := B + eLpNorm g r μ
  have hB' : B' < ⊤ := ENNReal.add_lt_top.mpr ⟨hB, hg.eLpNorm_lt_top⟩
  have hdiffBound : ∀ n, eLpNorm (f n - g) r μ ≤ B' := by
    intro n
    calc
      eLpNorm (f n - g) r μ ≤ eLpNorm (f n) r μ + eLpNorm g r μ :=
        eLpNorm_sub_le (μ := μ) (p := r) (f := f n) (g := g) hr1
      _ ≤ B + eLpNorm g r μ := add_le_add (hBbound n) le_rfl
  have hdiffMem : ∀ n, MemLp (f n - g) r μ :=
    fun n => MemLp.sub (hf n) hg
  exact tendsto_eLpNorm_of_tendstoInMeasure_of_uniform_high
    hp hpr hr hdiffMem ⟨B', hB', hdiffBound⟩ hmeasure

/-- Strong L² convergence and a uniform higher-exponent bound pass that bound
to the limit and yield strong convergence at every intermediate exponent.
This is the Fatou and interpolation step in cor:compactness-Lq. -/
theorem tendsto_eLpNorm_sub_of_tendsto_two_of_uniform_high
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {p r : ℝ≥0∞} {f : ℕ → α → E} {g : α → E}
    (hp : 1 ≤ p) (hpr : p < r) (hr : r ≠ ⊤)
    (hf : ∀ n, MemLp (f n) r μ)
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n, eLpNorm (f n) r μ ≤ B)
    (h2 : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (nhds 0)) :
    MemLp g r μ ∧ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0) := by
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (μ := μ) (p := (2 : ℝ≥0∞)) (f := f) (g := g) (l := atTop)
    (by norm_num) h2
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hgMeas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun i => (hf (ns i)).aestronglyMeasurable) hae
  obtain ⟨B, hB, hBbound⟩ := hbound
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := r)
    (fun i => (hf (ns i)).aestronglyMeasurable) g hgMeas hae
  have hliminf : atTop.liminf (fun i => eLpNorm (f (ns i)) r μ) ≤ B :=
    liminf_le_of_frequently_le' <|
      (Eventually.of_forall fun i => hBbound (ns i)).frequently
  have hg : MemLp g r μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hFatou.trans hliminf) hB
  have hstrong := tendsto_eLpNorm_sub_of_tendsto_eLpNorm_two_of_uniform_high
    hp hpr hr hf hg ⟨B, hB, hBbound⟩ h2
  exact ⟨hg, hstrong⟩

/-- Strong local L² convergence and a uniform local L^(10/3) bound imply
strong local Lᵖ convergence for every 1 ≤ p < 10/3. This is the upgrade in
cor:compactness-Lq. -/
theorem tendsto_eLpNorm_sub_of_tendsto_two_of_uniform_ten_thirds
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {f : ℕ → α → E} {g : α → E}
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ n, eLpNorm (f n) (10 / 3 : ℝ≥0∞) μ ≤ B)
    (h2 : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (nhds 0)) :
    ∀ p : ℝ≥0∞, 1 ≤ p → p < (10 / 3 : ℝ≥0∞) →
      Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0) := by
  intro p hp hpr
  obtain ⟨B, hB, hBbound⟩ := hbound
  have hfhigh : ∀ n, MemLp (f n) (10 / 3 : ℝ≥0∞) μ := by
    intro n
    rw [memLp_iff]
    exact lt_of_le_of_lt (hBbound n) hB
  obtain ⟨_hg, hconv⟩ := tendsto_eLpNorm_sub_of_tendsto_two_of_uniform_high
    hp hpr (ENNReal.div_ne_top ENNReal.ofNat_ne_top (by norm_num))
    hfhigh ⟨B, hB, hBbound⟩ h2
  exact hconv

/-- On each member of a family of finite-measure local regions, strong `L²`
convergence and a uniform `L^(10/3)` bound imply strong `Lᵖ` convergence for
every `1 ≤ p < 10/3`. Applied to compact subsets, this is
cor:compactness-Lq. -/
theorem cor_compactness_Lq
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : ℕ → α → E} {g : α → E} (Q : ι → Set α)
    [∀ i, IsFiniteMeasure (μ.restrict (Q i))]
    (hbound : ∀ i, ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ n, eLpNorm (f n) (10 / 3 : ℝ≥0∞) (μ.restrict (Q i)) ≤ B)
    (h2 : ∀ i, Tendsto
      (fun n => eLpNorm (f n - g) 2 (μ.restrict (Q i))) atTop (nhds 0)) :
    ∀ i p, 1 ≤ p → p < (10 / 3 : ℝ≥0∞) →
      Tendsto (fun n => eLpNorm (f n - g) p (μ.restrict (Q i))) atTop (nhds 0) := by
  intro i p hp hpr
  exact tendsto_eLpNorm_sub_of_tendsto_two_of_uniform_ten_thirds
    (hbound i) (h2 i) p hp hpr

end CKN.Leray
