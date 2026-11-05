/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DeGiorgiCoreTwo
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.LevelRecursion
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.Basic
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace

/-!
# DeGiorgiIterationTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-dimensional De Giorgi level recurrence

The `H¹ ↪ L⁴` matched-pair inequality in dimension two has an additional
`sqrt L` factor.  After truncation, Chebyshev, and squaring, this gives the
scale-correct coefficient `C² L E₀²` in the level-volume recurrence.
-/

namespace DivergenceFormProcess.Regularity

open HCPolySupport MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

private theorem deGiorgi_truncatedLevelEnergyBound :
    ∀ (C : ℝ),
      (0 : ℝ) ≤ C →
        (∀ (z : Vec (2 : ℕ)) (L : ℝ),
            (0 : ℝ) < L →
              ∀ (f g : H1Function (axisCube z L)),
                Measurable f.toFun →
                  Measurable g.toFun →
                    (MemH10 (axisCube z L) fun (x : Vec (2 : ℕ)) => f.toFun x - g.toFun x) →
                      (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧
                        f.toFun x ≠ (0 : ℝ)} +
                            (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) {x : Vec (2 : ℕ) | x ∈ axisCube z
                              L ∧ g.toFun x ≠ (0 : ℝ)} ≤
                          (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) (axisCube z L) →
                        (eLpNorm f.toFun (4 : ℝ≥0∞) (volumeMeasureOn (axisCube z L))).toReal +
                            (eLpNorm g.toFun (4 : ℝ≥0∞) (volumeMeasureOn (axisCube z L))).toReal ≤
                          C * √L *
                            (∑ i : Fin (2 : ℕ),
                                (eLpNorm (fun (x : Vec (2 : ℕ)) => f.grad x i) (2 : ℝ≥0∞)
                                    (volumeMeasureOn (axisCube z L))).toReal +
                              ∑ i : Fin (2 : ℕ),
                                (eLpNorm (fun (x : Vec (2 : ℕ)) => g.grad x i) (2 : ℝ≥0∞)
                                    (volumeMeasureOn (axisCube z L))).toReal)) →
          ∀ (z : Vec (2 : ℕ)) (L : ℝ),
            (0 : ℝ) < L →
              ∀ (w₁ w₂ : H1Function (axisCube z L)),
                Measurable w₁.toFun →
                  Measurable w₂.toFun →
                    (MemH10 (axisCube z L) fun (x : Vec (2 : ℕ)) => w₁.toFun x - w₂.toFun x) →
                      ∀ (m₀ E₀ : ℝ),
                        (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧
                          m₀ < w₁.toFun x} +
                              (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) {x : Vec (2 : ℕ) | x ∈ axisCube
                                z L ∧ m₀ < w₂.toFun x} ≤
                            (volume : Set (Vec (2 : ℕ)) → ℝ≥0∞) (axisCube z L) →
                          (∀ (k : ℝ),
                              (0 : ℝ) ≤ k →
                                ∑ i : Fin (2 : ℕ),
                                      (eLpNorm
                                          ({x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun
                                            x}.indicator
                                            fun (x : Vec (2 : ℕ)) => w₁.grad x i)
                                          (2 : ℝ≥0∞) (volumeMeasureOn (axisCube z L))).toReal +
                                    ∑ i : Fin (2 : ℕ),
                                      (eLpNorm
                                          ({x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun
                                            x}.indicator
                                            fun (x : Vec (2 : ℕ)) => w₂.grad x i)
                                          (2 : ℝ≥0∞) (volumeMeasureOn (axisCube z L))).toReal ≤
                                  E₀ *
                                    √(((volume : Set (Vec (2 : ℕ)) → ℝ≥0∞)
                                            {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k <
                                              w₁.toFun x}).toReal +
                                        ((volume : Set (Vec (2 : ℕ)) → ℝ≥0∞)
                                            {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k <
                                              w₂.toFun x}).toReal)) →
                            IsOpenBoundedConvexDomain (axisCube z L) →
                              MeasurableSet (axisCube z L) →
                                ∀ (k : ℝ),
                                  (0 : ℝ) ≤ k →
                                    ∃ (fk : H1Function (axisCube z L)) (gk : H1Function (axisCube
                                      z L)),
                                      (fk.toFun = fun (x : Vec (2 : ℕ)) => max (w₁.toFun x - (m₀ +
                                        k)) (0 : ℝ)) ∧
                                        (gk.toFun = fun (x : Vec (2 : ℕ)) => max (w₂.toFun x - (m₀
                                          + k)) (0 : ℝ)) ∧
                                          (eLpNorm fk.toFun (4 : ℝ≥0∞) (volumeMeasureOn (axisCube
                                            z L))).toReal +
                                              (eLpNorm gk.toFun (4 : ℝ≥0∞) (volumeMeasureOn
                                                (axisCube z L))).toReal ≤
                                            C * √L * E₀ *
                                              √(((volume : Set (Vec (2 : ℕ)) → ℝ≥0∞)
                                                      {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k
                                                        < w₁.toFun x}).toReal +
                                                  ((volume : Set (Vec (2 : ℕ)) → ℝ≥0∞)
                                                      {x : Vec (2 : ℕ) | x ∈ axisCube z L ∧ m₀ + k
                                                        < w₂.toFun x}).toReal) := by
  intro C hC hSobolev z L hL w₁ w₂ hw₁meas hw₂meas hmatch m₀ E₀ hmedian hlevel hUdom hUmeas k hk
  obtain ⟨fk, hfk, hfkgrad⟩ := exists_h1_max_sub_const hUdom w₁ (m₀ + k)
  obtain ⟨gk, hgk, hgkgrad⟩ := exists_h1_max_sub_const hUdom w₂ (m₀ + k)
  refine ⟨fk, gk, hfk, hgk, ?_⟩
  have hfkmeas : Measurable fk.toFun := by
    rw [hfk]
    exact (hw₁meas.sub measurable_const).max measurable_const
  have hgkmeas : Measurable gk.toFun := by
    rw [hgk]
    exact (hw₂meas.sub measurable_const).max measurable_const
  have hmatchfg : MemH10 (axisCube z L) (fun x => fk.toFun x - gk.toFun x) := by
    rw [show (fun x => fk.toFun x - gk.toFun x) =
      (fun x => max (w₁.toFun x - (m₀ + k)) 0 -
        max (w₂.toFun x - (m₀ + k)) 0) by funext x; rw [hfk, hgk]]
    exact memH10_max_sub_matched hUdom w₁ w₂ hmatch (m₀ + k)
  have hmaxne : ∀ w : ℝ, max (w - (m₀ + k)) 0 ≠ 0 ↔ m₀ + k < w := by
    intro w
    rw [ne_eq, max_eq_right_iff, not_le]
    constructor <;> intro h <;> linarith only [h]
  have hset1 : {x | x ∈ axisCube z L ∧ fk.toFun x ≠ 0} =
      {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x} := by
    ext x
    simp only [Set.mem_ofPred_eq, hfk]
    exact and_congr_right fun _ => hmaxne (w₁.toFun x)
  have hset2 : {x | x ∈ axisCube z L ∧ gk.toFun x ≠ 0} =
      {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x} := by
    ext x
    simp only [Set.mem_ofPred_eq, hgk]
    exact and_congr_right fun _ => hmaxne (w₂.toFun x)
  have hzero : volume {x | x ∈ axisCube z L ∧ fk.toFun x ≠ 0} +
      volume {x | x ∈ axisCube z L ∧ gk.toFun x ≠ 0} ≤
        volume (axisCube z L) := by
    rw [hset1, hset2]
    refine le_trans (add_le_add (measure_mono ?_) (measure_mono ?_)) hmedian
    · rintro x ⟨hxU, hx⟩
      exact ⟨hxU, by linarith only [hx, hk]⟩
    · rintro x ⟨hxU, hx⟩
      exact ⟨hxU, by linarith only [hx, hk]⟩
  have hs := hSobolev z L hL fk gk hfkmeas hgkmeas hmatchfg hzero
  have hcongr1 :
      (∑ i : Fin 2, (eLpNorm (fun x => fk.grad x i) 2
        (volumeMeasureOn (axisCube z L))).toReal) =
      ∑ i : Fin 2, (eLpNorm
        ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
          (fun x => w₁.grad x i)) 2
        (volumeMeasureOn (axisCube z L))).toReal := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hfkgrad, ae_restrict_mem hUmeas] with x hxgrad hxU
    rw [hxgrad]
    by_cases hx : m₀ + k < w₁.toFun x
    · rw [Set.indicator_of_mem
          (show x ∈ {y | m₀ + k < w₁.toFun y} from hx),
        Set.indicator_of_mem (show x ∈ {x | x ∈ axisCube z L ∧
          m₀ + k < w₁.toFun x} from ⟨hxU, hx⟩)]
    · rw [Set.indicator_of_notMem
          (show x ∉ {y | m₀ + k < w₁.toFun y} from hx),
        Set.indicator_of_notMem (fun h => hx h.2)]
      rfl
  have hcongr2 :
      (∑ i : Fin 2, (eLpNorm (fun x => gk.grad x i) 2
        (volumeMeasureOn (axisCube z L))).toReal) =
      ∑ i : Fin 2, (eLpNorm
        ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
          (fun x => w₂.grad x i)) 2
        (volumeMeasureOn (axisCube z L))).toReal := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hgkgrad, ae_restrict_mem hUmeas] with x hxgrad hxU
    rw [hxgrad]
    by_cases hx : m₀ + k < w₂.toFun x
    · rw [Set.indicator_of_mem
          (show x ∈ {y | m₀ + k < w₂.toFun y} from hx),
        Set.indicator_of_mem (show x ∈ {x | x ∈ axisCube z L ∧
          m₀ + k < w₂.toFun x} from ⟨hxU, hx⟩)]
    · rw [Set.indicator_of_notMem
          (show x ∉ {y | m₀ + k < w₂.toFun y} from hx),
        Set.indicator_of_notMem (fun h => hx h.2)]
      rfl
  rw [hcongr1, hcongr2] at hs
  calc
    (eLpNorm fk.toFun 4 (volumeMeasureOn (axisCube z L))).toReal +
        (eLpNorm gk.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
      C * Real.sqrt L *
        ((∑ i : Fin 2, (eLpNorm
            ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
              (fun x => w₁.grad x i)) 2
            (volumeMeasureOn (axisCube z L))).toReal) +
          ∑ i : Fin 2, (eLpNorm
            ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
              (fun x => w₂.grad x i)) 2
            (volumeMeasureOn (axisCube z L))).toReal) := hs
    _ ≤ C * Real.sqrt L *
        (E₀ * Real.sqrt
          ((volume
            {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
            (volume
              {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) :=
      mul_le_mul_of_nonneg_left (hlevel k hk)
        (mul_nonneg hC (Real.sqrt_nonneg L))
    _ = C * Real.sqrt L * E₀ * Real.sqrt
        ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
      ring

/-- The dimension-two combined upper-level volumes satisfy the De Giorgi
recurrence with exponent `1 / 2` and coefficient `C² L E₀²`. -/
theorem deGiorgi_levelRecursion_two :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L →
        ∀ (w₁ w₂ : H1Function (axisCube z L)),
          Measurable w₁.toFun → Measurable w₂.toFun →
          MemH10 (axisCube z L) (fun x => w₁.toFun x - w₂.toFun x) →
          ∀ (m₀ E₀ : ℝ), 0 ≤ E₀ →
          volume {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} +
              volume {x | x ∈ axisCube z L ∧ m₀ < w₂.toFun x} ≤
            volume (axisCube z L) →
          (∀ k : ℝ, 0 ≤ k →
            (∑ i : Fin 2, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
                  (fun x => w₁.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal) +
              ∑ i : Fin 2, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
                  (fun x => w₂.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal ≤
              E₀ * Real.sqrt
                ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
                  (volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) →
          ∀ k l : ℝ, 0 ≤ k → k < l →
            (l - k) ^ 2 *
                ((volume
                    {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal +
                  (volume
                    {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^
                    (1 / 2 : ℝ) ≤
              (C ^ 2 * L * E₀ ^ 2) *
                ((volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
                  (volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
  classical
  obtain ⟨C, hC, hSobolev⟩ := matchedPair_sobolev_two_sqrt
  obtain ⟨CE, hCE, hEmbedding⟩ := cube_sobolev_embedding_two
  refine ⟨C, hC, ?_⟩
  intro z L hL w₁ w₂ hw₁meas hw₂meas hmatch m₀ E₀ hE₀ hmedian hlevel
  have hUdom : IsOpenBoundedConvexDomain (axisCube z L) :=
    isOpenBoundedConvexDomain_axisCube z L
  have hUmeas : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) :=
    hUdom.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hVolU_top : volume (axisCube z L) ≠ ⊤ := by
    rw [axisCube, Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hSub_top : ∀ (S : Set (Vec 2)), S ⊆ axisCube z L → volume S ≠ ⊤ :=
    fun S hSU => ne_top_of_le_ne_top hVolU_top (measure_mono hSU)
  have hμvol : ∀ S : Set (Vec 2), S ⊆ axisCube z L →
      (volumeMeasureOn (axisCube z L)) S = volume S := by
    intro S hSU
    change (volume.restrict (axisCube z L)) S = volume S
    rw [Measure.restrict_apply' hUmeas, Set.inter_eq_left.mpr hSU]
  have hfin_four : ∀ u : H1Function (axisCube z L),
      eLpNorm u.toFun 4 (volumeMeasureOn (axisCube z L)) ≠ ⊤ := by
    intro u
    have hEu := hEmbedding z L hL u
    have hgrad_ne : ∀ i : Fin 2,
        eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
          (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      fun i => (u.gradMemL2 i).mono_exponent (by
        rw [← ENNReal.ofReal_ofNat]
        exact ENNReal.ofReal_le_ofReal (by norm_num)) |>.eLpNorm_lt_top.ne
    have hval_ne :
        eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
          (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      u.memL2.mono_exponent (by
        rw [← ENNReal.ofReal_ofNat]
        exact ENNReal.ofReal_le_ofReal (by norm_num)) |>.eLpNorm_lt_top.ne
    have hrhs_ne :
        (CE : ℝ≥0∞) *
          ((∑ i : Fin 2,
              eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
                (volumeMeasureOn (axisCube z L))) +
            ENNReal.ofReal L⁻¹ *
              eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
                (volumeMeasureOn (axisCube z L))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.2
          ⟨(ENNReal.sum_lt_top.2 fun i _ => (hgrad_ne i).lt_top).ne,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hval_ne⟩)
    exact (lt_of_le_of_lt hEu hrhs_ne.lt_top).ne
  have htrunc := @deGiorgi_truncatedLevelEnergyBound (C) (hC) (hSobolev) (z) (L) (hL) (w₁) (w₂)
    (hw₁meas) (hw₂meas) (hmatch) (m₀) (E₀) (hmedian) (hlevel) (hUdom) (hUmeas)
  intro k l hk hkl
  obtain ⟨fk, gk, hfk, hgk, hs⟩ := htrunc k hk
  have hε : 0 ≤ l - k := sub_nonneg.mpr hkl.le
  have hsub1 : ∀ x ∈ {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x},
      l - k ≤ fk.toFun x := by
    rintro x ⟨_, hx⟩
    rw [hfk, le_max_iff]
    exact Or.inl (by linarith only [hx])
  have hsub2 : ∀ x ∈ {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x},
      l - k ≤ gk.toFun x := by
    rintro x ⟨_, hx⟩
    rw [hgk, le_max_iff]
    exact Or.inl (by linarith only [hx])
  have hcheb1 := real_chebyshev_level (p := (4 : ℝ≥0∞)) (by norm_num)
    (by norm_num) (hfin_four fk) hε hsub1
  have hcheb2 := real_chebyshev_level (p := (4 : ℝ≥0∞)) (by norm_num)
    (by norm_num) (hfin_four gk) hε hsub2
  rw [hμvol _ (fun x hx => hx.1)] at hcheb1
  rw [hμvol _ (fun x hx => hx.1)] at hcheb2
  have hkey := sq_level_recursion_of_le (ε := l - k) (r := (1 / 4 : ℝ))
    (a := (volume
      {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal)
    (b := (volume
      {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal)
    hε (by norm_num) (by norm_num) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hcheb1 hcheb2 hs (by positivity)
  have hrsq :
      (C * Real.sqrt L * E₀ * Real.sqrt
        ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) ^ 2 =
        (C ^ 2 * L * E₀ ^ 2) *
          ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
            (volume
              {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL.le,
      Real.sq_sqrt (by positivity)]
  calc
    (l - k) ^ 2 *
        ((volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^
            (1 / 2 : ℝ) =
      (l - k) ^ 2 *
        ((volume {x | x ∈ axisCube z L ∧ m₀ + l < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + l < w₂.toFun x}).toReal) ^
            (2 * (1 / 4 : ℝ)) := by norm_num
    _ ≤ (C * Real.sqrt L * E₀ * Real.sqrt
        ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) ^ 2 := hkey
    _ = (C ^ 2 * L * E₀ ^ 2) *
        ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
          (volume
            {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal) := hrsq

end

end DivergenceFormProcess.Regularity
