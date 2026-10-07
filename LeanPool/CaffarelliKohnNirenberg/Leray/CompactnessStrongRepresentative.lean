/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessJointExtract
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessSliceRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrongIdentification

/-!
# Compactness Strong Representative

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The strong local `L²` limit selected by compactness agrees with the
mollified representative on every rectangle of the exhaustion. -/
theorem strong_l2_to_compactnessMollifiedLimit_on_exhaustion
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U) (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ T →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in T, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G)
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧ K j ⊆ K (j + 1) ∧
      K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧
      HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ U ∧
      (∀ x, χ j x ∈ Icc (0 : ℝ) 1) ∧ ∀ x ∈ K j, χ j x = 1)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (σ : ℕ → ℕ) (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x)))
    (hVcont : ∀ j x, Continuous (fun t => inner ℝ (V j t) x))
    (huniform : ∀ j (p : RationalCompactTimeWindow I) x ε, 0 < ε →
      ∀ᶠ k in atTop, ∀ t : RationalTimeSlice p,
        dist (inner ℝ ((hmem (σ k) j
          ⟨t.1, p.property.2 t.property⟩).toLp
          (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x)
          (inner ℝ (V j ⟨t.1, p.property.2 t.property⟩) x) < ε) :
    ∀ j, ∃ _hf : ∀ k, MemLp
      (fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))),
      Tendsto (fun k => eLpNorm
        ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
          (fun z : Vec3 × ℝ => (WithLp.toLp 2
            (compactnessMollifiedLimit u σ z) : L2Vec3))) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))))
        atTop (nhds 0) := by
  classical
  intro j
  let μ : Measure Vec3 := volume.restrict (K j)
  let ν : Measure ℝ := volume.restrict (J j)
  let ρ : Measure (Vec3 × ℝ) := μ.prod ν
  let : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hK j).1.measure_lt_top.ne
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (hJ j).1.measure_lt_top.ne
  obtain ⟨hf, G, hstrong⟩ :=
    strong_l2_on_compact_rectangle_of_cutoff_weak_slices
      hU hI u Du huMeas hDuMeas hweakGrad hbound hgradBound
      K χ hK hKcover hχ hmem σ V hweak hVcont huniform
      (hK j).1 (hK j).2.1 (hJ j).1 (hJ j).2
  let f : ℕ → Vec3 × ℝ → L2Vec3 :=
    fun k z => WithLp.toLp 2 (u (σ k) z)
  let v : Vec3 × ℝ → L2Vec3 :=
    fun z => WithLp.toLp 2 (compactnessMollifiedLimit u σ z)
  have hvMeas : Measurable v := by
    exact (WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := Vec3)).comp
      (measurable_compactnessMollifiedLimit u σ huMeas)
  have hsource (k : ℕ) (t : ℝ) (ht : t ∈ J j) :
      MemLp (fun x : Vec3 => f k (x,t)) 2 μ :=
    memLp_original_slice_on_exhaustion hI u huMeas K
      (fun a => ⟨(hK a).1, (hK a).2.1⟩)
      hbound (σ k) j ⟨t, (hJ j).2 ht⟩
  have hlimit (t : ℝ) (ht : t ∈ J j) :
      MemLp (fun x : Vec3 => v (x,t)) 2 μ :=
    compactnessMollifiedLimit_memLp_on_exhaustion u σ K χ
      (fun a => ⟨(hK a).1, (hK a).2.2.1, (hK a).2.2.2⟩)
      (fun a => (hχ a).2.2.2.2)
      hmem V hweak j ⟨t, (hJ j).2 ht⟩
  have hweakLocal (t : ℝ) (ht : t ∈ J j)
      (w : Lp L2Vec3 2 μ) : Tendsto
      (fun k => inner ℝ ((hsource k t ht).toLp
        (fun x => f k (x,t))) w) atTop
      (nhds (inner ℝ ((hlimit t ht).toLp
        (fun x => v (x,t))) w)) := by
    obtain ⟨hs, hl, hw⟩ :=
      weak_slices_to_compactnessMollifiedLimit_on_exhaustion hI
        u σ huMeas K χ hK (fun a => (hχ a).2.2.2.2)
        hbound hmem V hweak j ⟨t, (hJ j).2 ht⟩
    exact hw w
  obtain ⟨M, hM, hMb⟩ :=
    hbound (K j) (hK j).1 (hK j).2.1 (J j) (hJ j).1 (hJ j).2
  have hboundSlice (k : ℕ) (t : ℝ) (ht : t ∈ J j) :
      eLpNorm (fun x : Vec3 => f k (x,t)) 2 μ ≤
        M ^ (1 / 2 : ℝ) := by
    have henergy : (∫⁻ x : Vec3,
        ‖f k (x,t)‖ₑ ^ (2 : ℝ) ∂μ) ≤ M := by
      simpa only [f, μ, ← ofReal_norm, ← vec3EuclideanNorm_eq_l2] using
        hMb (σ k) t ht
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) (hsource k t ht).aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using
      ENNReal.rpow_le_rpow henergy (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hbound' : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ k t, t ∈ J j → eLpNorm (fun x : Vec3 => f k (x,t)) 2 μ ≤ B :=
    ⟨M ^ (1 / 2 : ℝ),
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM.ne,
      hboundSlice⟩
  have hEq := strong_product_limit_ae_eq_of_weak_slices
    (hJ j).1.measurableSet f v hvMeas hf G hstrong
    hsource hlimit hweakLocal hbound'
  have hvMem : MemLp v 2 ρ :=
    (memLp_congr_ae hEq).1 (Lp.memLp G)
  have hEqLp : hvMem.toLp v = G := by
    have h := MemLp.toLp_congr (Lp.memLp G) hvMem hEq
    exact h.symm.trans (Lp.toLp_coeFn G (Lp.memLp G))
  refine ⟨hf, ?_⟩
  have hstrong' : Tendsto (fun k => (hf k).toLp (f k))
      atTop (nhds (hvMem.toLp v)) := by simpa only [hEqLp] using hstrong
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf v hvMem).mp hstrong'

end CKN.Leray
