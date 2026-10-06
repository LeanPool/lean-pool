/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGlue
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationSliceLimit
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGoodSlices
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopfBridge

/-!
# Auxiliary facts for concatenating Leray–Hopf solutions

Time splitting of almost-everywhere statements and slab integrals, and the
continuity of the weak pairing of a strongly `L²`-continuous field
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The open interval `(a, c)` is the union of `(a, b)` and `(b, c)` up to a null set. -/
theorem lps_Ioo_ae_eq_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (Ioo a c : Set ℝ) =ᵐ[volume] (Ioo a b ∪ Ioo b c : Set ℝ) := by
  have heq : (Ioo a b ∪ Ioo b c : Set ℝ) = Ioo a c \ {b} := by
    ext t
    simp only [mem_union, mem_Ioo, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (ht | ht)
      · exact ⟨⟨ht.1, lt_of_lt_of_le ht.2 hbc⟩, ne_of_lt ht.2⟩
      · exact ⟨⟨lt_of_le_of_lt hab ht.1, ht.2⟩, ne_of_gt ht.1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
  rw [heq]
  exact (sdiff_null_ae_eq_self (measure_singleton b)).symm

/-- An almost-everywhere statement on two adjacent time intervals holds almost
everywhere on their union. -/
theorem lps_ae_restrict_Ioo_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {P : ℝ → Prop}
    (h1 : ∀ᵐ t ∂(volume.restrict (Ioo a b)), P t)
    (h2 : ∀ᵐ t ∂(volume.restrict (Ioo b c)), P t) :
    ∀ᵐ t ∂(volume.restrict (Ioo a c)), P t := by
  rw [Measure.restrict_congr_set (lps_Ioo_ae_eq_union hab hbc), ae_restrict_union_iff]
  exact ⟨h1, h2⟩

/-- The restrictions to the slabs `(a, b)` and `(b, c)` add up to the restriction to
`(a, c)`. -/
theorem lps_slab_restrict_eq_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c)) : Measure ParabolicPoint) =
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) +
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) := by
  refine le_antisymm (lps_slab_restrict_le_add a b c) ?_
  have hdisj : Disjoint (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) := by
    rw [Set.disjoint_left]
    intro z hz hz'
    exact lt_asymm hz.2.2 hz'.2.1
  have hmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  rw [← Measure.restrict_union hdisj hmeas]
  refine Measure.restrict_mono ?_ le_rfl
  intro z hz
  rcases hz with hz | hz
  · exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 hbc⟩
  · exact ⟨hz.1, lt_of_le_of_lt hab hz.2.1, hz.2.2⟩

/-- Lower integrals over adjacent slabs add. -/
theorem lps_lintegral_slab_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (f : ParabolicPoint → ℝ≥0∞) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), f z) =
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), f z) +
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), f z := by
  rw [lps_slab_restrict_eq_add hab hbc, lintegral_add_measure]

/-- A field with finite integral of the square of its norm and a.e. strongly
measurable is square integrable. -/
theorem lps_memLp_two_of_lintegral_lt_top {E : Type} [NormedAddCommGroup E]
    {μ : Measure ParabolicPoint} {f : ParabolicPoint → E} (hf : AEStronglyMeasurable f μ)
    (h : (∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) : MemLp f 2 μ := by
  have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := (2 : ℝ≥0∞)) (by norm_num)
    (by norm_num) hf).mpr (by simpa using h)
  exact this

/-- The weak pairing of a family that is strongly `L²`-continuous on an interval is
continuous on it. -/
theorem lps_pairing_continuousOn_of_l2 {α β : ℝ} {u : ParabolicPoint → Vec3}
    (hmem : ∀ t ∈ Icc α β, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hcont : ∀ t ∈ Icc α β, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t)) 2 volume)
      (nhdsWithin t (Icc α β)) (nhds 0))
    {w : Vec3 → Vec3} (hw : MemLp w 2 volume) :
    ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i) (Icc α β) := by
  intro t ht
  have hint (s : ℝ) (hs : s ∈ Icc α β) : (∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * w x i) =
      ∑ i : Fin 3, ∫ x : Vec3, u (x, s) i * w x i :=
    integral_finsetSum _ fun i _ =>
      (memLp_pi_iff.1 (hmem s hs) i).integrable_mul (memLp_pi_iff.1 hw i)
  have hm : ∀ᶠ s in nhdsWithin t (Icc α β), AEStronglyMeasurable
      (fun x : Vec3 => u (x, s) - u (x, t)) volume := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((hmem s hs).sub (hmem t ht)).aestronglyMeasurable
  have hcomp (i : Fin 3) : Tendsto (fun s : ℝ => ∫ x : Vec3, u (x, s) i * w x i)
      (nhdsWithin t (Icc α β)) (nhds (∫ x : Vec3, u (x, t) i * w x i)) := by
    refine lps_pairing_tendsto (l := nhdsWithin t (Icc α β)) (f := fun s x => u (x, s) i)
      (g := fun _ x => w x i) (memLp_pi_iff.1 (hmem t ht) i) (memLp_pi_iff.1 hw i) ?_
      (Eventually.of_forall fun _ => memLp_pi_iff.1 hw i)
      (lps_component_l2_tendsto (f := fun s x => u (x, s)) hm (hcont t ht) i) ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs using memLp_pi_iff.1 (hmem s hs) i
    · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (nhdsWithin t (Icc α β)) (nhds 0))
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ => hcomp i
  rw [ContinuousWithinAt, hint t ht]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hint s hs).symm

/-- The energy equality of a strong solution between its initial time and any later
time, in the extended-real form of the Leray–Hopf energy inequality
(`prop:lps-local-strong`). -/
theorem lps_strong_energy_ennreal {s s' : ℝ} {W : ParabolicPoint → Vec3}
    {DW : ParabolicPoint → Fin 3 → Vec3} {pW : ParabolicPoint → ℝ}
    (hW : IsLpsStrongSolution s s' W DW pW) {t : ℝ} (ht : t ∈ Icc s s') :
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (W (x, t))) ^ (2 : ℝ)) +
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
        ENNReal.ofReal (spatialGradientSq W DW z)) =
    ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (W (x, s))) ^ (2 : ℝ) := by
  have hs : s ∈ Icc s s' := ⟨le_rfl, hW.1.le⟩
  obtain ⟨-, -, -, -, -, -, hkin⟩ := ESS.LPS.lps_unregularised_h1_energy_identity hW
  obtain ⟨-, -, -, -, hMemDu, -, -⟩ := ESS.LPS.lps_strong_solution_derivative_data hW
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo s t) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo s s') :=
    fun z hz => ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht.2⟩
  have hDt : MemLp DW 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo s t))) :=
    hMemDu.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDint : Integrable (fun q : ParabolicPoint => ∑ k : Fin 3, ∑ j : Fin 3,
      DW q k j * DW q k j)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo s t))) :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ =>
      (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j).integrable_mul
        (memLp_pi_iff.1 (memLp_pi_iff.1 hDt k) j)
  have hgrad : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
      ENNReal.ofReal (spatialGradientSq W DW z)) =
      ENNReal.ofReal (∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
        ∑ k : Fin 3, ∑ j : Fin 3, DW q k j * DW q k j) := by
    rw [ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun q =>
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)]
    refine lintegral_congr fun q => ?_
    simp only [spatialGradientSq, pow_two]
  have hD0 : 0 ≤ ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
      ∑ k : Fin 3, ∑ j : Fin 3, DW q k j * DW q k j :=
    integral_nonneg fun q => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      mul_self_nonneg _
  have hW0 : 0 ≤ ∫ x : Vec3, ∑ k : Fin 3, W (x, t) k * W (x, t) k :=
    integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have hk := hkin s t hs ht ht.1
  have e2 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
      ∑ i : Fin 3, ∑ j : Fin 3, (DW z i j) ^ 2 =
      ∫ q in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
        ∑ k : Fin 3, ∑ j : Fin 3, DW q k j * DW q k j := by
    simp only [pow_two]
  have e1 : ∀ r : ℝ, ∫ x : Vec3, ∑ i : Fin 3, (W (x, r) i) ^ 2 =
      ∫ x : Vec3, ∑ k : Fin 3, W (x, r) k * W (x, r) k := by
    intro r
    simp only [pow_two]
  rw [e2, e1, e1] at hk
  have hmt := (ESS.lps_strong_solution_slice_memLp_two hW ht).1
  have hms := (ESS.lps_strong_solution_slice_memLp_two hW hs).1
  rw [serrin_lintegral_eucl_sq hmt, serrin_lintegral_eucl_sq hms, hgrad,
    ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hW0) hD0,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine congrArg ENNReal.ofReal ?_
  linarith only [hk]

/-- Approximate continuity of the pairing with a test field at the right end of an
interval, for a weakly continuous family with a uniform almost-everywhere `L²`
bound. -/
theorem lps_weak_pairing_test_hG {α s M : ℝ} (hαs : α ≤ s) {u : ParabolicPoint → Vec3}
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hweak : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i) (Icc α s))
    (hM : ∀ᵐ t ∂(volume.restrict (Ioo α s)), MemLp (fun x : Vec3 => u (x, t)) 2 volume ∧
      (eLpNorm (fun x : Vec3 => u (x, t)) 2 volume).toReal ≤ M) :
    ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo α s)), s - η < t →
      |(∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i) -
        ∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * φ (x, s) i| < δ := by
  intro δ hδ
  have hφi (i : Fin 3) : Continuous (fun y : Vec3 × ℝ => φ y i) :=
    (contDiff_pi.mp hφ i).continuous
  have hφic (i : Fin 3) : HasCompactSupport (fun y : Vec3 × ℝ => φ y i) :=
    hφc.comp_left (g := fun v : Vec3 => v i) (by simp)
  have hφmemS (i : Fin 3) (r : ℝ) : MemLp (fun x : Vec3 => φ (x, r) i) 2 volume :=
    ((hφi i).comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport (by
      refine IsCompact.of_isClosed_subset ((hφic i).image continuous_fst) (isClosed_tsupport _) ?_
      refine closure_minimal ?_ ((hφic i).image continuous_fst).isClosed
      intro x hx
      exact ⟨(x, r), subset_tsupport _ hx, rfl⟩)
  have hwS : MemLp (fun x : Vec3 => φ (x, s)) 2 volume :=
    memLp_pi_iff.2 fun i => hφmemS i s
  set g : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, s) i with hg
  have hgc : ContinuousWithinAt g (Icc α s) s := hweak (fun x => φ (x, s)) hwS s ⟨hαs, le_rfl⟩
  -- smallness of the test-field increments
  set N : ℝ → ℝ := fun t => ∑ i : Fin 3,
    (eLpNorm (fun x : Vec3 => φ (x, t) i - φ (x, s) i) 2 volume).toReal with hN
  have hN0 : Tendsto N (nhds s) (nhds 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (lps_test_slice_l2_tendsto (hφi i) (hφic i) s)
    simpa [hN, Function.comp_def] using this
  have hMN : Tendsto (fun t => M * N t) (nhds s) (nhds 0) := by
    simpa using hN0.const_mul M
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.tendsto_nhds_nhds.mp hMN (δ / 2) (by linarith only [hδ])
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.continuousWithinAt_iff.mp hgc (δ / 2) (by linarith only [hδ])
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, ?_⟩
  filter_upwards [hM, ae_restrict_mem measurableSet_Ioo] with t ⟨htm, htb⟩ htI hlt
  have hd1 : dist t s < η₁ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htI.2.le)]
    linarith only [hlt, min_le_left η₁ η₂]
  have hd2 : dist t s < η₂ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htI.2.le)]
    linarith only [hlt, min_le_right η₁ η₂]
  have hA := h₁ hd1
  have hB := h₂ (show t ∈ Icc α s from ⟨htI.1.le, htI.2.le⟩) hd2
  rw [Real.dist_eq, sub_zero] at hA
  rw [Real.dist_eq] at hB
  -- the decomposition
  have hui (i : Fin 3) : MemLp (fun x : Vec3 => u (x, t) i) 2 volume := memLp_pi_iff.1 htm i
  have hI1 (i : Fin 3) : Integrable (fun x : Vec3 => u (x, t) i *
      (φ (x, t) i - φ (x, s) i)) volume :=
    (hui i).integrable_mul ((hφmemS i t).sub (hφmemS i s))
  have hI2 (i : Fin 3) : Integrable (fun x : Vec3 => u (x, t) i * φ (x, s) i) volume :=
    (hui i).integrable_mul (hφmemS i s)
  have hI3 (i : Fin 3) : Integrable (fun x : Vec3 => u (x, t) i * φ (x, t) i) volume :=
    (hui i).integrable_mul (hφmemS i t)
  have hdec : (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i) -
      (∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * φ (x, s) i) =
      (∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)) + (g t - g s) := by
    have e1 : (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i) =
        ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * φ (x, t) i :=
      integral_finsetSum _ fun i _ => hI3 i
    have e2 : g t = ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * φ (x, s) i :=
      integral_finsetSum _ fun i _ => hI2 i
    have e3 : (∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * φ (x, s) i) = g s := rfl
    have this' : ∀ i : Fin 3, (∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)) +
        (∫ x : Vec3, u (x, t) i * φ (x, s) i) = ∫ x : Vec3, u (x, t) i * φ (x, t) i := by
      intro i
      rw [← integral_add (hI1 i) (hI2 i)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hsum : (∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * φ (x, t) i) =
        (∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)) +
          ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * φ (x, s) i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (this' i).symm
    rw [e1, e3, e2, hsum]
    ring
  have hcomp (i : Fin 3) : (eLpNorm (fun x : Vec3 => u (x, t) i) 2 volume).toReal ≤ M := by
    refine le_trans (ENNReal.toReal_mono htm.eLpNorm_ne_top ?_) htb
    exact eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable htm.aestronglyMeasurable)
      fun x => norm_le_pi_norm (u (x, t)) i
  have hb1 : |∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)| ≤ M * N t := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hN, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (lps_abs_integral_mul_le (hui i) ((hφmemS i t).sub (hφmemS i s))).trans ?_
    exact mul_le_mul_of_nonneg_right (hcomp i) ENNReal.toReal_nonneg
  rw [hdec]
  calc |(∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)) + (g t - g s)|
      ≤ |∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * (φ (x, t) i - φ (x, s) i)| + |g t - g s| :=
        abs_add_le _ _
    _ < δ := by
        have := lt_of_le_of_lt hb1 (lt_of_le_of_lt (le_abs_self _) hA)
        linarith only [this, hB]

end ESS

end
