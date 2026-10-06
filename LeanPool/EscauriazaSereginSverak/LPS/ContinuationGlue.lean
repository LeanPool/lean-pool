/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationTestField
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongShift
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateGoodSlices

/-!
# Gluing strong solutions across an intermediate time

Two strong solutions on `[a, b]` and `[b, c]` with the same slice at time `b`
form a strong solution on `[a, c]` (`lem:lps-continuation`). The weak time
derivative across `b` comes from the boundary-term lemma; the equation follows
by a time cutoff around `b`, since it involves no time derivative of the test
field once the weak time derivative is available.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slab `(a, c)` is covered by the slabs `(a, b)` and `(b, c)` up to the null
slice `t = b`. -/
theorem lps_slab_restrict_le_add (a b c : ℝ) :
    (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c)) : Measure ParabolicPoint) ≤
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) +
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) := by
  have hnull : (volume : Measure ParabolicPoint) (spaceTimeSet (Set.univ : Set Vec3) {b}) = 0 := by
    change (volume : Measure (Vec3 × ℝ)) ((Set.univ : Set Vec3) ×ˢ ({b} : Set ℝ)) = 0
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hcover : spaceTimeSet (Set.univ : Set Vec3) (Ioo a c) ⊆
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) ∪ spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))
        ∪ spaceTimeSet (Set.univ : Set Vec3) {b} := by
    intro z hz
    obtain ⟨-, h1, h2⟩ := hz
    rcases lt_trichotomy z.2 b with h | h | h
    · exact Or.inl (Or.inl ⟨mem_univ _, h1, h⟩)
    · exact Or.inr ⟨mem_univ _, h⟩
    · exact Or.inl (Or.inr ⟨mem_univ _, h, h2⟩)
  calc (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c)) : Measure ParabolicPoint)
      ≤ volume.restrict ((spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) ∪
          spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) ∪
            spaceTimeSet (Set.univ : Set Vec3) {b}) := Measure.restrict_mono hcover le_rfl
    _ ≤ (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) ∪
          spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))) +
          volume.restrict (spaceTimeSet (Set.univ : Set Vec3) {b}) := Measure.restrict_union_le _ _
    _ = volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) ∪
          spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) := by
        rw [Measure.restrict_eq_zero.mpr hnull, add_zero]
    _ ≤ _ := Measure.restrict_union_le _ _

/-- Integrals over adjacent slabs add, for a field whose coordinate representative is
integrable for the product slab measure. -/
theorem lps_slab_integral_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {f : ParabolicPoint → ℝ}
    (hf : Integrable (fun q : Vec3 × ℝ => f (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c)))) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), f z) =
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), f z) +
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), f z := by
  have hdisj : Disjoint (Ioo a b) (Ioo b c) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact lt_asymm ht.2 ht'.1
  have hmeas : MeasurableSet (Ioo b c) := measurableSet_Ioo
  have hae : (Ioo a c : Set ℝ) =ᵐ[volume] (Ioo a b ∪ Ioo b c : Set ℝ) := by
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
  have hμ : (volume.restrict (Ioo a c) : Measure ℝ) =
      volume.restrict (Ioo a b) + volume.restrict (Ioo b c) := by
    rw [Measure.restrict_congr_set hae, Measure.restrict_union hdisj hmeas]
  have hν : ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) +
        (volume : Measure Vec3).prod (volume.restrict (Ioo b c)) := by
    rw [hμ, Measure.prod_add]
  rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod]
  rw [hν] at hf ⊢
  exact integral_add_measure (hf.mono_measure (Measure.le_add_right le_rfl))
    (hf.mono_measure (Measure.le_add_left le_rfl))

/-- Square integrability on two adjacent slabs gives square integrability on the
union slab. -/
theorem lps_memLp_slab_glue {a b c : ℝ} {E : Type} [NormedAddCommGroup E] {F F₁ F₂ : ParabolicPoint → E}
    (h₁ : MemLp F₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (h₂ : MemLp F₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hF₁ : ∀ z : ParabolicPoint, z.2 ≤ b → F z = F₁ z)
    (hF₂ : ∀ z : ParabolicPoint, b < z.2 → F z = F₂ z) :
    MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))) := by
  have hm₁ : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))) := by
    refine (memLp_congr_ae ?_).mpr h₁
    filter_upwards [ae_restrict_mem ((MeasurableSet.univ.prod measurableSet_Ioo :
      MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))] with z hz
    exact hF₁ z hz.2.2.le
  have hm₂ : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))) := by
    refine (memLp_congr_ae ?_).mpr h₂
    filter_upwards [ae_restrict_mem ((MeasurableSet.univ.prod measurableSet_Ioo :
      MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))] with z hz
    exact hF₂ z hz.2.1
  have hae : AEStronglyMeasurable F
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) +
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))) :=
    hm₁.aestronglyMeasurable.add_measure hm₂.aestronglyMeasurable
  have hint : Integrable (fun z => ‖F z‖ ^ 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) +
        volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))) :=
    ((memLp_two_iff_integrable_sq_norm hm₁.aestronglyMeasurable).mp hm₁).add_measure
      ((memLp_two_iff_integrable_sq_norm hm₂.aestronglyMeasurable).mp hm₂)
  have hsum : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) +
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))) :=
    (memLp_two_iff_integrable_sq_norm hae).mpr hint
  exact hsum.mono_measure (lps_slab_restrict_le_add a b c)

/-- Strong `L²` continuity in time passes to the glued field: on each side from
the corresponding piece, and at the junction because the two slices agree
almost everywhere. -/
theorem lps_glue_l2_continuity {a b c : ℝ} (hab : a < b) (hbc : b < c) {E : Type}
    [NormedAddCommGroup E] {F F₁ F₂ : ParabolicPoint → E}
    (hF₁ : ∀ z : ParabolicPoint, z.2 ≤ b → F z = F₁ z)
    (hF₂ : ∀ z : ParabolicPoint, b < z.2 → F z = F₂ z)
    (h₁ : ∀ t ∈ Icc a b, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => F₁ (x, s) - F₁ (x, t)) 2 volume)
      (nhdsWithin t (Icc a b)) (nhds 0))
    (h₂ : ∀ t ∈ Icc b c, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => F₂ (x, s) - F₂ (x, t)) 2 volume)
      (nhdsWithin t (Icc b c)) (nhds 0))
    (htrace : (fun x : Vec3 => F₂ (x, b)) =ᵐ[volume] (fun x : Vec3 => F₁ (x, b))) :
    ∀ t ∈ Icc a c, Tendsto
      (fun s : ℝ => eLpNorm (fun x : Vec3 => F (x, s) - F (x, t)) 2 volume)
      (nhdsWithin t (Icc a c)) (nhds 0) := by
  intro t ht
  rcases lt_trichotomy t b with hlt | heq | hgt
  · -- left of the junction
    have hmem : Icc a b ∈ 𝓝[Icc a c] t := by
      refine mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, hlt, ?_⟩
      intro s hs
      exact ⟨hs.2.1, le_of_lt hs.1⟩
    have hT := (h₁ t ⟨ht.1, hlt.le⟩).mono_left (nhdsWithin_le_of_mem hmem)
    refine hT.congr' ?_
    filter_upwards [Iio_mem_nhds hlt |> fun h => mem_nhdsWithin_of_mem_nhds h] with s hs
    refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF₁ (x, s) (le_of_lt hs), hF₁ (x, t) hlt.le]
  · subst heq
    have hunion : Icc a c = Icc a t ∪ Icc t c := (Icc_union_Icc_eq_Icc hab.le hbc.le).symm
    rw [hunion, nhdsWithin_union, tendsto_sup]
    constructor
    · refine (h₁ t ⟨hab.le, le_rfl⟩).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hF₁ (x, s) hs.2, hF₁ (x, t) le_rfl]
    · refine (h₂ t ⟨le_rfl, hbc.le⟩).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · subst h
        simp
      · have hFs : ∀ x : Vec3, F (x, s) = F₂ (x, s) := fun x => hF₂ (x, s) h
        have h1 : (fun x : Vec3 => F (x, s) - F (x, t)) =ᵐ[volume]
            fun x : Vec3 => F₂ (x, s) - F₂ (x, t) := by
          filter_upwards [htrace] with x hx
          rw [hFs x, hF₁ (x, t) le_rfl, ← hx]
        exact (eLpNorm_congr_ae h1).symm
  · have hmem : Icc b c ∈ 𝓝[Icc a c] t := by
      refine mem_nhdsWithin.mpr ⟨Ioi b, isOpen_Ioi, hgt, ?_⟩
      intro s hs
      exact ⟨le_of_lt hs.1, hs.2.2⟩
    have hT := (h₂ t ⟨hgt.le, ht.2⟩).mono_left (nhdsWithin_le_of_mem hmem)
    refine hT.congr' ?_
    filter_upwards [Ioi_mem_nhds hgt |> fun h => mem_nhdsWithin_of_mem_nhds h] with s hs
    refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF₂ (x, s) hs, hF₂ (x, t) hgt]

private theorem lps_spatialPartial_eq_fderiv {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial φ j z = (fderiv ℝ φ (z.1, z.2)) (basisVec j, 0) := by
  unfold spatialPartial
  have hd : HasFDerivAt (fun x : Vec3 => φ (x, z.2))
      ((fderiv ℝ φ (z.1, z.2)).comp ((ContinuousLinearMap.id ℝ Vec3).prod 0)) z.1 := by
    have h1 : HasFDerivAt φ (fderiv ℝ φ (z.1, z.2)) (z.1, z.2) :=
      (hφ.differentiable (by simp) (z.1, z.2)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Vec3 => (x, z.2))
        ((ContinuousLinearMap.id ℝ Vec3).prod 0) z.1 :=
      (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
    exact h1.comp z.1 h2
  rw [hd.fderiv]
  simp

/-- The spatial derivative of a test field is continuous with compact support. -/
theorem lps_spatialPartial_cont_compact {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (j : Fin 3) :
    Continuous (fun q : Vec3 × ℝ => spatialPartial φ j q) ∧
      HasCompactSupport (fun q : Vec3 × ℝ => spatialPartial φ j q) := by
  have hfun : (fun q : Vec3 × ℝ => spatialPartial φ j q) =
      fun q => (fderiv ℝ φ q) (basisVec j, 0) := by
    funext q
    exact lps_spatialPartial_eq_fderiv hφ j q
  rw [hfun]
  exact ⟨(hφ.continuous_fderiv (by simp)).clm_apply continuous_const,
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec j, 0)⟩

/-- The time derivative of a test function is continuous with compact support. -/
theorem lps_timePartial_cont_compact {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Continuous (fun q : Vec3 × ℝ => timePartial φ q) ∧
      HasCompactSupport (fun q : Vec3 × ℝ => timePartial φ q) := by
  have hfun : (fun q : Vec3 × ℝ => timePartial φ q) =
      fun q => (fderiv ℝ φ q) (0, 1) := by
    funext q
    unfold timePartial
    have hd : HasFDerivAt (fun s : ℝ => φ (q.1, s))
        ((fderiv ℝ φ (q.1, q.2)).comp ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)))
          q.2 := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ (q.1, q.2)) (q.1, q.2) :=
        (hφ.differentiable (by simp) (q.1, q.2)).hasFDerivAt
      have h2 : HasFDerivAt (fun s : ℝ => (q.1, s))
          ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) q.2 :=
        (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
      exact h1.comp q.2 h2
    rw [hd.fderiv]
    simp
  rw [hfun]
  exact ⟨(hφ.continuous_fderiv (by simp)).clm_apply continuous_const,
    hφc.fderiv_apply (𝕜 := ℝ) ((0 : Vec3), (1 : ℝ))⟩

/-- Slice-wise weak derivatives give the space-time spatial weak derivative
identity for test fields. -/
theorem lps_slab_spatial_weak_of_slices {a c : ℝ} {F G : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a c))))
    (j : Fin 3)
    (hslice : ∀ᵐ t ∂(volume.restrict (Ioo a c)),
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x : Vec3 => F (x, t))
        (fun x : Vec3 => G (x, t)))
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), F z * spatialPartial φ j z) =
      -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), G z * φ z := by
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hFν := lps_memLp_slab_to_prod hF
  have hGν := lps_memLp_slab_to_prod hG
  obtain ⟨hdc, hdk⟩ := lps_spatialPartial_cont_compact hφs hφc j
  have h1 : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
      spatialPartial φ j (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    hFν.integrable_mul (q := 2) (hdc.memLp_of_hasCompactSupport hdk)
  have h2 : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) *
      φ (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    hGν.integrable_mul (q := 2) (hφs.continuous.memLp_of_hasCompactSupport hφc)
  rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod]
  rw [integral_prod_symm _ h1, integral_prod_symm _ h2]
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hslice] with t ht
  have hφt : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => φ (x, t)) :=
    hφs.comp (contDiff_id.prodMk contDiff_const)
  have hφtc : HasCompactSupport (fun x : Vec3 => φ (x, t)) := by
    refine IsCompact.of_isClosed_subset ((hφc.image continuous_fst)) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (hφc.image continuous_fst).isClosed
    intro x hx
    exact ⟨(x, t), subset_tsupport _ hx, rfl⟩
  have := ht (fun x => φ (x, t)) hφt hφtc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at this
  exact this

/-- Boundary term for the weak time derivative at the right end of a slab. -/
theorem lps_time_weak_boundary_right {a b c : ℝ} (hab : a < b) {F G : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hw : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z * timePartial φ z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G z * φ z)
    (hcont : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => F (x, s) - F (x, b)) 2 volume)
      (nhdsWithin b (Icc a b)) (nhds 0))
    (hFb : MemLp (fun x : Vec3 => F (x, b)) 2 volume)
    (hFs : ∀ s ∈ Icc a b, MemLp (fun x : Vec3 => F (x, s)) 2 volume)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), (F z * timePartial φ z + G z * φ z)) =
      ∫ x : Vec3, F (x, b) * φ (x, b) := by
  have hφ0 := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
    with hν
  have hFν := lps_memLp_slab_to_prod hF
  have hGν := lps_memLp_slab_to_prod hG
  obtain ⟨hdc, hdk⟩ : Continuous (fun q : Vec3 × ℝ => timePartial φ q) ∧
      HasCompactSupport (fun q : Vec3 × ℝ => timePartial φ q) := by
    have hfun : (fun q : Vec3 × ℝ => timePartial φ q) =
        fun q => (fderiv ℝ φ q) (0, 1) := by
      funext q
      unfold timePartial
      have hd : HasFDerivAt (fun s : ℝ => φ (q.1, s))
          ((fderiv ℝ φ (q.1, q.2)).comp ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ))) q.2 := by
        have h1 : HasFDerivAt φ (fderiv ℝ φ (q.1, q.2)) (q.1, q.2) :=
          (hφs.differentiable (by simp) (q.1, q.2)).hasFDerivAt
        have h2 : HasFDerivAt (fun s : ℝ => (q.1, s))
            ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) q.2 :=
          (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
        exact h1.comp q.2 h2
      rw [hd.fderiv]
      simp
    rw [hfun]
    exact ⟨(hφs.continuous_fderiv (by simp)).clm_apply continuous_const,
      hφc.fderiv_apply (𝕜 := ℝ) ((0 : Vec3), (1 : ℝ))⟩
  have hφ2 : MemLp φ 2 ν := hφs.continuous.memLp_of_hasCompactSupport hφc
  have hd2 : MemLp (fun q : Vec3 × ℝ => timePartial φ q) 2 ν :=
    hdc.memLp_of_hasCompactSupport hdk
  set F1 : Vec3 × ℝ → ℝ := fun q => F (parabolicHomeomorph.symm q) * timePartial φ q +
    G (parabolicHomeomorph.symm q) * φ q with hF1
  set F2 : Vec3 × ℝ → ℝ := fun q => -(F (parabolicHomeomorph.symm q) * φ q) with hF2
  have hF1i : Integrable F1 ν :=
    (hFν.integrable_mul (q := 2) hd2).add (hGν.integrable_mul (q := 2) hφ2)
  have hF2i : Integrable F2 ν := (hFν.integrable_mul (q := 2) hφ2).neg
  -- the boundary limit
  set ℓ : ℝ := -∫ x : Vec3, F (x, b) * φ (x, b) with hℓ
  have hlimit : Tendsto (fun s : ℝ => ∫ x : Vec3, F (x, s) * φ (x, s)) (nhdsWithin b (Icc a b))
      (nhds (∫ x : Vec3, F (x, b) * φ (x, b))) := by
    have hφcont : ∀ s : ℝ, Continuous fun x : Vec3 => φ (x, s) := fun s =>
      hφs.continuous.comp (continuous_id.prodMk continuous_const)
    have hφb : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => φ (x, s) - φ (x, b)) 2 volume)
        (nhds b) (nhds 0) := lps_test_slice_l2_tendsto hφs.continuous hφc b
    have hφmemS (s : ℝ) : MemLp (fun x : Vec3 => φ (x, s)) 2 volume :=
      (hφcont s).memLp_of_hasCompactSupport (by
        refine IsCompact.of_isClosed_subset (hφc.image continuous_fst) (isClosed_tsupport _) ?_
        refine closure_minimal ?_ (hφc.image continuous_fst).isClosed
        intro x hx
        exact ⟨(x, s), subset_tsupport _ hx, rfl⟩)
    exact lps_pairing_tendsto (l := nhdsWithin b (Icc a b)) hFb (hφmemS b)
      (by filter_upwards [self_mem_nhdsWithin] with s hs using hFs s hs)
      (Eventually.of_forall hφmemS) hcont (hφb.mono_left nhdsWithin_le_nhds)
  have hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ q : Vec3 × ℝ,
      (lpsCutoffRight b ε q.2 * F1 q - deriv (lpsCutoffRight b ε) q.2 * F2 q) ∂ν = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hηs : tsupport (lpsCutoffRight b ε) ⊆ Iic (b - ε) := by
      refine closure_minimal ?_ isClosed_Iic
      intro t ht
      by_contra hnot
      exact ht (lpsCutoffRight_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
    have hmem := lps_cutoff_test_mem_right (β := b - ε) (b := b) hφ0
      (lpsCutoffRight_contDiff b ε) hηs (by linarith only [hε0])
    have hwε := hw _ hmem
    have hmulEq : (fun z : Vec3 × ℝ => lpsCutoffRight b ε z.2 • φ z) =
        fun z => lpsCutoffRight b ε z.2 * φ z := by
      funext z
      exact smul_eq_mul _ _
    rw [hmulEq] at hwε
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at hwε
    have hηc : ContDiff ℝ (⊤ : ℕ∞) (lpsCutoffRight b ε) := lpsCutoffRight_contDiff b ε
    have hη1 : Continuous (deriv (lpsCutoffRight b ε)) := hηc.continuous_deriv (by simp)
    have hφ' : Continuous (fun q : Vec3 × ℝ => φ q) := hφs.continuous
    -- the two integrable pieces
    have hcont1 : Continuous (fun q : Vec3 × ℝ =>
        deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q) :=
      ((hη1.comp continuous_snd).mul hφ').add ((hηc.continuous.comp continuous_snd).mul hdc)
    have hcomp1 : HasCompactSupport (fun q : Vec3 × ℝ =>
        deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q) :=
      (hφc.mul_left (f := fun q : Vec3 × ℝ => deriv (lpsCutoffRight b ε) q.2)).add
        (hdk.mul_left (f := fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2))
    have hcont2 : Continuous (fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2 * φ q) :=
      (hηc.continuous.comp continuous_snd).mul hφ'
    have hcomp2 : HasCompactSupport (fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2 * φ q) :=
      hφc.mul_left (f := fun q : Vec3 × ℝ => lpsCutoffRight b ε q.2)
    have hA : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
        (deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q)) ν :=
      hFν.integrable_mul (q := 2) (hcont1.memLp_of_hasCompactSupport hcomp1)
    have hB : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) *
        (lpsCutoffRight b ε q.2 * φ q)) ν :=
      hGν.integrable_mul (q := 2) (hcont2.memLp_of_hasCompactSupport hcomp2)
    have hptw : ∀ q : Vec3 × ℝ,
        (lpsCutoffRight b ε q.2 * F1 q - deriv (lpsCutoffRight b ε) q.2 * F2 q) =
        F (parabolicHomeomorph.symm q) *
          (deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q) +
        G (parabolicHomeomorph.symm q) * (lpsCutoffRight b ε q.2 * φ q) := by
      intro q
      simp only [hF1, hF2]
      ring
    have hwε' : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
        (deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q) ∂ν) =
        -∫ q : Vec3 × ℝ, G (parabolicHomeomorph.symm q) *
          (lpsCutoffRight b ε q.2 * φ q) ∂ν := by
      have hsame : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
          timePartial (fun y : ParabolicPoint => lpsCutoffRight b ε y.2 * φ y)
            (parabolicHomeomorph.symm q) ∂ν) =
          ∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
            (deriv (lpsCutoffRight b ε) q.2 * φ q + lpsCutoffRight b ε q.2 * timePartial φ q)
              ∂ν := by
        congr 1
        funext q
        rw [lps_cutoff_timePartial hηc hφs]
        rfl
      rw [← hsame]
      exact hwε
    simp_rw [hptw]
    rw [integral_add hA hB, hwε']
    ring
  have hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      b - η < t → |(∫ x : Vec3, F2 (x, t)) - ℓ| < δ := by
    intro δ hδ
    obtain ⟨η, hη, hη'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlimit) δ hδ
    refine ⟨η, hη, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht hbt
    have hd : dist t b < η := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2.le)]
      linarith only [hbt]
    have h := hη' (show t ∈ Icc a b from ⟨ht.1.le, ht.2.le⟩) hd
    rw [Real.dist_eq] at h
    have hF2t : (∫ x : Vec3, F2 (x, t)) = -∫ x : Vec3, F (x, t) * φ (x, t) := by
      exact integral_neg (fun x : Vec3 => F (x, t) * φ (x, t))
    rw [hF2t, hℓ]
    have : -(∫ x : Vec3, F (x, t) * φ (x, t)) - -∫ x : Vec3, F (x, b) * φ (x, b) =
        -((∫ x : Vec3, F (x, t) * φ (x, t)) - ∫ x : Vec3, F (x, b) * φ (x, b)) := by ring
    rw [this, abs_neg]
    exact h
  have hECL := lps_endpoint_boundary_right hab hF1i hF2i hid hG
  rw [lps_setIntegral_slab_to_prod]
  rw [show (∫ q : Vec3 × ℝ, (fun z : ParabolicPoint => F z * timePartial φ z + G z * φ z)
      (parabolicHomeomorph.symm q) ∂ν) = ∫ q : Vec3 × ℝ, F1 q ∂ν from rfl, hECL, hℓ]
  ring

/-- Boundary term for the weak time derivative at the left end of a slab. -/
theorem lps_time_weak_boundary_left {a b a₀ : ℝ} (hab : a < b) {F G : ParabolicPoint → ℝ}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hw : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z * timePartial φ z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G z * φ z)
    (hcont : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => F (x, s) - F (x, a)) 2 volume)
      (nhdsWithin a (Icc a b)) (nhds 0))
    (hFb : MemLp (fun x : Vec3 => F (x, a)) 2 volume)
    (hFs : ∀ s ∈ Icc a b, MemLp (fun x : Vec3 => F (x, s)) 2 volume)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a₀ b)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), (F z * timePartial φ z + G z * φ z)) =
      -∫ x : Vec3, F (x, a) * φ (x, a) := by
  have hφ0 := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
    with hν
  have hFν := lps_memLp_slab_to_prod hF
  have hGν := lps_memLp_slab_to_prod hG
  obtain ⟨hdc, hdk⟩ : Continuous (fun q : Vec3 × ℝ => timePartial φ q) ∧
      HasCompactSupport (fun q : Vec3 × ℝ => timePartial φ q) := by
    have hfun : (fun q : Vec3 × ℝ => timePartial φ q) =
        fun q => (fderiv ℝ φ q) (0, 1) := by
      funext q
      unfold timePartial
      have hd : HasFDerivAt (fun s : ℝ => φ (q.1, s))
          ((fderiv ℝ φ (q.1, q.2)).comp ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ))) q.2 := by
        have h1 : HasFDerivAt φ (fderiv ℝ φ (q.1, q.2)) (q.1, q.2) :=
          (hφs.differentiable (by simp) (q.1, q.2)).hasFDerivAt
        have h2 : HasFDerivAt (fun s : ℝ => (q.1, s))
            ((0 : ℝ →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ ℝ)) q.2 :=
          (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
        exact h1.comp q.2 h2
      rw [hd.fderiv]
      simp
    rw [hfun]
    exact ⟨(hφs.continuous_fderiv (by simp)).clm_apply continuous_const,
      hφc.fderiv_apply (𝕜 := ℝ) ((0 : Vec3), (1 : ℝ))⟩
  have hφ2 : MemLp φ 2 ν := hφs.continuous.memLp_of_hasCompactSupport hφc
  have hd2 : MemLp (fun q : Vec3 × ℝ => timePartial φ q) 2 ν :=
    hdc.memLp_of_hasCompactSupport hdk
  set F1 : Vec3 × ℝ → ℝ := fun q => F (parabolicHomeomorph.symm q) * timePartial φ q +
    G (parabolicHomeomorph.symm q) * φ q with hF1
  set F2 : Vec3 × ℝ → ℝ := fun q => -(F (parabolicHomeomorph.symm q) * φ q) with hF2
  have hF1i : Integrable F1 ν :=
    (hFν.integrable_mul (q := 2) hd2).add (hGν.integrable_mul (q := 2) hφ2)
  have hF2i : Integrable F2 ν := (hFν.integrable_mul (q := 2) hφ2).neg
  -- the boundary limit
  set ℓ : ℝ := -∫ x : Vec3, F (x, a) * φ (x, a) with hℓ
  have hlimit : Tendsto (fun s : ℝ => ∫ x : Vec3, F (x, s) * φ (x, s)) (nhdsWithin a (Icc a b))
      (nhds (∫ x : Vec3, F (x, a) * φ (x, a))) := by
    have hφcont : ∀ s : ℝ, Continuous fun x : Vec3 => φ (x, s) := fun s =>
      hφs.continuous.comp (continuous_id.prodMk continuous_const)
    have hφb : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => φ (x, s) - φ (x, a)) 2 volume)
        (nhds a) (nhds 0) := lps_test_slice_l2_tendsto hφs.continuous hφc a
    have hφmemS (s : ℝ) : MemLp (fun x : Vec3 => φ (x, s)) 2 volume :=
      (hφcont s).memLp_of_hasCompactSupport (by
        refine IsCompact.of_isClosed_subset (hφc.image continuous_fst) (isClosed_tsupport _) ?_
        refine closure_minimal ?_ (hφc.image continuous_fst).isClosed
        intro x hx
        exact ⟨(x, s), subset_tsupport _ hx, rfl⟩)
    exact lps_pairing_tendsto (l := nhdsWithin a (Icc a b)) hFb (hφmemS a)
      (by filter_upwards [self_mem_nhdsWithin] with s hs using hFs s hs)
      (Eventually.of_forall hφmemS) hcont (hφb.mono_left nhdsWithin_le_nhds)
  have hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ q : Vec3 × ℝ,
      (lpsCutoffLeft a ε q.2 * F1 q - deriv (lpsCutoffLeft a ε) q.2 * F2 q) ∂ν = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : 0 < ε := hε
    have hηs : tsupport (lpsCutoffLeft a ε) ⊆ Ici (a + ε) := by
      refine closure_minimal ?_ isClosed_Ici
      intro t ht
      by_contra hnot
      exact ht (lpsCutoffLeft_eq_zero hε0 (le_of_lt (not_le.mp hnot)))
    have hmem := lps_cutoff_test_mem_left (α := a + ε) (b := a) hφ0
      (lpsCutoffLeft_contDiff a ε) hηs (by linarith only [hε0])
    have hwε := hw _ hmem
    have hmulEq : (fun z : Vec3 × ℝ => lpsCutoffLeft a ε z.2 • φ z) =
        fun z => lpsCutoffLeft a ε z.2 * φ z := by
      funext z
      exact smul_eq_mul _ _
    rw [hmulEq] at hwε
    rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod] at hwε
    have hηc : ContDiff ℝ (⊤ : ℕ∞) (lpsCutoffLeft a ε) := lpsCutoffLeft_contDiff a ε
    have hη1 : Continuous (deriv (lpsCutoffLeft a ε)) := hηc.continuous_deriv (by simp)
    have hφ' : Continuous (fun q : Vec3 × ℝ => φ q) := hφs.continuous
    -- the two integrable pieces
    have hcont1 : Continuous (fun q : Vec3 × ℝ =>
        deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q) :=
      ((hη1.comp continuous_snd).mul hφ').add ((hηc.continuous.comp continuous_snd).mul hdc)
    have hcomp1 : HasCompactSupport (fun q : Vec3 × ℝ =>
        deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q) :=
      (hφc.mul_left (f := fun q : Vec3 × ℝ => deriv (lpsCutoffLeft a ε) q.2)).add
        (hdk.mul_left (f := fun q : Vec3 × ℝ => lpsCutoffLeft a ε q.2))
    have hcont2 : Continuous (fun q : Vec3 × ℝ => lpsCutoffLeft a ε q.2 * φ q) :=
      (hηc.continuous.comp continuous_snd).mul hφ'
    have hcomp2 : HasCompactSupport (fun q : Vec3 × ℝ => lpsCutoffLeft a ε q.2 * φ q) :=
      hφc.mul_left (f := fun q : Vec3 × ℝ => lpsCutoffLeft a ε q.2)
    have hA : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
        (deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q)) ν :=
      hFν.integrable_mul (q := 2) (hcont1.memLp_of_hasCompactSupport hcomp1)
    have hB : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) *
        (lpsCutoffLeft a ε q.2 * φ q)) ν :=
      hGν.integrable_mul (q := 2) (hcont2.memLp_of_hasCompactSupport hcomp2)
    have hptw : ∀ q : Vec3 × ℝ,
        (lpsCutoffLeft a ε q.2 * F1 q - deriv (lpsCutoffLeft a ε) q.2 * F2 q) =
        F (parabolicHomeomorph.symm q) *
          (deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q) +
        G (parabolicHomeomorph.symm q) * (lpsCutoffLeft a ε q.2 * φ q) := by
      intro q
      simp only [hF1, hF2]
      ring
    have hwε' : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
        (deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q) ∂ν) =
        -∫ q : Vec3 × ℝ, G (parabolicHomeomorph.symm q) *
          (lpsCutoffLeft a ε q.2 * φ q) ∂ν := by
      have hsame : (∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
          timePartial (fun y : ParabolicPoint => lpsCutoffLeft a ε y.2 * φ y)
            (parabolicHomeomorph.symm q) ∂ν) =
          ∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q) *
            (deriv (lpsCutoffLeft a ε) q.2 * φ q + lpsCutoffLeft a ε q.2 * timePartial φ q)
              ∂ν := by
        congr 1
        funext q
        rw [lps_cutoff_timePartial hηc hφs]
        rfl
      rw [← hsame]
      exact hwε
    simp_rw [hptw]
    rw [integral_add hA hB, hwε']
    ring
  have hG : ∀ δ > 0, ∃ η > 0, ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      t < a + η → |(∫ x : Vec3, F2 (x, t)) - ℓ| < δ := by
    intro δ hδ
    obtain ⟨η, hη, hη'⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlimit) δ hδ
    refine ⟨η, hη, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht hbt
    have hd : dist t a < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      linarith only [hbt]
    have h := hη' (show t ∈ Icc a b from ⟨ht.1.le, ht.2.le⟩) hd
    rw [Real.dist_eq] at h
    have hF2t : (∫ x : Vec3, F2 (x, t)) = -∫ x : Vec3, F (x, t) * φ (x, t) := by
      exact integral_neg (fun x : Vec3 => F (x, t) * φ (x, t))
    rw [hF2t, hℓ]
    have : -(∫ x : Vec3, F (x, t) * φ (x, t)) - -∫ x : Vec3, F (x, a) * φ (x, a) =
        -((∫ x : Vec3, F (x, t) * φ (x, t)) - ∫ x : Vec3, F (x, a) * φ (x, a)) := by ring
    rw [this, abs_neg]
    exact h
  have hECL := lps_endpoint_boundary_left hab hF1i hF2i hid hG
  rw [lps_setIntegral_slab_to_prod]
  rw [show (∫ q : Vec3 × ℝ, (fun z : ParabolicPoint => F z * timePartial φ z + G z * φ z)
      (parabolicHomeomorph.symm q) ∂ν) = ∫ q : Vec3 × ℝ, F1 q ∂ν from rfl, hECL, hℓ]


/-- The weak time derivative passes across the gluing time: if the two pieces have
weak time derivatives, are strongly `L²`-continuous up to the junction and agree
there, the glued field has the glued weak time derivative. -/
theorem lps_time_weak_glue {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {F₁ F₂ F G₁ G₂ G : ParabolicPoint → ℝ}
    (hF₁ : MemLp F₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG₁ : MemLp G₁ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hF₂ : MemLp F₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hG₂ : MemLp G₂ 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c))))
    (hw₁ : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F₁ z * timePartial φ z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), G₁ z * φ z)
    (hw₂ : ∀ φ : Vec3 × ℝ → ℝ,
      φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo b c) →
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), F₂ z * timePartial φ z) =
        -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c), G₂ z * φ z)
    (hcont₁ : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => F₁ (x, s) - F₁ (x, b)) 2 volume)
      (nhdsWithin b (Icc a b)) (nhds 0))
    (hcont₂ : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => F₂ (x, s) - F₂ (x, b)) 2 volume)
      (nhdsWithin b (Icc b c)) (nhds 0))
    (hFb₁ : MemLp (fun x : Vec3 => F₁ (x, b)) 2 volume)
    (hFs₁ : ∀ s ∈ Icc a b, MemLp (fun x : Vec3 => F₁ (x, s)) 2 volume)
    (hFb₂ : MemLp (fun x : Vec3 => F₂ (x, b)) 2 volume)
    (hFs₂ : ∀ s ∈ Icc b c, MemLp (fun x : Vec3 => F₂ (x, s)) 2 volume)
    (htrace : (fun x : Vec3 => F₂ (x, b)) =ᵐ[volume] (fun x : Vec3 => F₁ (x, b)))
    (hF : ∀ z : ParabolicPoint, z.2 ≤ b → F z = F₁ z)
    (hF' : ∀ z : ParabolicPoint, b < z.2 → F z = F₂ z)
    (hG : ∀ z : ParabolicPoint, z.2 ≤ b → G z = G₁ z)
    (hG' : ∀ z : ParabolicPoint, b < z.2 → G z = G₂ z)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a c)) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), F z * timePartial φ z) =
      -∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c), G z * φ z := by
  have hφ0 := hφ
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hFm := lps_memLp_slab_glue hF₁ hF₂ hF hF'
  have hGm := lps_memLp_slab_glue hG₁ hG₂ hG hG'
  obtain ⟨hdc, hdk⟩ := lps_timePartial_cont_compact hφs hφc
  have hFν := lps_memLp_slab_to_prod hFm
  have hGν := lps_memLp_slab_to_prod hGm
  have hI1 : Integrable (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q) *
      timePartial φ (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    hFν.integrable_mul (q := 2) (hdc.memLp_of_hasCompactSupport hdk)
  have hI2 : Integrable (fun q : Vec3 × ℝ => G (parabolicHomeomorph.symm q) *
      φ (parabolicHomeomorph.symm q))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a c))) :=
    hGν.integrable_mul (q := 2) (hφs.continuous.memLp_of_hasCompactSupport hφc)
  have hsplit := lps_slab_integral_split hab.le hbc.le
    (f := fun z => F z * timePartial φ z + G z * φ z) (hI1.add hI2)
  have hR := lps_time_weak_boundary_right hab hF₁ hG₁ hw₁ hcont₁ hFb₁ hFs₁ hφ0
  have hL := lps_time_weak_boundary_left hbc hF₂ hG₂ hw₂ hcont₂ hFb₂ hFs₂ hφ0
  have hmeas1 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hmeas2 : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo b c)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hc1 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b),
      (F z * timePartial φ z + G z * φ z)) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b),
        (F₁ z * timePartial φ z + G₁ z * φ z) := by
    refine setIntegral_congr_fun hmeas1 fun z hz => ?_
    simp only [hF z hz.2.2.le, hG z hz.2.2.le]
  have hc2 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c),
      (F z * timePartial φ z + G z * φ z)) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo b c),
        (F₂ z * timePartial φ z + G₂ z * φ z) := by
    refine setIntegral_congr_fun hmeas2 fun z hz => ?_
    simp only [hF' z hz.2.1, hG' z hz.2.1]
  have htr : (∫ x : Vec3, F₂ (x, b) * φ (x, b)) = ∫ x : Vec3, F₁ (x, b) * φ (x, b) := by
    refine integral_congr_ae ?_
    filter_upwards [htrace] with x hx
    rw [hx]
  have hsum0 : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a c),
      (F z * timePartial φ z + G z * φ z)) = 0 := by
    rw [hsplit, hc1, hc2, hR, hL, htr]
    ring
  rw [lps_setIntegral_slab_to_prod] at hsum0
  rw [lps_setIntegral_slab_to_prod, lps_setIntegral_slab_to_prod]
  have := integral_add hI1 hI2
  linarith only [hsum0, this]

end ESS

end
