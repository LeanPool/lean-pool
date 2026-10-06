/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularityCore
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest

/-!
# Spatial Sobolev slices for time regularity

The weak spatial derivative and slice-disintegration lemmas used by the
all-order time-regularity argument.
-/

public section

open MeasureTheory
open Set
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

open CKN.Leray

/-- The product norm on space-time points used for spatial Sobolev slices. -/
local instance smoothingTimeRegularitySpatialPointNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real product normed-space structure used for spatial Sobolev slices. -/
local instance smoothingTimeRegularitySpatialPointNormedSpace :
    NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

private theorem lps_memLp_mul_of_bounded_left
    {f g : Vec3 → ℝ} {L : ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hbound : ∀ x, |g x| ≤ L) :
    MemLp (fun x => g x * f x) 2 volume := by
  apply MemLp.of_le_mul hf (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · filter_upwards [] with x
    change |g x * f x| ≤ L * |f x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg (f x))

private theorem lps_weakPartial_congr_ae {U : Set Vec3} {i : Fin 3}
    {f f' df df' : Vec3 → ℝ} (hweak : HasWeakPartialDerivOn U i f df)
    (hf : f =ᵐ[volume.restrict U] f')
    (hdf : df =ᵐ[volume.restrict U] df') :
    HasWeakPartialDerivOn U i f' df' := by
  intro φ hφ hφc hφU
  calc
    ∫ x in U, f' x * spatialDeriv φ i x =
        ∫ x in U, f x * spatialDeriv φ i x := by
          apply integral_congr_ae
          filter_upwards [hf] with x hx
          rw [hx]
    _ = -∫ x in U, df x * φ x := hweak φ hφ hφc hφU
    _ = -∫ x in U, df' x * φ x := by
          congr 1
          apply integral_congr_ae
          filter_upwards [hdf] with x hx
          rw [hx]

/-- A bounded `H¹` velocity slice has an `L²` weak gradient for each
component of its tensor product (`eq:lps-Hm-energy`). -/
theorem lps_velocityTensor_component_hasWeakGradientOn
    (u : Vec3 → Vec3) (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i : Fin 3,
      IsSobolevFamilyOn 1 (Set.univ : Set Vec3) (fun x => u x i) (D i))
    {L : ℝ} (hbound : ∀ i x, |u x i| ≤ L) (i j : Fin 3) :
    HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x i * u x j)
      (fun x k => D i [k] x * u x j + u x i * D j [k] x) ∧
    ∀ k : Fin 3,
      MemLp (fun x => D i [k] x * u x j + u x i * D j [k] x) 2 volume := by
  let hi := hD i
  let hj := hD j
  have hzero_i : D i [] =ᵐ[volume.restrict (Set.univ : Set Vec3)]
      (fun x => u x i) := hi.zero
  have hzero_j : D j [] =ᵐ[volume.restrict (Set.univ : Set Vec3)]
      (fun x => u x j) := hj.zero
  have hu_i : MemLp (fun x : Vec3 => u x i) 2
      (volume.restrict (Set.univ : Set Vec3)) := by
    exact (hi.memL2 [] (by simp)).ae_eq hzero_i
  have hu_j : MemLp (fun x : Vec3 => u x j) 2
      (volume.restrict (Set.univ : Set Vec3)) := by
    exact (hj.memL2 [] (by simp)).ae_eq hzero_j
  have hDu_i : ∀ k : Fin 3, MemLp (fun x => D i [k] x) 2
      (volume.restrict (Set.univ : Set Vec3)) := by
    intro k
    exact hi.memL2 [k] (by simp)
  have hDu_j : ∀ k : Fin 3, MemLp (fun x => D j [k] x) 2
      (volume.restrict (Set.univ : Set Vec3)) := by
    intro k
    exact hj.memL2 [k] (by simp)
  have hweak_i : HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x i) (fun x k => D i [k] x) := by
    intro k
    simpa only [List.nil_append] using
      lps_weakPartial_congr_ae (hi.weak [] k (by simp)) hzero_i
        Filter.EventuallyEq.rfl
  have hweak_j : HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x j) (fun x k => D j [k] x) := by
    intro k
    simpa only [List.nil_append] using
      lps_weakPartial_congr_ae (hj.weak [] k (by simp)) hzero_j
        Filter.EventuallyEq.rfl
  have hweak := HasWeakGradientOn.mul_of_memLp_two isOpen_univ
    hu_i hu_j hDu_i hDu_j hweak_i hweak_j
  refine ⟨hweak, ?_⟩
  intro k
  have hDu_i_vol : MemLp (fun x => D i [k] x) 2 volume := by
    simpa only [Measure.restrict_univ] using hDu_i k
  have hDu_j_vol : MemLp (fun x => D j [k] x) 2 volume := by
    simpa only [Measure.restrict_univ] using hDu_j k
  have hu_i_vol : MemLp (fun x => u x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu_i
  have hu_j_vol : MemLp (fun x => u x j) 2 volume := by
    simpa only [Measure.restrict_univ] using hu_j
  have hfirst := lps_memLp_mul_of_bounded_left
    hDu_i_vol hu_j_vol (hbound j)
  have hfirst' : MemLp (fun x => D i [k] x * u x j) 2 volume := by
    apply hfirst.ae_eq
    exact Filter.Eventually.of_forall fun x => by ring
  have hsecond := lps_memLp_mul_of_bounded_left
    hDu_j_vol hu_i_vol (hbound i)
  have hsecond' : MemLp (fun x => u x i * D j [k] x) 2 volume := by
    exact hsecond
  exact hfirst'.add hsecond'

/-- The divergence of the velocity tensor is spatially `L²` for a bounded
`H¹` slice (`prop:lps-smoothing`). -/
theorem lps_velocityTensor_divergence_memLp
    (u : Vec3 → Vec3) (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i : Fin 3,
      IsSobolevFamilyOn 1 (Set.univ : Set Vec3) (fun x => u x i) (D i))
    {L : ℝ} (hbound : ∀ i x, |u x i| ≤ L) (i : Fin 3) :
    MemLp (fun x => ∑ j : Fin 3,
      (D i [j] x * u x j + u x i * D j [j] x)) 2 volume := by
  exact memLp_finsetSum Finset.univ (fun j _ =>
    (lps_velocityTensor_component_hasWeakGradientOn u D hD hbound i j).2 j)

/-- The spatial Laplacian of an `H²` slice belongs to spatial `L²`
(`prop:lps-smoothing`). -/
theorem lps_spatialLaplacian_memLp
    {f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hD : IsSobolevFamilyOn 2 (Set.univ : Set Vec3) f D) :
    MemLp (fun x => ∑ j : Fin 3, D [j, j] x) 2 volume := by
  exact memLp_finsetSum Finset.univ (fun j _ => by
    simpa only [Measure.restrict_univ] using hD.memL2 [j, j] (by simp))

/-- Every ordered derivative in a space-time `L²(I; H^m)` family has an
spatial `L²` representative on almost every time slice. -/
theorem lps_sobolevFamily_slice_memLp_ae
    {m : ℕ} {I : Set ℝ} {f : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hD : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I f D)
    (α : List (Fin 3)) (hα : α.length ≤ m) :
    ∀ᵐ t ∂(volume.restrict I),
      MemLp (fun x : Vec3 => D α (x, t)) 2 volume := by
  have hspaceTime : MemLp (D α) 2
      ((volume : Measure Vec3).prod (volume.restrict I)) := by
    have hrestricted : MemLp (D α) 2
        (volume.restrict ((Set.univ : Set Vec3) ×ˢ I)) := hD.memL2 α hα
    convert hrestricted using 1
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict Set.univ I,
      Measure.restrict_univ]
  have hsq : Integrable (fun q => ‖D α q‖ ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict I)) :=
    (memLp_two_iff_integrable_sq_norm hspaceTime.aestronglyMeasurable).1 hspaceTime
  filter_upwards [hspaceTime.aestronglyMeasurable.prodMk_right,
    hsq.prod_left_ae] with t hmeas hint
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hint

/-- The slice representatives supplied by an `L²(I; H^m)` family are
simultaneously square-integrable for all ordered words through order `m`. -/
theorem lps_sobolevFamily_allSlices_memLp_ae
    {m : ℕ} {I : Set ℝ} {f : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hD : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) I f D) :
    ∀ᵐ t ∂(volume.restrict I), ∀ α : List (Fin 3), α.length ≤ m →
      MemLp (fun x : Vec3 => D α (x, t)) 2 volume := by
  rw [ae_all_iff]
  intro α
  rw [ae_all_iff]
  intro hα
  exact lps_sobolevFamily_slice_memLp_ae hD α hα

private theorem lps_spatialTest_memLp_slab {a b : ℝ} {g : Vec3 → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    MemLp (fun p : Vec3 × ℝ => g p.1) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
  rw [lps_measure_slab_eq_prod]
  have hmeas : AEStronglyMeasurable (fun p : Vec3 × ℝ => g p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    hg.aestronglyMeasurable.comp_fst
  rw [memLp_two_iff_integrable_sq hmeas]
  have hspace : Integrable (fun x : Vec3 => g x ^ 2) volume :=
    (hg.memLp_of_hasCompactSupport hgc).integrable_sq
  have htime : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo a b)) :=
    integrable_const _
  have hprod := hspace.mul_prod htime
  simpa using hprod

private theorem lps_continuous_compact_support_bounded {θ : ℝ → ℝ}
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    ∃ C : ℝ, ∀ t, ‖θ t‖ ≤ C := by
  by_cases hne : (tsupport θ).Nonempty
  · obtain ⟨t₀, ht₀, hmax⟩ := hθc.isCompact.exists_isMaxOn hne
      hθ.norm.continuousOn
    refine ⟨‖θ t₀‖, fun t => ?_⟩
    by_cases ht : t ∈ tsupport θ
    · simpa only [Set.mem_ofPred_eq] using hmax ht
    · have hzero : θ t = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  · have hzero : θ = 0 := by
      funext t
      by_contra ht
      exact hne ⟨t, (subset_tsupport (f := θ)) (Function.mem_support.mpr ht)⟩
    exact ⟨0, by simp [hzero]⟩

/-- Fubini factors a square-integrable space-time field against a separated
spatial and temporal test. -/
private theorem lps_integral_slab_separated {a b : ℝ}
    {F : Vec3 × ℝ → ℝ} {g : Vec3 → ℝ} {θ : ℝ → ℝ}
    (hF : MemLp F 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Integrable (fun p : Vec3 × ℝ => F p * g p.1)
        (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) ∧
      (∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
        F p * (g p.1 * θ p.2)) =
        ∫ t in Ioo a b, θ t * ∫ x : Vec3, F (x, t) * g x := by
  have hFg := hF.integrable_mul
    (lps_spatialTest_memLp_slab (a := a) (b := b) hg hgc)
  obtain ⟨C, hC⟩ := lps_continuous_compact_support_bounded hθ hθc
  have hFgθ : Integrable (fun p : Vec3 × ℝ => F p * (g p.1 * θ p.2))
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
    have h := hFg.mul_bdd (hθ.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun p => hC p.2)
    refine h.congr (ae_of_all _ fun p => ?_)
    change (F p * g p.1) * θ p.2 = F p * (g p.1 * θ p.2)
    ring
  have hmeasure := lps_measure_slab_eq_prod a b
  have hFgProd : Integrable (fun p : Vec3 × ℝ => F p * g p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← hmeasure]
    exact hFg
  have hFgθProd : Integrable
      (fun p : Vec3 × ℝ => F p * (g p.1 * θ p.2))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← hmeasure]
    exact hFgθ
  refine ⟨hFg, ?_⟩
  rw [hmeasure, integral_prod_symm _ hFgθProd]
  refine integral_congr_ae ?_
  filter_upwards [hFgProd.prod_left_ae] with t ht
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change F (x, t) * (g x * θ t) = θ t * (F (x, t) * g x)
  ring

/-- A space-time weak spatial derivative in an `L²(I; H^m)` family is a
weak derivative on almost every spatial slice. -/
theorem lps_sobolevFamily_slice_weak_partial_ae
    {a b : ℝ} {m : ℕ} {f : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hD : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) f D)
    (α : List (Fin 3)) (j : Fin 3) (hα : α.length < m) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j
        (fun x => D α (x, t)) (fun x => D (α ++ [j]) (x, t)) := by
  have hαle : α.length ≤ m := hα.le
  have hnextle : (α ++ [j]).length ≤ m := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hloc : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      LocallyIntegrableOn (fun x : Vec3 => D α (x, t)) Set.univ volume ∧
      LocallyIntegrableOn (fun x : Vec3 => D (α ++ [j]) (x, t)) Set.univ volume := by
    filter_upwards [lps_sobolevFamily_slice_memLp_ae hD α hαle,
      lps_sobolevFamily_slice_memLp_ae hD (α ++ [j]) hnextle] with t hαL2 hnextL2
    exact ⟨(hαL2.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ,
      (hnextL2.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ⟩
  have hslice : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Set.univ →
      ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        ∫ x in Set.univ,
          (D α (x, t) * (fderiv ℝ ψ x) (basisVec j) +
            D (α ++ [j]) (x, t) * ψ x) = 0 := by
    intro ψ hψ hψc hψI
    have hψderiv : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ j) :=
      contDiff_spatialDeriv_smooth hψ j
    have hψderivC : Continuous (spatialDeriv ψ j) := hψderiv.continuous
    have hψderivCpt : HasCompactSupport (spatialDeriv ψ j) := by
      change HasCompactSupport (fun x => (fderiv ℝ ψ x) (basisVec j))
      exact hψc.fderiv_apply (𝕜 := ℝ) (basisVec j)
    let A₁ : ℝ → ℝ := fun t =>
      ∫ x : Vec3, D α (x, t) * spatialDeriv ψ j x
    let A₂ : ℝ → ℝ := fun t =>
      ∫ x : Vec3, D (α ++ [j]) (x, t) * ψ x
    have hbase₁Restr := (hD.memL2 α hαle).integrable_mul
      (lps_spatialTest_memLp_slab hψderivC hψderivCpt)
    have hbase₂Restr := (hD.memL2 (α ++ [j]) hnextle).integrable_mul
      (lps_spatialTest_memLp_slab hψ.continuous hψc)
    have hbase₁Prod : Integrable
        (fun p : Vec3 × ℝ => D α p * spatialDeriv ψ j p.1)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
      rw [← lps_measure_slab_eq_prod a b]
      exact hbase₁Restr
    have hbase₂Prod : Integrable
        (fun p : Vec3 × ℝ => D (α ++ [j]) p * ψ p.1)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
      rw [← lps_measure_slab_eq_prod a b]
      exact hbase₂Restr
    have hA₁ : Integrable A₁ (volume.restrict (Ioo a b)) := by
      simpa only [A₁] using hbase₁Prod.integral_prod_right
    have hA₂ : Integrable A₂ (volume.restrict (Ioo a b)) := by
      simpa only [A₂] using hbase₂Prod.integral_prod_right
    have hAloc : LocallyIntegrableOn (fun t => A₁ t + A₂ t) (Ioo a b) volume := by
      have hAintOn : IntegrableOn (fun t => A₁ t + A₂ t) (Ioo a b) volume :=
        hA₁.add hA₂
      exact hAintOn.locallyIntegrableOn
    have hweightedZero : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
        HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
        (∫ t in Ioo a b, θ t * (A₁ t + A₂ t)) = 0 := by
      intro θ hθ hθc hθI
      let φ : Vec3 × ℝ → ℝ := fun p => ψ p.1 * θ p.2
      have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
        CKN.Core.Endgame.contDiff_separatedProduct hψ hθ
      have hφc : HasCompactSupport φ := by
        refine HasCompactSupport.intro (hψc.isCompact.prod hθc.isCompact) fun p hp => ?_
        rcases not_and_or.mp hp with hspace | htime
        · simp [φ, image_eq_zero_of_notMem_tsupport hspace]
        · simp [φ, image_eq_zero_of_notMem_tsupport htime]
      have hφI : tsupport φ ⊆ (Set.univ : Set Vec3) ×ˢ Ioo a b := by
        exact (CKN.Core.Endgame.tsupport_separatedProduct_subset ψ θ).trans
          (prod_mono (subset_univ _) hθI)
      have hweak := hD.weak α j hα φ hφ hφc hφI
      have hpartial (p : Vec3 × ℝ) :
          spatialPartial φ j p = spatialDeriv ψ j p.1 * θ p.2 :=
        CKN.Core.Endgame.spatialPartial_separatedProduct θ hψ j p
      have hleftSep := (lps_integral_slab_separated
        (hD.memL2 α hαle) hψderivC hψderivCpt hθ.continuous hθc).2
      have hrightSep := (lps_integral_slab_separated
        (hD.memL2 (α ++ [j]) hnextle) hψ.continuous hψc hθ.continuous hθc).2
      have hleft :
          (∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
            D α p * spatialPartial φ j p) =
            ∫ t in Ioo a b, θ t * A₁ t := by
        calc
          _ = ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
              D α p * (spatialDeriv ψ j p.1 * θ p.2) := by
                apply integral_congr_ae
                filter_upwards [] with p
                rw [hpartial]
          _ = ∫ t in Ioo a b, θ t * A₁ t := by
                simpa only [A₁] using hleftSep
      have hright :
          (∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
            D (α ++ [j]) p * φ p) =
            ∫ t in Ioo a b, θ t * A₂ t := by
        simpa only [φ, A₂] using hrightSep
      obtain ⟨C, hC⟩ := lps_continuous_compact_support_bounded
        hθ.continuous hθc
      have hθmeas : AEStronglyMeasurable θ (volume.restrict (Ioo a b)) :=
        hθ.continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      have hA₁θ : Integrable (fun t => θ t * A₁ t) (volume.restrict (Ioo a b)) := by
        have h := hA₁.mul_bdd hθmeas (ae_of_all _ hC)
        exact h.congr (ae_of_all _ fun t => by ring)
      have hA₂θ : Integrable (fun t => θ t * A₂ t) (volume.restrict (Ioo a b)) := by
        have h := hA₂.mul_bdd hθmeas (ae_of_all _ hC)
        exact h.congr (ae_of_all _ fun t => by ring)
      have hweakSep :
          (∫ t in Ioo a b, θ t * A₁ t) =
            -(∫ t in Ioo a b, θ t * A₂ t) := by
        calc
          _ = ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
                D α p * spatialPartial φ j p := hleft.symm
          _ = -∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b,
                D (α ++ [j]) p * φ p := hweak
          _ = -(∫ t in Ioo a b, θ t * A₂ t) := by rw [hright]
      calc
        _ = ∫ t in Ioo a b, θ t * A₁ t + θ t * A₂ t := by
              apply integral_congr_ae
              exact ae_of_all _ fun t => by ring
        _ = (∫ t in Ioo a b, θ t * A₁ t) +
              ∫ t in Ioo a b, θ t * A₂ t := integral_add hA₁θ hA₂θ
        _ = 0 := by rw [hweakSep]; ring
    have hfullTest : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
        HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
        (∫ t, θ t • (A₁ t + A₂ t) ∂(volume : Measure ℝ)) = 0 := by
      intro θ hθ hθc hθI
      have hweighted := hweightedZero θ hθ hθc hθI
      have hcompl : ∀ t ∉ Ioo a b, θ t • (A₁ t + A₂ t) = 0 := by
        intro t ht
        have hθzero : θ t = 0 := by
          by_contra hne
          exact ht (hθI ((subset_tsupport (f := θ))
            (Function.mem_support.mpr hne)))
        simp [hθzero]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
      simpa only [smul_eq_mul] using hweighted
    have hzero := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hAloc hfullTest
    have hzeroI : ∀ᵐ t ∂(volume.restrict (Ioo a b)), A₁ t + A₂ t = 0 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact hzero
    filter_upwards [hzeroI, hbase₁Prod.prod_left_ae, hbase₂Prod.prod_left_ae]
      with t hAt hslice₁ hslice₂
    have hsum :
        (∫ x : Vec3, D α (x, t) * spatialDeriv ψ j x +
          D (α ++ [j]) (x, t) * ψ x) = A₁ t + A₂ t := by
      rw [integral_add hslice₁ hslice₂]
    have hsumzero := hsum ▸ hAt
    simpa only [Measure.restrict_univ, spatialDeriv] using hsumzero
  exact stability_ae_slice_weak_partial_of_forall_test isOpen_univ j hloc hslice

/-- An `L²(I; H^m)` space-time family restricts to a spatial Sobolev family
on almost every time slice. -/
theorem lps_sobolevFamily_spatialSlices_ae
    {a b : ℝ} {m : ℕ} {f : Vec3 × ℝ → ℝ}
    {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hD : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) f D) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      IsSobolevFamilyOn m (Set.univ : Set Vec3) (fun x => f (x, t))
        (fun α x => D α (x, t)) := by
  have hzeroProd : D [] =ᵐ[((volume : Measure Vec3).prod
      (volume.restrict (Ioo a b)))] f := by
    have hz := hD.zero
    rw [lps_measure_slab_eq_prod a b] at hz
    exact hz
  have hswap : MeasurePreserving Prod.swap
      ((volume.restrict (Ioo a b)).prod (volume : Measure Vec3))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    Measure.measurePreserving_swap
  have hzeroSwap := hswap.quasiMeasurePreserving.ae_eq_comp hzeroProd
  have hzeroSlice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (fun x : Vec3 => D [] (x, t)) =ᵐ[volume]
        (fun x => f (x, t)) :=
    Measure.ae_ae_of_ae_prod hzeroSwap
  have hmem := lps_sobolevFamily_allSlices_memLp_ae hD
  have hweak : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ α : List (Fin 3), ∀ j : Fin 3, α.length < m →
        HasWeakPartialDerivOn (Set.univ : Set Vec3) j
          (fun x => D α (x, t)) (fun x => D (α ++ [j]) (x, t)) := by
    rw [ae_all_iff]
    intro α
    rw [ae_all_iff]
    intro j
    by_cases hα : α.length < m
    · filter_upwards [lps_sobolevFamily_slice_weak_partial_ae hD α j hα]
        with t ht
      exact fun _ => ht
    · filter_upwards [] with t ht
      exact False.elim (hα ht)
  filter_upwards [hzeroSlice, hmem, hweak] with t hzero hm hw
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using hzero
  · intro α hα
    simpa only [Measure.restrict_univ] using hm α hα
  · intro α j hα
    exact hw α j hα

/-- The agreed all-order spatial provider yields slice Sobolev families with
the same uniform energy bound on every positive-time slab. -/
theorem lps_sobolevProvider_spatialSlices
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    (hspatial : ∀ m : ℕ, ∀ δ : ℝ, 0 < δ → δ < t₁ - t₀ →
      ∃ (D : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ) (B : ℝ),
        0 ≤ B ∧
        (∀ i : Fin 3,
          IsL2SobolevFamilyOn m (Set.univ : Set Vec3)
            (Ioo (t₀ + δ) t₁) (fun z => u z i) (D i)) ∧
        ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
          ∑ i : Fin 3, ∑ α ∈ sobolevWords m,
            ∫ x : Vec3, (D i α (x, t)) ^ 2 ≤ B)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδT : δ < t₁ - t₀) :
    ∃ (D : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ) (B : ℝ),
      0 ≤ B ∧
      (∀ i : Fin 3, ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
        IsSobolevFamilyOn m (Set.univ : Set Vec3)
          (fun x => u (x, t) i) (fun α x => D i α (x, t))) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (t₀ + δ) t₁)),
        ∑ i : Fin 3, ∑ α ∈ sobolevWords m,
          ∫ x : Vec3, (D i α (x, t)) ^ 2 ≤ B := by
  obtain ⟨D, B, hB, hD, hbound⟩ := hspatial m δ hδ hδT
  refine ⟨D, B, hB, ?_, hbound⟩
  intro i
  exact lps_sobolevFamily_spatialSlices_ae (hD i)

/-- A continuously differentiable spatial `L²` curve remains continuously
differentiable after Leray projection (`prop:lps-smoothing`). -/
theorem realLerayProjectionCLM_contDiff_comp
    {n : ℕ∞} {I : Set ℝ} {f : ℝ → RealVectorL2}
    (hf : ContDiffOn ℝ n f I) :
    ContDiffOn ℝ n (fun t => realLerayProjectionCLM (f t)) I := by
  exact realLerayProjectionCLM.contDiff.comp_contDiffOn hf

/-- Pointwise differentiation commutes with the spatial Leray projection on
a spatial `L²` curve (`prop:lps-smoothing`). -/
theorem realLerayProjectionCLM_hasDerivAt
    {f f' : ℝ → RealVectorL2} {t : ℝ}
    (hf : HasDerivAt f (f' t) t) :
    HasDerivAt (fun s => realLerayProjectionCLM (f s))
      (realLerayProjectionCLM (f' t)) t := by
  have hA : HasFDerivAt (fun v : RealVectorL2 => realLerayProjectionCLM v)
      realLerayProjectionCLM (f t) := realLerayProjectionCLM.hasFDerivAt
  have hcomp := hA.comp t hf.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hcomp.hasDerivAt

end ESS.LPS

end
