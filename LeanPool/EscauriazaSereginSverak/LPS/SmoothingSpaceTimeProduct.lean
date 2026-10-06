/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingProductFamilyTwo
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularitySpatial
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGlue
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainLeibniz

/-!
# Products of space-time Sobolev families

A field in `L²(I; H^m(ℝ³))` whose `H^m` slices are uniformly bounded in time
multiplies `L²(I; H^m(ℝ³))` into itself, with the space-time Leibniz family as
the family of weak derivatives of the product. On almost every time slice the
whole-space product estimate applies to the two slice families; the slice
estimates integrate in time by Tonelli, and the slice Leibniz rules integrate
to the space-time weak derivative identities by Fubini. This is the product
estimate for the nonlinear term in `prop:lps-smoothing`.

The reduction is stated once for any slice product estimate from `H^{m₁}`
times `H^{m₂}` to `H^{m₂}` with `m₂ ≤ m₁`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- On a time slice, the space-time Leibniz family is the spatial Leibniz
family of the slices of the two factors. -/
theorem stLeibniz_slice (α : List (Fin 3)) (A B : List (Fin 3) → Vec3 × ℝ → ℝ)
    (x : Vec3) (t : ℝ) :
    stLeibniz α A B (x, t) =
      sobolevLeibnizFamily α (fun β y => A β (y, t)) (fun β y => B β (y, t)) x := by
  induction α generalizing A B with
  | nil => rfl
  | cons j α ih =>
      simp only [stLeibniz, sobolevLeibnizFamily, ih]

/-- Tonelli for the square of a field in `L²` of a slab: the time profile of
the slice integrals is integrable and integrates to the slab integral. -/
private theorem lps_stp_integral_sq_slab {a b : ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : MemLp F 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b))) :
    Integrable (fun t => ∫ x : Vec3, F (x, t) ^ 2) (volume.restrict (Ioo a b)) ∧
      ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, F p ^ 2 =
        ∫ t in Ioo a b, ∫ x : Vec3, F (x, t) ^ 2 := by
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsq : Integrable (fun p => F p ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← hslab]
    exact hF.integrable_sq
  refine ⟨hsq.integral_prod_right, ?_⟩
  rw [hslab]
  exact integral_prod_symm _ hsq

/-- A measurable field on a slab whose slices are square integrable, with
squared slice norms dominated by an integrable time profile, is square
integrable on the slab. -/
private theorem lps_stp_memLp_of_slice_bound {a b : ℝ} {F : Vec3 × ℝ → ℝ} {G : ℝ → ℝ}
    (hFm : AEStronglyMeasurable F (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (hG : Integrable G (volume.restrict (Ioo a b)))
    (hslice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      MemLp (fun x : Vec3 => F (x, t)) 2 volume ∧ ∫ x : Vec3, F (x, t) ^ 2 ≤ G t) :
    MemLp F 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hslab] at hFm ⊢
  rw [memLp_two_iff_integrable_sq hFm]
  have hFm2 : AEStronglyMeasurable (fun p => F p ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := hFm.pow 2
  rw [integrable_prod_iff' hFm2]
  refine ⟨?_, ?_⟩
  · filter_upwards [hslice] with t ht
    exact ht.1.integrable_sq
  · refine hG.mono' hFm2.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [hslice] with t ht
    have hnorm : (fun x : Vec3 => ‖F (x, t) ^ 2‖) = fun x => F (x, t) ^ 2 :=
      funext fun x => Real.norm_of_nonneg (sq_nonneg _)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _), hnorm]
    exact ht.2

/-- Lifting a whole-space product estimate from slices to space time
(`prop:lps-smoothing`): if the product of an `H^{m₁}` family and an `H^{m₂}`
family is an `H^{m₂}` family with the Leibniz derivatives and
`‖fg‖²_{H^{m₂}} ≤ C ‖f‖²_{H^{m₁}} ‖g‖²_{H^{m₂}}`, then for `f` in
`L²(I; H^{m₁})` with `H^{m₁}` slices bounded by `K` and `g` in
`L²(I; H^{m₂})`, the product is in `L²(I; H^{m₂})` with the space-time Leibniz
family and `‖fg‖²_{L²H^{m₂}} ≤ C K ‖g‖²_{L²H^{m₂}}`. -/
theorem lps_spaceTime_mul_family_of_slice {m₁ m₂ : ℕ} (hm : m₂ ≤ m₁) {C : ℝ} (hC : 0 ≤ C)
    (hslice : ∀ (f g : Vec3 → ℝ) (D E : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn m₁ univ f D → IsSobolevFamilyOn m₂ univ g E →
      IsSobolevFamilyOn m₂ univ (fun x => f x * g x) (fun α => sobolevLeibnizFamily α D E) ∧
      sobolevNormSqOn m₂ univ (fun α => sobolevLeibnizFamily α D E) ≤
        C * sobolevNormSqOn m₁ univ D * sobolevNormSqOn m₂ univ E)
    {a b : ℝ} {f g : Vec3 × ℝ → ℝ} {Df Dg : List (Fin 3) → Vec3 × ℝ → ℝ} {K : ℝ}
    (hf : IsL2SobolevFamilyOn m₁ (Set.univ : Set Vec3) (Ioo a b) f Df)
    (hg : IsL2SobolevFamilyOn m₂ (Set.univ : Set Vec3) (Ioo a b) g Dg)
    (hK : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∑ α ∈ sobolevWords m₁, ∫ x : Vec3, (Df α (x, t)) ^ 2 ≤ K) :
    IsL2SobolevFamilyOn m₂ (Set.univ : Set Vec3) (Ioo a b) (fun z => f z * g z)
        (fun α => stLeibniz α Df Dg) ∧
      l2SobolevNormSqOn m₂ (Set.univ : Set Vec3) (Ioo a b) (fun α => stLeibniz α Df Dg) ≤
        C * K * l2SobolevNormSqOn m₂ (Set.univ : Set Vec3) (Ioo a b) Dg := by
  -- The slice product estimate on almost every time slice.
  have hsl : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      IsSobolevFamilyOn m₂ univ (fun x => f (x, t) * g (x, t))
          (fun α x => stLeibniz α Df Dg (x, t)) ∧
        ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, stLeibniz α Df Dg (x, t) ^ 2 ≤
          C * K * ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, Dg α (x, t) ^ 2 := by
    filter_upwards [LPS.lps_sobolevFamily_spatialSlices_ae hf,
      LPS.lps_sobolevFamily_spatialSlices_ae hg, hK] with t hft hgt hKt
    obtain ⟨hfam, hnorm⟩ := hslice _ _ _ _ hft hgt
    simp only [stLeibniz_slice]
    refine ⟨hfam, ?_⟩
    have hE0 : 0 ≤ ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, Dg α (x, t) ^ 2 :=
      Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
    simp only [sobolevNormSqOn, Measure.restrict_univ] at hnorm
    calc
      _ ≤ C * (∑ α ∈ sobolevWords m₁, ∫ x : Vec3, Df α (x, t) ^ 2) *
            ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, Dg α (x, t) ^ 2 := hnorm
      _ ≤ C * K * ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, Dg α (x, t) ^ 2 := by
          gcongr
  -- Square integrability of each Leibniz slot on the slab.
  have hDg := fun (α : List (Fin 3)) (hα : α ∈ sobolevWords m₂) =>
    lps_stp_integral_sq_slab (hg.memL2 α (mem_sobolevWords.1 hα))
  have hGint : Integrable
      (fun t => C * K * ∑ α ∈ sobolevWords m₂, ∫ x : Vec3, Dg α (x, t) ^ 2)
      (volume.restrict (Ioo a b)) :=
    (integrable_finsetSum _ fun α hα => (hDg α hα).1).const_mul (C * K)
  have hLmem : ∀ α : List (Fin 3), α.length ≤ m₂ →
      MemLp (stLeibniz α Df Dg) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
    intro α hα
    refine lps_stp_memLp_of_slice_bound
      (stLeibniz_aestronglyMeasurable α Df Dg
        (fun γ hγ => (hf.memL2 γ (by omega)).aestronglyMeasurable)
        (fun γ hγ => (hg.memL2 γ (by omega)).aestronglyMeasurable)) hGint ?_
    filter_upwards [hsl] with t ht
    refine ⟨?_, ?_⟩
    · simpa only [Measure.restrict_univ] using ht.1.memL2 α hα
    · refine le_trans ?_ ht.2
      exact Finset.single_le_sum
        (f := fun β : List (Fin 3) => ∫ x : Vec3, stLeibniz β Df Dg (x, t) ^ 2)
        (fun β _ => integral_nonneg fun _ => sq_nonneg _) (mem_sobolevWords.2 hα)
  have hzero : stLeibniz [] Df Dg =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)]
      fun z => f z * g z := by
    filter_upwards [hf.zero, hg.zero] with p h1 h2
    change Df [] p * Dg [] p = f p * g p
    rw [h1, h2]
  have hweak : ∀ (α : List (Fin 3)) (j : Fin 3), α.length < m₂ →
      ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set Vec3) ×ˢ Ioo a b →
        ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, stLeibniz α Df Dg p * spatialPartial φ j p =
          -∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, stLeibniz (α ++ [j]) Df Dg p * φ p := by
    intro α j hα φ hφ hφc hφI
    have hs : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => stLeibniz α Df Dg (x, t))
          (fun x => stLeibniz (α ++ [j]) Df Dg (x, t)) := by
      filter_upwards [hsl] with t ht
      exact ht.1.weak α j hα
    have hnext : (α ++ [j]).length ≤ m₂ := by
      simp only [List.length_append, List.length_singleton]
      omega
    exact lps_slab_spatial_weak_of_slices (hLmem α hα.le) (hLmem (α ++ [j]) hnext) j hs
      ⟨hφ, hφc, hφI⟩
  refine ⟨⟨hLmem, hzero, hweak⟩, ?_⟩
  -- Integrate the slice estimate in time.
  have hL := fun (α : List (Fin 3)) (hα : α ∈ sobolevWords m₂) =>
    lps_stp_integral_sq_slab (hLmem α (mem_sobolevWords.1 hα))
  show ∑ α ∈ sobolevWords m₂, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, stLeibniz α Df Dg p ^ 2 ≤
    C * K * ∑ α ∈ sobolevWords m₂, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, Dg α p ^ 2
  rw [Finset.sum_congr rfl fun α hα => (hL α hα).2,
    Finset.sum_congr rfl fun α hα => (hDg α hα).2,
    ← integral_finsetSum _ fun α hα => (hL α hα).1,
    ← integral_finsetSum _ fun α hα => (hDg α hα).1, ← integral_const_mul]
  exact integral_mono_ae (integrable_finsetSum _ fun α hα => (hL α hα).1) hGint
    (by filter_upwards [hsl] with t ht; exact ht.2)

/-- The space-time algebra estimate (`prop:lps-smoothing`): for `m ≥ 2`, a
field `f` in `L²(I; H^m(ℝ³))` whose `H^m` slices have squared norm at most `K`
multiplies `g ∈ L²(I; H^m(ℝ³))` into `L²(I; H^m(ℝ³))`; the product has the
space-time Leibniz family and `‖fg‖²_{L²H^m} ≤ C K ‖g‖²_{L²H^m}`. -/
theorem lps_spaceTime_mul_family {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} {f g : Vec3 × ℝ → ℝ}
      {Df Dg : List (Fin 3) → Vec3 × ℝ → ℝ} {K : ℝ},
      IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) f Df →
      IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) g Dg →
      (∀ᵐ t ∂(volume.restrict (Ioo a b)),
        ∑ α ∈ sobolevWords m, ∫ x : Vec3, (Df α (x, t)) ^ 2 ≤ K) →
      IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) (fun z => f z * g z)
          (fun α => stLeibniz α Df Dg) ∧
        l2SobolevNormSqOn m (Set.univ : Set Vec3) (Ioo a b) (fun α => stLeibniz α Df Dg) ≤
          C * K * l2SobolevNormSqOn m (Set.univ : Set Vec3) (Ioo a b) Dg := by
  obtain ⟨C, hC, hslice⟩ := lps_sobolevFamily_mul_of_two_le hm
  exact ⟨C, hC, fun hf hg hK => lps_spaceTime_mul_family_of_slice le_rfl hC hslice hf hg hK⟩

end ESS
