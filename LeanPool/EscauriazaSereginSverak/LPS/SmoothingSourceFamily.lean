/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSourceProjected
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGlue
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingTimeRegularitySpatial
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMeasurableCurve

/-!
# Space-time Sobolev families of the Leray projection

`prop:lps-smoothing`: if a vector field `B` lies in `L²(I; H^M(ℝ³))`, with space-time
derivative families `DB`, then the time slices of the Leray projection `-P B(t)` form a field
in `L²(I; H^M(ℝ³))`: for each word `α` the curve `t ↦ -P(DB α)(t)` of `L²` classes is
measurable, and a jointly measurable representative gives the derivative family. The
projection commutes with weak derivatives and does not increase `L²` norms, so the new family
satisfies the weak derivative relations and has norm at most that of `DB`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A square-integrable function on a slab has a strongly measurable curve of `L²(ℝ³)` classes
agreeing with almost every time slice (`prop:lps-smoothing`). -/
theorem lps_exists_slice_curve {a b : ℝ} (F : Vec3 × ℝ → ℝ) :
    ∃ γ : ℝ → Lp ℝ 2 (volume : Measure Vec3), StronglyMeasurable γ ∧
      (MemLp F 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) →
        ∀ᵐ t ∂(volume.restrict (Ioo a b)), (γ t : Vec3 → ℝ) =ᵐ[volume] fun x => F (x, t)) := by
  classical
  by_cases hF : MemLp F 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b))
  swap
  · exact ⟨fun _ => 0, stronglyMeasurable_const, fun h => absurd h hF⟩
  have hFm : AEStronglyMeasurable F
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
    rw [← lps_measure_slab_eq_prod]
    exact hF.aestronglyMeasurable
  set Fm := hFm.mk F with hFm_def
  have hFms : StronglyMeasurable Fm := hFm.stronglyMeasurable_mk
  let S : Set ℝ := {t | ∫⁻ x, ‖Fm (x, t)‖ₑ ^ (2 : ℝ) < ⊤}
  have hS : MeasurableSet S :=
    measurableSet_lt (Measurable.lintegral_prod_left' (hFms.measurable.enorm.pow_const _))
      measurable_const
  let Γ : Vec3 × ℝ → ℝ := (Prod.snd ⁻¹' S).indicator Fm
  have hΓ : StronglyMeasurable Γ := hFms.indicator (measurable_snd hS)
  have hΓin : ∀ t ∈ S, (fun x => Γ (x, t)) = fun x => Fm (x, t) := by
    intro t ht
    funext x
    exact Set.indicator_of_mem (show (x, t) ∈ Prod.snd ⁻¹' S from ht) _
  have hΓout : ∀ t ∉ S, (fun x => Γ (x, t)) = fun _ => 0 := by
    intro t ht
    funext x
    exact Set.indicator_of_notMem (show (x, t) ∉ Prod.snd ⁻¹' S from ht) _
  have hslice : ∀ t, MemLp (fun x => Γ (x, t)) 2 volume := by
    intro t
    by_cases ht : t ∈ S
    · rw [hΓin t ht]
      have hm : AEStronglyMeasurable (fun x => Fm (x, t)) volume :=
        (hFms.comp_measurable measurable_prodMk_right).aestronglyMeasurable
      have ht2 : ∫⁻ x, ‖Fm (x, t)‖ₑ ^ (2 : ℝ) < ⊤ := ht
      exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
        hm).2 (by simpa using ht2)
    · rw [hΓout t ht]
      exact MemLp.zero
  refine ⟨fun t => (hslice t).toLp _,
    CKN.Leray.stronglyMeasurable_of_jointRep Γ hΓ _ (fun t => (hslice t).coeFn_toLp.symm),
    fun _ => ?_⟩
  have hae : F =ᵐ[(volume : Measure Vec3).prod (volume.restrict (Ioo a b))] Fm :=
    hFm.ae_eq_mk
  have hswap : MeasurePreserving Prod.swap
      ((volume.restrict (Ioo a b)).prod (volume : Measure Vec3))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    Measure.measurePreserving_swap
  have hae' := Measure.ae_ae_of_ae_prod (hswap.quasiMeasurePreserving.ae_eq_comp hae)
  filter_upwards [hae', lps_slice_memLp_two_ae_slab (F := F) hF] with t ht hFt
  have ht' : (fun x => F (x, t)) =ᵐ[volume] fun x => Fm (x, t) := ht
  have hmem : t ∈ S := by
    have hFmt : MemLp (fun x => Fm (x, t)) 2 volume := hFt.ae_eq ht'
    have h := hFmt.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      hFmt.aestronglyMeasurable] at h
    change ∫⁻ x, ‖Fm (x, t)‖ₑ ^ (2 : ℝ) < ⊤
    simpa using h
  filter_upwards [(hslice t).coeFn_toLp, ht'] with x h1 h2
  rw [h1, show Γ (x, t) = Fm (x, t) from congrFun (hΓin t hmem) x, h2]

/-- A curve of fields in `L²(ℝ³; ℝ³)` whose three components are strongly measurable curves is
strongly measurable (`prop:lps-smoothing`). -/
theorem lps_stronglyMeasurable_field_curve {γ : Fin 3 → ℝ → Lp ℝ 2 (volume : Measure Vec3)}
    (hγ : ∀ k, StronglyMeasurable (γ k)) :
    StronglyMeasurable (fun t => (WithLp.toLp 2 (fun k => γ k t) : LpsL2Field)) := by
  have h2top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  borelize (↥(Lp ℝ 2 (volume : Measure Vec3)))
  have hm : Measurable (fun t => (fun k => γ k t)) :=
    measurable_pi_iff.mpr fun k => (hγ k).measurable
  exact (PiLp.continuous_toLp 2 _).comp_stronglyMeasurable hm.stronglyMeasurable

/-- Two functions on a slab whose time slices agree almost everywhere for almost every time
agree almost everywhere on the slab. -/
private theorem lps_ae_eq_slab_of_slices {a b : ℝ} {F G : Vec3 × ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (hG : AEStronglyMeasurable G (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), (fun x => F (x, t)) =ᵐ[volume] fun x => G (x, t)) :
    F =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)] G := by
  rw [lps_measure_slab_eq_prod] at hF hG ⊢
  have hm : AEMeasurable (fun z => ‖F z - G z‖ₑ)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := (hF.sub hG).enorm
  have hint : ∫⁻ z, ‖F z - G z‖ₑ ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b)))
      = 0 := by
    rw [lintegral_prod_symm _ hm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h] with t ht
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ht] with x hx
    simp [hx]
  filter_upwards [(lintegral_eq_zero_iff' hm).mp hint] with z hz
  simpa [sub_eq_zero] using hz

/-- `prop:lps-smoothing`: the Leray projection of a field in `L²(I; H^M(ℝ³))`. If the three
components `f k` have space-time derivative families `DB k` through order `M` on
`ℝ³ × (a, b)`, and almost every time slice of `g` is the negative Leray projection of the
slice of `f`, then `g` has space-time derivative families through order `M` whose total
squared norm is at most that of `DB`. -/
theorem lps_leray_l2SobolevFamily {a b : ℝ} {M : ℕ} {f g : Fin 3 → Vec3 × ℝ → ℝ}
    {DB : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ}
    (hB : ∀ k, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo a b) (f k) (DB k))
    (hgm : ∀ i, AEStronglyMeasurable (g i)
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (hg : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ i
      (hf : ∀ k, MemLp (fun y => f k (y, t)) 2 volume),
      (fun x => g i (x, t)) =ᵐ[volume] fun x => -lpsLerayApply (fun k y => f k (y, t)) hf i x) :
    ∃ DG : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ,
      (∀ i, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo a b) (g i) (DG i)) ∧
      ∑ i, l2SobolevNormSqOn M (Set.univ : Set Vec3) (Ioo a b) (DG i) ≤
        ∑ i, l2SobolevNormSqOn M (Set.univ : Set Vec3) (Ioo a b) (DB i) := by
  classical
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo a b))
    with hν
  have hslab : (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) : Measure (Vec3 × ℝ)) = ν :=
    lps_measure_slab_eq_prod a b
  choose γ hγm hγ using fun (k : Fin 3) (α : List (Fin 3)) =>
    lps_exists_slice_curve (a := a) (b := b) (DB k α)
  let V : List (Fin 3) → ℝ → LpsL2Field := fun α t => WithLp.toLp 2 (fun k => γ k α t)
  have hVm : ∀ α, StronglyMeasurable (V α) := fun α =>
    lps_stronglyMeasurable_field_curve fun k => hγm k α
  have hPm : ∀ i α, StronglyMeasurable (fun t => lpsLerayP (V α t) i) := fun i α =>
    ((PiLp.continuous_apply 2 _ i).comp lpsLerayP.continuous).comp_stronglyMeasurable (hVm α)
  choose Γ hΓm hΓ using fun (i : Fin 3) (α : List (Fin 3)) =>
    CKN.Leray.exists_jointRep_of_stronglyMeasurable (μ := (volume : Measure Vec3))
      (fun t => lpsLerayP (V α t) i) (hPm i α)
  let DG : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ := fun i α z => -Γ i α z
  -- slice square integrals of the new family
  have hsq : ∀ i α t, ∫ x, DG i α (x, t) ^ 2 = ‖lpsLerayP (V α t) i‖ ^ 2 := by
    intro i α t
    rw [lpsLp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hΓ i α t] with x hx
    simp only [DG, neg_sq, hx]
  have hPle : ∀ α t, ∑ i, ‖lpsLerayP (V α t) i‖ ^ 2 ≤ ∑ k, ‖V α t k‖ ^ 2 := by
    intro α t
    have h := pow_le_pow_left₀ (norm_nonneg _) (lpsLerayP_norm_le (V α t)) 2
    rwa [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2] at h
  -- the curves agree with the slices of the given family
  have hVae : ∀ α : List (Fin 3), α.length ≤ M → ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ k,
      (V α t k : Vec3 → ℝ) =ᵐ[volume] fun x => DB k α (x, t) := by
    intro α hα
    rw [ae_all_iff]
    intro k
    exact hγ k α ((hB k).memL2 α hα)
  have hVnorm : ∀ α : List (Fin 3), α.length ≤ M → ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ k,
      ‖V α t k‖ ^ 2 = ∫ x, DB k α (x, t) ^ 2 := by
    intro α hα
    filter_upwards [hVae α hα] with t ht k
    rw [lpsLp_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [ht k] with x hx
    rw [hx]
  have hDBint : ∀ k (α : List (Fin 3)), α.length ≤ M →
      Integrable (fun t => ∫ x, DB k α (x, t) ^ 2) (volume.restrict (Ioo a b)) ∧
        ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DB k α p ^ 2 =
          ∫ t in Ioo a b, ∫ x, DB k α (x, t) ^ 2 := by
    intro k α hα
    have hsqi : Integrable (fun p => DB k α p ^ 2) ν := by
      rw [← hslab]
      exact ((hB k).memL2 α hα).integrable_sq
    refine ⟨hsqi.integral_prod_right, ?_⟩
    rw [hslab]
    exact integral_prod_symm _ hsqi
  have hPint : ∀ i (α : List (Fin 3)), α.length ≤ M →
      Integrable (fun t => ‖lpsLerayP (V α t) i‖ ^ 2) (volume.restrict (Ioo a b)) := by
    intro i α hα
    refine (integrable_finsetSum Finset.univ fun k _ => (hDBint k α hα).1).mono'
      ((hPm i α).norm.pow 2).aestronglyMeasurable ?_
    filter_upwards [hVnorm α hα] with t ht
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖lpsLerayP (V α t) i‖ ^ 2 ≤ ∑ i', ‖lpsLerayP (V α t) i'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ‖lpsLerayP (V α t) i'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ k, ‖V α t k‖ ^ 2 := hPle α t
      _ = ∑ k, ∫ x, DB k α (x, t) ^ 2 := Finset.sum_congr rfl fun k _ => ht k
  have hDGmeas : ∀ i α, AEStronglyMeasurable (DG i α) ν := fun i α =>
    (hΓm i α).neg.aestronglyMeasurable
  have hDGslice : ∀ i α t, MemLp (fun x => DG i α (x, t)) 2 volume := by
    intro i α t
    refine ((Lp.memLp (lpsLerayP (V α t) i)).neg).ae_eq ?_
    filter_upwards [hΓ i α t] with x hx
    simp only [DG, hx, Pi.neg_apply]
  have hDGsq : ∀ i (α : List (Fin 3)), α.length ≤ M → Integrable (fun p => DG i α p ^ 2) ν := by
    intro i α hα
    have hm2 : AEStronglyMeasurable (fun p => DG i α p ^ 2) ν := (hDGmeas i α).pow 2
    rw [integrable_prod_iff' hm2]
    refine ⟨Eventually.of_forall fun t => (hDGslice i α t).integrable_sq, ?_⟩
    refine (hPint i α hα).congr (Eventually.of_forall fun t => ?_)
    change ‖lpsLerayP (V α t) i‖ ^ 2 = ∫ x, ‖DG i α (x, t) ^ 2‖
    rw [← hsq i α t]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (Real.norm_of_nonneg (sq_nonneg _)).symm
  have hDGmem : ∀ i (α : List (Fin 3)), α.length ≤ M →
      MemLp (DG i α) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
    intro i α hα
    rw [hslab, memLp_two_iff_integrable_sq (hDGmeas i α)]
    exact hDGsq i α hα
  have hDGint : ∀ i (α : List (Fin 3)), α.length ≤ M →
      ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DG i α p ^ 2 =
        ∫ t in Ioo a b, ‖lpsLerayP (V α t) i‖ ^ 2 := by
    intro i α hα
    rw [hslab, integral_prod_symm _ (hDGsq i α hα)]
    exact integral_congr_ae (Eventually.of_forall fun t => hsq i α t)
  -- slices of the given families
  have hsl : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ k,
      IsSobolevFamilyOn M (Set.univ : Set Vec3) (fun x => f k (x, t))
        (fun β x => DB k β (x, t)) :=
    ae_all_iff.mpr fun k => LPS.lps_sobolevFamily_spatialSlices_ae (hB k)
  -- the zeroth slot
  have hzero : ∀ i, DG i [] =ᵐ[volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)] g i := by
    intro i
    refine lps_ae_eq_slab_of_slices (hDGmem i [] (Nat.zero_le _)).aestronglyMeasurable (hgm i) ?_
    filter_upwards [hg, hsl, hVae [] (Nat.zero_le _)] with t hgt hst hV0
    have hfk : ∀ k, (fun x => f k (x, t)) =ᵐ[volume] (V [] t k : Vec3 → ℝ) := by
      intro k
      have hz := (hst k).zero
      rw [Measure.restrict_univ] at hz
      exact hz.symm.trans (hV0 k).symm
    have hfmem : ∀ k, MemLp (fun x => f k (x, t)) 2 volume := fun k =>
      (Lp.memLp (V [] t k)).ae_eq (hfk k).symm
    have hfield : lpsFieldOf (fun k y => f k (y, t)) hfmem = V [] t := by
      refine PiLp.ext fun k => ?_
      exact Lp.ext ((hfmem k).coeFn_toLp.trans (hfk k))
    have hPf : lpsLerayApply (fun k y => f k (y, t)) hfmem i = ⇑(lpsLerayP (V [] t) i) := by
      rw [lpsLerayApply_eq hfmem, hfield]
    filter_upwards [hgt i hfmem, hΓ i [] t] with x h1 h2
    simp only [DG, h1, h2, hPf]
  -- the weak derivative relations
  have hweak : ∀ i (α : List (Fin 3)) (j : Fin 3), α.length < M →
      ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set Vec3) ×ˢ Ioo a b →
        ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DG i α p * spatialPartial φ j p =
          -∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DG i (α ++ [j]) p * φ p := by
    intro i α j hα φ hφ hφc hφI
    have hnext : (α ++ [j]).length ≤ M := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hs : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
        HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => DG i α (x, t))
          (fun x => DG i (α ++ [j]) (x, t)) := by
      filter_upwards [hsl, hVae α hα.le, hVae (α ++ [j]) hnext] with t hst h1 h2
      have hk : ∀ k, HasWeakPartialDerivOn (Set.univ : Set Vec3) j (V α t k : Vec3 → ℝ)
          (V (α ++ [j]) t k : Vec3 → ℝ) := fun k =>
        lps_hasWeakPartialDerivOn_congr ((hst k).weak α j hα)
          (ae_restrict_of_ae (h1 k).symm) (ae_restrict_of_ae (h2 k).symm)
      have hP := lpsLerayP_weakPartial j hk i
      have hPneg : HasWeakPartialDerivOn (Set.univ : Set Vec3) j
          (fun x => -(lpsLerayP (V α t) i : Vec3 → ℝ) x)
          (fun x => -(lpsLerayP (V (α ++ [j]) t) i : Vec3 → ℝ) x) := by
        intro ψ hψ hψc hψs
        have hb := hP ψ hψ hψc hψs
        simp only [neg_mul]
        rw [integral_neg, integral_neg, hb, neg_neg]
      refine lps_hasWeakPartialDerivOn_congr hPneg ?_ ?_
      · filter_upwards [ae_restrict_of_ae (hΓ i α t)] with x hx
        simp only [DG, hx]
      · filter_upwards [ae_restrict_of_ae (hΓ i (α ++ [j]) t)] with x hx
        simp only [DG, hx]
    exact lps_slab_spatial_weak_of_slices (hDGmem i α hα.le) (hDGmem i (α ++ [j]) hnext) j hs
      ⟨hφ, hφc, hφI⟩
  refine ⟨DG, fun i => ⟨fun α hα => hDGmem i α hα, hzero i, hweak i⟩, ?_⟩
  simp only [l2SobolevNormSqOn]
  have hL : ∑ i, ∑ α ∈ sobolevWords M, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DG i α p ^ 2 =
      ∑ α ∈ sobolevWords M, ∑ i, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DG i α p ^ 2 :=
    Finset.sum_comm
  have hR : ∑ i, ∑ α ∈ sobolevWords M, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DB i α p ^ 2 =
      ∑ α ∈ sobolevWords M, ∑ i, ∫ p in (Set.univ : Set Vec3) ×ˢ Ioo a b, DB i α p ^ 2 :=
    Finset.sum_comm
  rw [hL, hR]
  refine Finset.sum_le_sum fun α hα => ?_
  have hαM := mem_sobolevWords.1 hα
  rw [Finset.sum_congr rfl fun i _ => hDGint i α hαM,
    Finset.sum_congr rfl fun k _ => (hDBint k α hαM).2,
    ← integral_finsetSum _ fun i _ => hPint i α hαM,
    ← integral_finsetSum _ fun k _ => (hDBint k α hαM).1]
  refine integral_mono_ae (integrable_finsetSum _ fun i _ => hPint i α hαM)
    (integrable_finsetSum _ fun k _ => (hDBint k α hαM).1) ?_
  filter_upwards [hVnorm α hαM] with t ht
  calc ∑ i, ‖lpsLerayP (V α t) i‖ ^ 2 ≤ ∑ k, ‖V α t k‖ ^ 2 := hPle α t
    _ = ∑ k, ∫ x, DB k α (x, t) ^ 2 := Finset.sum_congr rfl fun k _ => ht k

/-- `prop:lps-smoothing`: the source of a strong solution in `L²(I; H^M)`. On a time interval
`(a, b) ⊆ (t₀, T)`, if the convection field `(u·∇)u`, with components `Σⱼ uⱼ ∂ⱼuᵢ`, has
space-time derivative families `DB` through order `M`, then so does the source
`∂ₜu - Δu = -P((u·∇)u)`, with total squared `L²(I; H^M)` norm at most that of `DB`. -/
theorem lps_source_family {t₀ T : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hsol : IsLpsStrongSolution t₀ T u Du p)
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    {a b : ℝ} (ha : t₀ ≤ a) (hb : b ≤ T) {M : ℕ}
    (DB : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ)
    (hB : ∀ i, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo a b)
      (fun z => ∑ j, u z j * Du z i j) (DB i)) :
    ∃ DG : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ,
      (∀ i, IsL2SobolevFamilyOn M (Set.univ : Set Vec3) (Ioo a b)
        (fun z => Dtu z i - ∑ j, D2u z i j j) (DG i)) ∧
      ∑ i, l2SobolevNormSqOn M (Set.univ : Set Vec3) (Ioo a b) (DG i) ≤
        ∑ i, l2SobolevNormSqOn M (Set.univ : Set Vec3) (Ioo a b) (DB i) := by
  have hsub : Ioo a b ⊆ Ioo t₀ T := Ioo_subset_Ioo ha hb
  have hmono : (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) : Measure (Vec3 × ℝ)) ≤
      volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T) :=
    Measure.restrict_mono (prod_mono subset_rfl hsub) le_rfl
  refine lps_leray_l2SobolevFamily hB (fun i => ?_) ?_
  · have hG : MemLp (fun z : Vec3 × ℝ => Dtu z i - ∑ j, D2u z i j j) 2
        (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo t₀ T)) :=
      (hDtu.eval i).sub (memLp_finsetSum Finset.univ fun j _ => ((hD2u.eval i).eval j).eval j)
    exact hG.aestronglyMeasurable.mono_measure hmono
  · exact ae_restrict_of_ae_restrict_of_subset hsub
      (lps_strong_slice_projected_equation hsol hderiv hu hDu hD2u hDtu)

end ESS
