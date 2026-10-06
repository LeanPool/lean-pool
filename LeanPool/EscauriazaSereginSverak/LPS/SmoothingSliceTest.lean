/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingJointDeriv

/-!
# Slice identities from space-time identities

`prop:lps-smoothing`: a space-time identity tested against products `χ(t) ψ(x)`
holds, for almost every time, against every spatial test `ψ` of a linear family.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The slab measure factors as space times the time interval. -/
theorem lps_measure_slab_eq_prod (a b : ℝ) :
    (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- A square-integrable function of space alone is square-integrable on a slab. -/
theorem lps_memLp_slab_of_space {a b : ℝ} {g : Vec3 → ℝ} (hg : MemLp g 2 volume) :
    MemLp (fun p : Vec3 × ℝ => g p.1) 2
      (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)) := by
  rw [lps_measure_slab_eq_prod]
  have hmeas : AEStronglyMeasurable (fun p : Vec3 × ℝ => g p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    hg.aestronglyMeasurable.comp_fst
  rw [memLp_two_iff_integrable_sq hmeas]
  have hprod := hg.integrable_sq.mul_prod (integrable_const (1 : ℝ) :
    Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioo a b)))
  simpa using hprod

/-- The slice pairing of an `L²` space-time field with a spatial `L²` function is
integrable in time. -/
theorem lps_integrable_slice_pairing {a b : ℝ} {A : Vec3 × ℝ → ℝ} {f : Vec3 → ℝ}
    (hA : MemLp A 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (hf : MemLp f 2 volume) :
    Integrable (fun p : Vec3 × ℝ => A p * f p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  rw [← lps_measure_slab_eq_prod]
  exact hA.integrable_mul (lps_memLp_slab_of_space hf)

/-- Slice identity for one fixed test: a space-time identity against `χ(t)ψ(x)` for every
smooth `χ` compactly supported in `(a,b)` gives the identity for almost every time. -/
theorem lps_ae_slice_test_single {a b : ℝ} {N : ℕ}
    (A : Fin N → Vec3 × ℝ → ℝ)
    (hA : ∀ k, MemLp (A k) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (f : Fin N → Vec3 → ℝ) (hf : ∀ k, MemLp (f k) 2 volume)
    (hzero : ∀ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo a b →
      ∫ t in Ioo a b, χ t * ∫ x, ∑ k, A k (x, t) * f k x = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∫ x, ∑ k, A k (x, t) * f k x = 0 := by
  have hint : ∀ k, Integrable (fun p : Vec3 × ℝ => A k p * f k p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    fun k => lps_integrable_slice_pairing (hA k) (hf k)
  have hsum : Integrable (fun p : Vec3 × ℝ => ∑ k, A k p * f k p.1)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    integrable_finsetSum _ fun k _ => hint k
  have hg : Integrable (fun t => ∫ x, ∑ k, A k (x, t) * f k x) (volume.restrict (Ioo a b)) :=
    hsum.integral_prod_right
  have hloc : LocallyIntegrableOn (fun t => ∫ x, ∑ k, A k (x, t) * f k x) (Ioo a b) volume :=
    (show IntegrableOn _ (Ioo a b) volume from hg).locallyIntegrableOn
  have hfull : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b →
      ∫ t, θ t • (∫ x, ∑ k, A k (x, t) * f k x) ∂(volume : Measure ℝ) = 0 := by
    intro θ hθ hθc hθI
    have hcompl : ∀ t ∉ Ioo a b, θ t • (∫ x, ∑ k, A k (x, t) * f k x) = 0 := by
      intro t ht
      have hθzero : θ t = 0 := by
        by_contra hne
        exact ht (hθI ((subset_tsupport (f := θ)) (Function.mem_support.mpr hne)))
      simp [hθzero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
    simpa only [smul_eq_mul] using hzero θ hθ hθc hθI
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hfull
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact hz

/-- Slice identity for a linear family of tests: the identity holds for almost every time
against every test simultaneously. -/
theorem lps_ae_slice_test_eq_zero {a b : ℝ} {N : ℕ} {T : Type*} [AddCommGroup T]
    [Module ℝ T]
    (A : Fin N → Vec3 × ℝ → ℝ)
    (hA : ∀ k, MemLp (A k) 2 (volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b)))
    (ι : T →ₗ[ℝ] (Fin N → Vec3 → ℝ))
    (hι : ∀ ψ k, MemLp (ι ψ k) 2 volume)
    (hzero : ∀ (ψ : T) (χ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo a b →
      ∫ t in Ioo a b, χ t * ∫ x, ∑ k, A k (x, t) * ι ψ k x = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ψ : T, ∫ x, ∑ k, A k (x, t) * ι ψ k x = 0 := by
  classical
  -- the embedding into `L²`
  let ιL : T → (Fin N → Lp ℝ 2 (volume : Measure Vec3)) := fun ψ k => (hι ψ k).toLp (ι ψ k)
  have h2top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology (Fin N → Lp ℝ 2 (volume : Measure Vec3)) := inferInstance
  have hR : TopologicalSpace.IsSeparable (Set.range ιL) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨C, hCR, hCcount, hCdense⟩ := hR.exists_countable_dense_subset
  -- a countable set of tests
  choose ψc hψc using fun c : C => hCR c.2
  have hae_count : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ c : C, ∫ x, ∑ k, A k (x, t) * ι (ψc c) k x = 0 := by
    have : Countable C := hCcount.to_subtype
    rw [ae_all_iff]
    intro c
    exact lps_ae_slice_test_single A hA (ι (ψc c)) (hι (ψc c)) (hzero (ψc c))
  have hslice : ∀ k, ∀ᵐ t ∂(volume.restrict (Ioo a b)), MemLp (fun x => A k (x, t)) 2 volume := by
    intro k
    have hspaceTime : MemLp (A k) 2
        ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
      rw [← lps_measure_slab_eq_prod]
      exact hA k
    have hsq : Integrable (fun q => ‖A k q‖ ^ 2)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
      (memLp_two_iff_integrable_sq_norm hspaceTime.aestronglyMeasurable).1 hspaceTime
    filter_upwards [hspaceTime.aestronglyMeasurable.prodMk_right, hsq.prod_left_ae]
      with t hmeas hint
    exact (memLp_two_iff_integrable_sq_norm hmeas).2 hint
  filter_upwards [hae_count, ae_all_iff.mpr hslice] with t ht hAt ψ
  -- density: the functional is continuous in the `L²` norm of the test data
  let Λ : T → ℝ := fun ψ => ∫ x, ∑ k, A k (x, t) * ι ψ k x
  have hΛlin : ∀ ψ ψ', Λ ψ - Λ ψ' = Λ (ψ - ψ') := by
    intro ψ ψ'
    have h1 : ∀ k, Integrable (fun x => A k (x, t) * ι ψ k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ k)
    have h2 : ∀ k, Integrable (fun x => A k (x, t) * ι ψ' k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ' k)
    simp only [Λ, map_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [integral_sub (integrable_finsetSum _ fun k _ => h1 k)
      (integrable_finsetSum _ fun k _ => h2 k)]
  have hΛbound : ∀ ψ, |Λ ψ| ≤ ∑ k, Real.sqrt (∫ x, A k (x, t) ^ 2) *
      Real.sqrt (∫ x, ι ψ k x ^ 2) := by
    intro ψ
    have h1 : ∀ k, Integrable (fun x => A k (x, t) * ι ψ k x) volume := fun k =>
      (hAt k).integrable_mul (hι ψ k)
    calc |Λ ψ| = |∑ k, ∫ x, A k (x, t) * ι ψ k x| := by
          simp only [Λ]
          rw [integral_finsetSum _ fun k _ => h1 k]
      _ ≤ ∑ k, |∫ x, A k (x, t) * ι ψ k x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, Real.sqrt (∫ x, A k (x, t) ^ 2) * Real.sqrt (∫ x, ι ψ k x ^ 2) :=
          Finset.sum_le_sum fun k _ => lps_abs_integral_pairing_le _ _ (hAt k) (hι ψ k)
  by_contra hne
  have hpos : 0 < |Λ ψ| := abs_pos.mpr hne
  set M : ℝ := ∑ k, Real.sqrt (∫ x, A k (x, t) ^ 2) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _
  have hε : 0 < |Λ ψ| / (M + 1) := by positivity
  have hcl : ιL ψ ∈ closure C := hCdense ⟨ψ, rfl⟩
  obtain ⟨c, hcC, hdist⟩ := Metric.mem_closure_iff.mp hcl (|Λ ψ| / (M + 1)) hε
  have hcψ : ιL (ψc ⟨c, hcC⟩) = c := hψc ⟨c, hcC⟩
  have hdk : ∀ k, ‖ιL ψ k - ιL (ψc ⟨c, hcC⟩) k‖ < |Λ ψ| / (M + 1) := by
    intro k
    rw [hcψ]
    have := (dist_pi_lt_iff hε).mp hdist k
    rwa [dist_eq_norm] at this
  have hsqrt : ∀ k, Real.sqrt (∫ x, ι (ψ - ψc ⟨c, hcC⟩) k x ^ 2) < |Λ ψ| / (M + 1) := by
    intro k
    have hm : MemLp (ι (ψ - ψc ⟨c, hcC⟩) k) 2 volume := hι _ k
    rw [vl_integral_sq_eq hm, Real.sqrt_sq ENNReal.toReal_nonneg]
    have h1 : ‖ιL ψ k - ιL (ψc ⟨c, hcC⟩) k‖ =
        (eLpNorm (ι (ψ - ψc ⟨c, hcC⟩) k) 2 volume).toReal := by
      have : ιL ψ k - ιL (ψc ⟨c, hcC⟩) k =
          (hm).toLp (ι (ψ - ψc ⟨c, hcC⟩) k) := by
        simp only [ιL, ← MemLp.toLp_sub]
        refine MemLp.toLp_congr _ _ ?_
        exact Eventually.of_forall fun x => by simp
      rw [this, Lp.norm_toLp]
    rw [← h1]
    exact hdk k
  have hΛ0 : Λ (ψc ⟨c, hcC⟩) = 0 := ht ⟨c, hcC⟩
  have hbd := hΛbound (ψ - ψc ⟨c, hcC⟩)
  rw [← hΛlin, hΛ0, sub_zero] at hbd
  have hbd2 : |Λ ψ| ≤ ∑ k, Real.sqrt (∫ x, A k (x, t) ^ 2) * (|Λ ψ| / (M + 1)) := by
    refine hbd.trans (Finset.sum_le_sum fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (hsqrt k).le (Real.sqrt_nonneg _)
  rw [← Finset.sum_mul, ← hM] at hbd2
  have : M * (|Λ ψ| / (M + 1)) < |Λ ψ| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith only [hpos, hM0]
  linarith only [hbd2, this]

end ESS
