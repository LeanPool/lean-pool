/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergySum

/-!
# The localized vorticity energy estimate

`lem:localized-vorticity-energy`: a distributional solution
`z ∈ L²((a, τ) × ℝ³; ℝ³)` of
`∂ₜ zᵢ - Δzᵢ = -∂ⱼ(vⱼ zᵢ - zⱼ vᵢ) + ∂ⱼ Fⱼᵢ + gᵢ`
with `v ∈ L^∞`, `F ∈ L²`, `g ∈ L²((a, τ); H⁻¹)` and initial trace `z₀ ∈ L²` lies in
`C([a, τ]; L²) ∩ L²((a, τ); H¹)` and satisfies the energy bound with an absolute
constant.

The `H⁻¹` datum is written `g = g₀ + div G` with `g₀, G ∈ L²`, and
`‖g₀‖² + ‖G‖²` stands for `‖g‖²_{L²(H⁻¹)}`. Every `g ∈ L²((a, τ); H⁻¹)` has such a
representation, and the infimum of `‖g₀‖² + ‖G‖²` over them is `‖g‖²_{L²(H⁻¹)}`.
The initial trace is the value at `a` of the continuous versions of the
pairings with spatial tests. This is the `H⁻²`-valued trace of the manuscript,
tested against the spatial tests, which separate `H⁻²`. The bound `M` is any
bound for `|v|`, in particular `‖v‖_∞`.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- The square of the `L²` norm of a vector field is at most the sum of the
squared component norms. -/
theorem vl_vec_norm_sq_le {F : Vec3 → Vec3} (hF : MemLp F 2 volume) :
    ‖hF.toLp F‖ ^ 2 ≤ ∑ i : Fin 3, ∫ x, (F x i) ^ 2 := by
  have hn : MemLp (fun x => ‖F x‖) 2 volume := hF.norm
  have hc : ∀ i, MemLp (fun x => F x i) 2 volume := fun i => memLp_pi_iff.1 hF i
  have h1 : ‖hF.toLp F‖ = (eLpNorm (fun x => ‖F x‖) 2 volume).toReal := by
    rw [Lp.norm_toLp, eLpNorm_norm F hF.aestronglyMeasurable]
  rw [h1, ← vl_integral_sq_eq hn, ← integral_finsetSum _ fun i _ => (hc i).integrable_sq]
  refine integral_mono hn.integrable_sq (integrable_finsetSum _ fun i _ => (hc i).integrable_sq)
    (fun x => ?_)
  have h := norm_le_vec3EuclideanNorm (F x)
  have hE : vec3EuclideanNorm (F x) ^ 2 = ∑ i : Fin 3, (F x i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc
    ‖F x‖ ^ 2 ≤ vec3EuclideanNorm (F x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i : Fin 3, (F x i) ^ 2 := hE

/-- `lem:localized-vorticity-energy`. -/
theorem localizedVorticityEnergy :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a τ M : ℝ) (hat : a < τ) (z v g₀ : Vec3 × ℝ → Vec3)
        (F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ) (z₀ : Vec3 → Vec3),
        MemLp z 2 (volume.restrict (vlSlab a τ)) →
        AEStronglyMeasurable v (volume.restrict (vlSlab a τ)) →
        (∀ᵐ p ∂(volume.restrict (vlSlab a τ)), vec3EuclideanNorm (v p) ≤ M) →
        (∀ j i, MemLp (fun p => F p j i) 2 (volume.restrict (vlSlab a τ))) →
        MemLp g₀ 2 (volume.restrict (vlSlab a τ)) →
        (∀ j i, MemLp (fun p => G p j i) 2 (volume.restrict (vlSlab a τ))) →
        MemLp z₀ 2 volume →
        (∀ φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo a τ),
          ∫ p in vlSlab a τ, ∑ i : Fin 3, z p i *
              (-vorticityTestTimeDerivative φ p i - vorticityTestLaplacian φ p i) =
            ∫ p in vlSlab a τ, (∑ j : Fin 3, ∑ i : Fin 3,
              (v p j * z p i - z p j * v p i - F p j i - G p j i) *
                CKN.spatialPartial (fun q : Vec3 × ℝ => φ q i) j p +
              ∑ i : Fin 3, g₀ p i * φ p i)) →
        (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧
            c a = ∫ x, ∑ i : Fin 3, z₀ x i * ψ x i ∧
            ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, ∑ i : Fin 3, z (x, t) i * ψ x i) →
        ∃ Z : Icc a τ → Lp Vec3 2 (volume : Measure Vec3),
        ∃ Dz : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ,
          Continuous Z ∧
          ((Z ⟨a, left_mem_Icc.2 hat.le⟩ : Vec3 → Vec3) =ᵐ[volume] z₀) ∧
          (∀ᵐ t ∂(volume.restrict (Ioo a τ)), ∀ ht : t ∈ Icc a τ,
            (Z ⟨t, ht⟩ : Vec3 → Vec3) =ᵐ[volume] fun x => z (x, t)) ∧
          (∀ i j, MemLp (fun p => Dz p i j) 2 (volume.restrict (vlSlab a τ))) ∧
          (∀ i j, ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a τ),
            ∫ p in vlSlab a τ, z p i * CKN.spatialPartial φ j p =
              -∫ p in vlSlab a τ, Dz p i j * φ p) ∧
          ∀ t : Icc a τ,
            (∫ x, ∑ i : Fin 3, ((Z t : Vec3 → Vec3) x i) ^ 2) +
                ∫ p in vlSlab a τ, ∑ i : Fin 3, ∑ j : Fin 3, (Dz p i j) ^ 2 ≤
              C * Real.exp (C * (1 + M ^ 2) * (τ - a)) *
                ((∫ x, ∑ i : Fin 3, (z₀ x i) ^ 2) +
                  (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2) +
                  ((∫ p in vlSlab a τ, ∑ i : Fin 3, (g₀ p i) ^ 2) +
                    ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2)) := by
  refine ⟨36, by norm_num, ?_⟩
  intro a τ M hat z v g₀ F G z₀ hz hv hvb hF hg hG hz₀ hweak htrace
  set μQ := (volume : Measure (Vec3 × ℝ)).restrict (vlSlab a τ) with hμQ
  -- components of the data
  have hzi : ∀ i, MemLp (fun p => z p i) 2 μQ := fun i => memLp_pi_iff.1 hz i
  have hgi : ∀ i, MemLp (fun p => g₀ p i) 2 μQ := fun i => memLp_pi_iff.1 hg i
  have hz₀i : ∀ i, MemLp (fun x => z₀ x i) 2 volume := fun i => memLp_pi_iff.1 hz₀ i
  have hvj : ∀ j, AEStronglyMeasurable (fun p => v p j) μQ := fun j =>
    (continuous_apply j).comp_aestronglyMeasurable hv
  -- measurable versions of the data
  let z' : Vec3 × ℝ → Vec3 := fun p i => (hzi i).aestronglyMeasurable.mk _ p
  let v' : Vec3 × ℝ → Vec3 := fun p j => (hvj j).mk _ p
  let F' : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun p j i => (hF j i).aestronglyMeasurable.mk _ p
  let G' : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun p j i => (hG j i).aestronglyMeasurable.mk _ p
  let g' : Vec3 × ℝ → Vec3 := fun p i => (hgi i).aestronglyMeasurable.mk _ p
  have hz'm : ∀ i, StronglyMeasurable (fun p => z' p i) := fun i =>
    (hzi i).aestronglyMeasurable.stronglyMeasurable_mk
  have hv'm : ∀ j, StronglyMeasurable (fun p => v' p j) := fun j => (hvj j).stronglyMeasurable_mk
  have hF'm : ∀ j i, StronglyMeasurable (fun p => F' p j i) := fun j i =>
    (hF j i).aestronglyMeasurable.stronglyMeasurable_mk
  have hG'm : ∀ j i, StronglyMeasurable (fun p => G' p j i) := fun j i =>
    (hG j i).aestronglyMeasurable.stronglyMeasurable_mk
  have hg'm : ∀ i, StronglyMeasurable (fun p => g' p i) := fun i =>
    (hgi i).aestronglyMeasurable.stronglyMeasurable_mk
  have hz'e : ∀ i, (fun p => z p i) =ᵐ[μQ] fun p => z' p i := fun i =>
    (hzi i).aestronglyMeasurable.ae_eq_mk
  have hv'e : ∀ j, (fun p => v p j) =ᵐ[μQ] fun p => v' p j := fun j => (hvj j).ae_eq_mk
  have hF'e : ∀ j i, (fun p => F p j i) =ᵐ[μQ] fun p => F' p j i := fun j i =>
    (hF j i).aestronglyMeasurable.ae_eq_mk
  have hG'e : ∀ j i, (fun p => G p j i) =ᵐ[μQ] fun p => G' p j i := fun j i =>
    (hG j i).aestronglyMeasurable.ae_eq_mk
  have hg'e : ∀ i, (fun p => g₀ p i) =ᵐ[μQ] fun p => g' p i := fun i =>
    (hgi i).aestronglyMeasurable.ae_eq_mk
  have hz'L : ∀ i, MemLp (fun p => z' p i) 2 μQ := fun i => (hzi i).ae_eq (hz'e i)
  have hF'L : ∀ j i, MemLp (fun p => F' p j i) 2 μQ := fun j i => (hF j i).ae_eq (hF'e j i)
  have hG'L : ∀ j i, MemLp (fun p => G' p j i) 2 μQ := fun j i => (hG j i).ae_eq (hG'e j i)
  have hg'L : ∀ i, MemLp (fun p => g' p i) 2 μQ := fun i => (hgi i).ae_eq (hg'e i)
  -- vector almost everywhere equalities
  have hzv : ∀ᵐ p ∂μQ, z p = z' p := by
    filter_upwards [ae_all_iff.2 hz'e] with p hp
    funext i
    exact hp i
  have hvv : ∀ᵐ p ∂μQ, v p = v' p := by
    filter_upwards [ae_all_iff.2 hv'e] with p hp
    funext j
    exact hp j
  have hgv : ∀ᵐ p ∂μQ, g₀ p = g' p := by
    filter_upwards [ae_all_iff.2 hg'e] with p hp
    funext i
    exact hp i
  have hFv : ∀ᵐ p ∂μQ, F p = F' p := by
    filter_upwards [ae_all_iff.2 fun j => ae_all_iff.2 fun i => hF'e j i] with p hp
    funext j i
    exact hp j i
  have hGv : ∀ᵐ p ∂μQ, G p = G' p := by
    filter_upwards [ae_all_iff.2 fun j => ae_all_iff.2 fun i => hG'e j i] with p hp
    funext j i
    exact hp j i
  have hvb' : ∀ᵐ p ∂μQ, vec3EuclideanNorm (v' p) ≤ M := by
    filter_upwards [hvb, hvv] with p h1 h2
    rwa [← h2]
  -- the equation and the trace for the measurable versions
  have hweak' : (∀ φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo a τ),
      ∫ p in vlSlab a τ, ∑ i : Fin 3, z' p i *
          (-vorticityTestTimeDerivative φ p i - vorticityTestLaplacian φ p i) =
        ∫ p in vlSlab a τ, (∑ j : Fin 3, ∑ i : Fin 3,
          (v' p j * z' p i - z' p j * v' p i - F' p j i - G' p j i) *
            CKN.spatialPartial (fun q : Vec3 × ℝ => φ q i) j p +
          ∑ i : Fin 3, g' p i * φ p i)) := by
    intro φ hφ
    refine (integral_congr_ae ?_).trans ((hweak φ hφ).trans (integral_congr_ae ?_))
    · filter_upwards [hzv] with p hp
      rw [hp]
    · filter_upwards [hzv, hvv, hFv, hGv, hgv] with p h1 h2 h3 h4 h5
      rw [h1, h2, h3, h4, h5]
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo a τ)), ∀ i,
      (fun x => z (x, t) i) =ᵐ[volume] fun x => z' (x, t) i :=
    ae_all_iff.2 fun i => vlSlab_slice_ae_eq (hz'e i)
  have htrace' : (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧ c a = ∫ x, ∑ i : Fin 3, z₀ x i * ψ x i ∧
        ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, ∑ i : Fin 3, z' (x, t) i * ψ x i) := by
    intro ψ hψ hψc
    obtain ⟨c, hc, hca, hct⟩ := htrace ψ hψ hψc
    refine ⟨c, hc, hca, ?_⟩
    filter_upwards [hct, hslice] with t ht hs
    rw [ht]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hs] with x hx
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]
  -- the component heat solutions and their energy estimates
  have sol : ∀ i, VlHeatSolution a τ (fun p => z' p i) (vlCompFlux z' v' F' G' i)
      (fun p => g' p i) (fun x => z₀ x i) := fun i =>
    vlVector_componentSolution hat hz'm hv'm hF'm hG'm hg'm hz'L hvb' hF'L hG'L hg'L hz₀i
      hweak' htrace' i
  choose Zc Dc hZc using fun i => vlHeat_energy (sol i)
  -- the vector curve
  have hZmem : ∀ t, MemLp (fun x : Vec3 => fun i => (Zc i t : Vec3 → ℝ) x) 2 volume :=
    fun t => memLp_pi_iff.2 fun i => Lp.memLp (Zc i t)
  let Zv : Icc a τ → Lp Vec3 2 (volume : Measure Vec3) := fun t => (hZmem t).toLp _
  have hZv_coe : ∀ t i, (fun x => (Zv t : Vec3 → Vec3) x i) =ᵐ[volume]
      (Zc i t : Vec3 → ℝ) := by
    intro t i
    filter_upwards [(hZmem t).coeFn_toLp] with x hx
    rw [hx]
  have hdist : ∀ t t', ‖Zv t - Zv t'‖ ^ 2 ≤ ∑ i : Fin 3, ‖Zc i t - Zc i t'‖ ^ 2 := by
    intro t t'
    have hsub : Zv t - Zv t' = ((hZmem t).sub (hZmem t')).toLp _ := (MemLp.toLp_sub _ _).symm
    rw [hsub]
    refine (vl_vec_norm_sq_le _).trans_eq ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vl_Lp_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (Zc i t) (Zc i t')] with x hx
    rw [hx]
    rfl
  have hZvc : Continuous Zv := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have hc : Continuous (fun t => Real.sqrt (∑ i : Fin 3, ‖Zc i t - Zc i t₀‖ ^ 2)) :=
      (continuous_finsetSum _ fun i _ => ((hZc i).1.sub continuous_const).norm.pow 2).sqrt
    have hlim : Tendsto (fun t => Real.sqrt (∑ i : Fin 3, ‖Zc i t - Zc i t₀‖ ^ 2)) (𝓝 t₀)
        (𝓝 0) := by
      simpa using hc.tendsto t₀
    exact squeeze_zero (fun t => norm_nonneg _)
      (fun t => Real.le_sqrt_of_sq_le (hdist t t₀)) hlim
  -- the gradient
  let Dz : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun p i j => Dc i j p
  refine ⟨Zv, Dz, hZvc, ?_, ?_, fun i j => (hZc i).2.2.2.1 j, ?_, ?_⟩
  · -- the initial value
    have hi : ∀ i, (fun x => (Zv ⟨a, left_mem_Icc.2 hat.le⟩ : Vec3 → Vec3) x i) =ᵐ[volume]
        fun x => z₀ x i := fun i => (hZv_coe _ i).trans (hZc i).2.1
    filter_upwards [ae_all_iff.2 hi] with x hx
    funext i
    exact hx i
  · -- the time slices
    filter_upwards [ae_all_iff.2 fun i => (hZc i).2.2.1, hslice] with t h1 h2 ht
    have hi : ∀ i, (fun x => (Zv ⟨t, ht⟩ : Vec3 → Vec3) x i) =ᵐ[volume] fun x => z (x, t) i :=
      fun i => ((hZv_coe _ i).trans (h1 i ht)).trans (h2 i).symm
    filter_upwards [ae_all_iff.2 hi] with x hx
    funext i
    exact hx i
  · -- the weak gradient
    intro i j φ hφ
    have hcongr : ∫ p in vlSlab a τ, z p i * CKN.spatialPartial φ j p =
        ∫ p in vlSlab a τ, z' p i * CKN.spatialPartial φ j p := by
      refine integral_congr_ae ?_
      filter_upwards [hz'e i] with p hp
      rw [hp]
    rw [hcongr]
    exact (hZc i).2.2.2.2.1 j φ hφ
  · -- the energy estimate
    intro t
    set L : ℝ := 36 * M ^ 2 + 1 with hL_def
    have hLpos : 0 < L := by positivity
    set K : ℝ := (∑ i : Fin 3, ∫ x, (z₀ x i) ^ 2) +
        3 * (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F' p j i) ^ 2) +
        3 * (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G' p j i) ^ 2) +
        (∫ p in vlSlab a τ, ∑ i : Fin 3, (g' p i) ^ 2) with hK_def
    let e : ℝ → ℝ := fun s => ∑ i : Fin 3, ‖Zc i (projIcc a τ hat.le s)‖ ^ 2
    let d : ℝ → ℝ := fun s => ∑ i : Fin 3, ∑ j : Fin 3, ∫ p in vlSlab a s, (Dc i j p) ^ 2
    have he_at : ∀ s (hs : s ∈ Icc a τ), e s = ∑ i : Fin 3, ‖Zc i ⟨s, hs⟩‖ ^ 2 := by
      intro s hs
      simp only [e, projIcc_of_mem hat.le hs]
    have hec : ContinuousOn e (Icc a τ) :=
      (continuous_finsetSum _ fun i _ =>
        ((hZc i).1.comp continuous_projIcc).norm.pow 2).continuousOn
    have he0 : ∀ s ∈ Icc a τ, 0 ≤ e s := fun s _ => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hd0 : ∀ s ∈ Icc a τ, 0 ≤ d s := fun s _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        integral_nonneg fun p => sq_nonneg _
    have hineq : ∀ s ∈ Icc a τ, e s + d s ≤ K + L * ∫ r in Ioo a s, e r := by
      intro s hs
      have hcomp : e s + d s ≤ ∑ i : Fin 3, vlDataEnergy (fun x => z₀ x i) (fun p => z' p i)
          (vlCompFlux z' v' F' G' i) (fun p => g' p i) a s := by
        rw [he_at s hs]
        simp only [d]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => (hZc i).2.2.2.2.2 ⟨s, hs⟩
      have hsum := vl_dataEnergy_sum_le sol hF'L hG'L hvb' hs
      have hzs : ∫ p in vlSlab a s, ∑ i : Fin 3, (z' p i) ^ 2 = ∫ r in Ioo a s, e r := by
        have hint : Integrable (fun p => ∑ i : Fin 3, (z' p i) ^ 2)
            (volume.restrict (vlSlab a s)) :=
          integrable_finsetSum _ fun i _ => (vlSlab_memLp_mono hs.2 (hz'L i)).integrable_sq
        rw [vlSlab_integral_eq hint]
        refine setIntegral_congr_ae measurableSet_Ioo ?_
        have hae := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hs.2)
          (ae_all_iff.2 fun i => (hZc i).2.2.1)
        rw [ae_restrict_iff' measurableSet_Ioo] at hae
        filter_upwards [hae] with r hr hrI
        have hrI' : r ∈ Icc a τ := ⟨hrI.1.le, hrI.2.le.trans hs.2⟩
        have hri : ∀ i, (Zc i ⟨r, hrI'⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => z' (x, r) i :=
          fun i => hr hrI i hrI'
        symm
        calc
          e r = ∑ i : Fin 3, ‖Zc i ⟨r, hrI'⟩‖ ^ 2 := he_at r hrI'
          _ = ∑ i : Fin 3, ∫ x, (z' (x, r) i) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [vl_Lp_norm_sq]
            refine integral_congr_ae ?_
            filter_upwards [hri i] with x hx
            rw [hx]
          _ = ∫ x, ∑ i : Fin 3, (z' (x, r) i) ^ 2 := by
            refine (integral_finsetSum _ fun i _ => ?_).symm
            refine (Lp.memLp (Zc i ⟨r, hrI'⟩)).integrable_sq.congr ?_
            filter_upwards [hri i] with x hx
            rw [hx]
      rw [hzs] at hsum
      linarith only [hcomp, hsum]
    have hgr := vl_gronwall hat.le hLpos hec he0 hd0 hineq
    have hgt := hgr t.1 t.2
    have hgτ := hgr τ (right_mem_Icc.2 hat.le)
    -- the two sides of the estimate
    have hLHS1 : ∫ x, ∑ i : Fin 3, ((Zv t : Vec3 → Vec3) x i) ^ 2 = e t.1 := by
      have hc : ∀ i, MemLp (fun x => (Zv t : Vec3 → Vec3) x i) 2 volume := fun i =>
        memLp_pi_iff.1 (Lp.memLp (Zv t)) i
      rw [integral_finsetSum _ fun i _ => (hc i).integrable_sq, he_at t.1 t.2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [vl_Lp_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [hZv_coe t i] with x hx
      rw [hx]
    have hLHS2 : ∫ p in vlSlab a τ, ∑ i : Fin 3, ∑ j : Fin 3, (Dz p i j) ^ 2 = d τ := by
      simp only [d, Dz]
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        ((hZc i).2.2.2.1 j).integrable_sq]
      exact Finset.sum_congr rfl fun i _ =>
        integral_finsetSum _ fun j _ => ((hZc i).2.2.2.1 j).integrable_sq
    -- comparison of the data
    have hz₀sum : (∑ i : Fin 3, ∫ x, (z₀ x i) ^ 2) = ∫ x, ∑ i : Fin 3, (z₀ x i) ^ 2 :=
      (integral_finsetSum _ fun i _ => (hz₀i i).integrable_sq).symm
    have hFeq : ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F' p j i) ^ 2 =
        ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hFv] with p hp
      rw [hp]
    have hGeq : ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G' p j i) ^ 2 =
        ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hGv] with p hp
      rw [hp]
    have hgeq : ∫ p in vlSlab a τ, ∑ i : Fin 3, (g' p i) ^ 2 =
        ∫ p in vlSlab a τ, ∑ i : Fin 3, (g₀ p i) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hgv] with p hp
      rw [hp]
    set S : ℝ := (∫ x, ∑ i : Fin 3, (z₀ x i) ^ 2) +
        (∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2) +
        ((∫ p in vlSlab a τ, ∑ i : Fin 3, (g₀ p i) ^ 2) +
          ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2) with hS_def
    have hz0n : 0 ≤ ∫ x, ∑ i : Fin 3, (z₀ x i) ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hFn : 0 ≤ ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (F p j i) ^ 2 :=
      integral_nonneg fun p => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        sq_nonneg _
    have hGn : 0 ≤ ∫ p in vlSlab a τ, ∑ j : Fin 3, ∑ i : Fin 3, (G p j i) ^ 2 :=
      integral_nonneg fun p => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
        sq_nonneg _
    have hgn : 0 ≤ ∫ p in vlSlab a τ, ∑ i : Fin 3, (g₀ p i) ^ 2 :=
      integral_nonneg fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hK0 : 0 ≤ K := by
      rw [hK_def, hFeq, hGeq, hgeq, hz₀sum]
      linarith only [hz0n, hFn, hGn, hgn]
    have hKS : 2 * K ≤ 36 * S := by
      rw [hK_def, hFeq, hGeq, hgeq, hz₀sum, hS_def]
      linarith only [hz0n, hFn, hGn, hgn]
    set E : ℝ := Real.exp (36 * (1 + M ^ 2) * (τ - a)) with hE_def
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hL36 : L ≤ 36 * (1 + M ^ 2) := by
      rw [hL_def]
      linarith only [sq_nonneg M]
    have hexp : ∀ s ∈ Icc a τ, Real.exp (L * (s - a)) ≤ E := by
      intro s hs
      rw [hE_def]
      refine Real.exp_le_exp.2 ?_
      have h1 : L * (s - a) ≤ L * (τ - a) :=
        mul_le_mul_of_nonneg_left (by linarith only [hs.2]) hLpos.le
      have h2 : L * (τ - a) ≤ 36 * (1 + M ^ 2) * (τ - a) :=
        mul_le_mul_of_nonneg_right hL36 (by linarith only [hat])
      linarith only [h1, h2]
    have het : e t.1 ≤ K * E :=
      calc
        e t.1 ≤ K * Real.exp (L * (t.1 - a)) := by linarith only [hgt, hd0 t.1 t.2]
        _ ≤ K * E := mul_le_mul_of_nonneg_left (hexp t.1 t.2) hK0
    have hdτ : d τ ≤ K * E :=
      calc
        d τ ≤ K * Real.exp (L * (τ - a)) := by
          linarith only [hgτ, he0 τ (right_mem_Icc.2 hat.le)]
        _ ≤ K * E := mul_le_mul_of_nonneg_left (hexp τ (right_mem_Icc.2 hat.le)) hK0
    have hfin : E * (2 * K) ≤ E * (36 * S) := mul_le_mul_of_nonneg_left hKS hE0
    rw [hLHS1, hLHS2]
    linarith only [het, hdτ, hfin]

end ESS

end
