/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsAssembly
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformContracts
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitMain

/-!
# The compact-weight step of `lem:reg-tails`

For a compact, nonnegative smooth weight `q` with `|∇q| ≤ M`, the localized
energy of a regularized solution grows on `(s, t)` by at most
`18 M B² t^{1/2} + Q M B³ t^{1/4}`, where `B` is the Euclidean `L²` norm of the
initial datum (eq:reg-tails, lem:reg-tails).
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The constant multiplying `B³ t^{1/4}` in the flux estimate of
`lem:reg-tails`. -/
@[expose]
def regTailsFluxConstant : ℝ :=
  27 * CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) +
    486 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
      CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ)

/-- The flux constant of `lem:reg-tails` is nonnegative. -/
theorem regTailsFluxConstant_nonneg : 0 ≤ regTailsFluxConstant := by
  have hR : 0 ≤ rieszPressureOperatorBound (2 : ℝ) (by norm_num) := by
    unfold rieszPressureOperatorBound
    exact (Classical.choose_spec
      (CKN.Foundation.Euclidean.riesz_second_all_exponents (2 : ℝ) (by norm_num))).1
  have hG : 0 ≤ CKN.gagliardoNirenbergSobolevConstant.toReal ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  unfold regTailsFluxConstant
  positivity

/-- A square-integrable field has square-integrable Euclidean length, as used
for the exterior energies in `lem:reg-tails`. -/
theorem regTailsFinal_euclideanNorm_memLp {f : Vec3 → Vec3}
    (hf : MemLp f (2 : ℝ≥0∞) volume) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (f x)) 2 volume := by
  refine (hf.norm.const_mul (Real.sqrt 3)).of_le
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      hf.aestronglyMeasurable) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
  exact vec3EuclideanNorm_le_sqrt_three_mul_norm _

/-- The Euclidean slice norm of a regularized velocity is controlled by the
Euclidean `L²` norm of the datum, from (R5) (lem:reg-tails). -/
private theorem regTailsFinal_slice_norm_le
    (u : ParabolicPoint → Vec3) (a : Vec3 → Vec3)
    (ha : MemLp a (2 : ℝ≥0∞) volume) (t : ℝ)
    (hU : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hE : eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) :
    (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume).toReal ≤
      (eLpNorm (regUniformSpatialField a) 2 volume).toReal := by
  have hle : eLpNorm (regUniformVelocitySlice u t) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume :=
    (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hE
  have hslice := regTails_eLpNorm_euclidean_eq_spatialField
    (fun x : Vec3 => u (x, t)) hU
  have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha
  have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
    rw [← hfield]
    exact (regTailsFinal_euclideanNorm_memLp ha).eLpNorm_ne_top
  rw [hslice]
  exact ENNReal.toReal_mono hfin hle

section

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)



/-- For a compact nonnegative smooth weight `q` with `|∂_j q| ≤ M`, the
localized energy of the regularized solution increases on `(s, t)` by at most
`18 M B² t^{1/2} + Q M B³ t^{1/4}` (lem:reg-tails). -/
theorem regTailsFinal_compact_weight_bound
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (hq0 : ∀ x, 0 ≤ q x) {M : ℝ} (hM : 0 ≤ M)
    (hDq : ∀ x : Vec3, ∀ j : Fin 3, |spatialDeriv q j x| ≤ M)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    regTailsEnergyWeight (uε a ha ε) q t ≤
      regTailsEnergyWeight (uε a ha ε) q s +
        (18 * M * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (2 : ℕ) *
            t ^ (1 / 2 : ℝ) +
          regTailsFluxConstant * M *
            (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ (3 : ℕ) *
            t ^ (1 / 4 : ℝ)) := by
  have hLE := regLocalEnergy_of_regularised ρ uε pε hregularised a ha ε hε
  have hEB := regTails_contract_energy_bounds ρ uε pε hregularised a ha ε hε
  obtain ⟨⟨hSlice, _hSliceCont, _hInit, _hDiv⟩, hUc, hDc, _hDDc, _hDtc, hPc, _hDpc,
    hC1, _hDdiff, _hPdiff, hBounds, _hLocalLp, _hEq, hPress, hR5⟩ :=
    hregularised a ha ε hε
  set u : ParabolicPoint → Vec3 := uε a ha ε with hu_def
  set p : ParabolicPoint → ℝ := pε a ha ε with hp_def
  let J : ParabolicPoint → Vec3 := regUniformMollifiedVelocity ρ ε hε u
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y : ParabolicPoint => u y i) j z
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let B : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal
  let Q : ℝ := regTailsFluxConstant
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hQ : 0 ≤ Q := regTailsFluxConstant_nonneg
  have hUcont (i : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i) S :=
    (hUc i).comp continuous_prod_to_parabolicPoint.continuousOn (fun _ hz => hz)
  have hDcont (i j : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => D (z.1, z.2) i j) S :=
    (hDc i j).comp continuous_prod_to_parabolicPoint.continuousOn (fun _ hz => hz)
  have hPcont : ContinuousOn (fun z : Vec3 × ℝ => p (z.1, z.2)) S :=
    hPc.comp continuous_prod_to_parabolicPoint.continuousOn (fun _ hz => hz)
  have hJcont (i : Fin 3) :
      ContinuousOn (fun z : Vec3 × ℝ => J (z.1, z.2) i) S := by
    have hshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S :=
      fun z hz _ => ⟨Set.mem_univ _, hz.2⟩
    have hpositive : ∀ z ∈ S, 0 < z.2 := fun _ hz => hz.2
    exact regUniform_mollified_velocity_continuousOn ρ ε hε
      (fun τ hτ => hSlice τ hτ.le) hC1 hpositive hshift i
  have hUdiff (i : Fin 3) :
      ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u (z.1, z.2) i) S := hC1 i
  have hslice {τ : ℝ} (hτ : 0 < τ) (f : Vec3 × ℝ → ℝ) (hf : ContinuousOn f S) :
      Continuous (fun x : Vec3 => f (x, τ)) :=
    hf.comp_continuous (continuous_id.prodMk continuous_const)
      (fun _ => ⟨Set.mem_univ _, hτ⟩)
  -- the increment identity
  have hinc := regTails_compact_weight_interval_increment u p J hLE
    hUcont hDcont hPcont hJcont hUdiff q hq hqc hs hst
  let A : ℝ → ℝ := fun τ => ∫ x : Vec3,
    regTailsLocalizedSource u D p J q (x, τ) ∂volume
  have hAcont : ContinuousOn A (Ioi (0 : ℝ)) :=
    (regTails_localized_profiles_continuous u D p J q hq hqc
      hUcont hDcont hPcont hJcont).2
  -- the dissipation profile
  have hSpatialC1 := lerayLimit_contDiff_spatial_slices u
    (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) hC1
    (fun _ hτ _ => ⟨Set.mem_univ _, hτ⟩)
  have hTG := regTails_contract_timeGradientBounds ρ ε hε a ha u D hR5 hDc
    hSlice hSpatialC1 (fun _ _ _ _ _ => rfl)
  dsimp only at hTG
  obtain ⟨hTGT, hGid⟩ := hTG
  obtain ⟨hGmem, hGenergy, -⟩ := hTGT t (hs.trans hst)
  set G : ℝ → ℝ := fun τ => Real.sqrt
    (∫⁻ x : Vec3, ENNReal.ofReal (spatialGradientSq u
      (regTailsPositiveGradientExtension D) (x, τ)) ∂volume).toReal with hG_def
  have hG0 : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)), 0 ≤ G τ :=
    Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  -- slice hypotheses of the flux estimate
  have hU2 : ∀ τ : ℝ, 0 ≤ τ → MemLp (regUniformVelocitySlice u τ) 2 volume := by
    intro τ hτ
    have hcoord : MemLp (fun x : L2Vec3 => u (WithLp.ofLp x, τ)) 2 volume :=
      (hSlice τ hτ).comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hUbound : ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Vec3,
      vec3EuclideanNorm (u (x, τ)) ≤ K := by
    intro τ hτ
    obtain ⟨K, hK, hKb⟩ := hBounds τ (τ + 1) hτ (by linarith only)
    exact ⟨K, hK, fun x => (hKb (x, τ) ⟨Set.mem_univ _, le_rfl, by linarith only⟩).1⟩
  have hR4 : ∀ τ : ℝ, 0 < τ → ∃ hF : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, τ) i * u (x, τ) j)
        (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => p (x, τ)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 =>
            regUniformMollifiedVelocity ρ ε hε u (x, τ) i * u (x, τ) j)) := by
    intro τ hτ
    obtain ⟨hF, hae, -⟩ := hPress τ hτ
    exact ⟨hF, hae⟩
  -- the a.e. profile bound
  have hAprofile : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) t)),
      A τ ≤ 18 * M * B * G τ + Q * M * B ^ (3 / 2 : ℝ) * G τ ^ (3 / 2 : ℝ) := by
    have hsub : Ioo (0 : ℝ) t ⊆ Ioi 0 := fun _ hτ => hτ.1
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hGid,
      ae_restrict_of_ae_restrict_of_subset hsub hEB.2.2] with τ hτ hGτ hH1
    have hτ0 : 0 < τ := hτ.1
    have hsrc := regTails_localized_source_integral_le_flux u D p J q hq hqc hq0 τ
      (fun i => hslice hτ0 _ (hUcont i)) (fun i j => hslice hτ0 _ (hDcont i j))
      (hslice hτ0 _ hPcont) (fun j => hslice hτ0 _ (hJcont j))
    have hflux := regTails_slice_flux_bound ρ ε hε u p hU2 hUbound hR4 τ hτ0
      (hSlice τ hτ0.le) hH1 B (G τ) M hB (Real.sqrt_nonneg _) hM
      (regTailsFinal_slice_norm_le u a ha.1 τ (hSlice τ hτ0.le) (hEB.1 τ hτ0.le))
      hGτ q hq hDq
    exact hsrc.trans hflux
  have hbound := regTails_open_interval_flux_bound hs hst hB hM hQ G A
    hGmem hG0 hGenergy hAcont hAprofile
  have hinc' : regTailsEnergyWeight u q t - regTailsEnergyWeight u q s =
      ∫ τ in s..t, A τ ∂volume := hinc
  linarith only [hinc', hbound]

end

end CKN.Leray

end
