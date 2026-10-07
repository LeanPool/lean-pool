/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofLiouville
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.StartCaccioppoli
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Ess Local Proof Exterior

Local endpoint regularity through vorticity estimates and backward uniqueness.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem essLocal_matrixNormSq_le_spatialGradientSq
    (DU : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint) :
    ‖DU z‖ ^ (2 : ℝ) ≤ spatialGradientSq (fun _ => (0 : Vec3)) DU z := by
  let S : ℝ := spatialGradientSq (fun _ => (0 : Vec3)) DU z
  have hS : 0 ≤ S := by
    exact Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg (DU z i j)
  have hentry (i j : Fin 3) : (DU z i j) ^ 2 ≤ S := by
    dsimp [S, spatialGradientSq]
    exact le_trans
      (Finset.single_le_sum (fun k _ => sq_nonneg (DU z i k)) (Finset.mem_univ j))
      (Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (DU z k l))
        (Finset.mem_univ i))
  have hentryAbs (i j : Fin 3) : |DU z i j| ≤ Real.sqrt S :=
    Real.abs_le_sqrt (hentry i j)
  have hrow (i : Fin 3) : ‖DU z i‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2
    intro j
    rw [Real.norm_eq_abs]
    exact hentryAbs i j
  have hmatrix : ‖DU z‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2
    intro i
    exact hrow i
  calc
    ‖DU z‖ ^ (2 : ℝ) ≤ (Real.sqrt S) ^ (2 : ℝ) := by
      exact Real.rpow_le_rpow (norm_nonneg _) hmatrix (by norm_num)
    _ = S := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]

/-- The matrix-valued weak-gradient norm is controlled by the scalar Dirichlet
density used in the suitable-solution energy inequality. -/
theorem essLocal_matrixGradientEnergy_le_spatialGradientEnergy
    (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
    (x : Vec3) (t r E : ℝ)
    (hbound : (∫⁻ z in parabolicCylinder x t r,
      ENNReal.ofReal (spatialGradientSq U DU z) ∂(volume : Measure ParabolicPoint)) ≤
        ENNReal.ofReal (E ^ 2)) :
    (∫⁻ z in parabolicCylinder x t r,
      ‖DU z‖ₑ ^ (2 : ℝ) ∂(volume : Measure ParabolicPoint)) ≤
        ENNReal.ofReal (E ^ 2) := by
  calc
    _ ≤ ∫⁻ z in parabolicCylinder x t r,
        ENNReal.ofReal (spatialGradientSq U DU z)
        ∂(volume : Measure ParabolicPoint) := by
      apply lintegral_mono
      intro z
      change ‖DU z‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (spatialGradientSq U DU z)
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (DU z)) (by norm_num)]
      exact ENNReal.ofReal_le_ofReal
        (essLocal_matrixNormSq_le_spatialGradientSq DU z)
    _ ≤ ENNReal.ofReal (E ^ 2) := hbound

/-- Global critical velocity and pressure masses give one local Dirichlet
bound on every unit past cylinder whose top lies in `(-2,0)`. -/
theorem essLocal_uniformGradientEnergy_of_globalMass
    (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
    (q : ParabolicPoint → ℝ)
    (hsol : IsSuitableWeakSolutionIntegrable Set.univ (Ioo (-12 : ℝ) 0) 3
      U DU q (0 : ParabolicPoint → Vec3))
    (hUmass : (∫⁻ z in spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0),
      ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)) < ⊤)
    (hqmass : (∫⁻ z in spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0),
      ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)) < ⊤) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (x : Vec3) (t : ℝ), t ∈ Ioo (-2 : ℝ) 0 →
      (∫⁻ z in parabolicCylinder x t 1, ‖DU z‖ₑ ^ (2 : ℝ)
        ∂(volume : Measure ParabolicPoint)) ≤ ENNReal.ofReal (E ^ 2) := by
  let MU : ℝ≥0∞ := ∫⁻ z in spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0),
    ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
  let MP : ℝ≥0∞ := ∫⁻ z in spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0),
    ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
  have hMU : MU < ⊤ := by simpa [MU] using hUmass
  have hMP : MP < ⊤ := by simpa [MP] using hqmass
  let G : ℝ := ((2 : ℝ) ^ (-2 : ℝ) * MU.toReal) ^ (1 / 3 : ℝ)
  let D : ℝ := ((2 : ℝ) ^ (-2 : ℝ) * MP.toReal) ^ (1 / 3 : ℝ)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let B : ℝ := CKN.Core.Endgame.startGammaConstant *
    ((1 / 2 : ℝ) * G + (1 / 2 : ℝ) ^ (-1 : ℝ) * G ^ (3 / 2 : ℝ) +
      (1 / 2 : ℝ) ^ (-1 : ℝ) * D * G ^ (1 / 2 : ℝ))
  have hStart : 0 ≤ CKN.Core.Endgame.startGammaConstant := by
    unfold CKN.Core.Endgame.startGammaConstant
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsolInt := hsol
  refine ⟨B, hB, ?_⟩
  intro x t ht
  have hQ2 : parabolicCylinder x t 2 ⊆
      spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0) := by
    intro z hz
    rcases mem_parabolicCylinder.mp hz with ⟨_hx, htlo, hthi⟩
    change z.1 ∈ Set.univ ∧ z.2 ∈ Ioo (-12 : ℝ) 0
    refine ⟨Set.mem_univ _, ?_⟩
    constructor
    · have htime : t - 4 < z.2 := by
        simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using htlo
      linarith only [htime, ht.1]
    · exact lt_of_le_of_lt hthi ht.2
  have hQ2closure : closure (parabolicCylinder x t 2) ⊆
      spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0) := by
    intro z hz
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 2)] at hz
    rcases hz with ⟨_hx, htI⟩
    change z.1 ∈ Set.univ ∧ z.2 ∈ Ioo (-12 : ℝ) 0
    refine ⟨Set.mem_univ _, ⟨?_, ?_⟩⟩
    · linarith only [htI.1, ht.1]
    · exact lt_of_le_of_lt htI.2 ht.2
  have hQ1closure : closure (parabolicCylinder x t 1) ⊆
      spaceTimeSet Set.univ (Ioo (-12 : ℝ) 0) := by
    intro z hz
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hz
    rcases hz with ⟨_hx, htI⟩
    change z.1 ∈ Set.univ ∧ z.2 ∈ Ioo (-12 : ℝ) 0
    refine ⟨Set.mem_univ _, ⟨?_, ?_⟩⟩
    · linarith only [htI.1, ht.1]
    · exact lt_of_le_of_lt htI.2 ht.2
  have hgamma : gamma U (x, t) 2 ≤ G := by
    have hmass : (∫⁻ z in parabolicCylinder x t 2,
        ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
        ∂(volume : Measure ParabolicPoint)) ≤ MU := by
      exact lintegral_mono_set hQ2
    have hreal : (∫⁻ z in parabolicCylinder x t 2,
        ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
        ∂(volume : Measure ParabolicPoint)).toReal ≤ MU.toReal :=
      ENNReal.toReal_mono hMU.ne hmass
    dsimp [G, gamma]
    gcongr
  have hdelta : delta q (x, t) 2 ≤ D := by
    have hmass : (∫⁻ z in parabolicCylinder x t 2,
        ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
        ∂(volume : Measure ParabolicPoint)) ≤ MP := by
      exact lintegral_mono_set hQ2
    have hreal : (∫⁻ z in parabolicCylinder x t 2,
        ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
        ∂(volume : Measure ParabolicPoint)).toReal ≤ MP.toReal :=
      ENNReal.toReal_mono hMP.ne hmass
    dsimp [D, delta]
    gcongr
  have hgammaNonneg : 0 ≤ gamma U (x, t) 2 := by
    unfold gamma
    positivity
  have hdeltaNonneg : 0 ≤ delta q (x, t) 2 := by
    unfold delta
    positivity
  have hdisplay := CKN.Core.Endgame.caccioppoli_gamma_display_fixed hsolInt
    (z := (x, t)) (r := 1) (ρ := 2) (by norm_num) (by norm_num)
    (by norm_num) hQ2closure
  have hdisplay' : alpha U (x, t) 1 + beta U DU (x, t) 1 ≤
      CKN.Core.Endgame.startGammaConstant *
        ((1 / 2 : ℝ) * gamma U (x, t) 2 +
          (1 / 2 : ℝ) ^ (-1 : ℝ) * gamma U (x, t) 2 ^ (3 / 2 : ℝ) +
          (1 / 2 : ℝ) ^ (-1 : ℝ) * delta q (x, t) 2 *
            gamma U (x, t) 2 ^ (1 / 2 : ℝ)) := by
    have hzero : CKN.lambda 3 (0 : ParabolicPoint → Vec3) (x, t) 2 = 0 := by
      simp [CKN.lambda, vec3EuclideanNorm_zero]
    rw [hzero] at hdisplay
    simpa using hdisplay
  have hRhs : CKN.Core.Endgame.startGammaConstant *
        ((1 / 2 : ℝ) * gamma U (x, t) 2 +
          (1 / 2 : ℝ) ^ (-1 : ℝ) * gamma U (x, t) 2 ^ (3 / 2 : ℝ) +
          (1 / 2 : ℝ) ^ (-1 : ℝ) * delta q (x, t) 2 *
            gamma U (x, t) 2 ^ (1 / 2 : ℝ)) ≤ B := by
    dsimp [B]
    gcongr
  have hAlpha : 0 ≤ alpha U (x, t) 1 := by
    unfold alpha
    positivity
  have hbeta : beta U DU (x, t) 1 ≤ B := by
    linarith only [hdisplay', hRhs, hAlpha]
  have hbetaNonneg : 0 ≤ beta U DU (x, t) 1 := by
    unfold beta
    positivity
  have hspatial := CKN.sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
    hsolInt (x, t) (by norm_num) hQ1closure
  have hdirichlet : (∫⁻ z in parabolicCylinder x t 1,
      ENNReal.ofReal (spatialGradientSq U DU z)
      ∂(volume : Measure ParabolicPoint)) ≤ ENNReal.ofReal (B ^ 2) := by
    rw [hspatial]
    apply ENNReal.ofReal_le_ofReal
    have hsquare : beta U DU (x, t) 1 ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
      pow_le_pow_left₀ hbetaNonneg hbeta 2
    simpa only [one_mul] using hsquare
  exact essLocal_matrixGradientEnergy_le_spatialGradientEnergy U DU x t 1 B hdirichlet

/-- A finite essential supremum of the spatial `L³` norm gives space-time
`L³` membership on every finite time interval. -/
theorem essLocal_globalVelocity_memLp_three
    (U : ParabolicPoint → Vec3) (hU : Measurable U) (J : Set ℝ)
    (hJ : volume J < ⊤)
    (hL3 : essSup (fun t : ℝ => eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
      (3 : ℝ≥0∞) volume) (volume.restrict J) < ⊤) :
    MemLp (fun z : Vec3 × ℝ => vec3EuclideanNorm (U (z.1, z.2)))
      (3 : ℝ≥0∞) (volume.prod (volume.restrict J)) := by
  let f : Vec3 × ℝ → ℝ := fun z => vec3EuclideanNorm (U (z.1, z.2))
  let μt : Measure ℝ := volume.restrict J
  have hf : Measurable f := by
    exact CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
      (hU.comp measurable_id)
  have hfae : AEMeasurable f (volume.prod μt) := hf.aemeasurable
  have hslice : ∀ᵐ t ∂μt, AEStronglyMeasurable (fun x : Vec3 => f (x, t)) volume :=
    hfae.aestronglyMeasurable.prodMk_right
  let A : ℝ≥0∞ := essSup (fun t : ℝ => eLpNorm
    (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
    (3 : ℝ≥0∞) volume) μt
  have hAtop : A < ⊤ := by simpa [A, μt] using hL3
  have hbound : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => f (x, t)) (3 : ℝ≥0∞) volume ≤ A := by
    exact ENNReal.ae_le_essSup
      (fun t : ℝ => eLpNorm (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
        (3 : ℝ≥0∞) volume)
  have hpow : AEMeasurable (fun z : Vec3 × ℝ => ‖f z‖ₑ ^ (3 : ℝ))
      (volume.prod μt) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hfae.enorm
  have hsliceEq : ∀ᵐ t ∂μt,
      eLpNorm (fun x : Vec3 => f (x, t)) (3 : ℝ≥0∞) volume ^ (3 : ℝ) =
        ∫⁻ x : Vec3, ‖f (x, t)‖ₑ ^ (3 : ℝ) ∂volume := by
    filter_upwards [hslice] with t ht
    exact eLpNorm_three_pow_eq_lintegral ht
  have hmass : (∫⁻ z : Vec3 × ℝ, ‖f z‖ₑ ^ (3 : ℝ)
      ∂(volume.prod μt)) < ⊤ := by
    calc
      (∫⁻ z : Vec3 × ℝ, ‖f z‖ₑ ^ (3 : ℝ) ∂(volume.prod μt)) =
          ∫⁻ t, ∫⁻ x : Vec3, ‖f (x, t)‖ₑ ^ (3 : ℝ) ∂volume ∂μt :=
      (lintegral_prod_symm _ hpow)
      _ =
          ∫⁻ t, eLpNorm (fun x : Vec3 => f (x, t))
            (3 : ℝ≥0∞) volume ^ (3 : ℝ) ∂μt := by
              exact lintegral_congr_ae (hsliceEq.mono fun _ h => h.symm)
      _ ≤ ∫⁻ t, A ^ (3 : ℝ) ∂μt := lintegral_mono_ae <| by
            filter_upwards [hbound] with t ht
            exact ENNReal.rpow_le_rpow ht (by norm_num)
      _ = A ^ (3 : ℝ) * volume J := by
            rw [lintegral_const]
            simp [μt]
      _ < ⊤ := ENNReal.mul_lt_top
            (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAtop.ne) hJ
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hfae.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmass.ne

/-- The space-time integral of an integrable density outside expanding
spatial balls tends to zero. -/
theorem essLocal_exterior_lintegral_tendsto_zero
    (F : Vec3 × ℝ → ℝ≥0∞) (J : Set ℝ)
    (hF : AEMeasurable F (volume.prod (volume.restrict J)))
    (hFint : (∫⁻ z : Vec3 × ℝ, F z
      ∂(volume.prod (volume.restrict J))) ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫⁻ z in
      {z : Vec3 × ℝ | (n : ℝ) < vec3EuclideanNorm z.1}, F z
      ∂(volume.prod (volume.restrict J))) atTop (𝓝 0) := by
  let μ : Measure (Vec3 × ℝ) := volume.prod (volume.restrict J)
  let S : ℕ → Set (Vec3 × ℝ) := fun n =>
    {z | (n : ℝ) < vec3EuclideanNorm z.1}
  let G : ℕ → Vec3 × ℝ → ℝ≥0∞ := fun n => (S n).indicator F
  have hS : ∀ n, MeasurableSet (S n) := by
    intro n
    exact isOpen_lt continuous_const
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp continuous_fst) |>.measurableSet
  have hG : ∀ n, AEMeasurable (G n) μ := by
    intro n
    exact (aemeasurable_indicator_iff (hS n)).mpr hF.restrict
  have hanti : ∀ᵐ z ∂μ, Antitone (fun n => G n z) := by
    filter_upwards [] with z m n hmn
    dsimp [G, S]
    by_cases hn : (n : ℝ) < vec3EuclideanNorm z.1
    · have hm : (m : ℝ) < vec3EuclideanNorm z.1 := by
        exact lt_of_le_of_lt (by exact_mod_cast hmn) hn
      simp [hm, hn]
    · simp [hn]
  have hzero : ∀ᵐ z ∂μ, Tendsto (fun n => G n z) atTop (𝓝 0) := by
    filter_upwards [] with z
    obtain ⟨N, hN⟩ := exists_nat_gt (vec3EuclideanNorm z.1)
    have hevent : ∀ᶠ n : ℕ in atTop,
        ¬ (n : ℝ) < vec3EuclideanNorm z.1 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact not_lt_of_ge (le_trans hN.le hn')
    have heq : (fun n => G n z) =ᶠ[atTop] (fun _ => (0 : ℝ≥0∞)) := by
      filter_upwards [hevent] with n hn
      simp [G, S, hn]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have hG0 : (∫⁻ z, G 0 z ∂μ) ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ hFint.lt_top
    apply lintegral_mono
    intro z
    by_cases hz : z ∈ S 0
    · simp [G, hz]
    · simp [G, hz]
  have hmass : Tendsto (fun n => ∫⁻ z, G n z ∂μ) atTop (𝓝 0) := by
    simpa using (lintegral_tendsto_of_tendsto_of_antitone hG hanti hG0 hzero)
  have hEq (n : ℕ) : (∫⁻ z in S n, F z ∂μ) = ∫⁻ z, G n z ∂μ := by
    rw [← lintegral_indicator (hS n)]
  have hEqFun : (fun n : ℕ => ∫⁻ z in S n, F z ∂μ) =
      (fun n => ∫⁻ z, G n z ∂μ) := funext hEq
  rw [hEqFun]
  exact hmass

/-- A finite product-coordinate critical energy gives separate finite
velocity and pressure masses in CKN parabolic coordinates. -/
theorem essLocal_globalCriticalMasses_parabolic
    (U : ParabolicPoint → Vec3) (q : ParabolicPoint → ℝ) (J : Set ℝ)
    (hFtop : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤) :
    (∫⁻ z in spaceTimeSet Set.univ J,
      ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
      ∂(volume : Measure ParabolicPoint)) < ⊤ ∧
    (∫⁻ z in spaceTimeSet Set.univ J,
      ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
      ∂(volume : Measure ParabolicPoint)) < ⊤ := by
  have hUprod : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤ := by
    apply lt_of_le_of_lt ?_ hFtop
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_right (by positivity)
  have hqprod : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤ := by
    apply lt_of_le_of_lt ?_ hFtop
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_left (by positivity)
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict
      (Set.univ ×ˢ J) = volume.prod (volume.restrict J) := by
    have h := Measure.prod_restrict
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := Set.univ) (t := J)
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod Vec3 ℝ] using h.symm
  constructor
  · have hEq : (∫⁻ z in spaceTimeSet Set.univ J,
        ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
        ∂(volume : Measure ParabolicPoint)) =
      ∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ)
        ∂(volume.prod (volume.restrict J)) := by
      change (∫⁻ z, ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ)
          ∂((volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J))) = _
      rw [hmeasure]
    rw [hEq]
    exact hUprod
  · have hEq : (∫⁻ z in spaceTimeSet Set.univ J,
        ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
        ∂(volume : Measure ParabolicPoint)) =
      ∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
        ∂(volume.prod (volume.restrict J)) := by
      change (∫⁻ z, ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
          ∂((volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J))) = _
      rw [hmeasure]
    rw [hEq]
    exact hqprod

/-- A pressure `L^(3/2)` bound on a whole-space past cylinder transfers to
product coordinates. -/
theorem essLocal_pressure_memLp_product
    (q : ParabolicPoint → ℝ) (J : Set ℝ) (hJ : MeasurableSet J)
    (hq : MemLp q (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Set.univ J))) :
    MemLp (fun z : Vec3 × ℝ => q (parabolicHomeomorph.symm z))
      (3 / 2 : ℝ≥0∞)
      ((volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J)) := by
  have hset : MeasurableSet (spaceTimeSet Set.univ J) :=
    MeasurableSet.univ.prod hJ
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet Set.univ J =
      Set.univ ×ˢ J := by
    ext z
    change (parabolicHomeomorph.symm z).1 ∈ Set.univ ∧
      (parabolicHomeomorph.symm z).2 ∈ J ↔
        z.1 ∈ Set.univ ∧ z.2 ∈ J
    simp
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hset
  rw [hpre] at hmp
  have hprod := hq.comp_measurePreserving hmp
  change MemLp (fun z : Vec3 × ℝ => q (parabolicHomeomorph.symm z))
    (3 / 2 : ℝ≥0∞)
    ((volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J)) at hprod
  exact hprod

/-- The velocity and pressure hypotheses in the blow-up projection make the
critical energy density integrable on a finite past time interval. -/
theorem essLocal_globalCriticalEnergy_memLp
    (U : ParabolicPoint → Vec3) (q : ParabolicPoint → ℝ)
    (hU : Measurable U) (J : Set ℝ) (hJ : volume J < ⊤)
    (hJmeas : MeasurableSet J)
    (hL3 : essSup (fun t : ℝ => eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
      (3 : ℝ≥0∞) volume) (volume.restrict J) < ⊤)
    (hq : MemLp q (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Set.univ J))) :
    (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤ := by
  have hUmem := essLocal_globalVelocity_memLp_three U hU J hJ hL3
  have hUmass := eLpNorm_three_pow_eq_lintegral hUmem.aestronglyMeasurable
  have hUtop : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤ := by
    have hnorm := hUmem.eLpNorm_lt_top
    have hpow : eLpNorm (fun z : Vec3 × ℝ =>
        vec3EuclideanNorm (U (z.1, z.2)))
        (3 : ℝ≥0∞) (volume.prod (volume.restrict J)) ^ (3 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hnorm.ne
    rw [hUmass] at hpow
    have hmassEq : (∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ)
        ∂(volume.prod (volume.restrict J))) =
        ∫⁻ z : Vec3 × ℝ,
          ‖vec3EuclideanNorm (U (z.1, z.2))‖ₑ ^ (3 : ℝ)
          ∂(volume.prod (volume.restrict J)) := by
      apply lintegral_congr
      intro z
      rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
    rw [hmassEq]
    exact hpow
  have hqprod := essLocal_pressure_memLp_product q J hJmeas hq
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J) =
      volume.prod (volume.restrict J) := by
    have h := Measure.prod_restrict
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := Set.univ) (t := J)
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod Vec3 ℝ] using h.symm
  have hqprod' : MemLp (fun z : Vec3 × ℝ => q (parabolicHomeomorph.symm z))
      (3 / 2 : ℝ≥0∞) (volume.prod (volume.restrict J)) := by
    rw [← hmeasure]
    exact hqprod
  have hpne : (3 / 2 : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hqmass := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (3 / 2 : ℝ≥0∞)) (by norm_num) hpne hqprod'.eLpNorm_lt_top
  have hqtop : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
      ∂(volume.prod (volume.restrict J))) < ⊤ := by
    have htoReal : (3 / 2 : ℝ≥0∞).toReal = (3 / 2 : ℝ) := by norm_num
    rw [htoReal] at hqmass
    have hmassEq : (∫⁻ z : Vec3 × ℝ,
        ‖q (parabolicHomeomorph.symm z)‖ₑ ^ (3 / 2 : ℝ)
        ∂(volume.prod (volume.restrict J))) =
        (∫⁻ z : Vec3 × ℝ,
          ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
          ∂(volume.prod (volume.restrict J))) := by
      apply lintegral_congr
      intro z
      rw [show q (parabolicHomeomorph.symm z) = q ((z.1, z.2) : ParabolicPoint) by
        cases z
        rfl, Real.enorm_eq_ofReal_abs]
    rw [hmassEq] at hqmass
    exact hqmass
  have hUmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal
        (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ))
      (volume.prod (volume.restrict J)) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
          (hU.comp measurable_id)).aemeasurable)
  have hEq : (∫⁻ z : Vec3 × ℝ,
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
      ∂(volume.prod (volume.restrict J))) =
      (∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ)
        ∂(volume.prod (volume.restrict J))) +
      (∫⁻ z : Vec3 × ℝ,
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
        ∂(volume.prod (volume.restrict J))) := by
    rw [lintegral_add_left' hUmeas]
  rw [hEq]
  exact ENNReal.add_lt_top.mpr ⟨hUtop, hqtop⟩

/-- The critical velocity and pressure masses outside large spatial balls
are uniformly small. -/
theorem essLocal_exteriorCriticalTail
    (U : ParabolicPoint → Vec3) (q : ParabolicPoint → ℝ)
    (hU : Measurable U) (J : Set ℝ) (hJ : volume J < ⊤)
    (hJmeas : MeasurableSet J)
    (hL3 : essSup (fun t : ℝ => eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
      (3 : ℝ≥0∞) volume) (volume.restrict J) < ⊤)
    (hq : MemLp q (3 / 2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet Set.univ J)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ z in {z : Vec3 × ℝ | (n : ℝ) < vec3EuclideanNorm z.1},
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
          ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
        ∂(volume.prod (volume.restrict J))) < ε := by
  have hUmem := essLocal_globalVelocity_memLp_three U hU J hJ hL3
  have hqprod := essLocal_pressure_memLp_product q J hJmeas hq
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict (Set.univ ×ˢ J) =
      volume.prod (volume.restrict J) := by
    have h := Measure.prod_restrict
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := Set.univ) (t := J)
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod Vec3 ℝ] using h.symm
  have hqprod' : MemLp (fun z : Vec3 × ℝ => q (parabolicHomeomorph.symm z))
      (3 / 2 : ℝ≥0∞) (volume.prod (volume.restrict J)) := by
    rw [← hmeasure]
    exact hqprod
  have hqpair : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => q ((z.1, z.2) : ParabolicPoint))
      (volume.prod (volume.restrict J)) := by
    convert hqprod'.aestronglyMeasurable using 1
    funext z
    cases z
    rfl
  have hUmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal
        (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ))
      (volume.prod (volume.restrict J)) := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
          (hU.comp measurable_id)).aemeasurable)
  have hqmeas : AEMeasurable
      (fun z : Vec3 × ℝ => ENNReal.ofReal
        |q ((z.1, z.2) : ParabolicPoint)| ^ (3 / 2 : ℝ))
      (volume.prod (volume.restrict J)) := by
    have hnorm : AEMeasurable
        (fun z : Vec3 × ℝ => ‖q ((z.1, z.2) : ParabolicPoint)‖ₑ)
        (volume.prod (volume.restrict J)) := hqpair.enorm
    convert ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hnorm
      using 1
    · funext z
      exact congrArg (fun y : ℝ≥0∞ => y ^ (3 / 2 : ℝ))
        (Real.enorm_eq_ofReal_abs _).symm
  have hFmeas : AEMeasurable
      (fun z : Vec3 × ℝ =>
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
          ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ))
      (volume.prod (volume.restrict J)) := hUmeas.add hqmeas
  have hFtop := essLocal_globalCriticalEnergy_memLp U q hU J hJ hJmeas hL3 hq
  have htail := essLocal_exterior_lintegral_tendsto_zero
    (fun z : Vec3 × ℝ =>
      ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
        ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)) J hFmeas (ne_of_lt hFtop)
  have hev : ∀ᶠ n : ℕ in atTop,
      (∫⁻ z in {z : Vec3 × ℝ | (n : ℝ) < vec3EuclideanNorm z.1},
        ENNReal.ofReal (vec3EuclideanNorm (U (z.1, z.2))) ^ (3 : ℝ) +
          ENNReal.ofReal |q (z.1, z.2)| ^ (3 / 2 : ℝ)
        ∂(volume.prod (volume.restrict J))) < ε :=
    htail.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact ⟨N, fun n hn => hN n hn⟩

/-- On a set whose times lie in `J`, integration against the product
restriction agrees with integration against full space-time volume. -/
theorem essLocal_setIntegral_eq_productTimeRestriction
    (J : Set ℝ) (S : Set (Vec3 × ℝ))
    (hS : S ⊆ Set.univ ×ˢ J) (F : Vec3 × ℝ → ℝ≥0∞) :
    (∫⁻ z in S, F z ∂(volume : Measure (Vec3 × ℝ))) =
      ∫⁻ z in S, F z ∂(volume.prod (volume.restrict J)) := by
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict
      (Set.univ ×ˢ J) = volume.prod (volume.restrict J) := by
    have h := Measure.prod_restrict
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := Set.univ) (t := J)
    simpa only [Measure.restrict_univ, Measure.volume_eq_prod Vec3 ℝ] using h.symm
  have hrestrict : (volume : Measure (Vec3 × ℝ)).restrict S =
      (volume.prod (volume.restrict J)).restrict S := by
    rw [← hmeasure, Measure.restrict_restrict_of_subset hS]
  change (∫⁻ z, F z ∂(volume.restrict S)) =
    ∫⁻ z, F z ∂((volume.prod (volume.restrict J)).restrict S)
  rw [hrestrict]

end ESS
