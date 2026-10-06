/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.TenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevSupport
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Applications of Leray–Hopf energy interpolation

These consequences provide the energy-only estimate and tensor integrability
used in `lem:u-ten-thirds` and `thm:assoc-pressure`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The initial-energy consequence of `lem:u-ten-thirds`. The right-hand
side is the datum's squared `L²` mass raised to the `5/3` power. -/
theorem lerayHopf_tenThirds_initial_energy_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
      energyTenThirdsConstant *
        ((∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) ^
          (2 / 3 : ℝ) *
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))) := by
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let A : ℝ≥0∞ := ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)
  let B : ℝ≥0∞ := essSup
    (fun s : ℝ => ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ))
    (volume.restrict (Ioo 0 T))
  let G : ℝ≥0∞ := ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)
  let half : ℝ≥0∞ := ENNReal.ofReal (1 / 2 : ℝ)
  have hT : 0 < T := by
    rcases hLH with ⟨h, _, _, _, _, _, _, _, _, _, _, _⟩
    exact h
  have hEnergy : ∀ t₀ : ℝ, t₀ ∈ Icc 0 T →
      half * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z) ≤ half * A := by
    rcases hLH with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
    simpa [half, A] using h
  have hKineticBound : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ)) ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsIcc : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
    have hEnergyS := hEnergy s hsIcc
    apply (ENNReal.mul_le_mul_iff_right
      (by norm_num [half] : half ≠ 0)
      (by norm_num [half] : half ≠ ⊤)).mp
    exact le_trans (le_add_right le_rfl) hEnergyS
  have hBbound : B ≤ A := essSup_le_of_ae_le _ hKineticBound
  have hGhalf : G ≤ half * A := by
    have hEnergyT := hEnergy T ⟨le_of_lt hT, le_rfl⟩
    dsimp [G, Q]
    exact (le_add_left le_rfl).trans hEnergyT
  have hGbound : G ≤ A := by
    calc
      G ≤ half * A := hGhalf
      _ ≤ A := by
        calc
          half * A ≤ 1 * A :=
            mul_le_mul_of_nonneg_right (by norm_num [half] : half ≤ 1) (by positivity)
          _ = A := one_mul _
  have hmain := (lerayHopf_memLp_tenThirds hLH).2
  have hmassBound :
      (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
        energyTenThirdsConstant * (B ^ (2 / 3 : ℝ) * G) := by
    simpa [Q, B, G] using hmain
  calc
    (∫⁻ z in Q, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)) ≤
        energyTenThirdsConstant * (B ^ (2 / 3 : ℝ) * G) := hmassBound
    _ ≤ energyTenThirdsConstant * (A ^ (2 / 3 : ℝ) * A) := by
      gcongr
    _ = energyTenThirdsConstant *
          ((∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) ^
            (2 / 3 : ℝ) *
            (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))) := by
      rfl

/-- The velocity tensor of a Leray–Hopf solution has componentwise
space-time `L^{5/3}` integrability, as used by `thm:assoc-pressure`. -/
theorem lerayHopf_tensor_memLp_fiveThirds
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ i j : Fin 3,
      MemLp (fun z : ParabolicPoint => u z i * u z j)
        (ENNReal.ofReal (5 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hmem := (lerayHopf_memLp_tenThirds hLH).1
  let : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 10 / 3),
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 5 / 3),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  intro i j
  have hi : MemLp (fun z : ParabolicPoint => u z i)
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) :=
    (memLp_pi_iff.mp hmem) i
  have hj : MemLp (fun z : ParabolicPoint => u z j)
      (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) :=
    (memLp_pi_iff.mp hmem) j
  have hfun : (fun z : ParabolicPoint => u z i * u z j) =
      (fun z => u z i) * (fun z => u z j) := by
    funext z
    rfl
  rw [hfun]
  exact hi.mul hj

private theorem vec3Euclidean_mass_lt_top {a : Vec3 → Vec3}
    (ha : MemLp a 2 volume) :
    (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) < ⊤ := by
  have hmass : (∫⁻ x : Vec3, ‖a x‖ₑ ^ (2 : ℝ)) < ⊤ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      ha.aestronglyMeasurable).mp ha.eLpNorm_lt_top
  refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (by norm_num : (3 : ℝ≥0∞) < ⊤) hmass)
  calc
    (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) ≤
        ∫⁻ x : Vec3, 3 * ‖a x‖ₑ ^ (2 : ℝ) :=
      lintegral_mono fun x => vec3Euclidean_sq_le_three_enorm_sq (a x)
    _ = 3 * (∫⁻ x : Vec3, ‖a x‖ₑ ^ (2 : ℝ)) := by
      rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by norm_num)]

private theorem lintegral_three_le_two_tenThirds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (W : α → ℝ≥0∞) (hW : AEMeasurable W μ) :
    (∫⁻ q, W q ^ (3 : ℝ) ∂μ) ≤
      (∫⁻ q, W q ^ (2 : ℝ) ∂μ) ^ (1 / 4 : ℝ) *
        (∫⁻ q, W q ^ (10 / 3 : ℝ) ∂μ) ^ (3 / 4 : ℝ) := by
  let f : α → ℝ≥0∞ := fun q => W q ^ (1 / 2 : ℝ)
  let g : α → ℝ≥0∞ := fun q => W q ^ (5 / 2 : ℝ)
  have hfmeas : AEMeasurable f μ :=
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).measurable.comp_aemeasurable hW
  have hgmeas : AEMeasurable g μ :=
    (ENNReal.continuous_rpow_const (y := (5 / 2 : ℝ))).measurable.comp_aemeasurable hW
  have hf4 (q : α) : f q ^ (4 : ℝ) = W q ^ (2 : ℝ) := by
    dsimp [f]
    rw [← ENNReal.rpow_mul]
    congr 1
    norm_num
  have hgFourThirds (q : α) : g q ^ (4 / 3 : ℝ) = W q ^ (10 / 3 : ℝ) := by
    dsimp [g]
    rw [← ENNReal.rpow_mul]
    congr 1
    norm_num
  have hfg (q : α) : f q * g q = W q ^ (3 : ℝ) := by
    dsimp [f, g]
    by_cases hzero : W q = 0
    · simp [hzero]
    · by_cases htop : W q = ⊤
      · simp [htop]
      · rw [← ENNReal.rpow_add _ _ hzero htop]
        norm_num
  have hHolder := ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr
    (p := (1 : ℝ)) (q := (4 : ℝ)) (r := (4 / 3 : ℝ))
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 4)
    (by norm_num : (1 : ℝ) / 1 = (1 : ℝ) / 4 + (1 : ℝ) / (4 / 3))
    μ hfmeas hgmeas
  have hF4 : (∫⁻ q, f q ^ (4 : ℝ) ∂μ) = ∫⁻ q, W q ^ (2 : ℝ) ∂μ :=
    lintegral_congr fun q => hf4 q
  have hGFourThirds : (∫⁻ q, g q ^ (4 / 3 : ℝ) ∂μ) =
      ∫⁻ q, W q ^ (10 / 3 : ℝ) ∂μ :=
    lintegral_congr fun q => hgFourThirds q
  calc
    (∫⁻ q, W q ^ (3 : ℝ) ∂μ) = ∫⁻ q, (f q * g q) ^ (1 : ℝ) ∂μ := by
      apply lintegral_congr
      intro q
      rw [ENNReal.rpow_one, hfg q]
    _ ≤ (∫⁻ q, f q ^ (4 : ℝ) ∂μ) ^ (1 / 4 : ℝ) *
        (∫⁻ q, g q ^ (4 / 3 : ℝ) ∂μ) ^ (3 / 4 : ℝ) := by
      simpa [ENNReal.rpow_one] using hHolder
    _ = _ := by rw [hF4, hGFourThirds]

/-- The finite-time `L³` consequence in `eq:u-three`, with the datum energy
written as its squared Euclidean `L²` mass. -/
theorem lerayHopf_memLp_three_with_energy_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du) :
    MemLp u (ENNReal.ofReal 3)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) ≤
        energyTenThirdsConstant ^ (3 / 4 : ℝ) *
          ENNReal.ofReal T ^ (1 / 4 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) ^
              (3 / 2 : ℝ) := by
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let U : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  let μ : Measure ParabolicPoint := volume.restrict Q
  let μU : Measure (Vec3 × ℝ) := volume.restrict U
  let A : ℝ≥0∞ := ∫⁻ x : Vec3,
    ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)
  let M2 : ℝ≥0∞ := ∫⁻ z in Q,
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ)
  let M3 : ℝ≥0∞ := ∫⁻ z in Q,
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)
  let M10 : ℝ≥0∞ := ∫⁻ z in Q,
    ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)
  let C : ℝ≥0∞ := energyTenThirdsConstant
  let half : ℝ≥0∞ := ENNReal.ofReal (1 / 2 : ℝ)
  let W : Vec3 × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (vec3EuclideanNorm (u (parabolicHomeomorph.symm q)))
  have hAtop : A < ⊤ := vec3Euclidean_mass_lt_top hLH.2.1.1
  have hCtop : C < ⊤ := by
    dsimp [C]
    unfold energyTenThirdsConstant
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num))
      ENNReal.ofReal_lt_top
  have hQmeas : AEStronglyMeasurable u μ := by
    simpa [μ, Q] using hLH.2.2.1
  have hNmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) μ :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hQmeas
  have hQMP : MeasureTheory.Measure.QuasiMeasurePreserving parabolicHomeomorph.symm
      μU μ := by
    apply parabolicHomeomorphSymm_measurePreserving.quasiMeasurePreserving.restrict
    intro q hq
    exact hq
  have hWmeas : AEStronglyMeasurable W μU := by
    dsimp [W]
    exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      (hNmeas.comp_quasiMeasurePreserving hQMP))
  have hEnergy : ∀ t₀ : ℝ, t₀ ∈ Icc 0 T →
      half * (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ)) +
          ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z) ≤ half * A := by
    rcases hLH with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
    simpa [half, A] using h
  have hKineticBound : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ)) ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hsIcc : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
    have hEnergyS := hEnergy s hsIcc
    apply (ENNReal.mul_le_mul_iff_right
      (by norm_num [half] : half ≠ 0)
      (by norm_num [half] : half ≠ ⊤)).mp
    exact le_trans (le_add_right le_rfl) hEnergyS
  have hM2coordinate : M2 =
      ∫⁻ q in U, W q ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [M2, Q, U, W] using
      (setLIntegral_parabolic_to_product
        (Ω := (Set.univ : Set Vec3)) (I := Ioo 0 T)
        (F := fun z : ParabolicPoint =>
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ)))
  have hM3coordinate : M3 =
      ∫⁻ q in U, W q ^ (3 : ℝ) ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [M3, Q, U, W] using
      (setLIntegral_parabolic_to_product
        (Ω := (Set.univ : Set Vec3)) (I := Ioo 0 T)
        (F := fun z : ParabolicPoint =>
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)))
  have hM10coordinate : M10 =
      ∫⁻ q in U, W q ^ (10 / 3 : ℝ) ∂(volume : Measure (Vec3 × ℝ)) := by
    simpa [M10, Q, U, W] using
      (setLIntegral_parabolic_to_product
        (Ω := (Set.univ : Set Vec3)) (I := Ioo 0 T)
        (F := fun z : ParabolicPoint =>
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (10 / 3 : ℝ)))
  have hW2meas : AEMeasurable (fun q : Vec3 × ℝ => W q ^ (2 : ℝ)) μU :=
    (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp_aemeasurable
      hWmeas.aemeasurable
  have hM2Tonelli :
      (∫⁻ q in U, W q ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ))) =
        ∫⁻ s in Ioo 0 T, ∫⁻ x : Vec3, W (x, s) ^ (2 : ℝ) := by
    change (∫⁻ q in (Set.univ : Set Vec3) ×ˢ Ioo 0 T,
        W q ^ (2 : ℝ) ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
    have h := MeasureTheory.setLIntegral_prod_symm
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ))
      (s := (Set.univ : Set Vec3)) (t := Ioo 0 T)
      (fun q : Vec3 × ℝ => W q ^ (2 : ℝ)) hW2meas
    simpa only [Prod.fst, Prod.snd, Measure.restrict_univ] using h
  have hM2energy : M2 ≤ ENNReal.ofReal T * A := by
    calc
      M2 = ∫⁻ q in U, W q ^ (2 : ℝ) ∂(volume : Measure (Vec3 × ℝ)) :=
        hM2coordinate
      _ = ∫⁻ s in Ioo 0 T, ∫⁻ x : Vec3, W (x, s) ^ (2 : ℝ) := hM2Tonelli
      _ = ∫⁻ s in Ioo 0 T, ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ) := by
        simp only [W, CKN.Foundation.Parabolic.parabolicHomeomorph_symm_apply]
      _ ≤ ∫⁻ s in Ioo 0 T, A := lintegral_mono_ae hKineticBound
      _ = ENNReal.ofReal T * A := by
        rw [lintegral_const]
        simp [Real.volume_Ioo, mul_comm]
  have hM10energy : M10 ≤ C * (A ^ (2 / 3 : ℝ) * A) := by
    simpa [M10, Q, C, A] using
      (lerayHopf_tenThirds_initial_energy_bound hLH)
  have hM3holder : M3 ≤ M2 ^ (1 / 4 : ℝ) * M10 ^ (3 / 4 : ℝ) := by
    rw [hM3coordinate, hM2coordinate, hM10coordinate]
    exact lintegral_three_le_two_tenThirds μU W hWmeas.aemeasurable
  have hApowTop : A ^ (2 / 3 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hAtop.ne
  have hM10top : M10 < ⊤ :=
    lt_of_le_of_lt hM10energy
      (ENNReal.mul_lt_top hCtop (ENNReal.mul_lt_top hApowTop hAtop))
  have hM2top : M2 < ⊤ :=
    lt_of_le_of_lt hM2energy
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAtop)
  have hM3top : M3 < ⊤ :=
    lt_of_le_of_lt hM3holder
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM2top.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hM10top.ne))
  have hSupM3top :
      (∫⁻ z in Q, ‖u z‖ₑ ^ (3 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono ?_) hM3top
    intro z
    calc
      ‖u z‖ₑ ^ (3 : ℝ) = ENNReal.ofReal (‖u z‖ ^ (3 : ℝ)) := by
        rw [← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      _ ≤ ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℝ)) :=
        ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (norm_nonneg _) (norm_le_vec3EuclideanNorm _)
            (by norm_num))
      _ = ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) := by
        rw [(ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg _)
          (by norm_num)).symm]
  have hMemThree : MemLp u (ENNReal.ofReal 3) μ := by
    rw [memLp_iff,
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : ENNReal.ofReal 3 ≠ 0) ENNReal.ofReal_ne_top hQmeas,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3)]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSupM3top.ne
  have hThreeEnergy :
      M3 ≤ C ^ (3 / 4 : ℝ) * ENNReal.ofReal T ^ (1 / 4 : ℝ) *
        A ^ (3 / 2 : ℝ) := by
    calc
      M3 ≤ M2 ^ (1 / 4 : ℝ) * M10 ^ (3 / 4 : ℝ) := hM3holder
      _ ≤ (ENNReal.ofReal T * A) ^ (1 / 4 : ℝ) *
            (C * (A ^ (2 / 3 : ℝ) * A)) ^ (3 / 4 : ℝ) := by
        gcongr
      _ = C ^ (3 / 4 : ℝ) * ENNReal.ofReal T ^ (1 / 4 : ℝ) *
            A ^ (3 / 2 : ℝ) := by
        by_cases hAzero : A = 0
        · simp [hAzero]
        calc
          (ENNReal.ofReal T * A) ^ (1 / 4 : ℝ) *
              (C * (A ^ (2 / 3 : ℝ) * A)) ^ (3 / 4 : ℝ) =
            ENNReal.ofReal T ^ (1 / 4 : ℝ) * A ^ (1 / 4 : ℝ) *
              (C ^ (3 / 4 : ℝ) *
                ((A ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) * A ^ (3 / 4 : ℝ))) := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4),
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4),
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 4)]
          _ = ENNReal.ofReal T ^ (1 / 4 : ℝ) * C ^ (3 / 4 : ℝ) *
                ((A ^ (1 / 4 : ℝ) * A ^ (1 / 2 : ℝ)) * A ^ (3 / 4 : ℝ)) := by
              rw [← ENNReal.rpow_mul]
              have he : (2 / 3 : ℝ) * (3 / 4 : ℝ) = 1 / 2 := by norm_num
              rw [he]
              ac_rfl
          _ = ENNReal.ofReal T ^ (1 / 4 : ℝ) * C ^ (3 / 4 : ℝ) *
                (A ^ (3 / 4 : ℝ) * A ^ (3 / 4 : ℝ)) := by
              rw [← ENNReal.rpow_add _ _ hAzero (ne_of_lt hAtop)]
              norm_num
          _ = ENNReal.ofReal T ^ (1 / 4 : ℝ) * C ^ (3 / 4 : ℝ) *
                A ^ (3 / 2 : ℝ) := by
              rw [← ENNReal.rpow_add _ _ hAzero (ne_of_lt hAtop)]
              norm_num
          _ = C ^ (3 / 4 : ℝ) * ENNReal.ofReal T ^ (1 / 4 : ℝ) *
                A ^ (3 / 2 : ℝ) := by ac_rfl
  refine ⟨?_, ?_⟩
  · simpa [μ, Q] using hMemThree
  · simpa [M3, C, A, Q] using hThreeEnergy

end CKN

end
