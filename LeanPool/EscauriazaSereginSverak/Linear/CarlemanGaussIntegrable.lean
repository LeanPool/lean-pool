/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussIntegralTools
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanCoreLocalDerivs

/-!
# Integrability of the Gaussian heat density

The heat density in `prop:carleman-gauss` is smooth where the weight is
defined and has compact support in the positive-time cylinder.
-/

public section


open CKN CKN.Foundation.Parabolic Set MeasureTheory

noncomputable section

namespace ESS

/-- The product norm on parabolic space-time used in this identity. -/
local instance gaussIntegrableNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance gaussIntegrableNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The original Gaussian weight is smooth on the positive-time cylinder. -/
theorem gauss_original_weight_contDiffOn (a : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)))
      (spaceTimeSet univ (Ioo (0 : ℝ) 2)) := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have htime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => gaussCarlemanTimeWeight z.2) := by
    unfold gaussCarlemanTimeWeight
    fun_prop
  have htime_ne : ∀ z ∈ U, gaussCarlemanTimeWeight z.2 ≠ 0 := by
    intro z hz
    unfold gaussCarlemanTimeWeight
    exact ne_of_gt (mul_pos hz.2.1 (Real.exp_pos _))
  have htimepow : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => gaussCarlemanTimeWeight z.2 ^ (-2 * a)) U :=
    htime.contDiffOn.rpow_const_of_ne htime_ne
  have hQ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => ∑ i : Fin 3, z.1 i ^ 2) := by
    fun_prop
  have hden : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => 4 * z.2) := by fun_prop
  have hden_ne : ∀ z ∈ U, (4 : ℝ) * z.2 ≠ 0 := by
    intro z hz
    exact mul_ne_zero (by norm_num) (ne_of_gt hz.2.1)
  have hG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) U := by
    have hG0 : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint =>
          Real.exp (-(∑ i : Fin 3, z.1 i ^ 2) * (4 * z.2)⁻¹)) U :=
      (hQ.contDiffOn.neg.mul (hden.contDiffOn.inv hden_ne)).exp
    apply hG0.congr
    intro z hz
    rw [gauss_vec3EuclideanNorm_sq]
    ring_nf
  exact htimepow.mul hG

/-- The squared vector heat density is smooth and has no support outside the
original vector field. -/
theorem gauss_heat_density_smooth_support
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) ∧
    HasCompactSupport (fun z : ParabolicPoint =>
      vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
        ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) ∧
    tsupport (fun z : ParabolicPoint =>
      vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
        ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) ⊆ tsupport w := by
  let H : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
      ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2
  have hcomponent (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => timePartial (fun y => w y i) z +
        scalarLaplacian (fun y => w y i) z) := by
    have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z i) := by
      fun_prop
    have ht := CKN.contDiff_timePartial hwi
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => scalarLaplacian (fun y => w y i) z) := by
      unfold scalarLaplacian
      apply ContDiff.sum
      intro j hj
      exact CKN.spatialPartial_contDiff
        (CKN.spatialPartial_contDiff hwi j) j
    exact ht.add hs
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    have heq : H = fun z : ParabolicPoint => ∑ i : Fin 3,
        (timePartial (fun y => w y i) z +
          scalarLaplacian (fun y => w y i) z) ^ 2 := by
      funext z
      exact gauss_heatVec_norm_sq w z
    rw [heq]
    exact ContDiff.sum (fun i _ => (hcomponent i).pow 2)
  have hzero (z : ParabolicPoint) (hz : z ∉ tsupport w) : H z = 0 := by
    have hheat : (fun i : Fin 3 => timePartial (fun y => w y i) z +
        ∑ j, spatialSecondPartial (fun y => w y i) j j z) = 0 := by
      funext i
      obtain ⟨_, ht, hs⟩ := gauss_component_zero_outside w z hz i
      simp [ht, fun j => (hs j).2]
    simp [H, hheat, vec3EuclideanNorm_zero]
  have hHs : tsupport H ⊆ tsupport w := by
    apply closure_minimal _ (isClosed_tsupport w)
    intro z hz
    by_contra hnot
    exact hz (hzero z hnot)
  have hHc : HasCompactSupport H :=
    hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) hHs
  exact ⟨hH, hHc, hHs⟩

/-- The right-hand heat density of `prop:carleman-gauss` is integrable. -/
theorem gauss_original_heat_integrable (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ =>
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  obtain ⟨hH, hHc, hHs⟩ := gauss_heat_density_smooth_support w hw hwc
  exact integrable_mul_of_tsupport hU (gauss_original_weight_contDiffOn a)
    hH hHc (hHs.trans hwU)

/-- The coefficient of the conjugated heat energy is smooth on positive time. -/
theorem gauss_phase_energy_coefficient_contDiffOn (q : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        z.2 ^ 2 * Real.exp (2 * gaussCarlemanPhase q z))
      (spaceTimeSet univ (Ioo (0 : ℝ) 2)) := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun z : ParabolicPoint => z.2 ^ 2) := by
    fun_prop
  have htwo : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun _ : ParabolicPoint => (2 : ℝ))
      (spaceTimeSet univ (Ioo (0 : ℝ) 2)) := contDiffOn_const
  exact ht.contDiffOn.mul
    ((htwo.mul (gaussCarlemanPhase_contDiffOn q)).exp)

/-- The conjugated vector heat energy is integrable on space-time. -/
theorem gauss_conjugated_heat_integrable (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 *
      ∑ i : Fin 3, carlemanConj (gaussCarlemanPhase q)
        (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  let φ := gaussCarlemanPhase q
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U := gaussCarlemanPhase_contDiffOn q
  have hcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 ^ 2 * Real.exp (2 * φ z)) U :=
    gauss_phase_energy_coefficient_contDiffOn q
  obtain ⟨hH, hHc, hHs⟩ := gauss_heat_density_smooth_support w hw hwc
  have hint : Integrable (fun z : Vec3 × ℝ =>
      (z.2 ^ 2 * Real.exp (2 * φ z)) *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) volume :=
    integrable_mul_of_tsupport hU hcoeff hH hHc (hHs.trans hwU)
  have heq : (fun z : Vec3 × ℝ => z.2 ^ 2 *
      ∑ i : Fin 3, carlemanConj φ
        (fun y => Real.exp (φ y) * w y i) z ^ 2) =
      (fun z : Vec3 × ℝ => (z.2 ^ 2 * Real.exp (2 * φ z)) *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) := by
    funext z
    rw [gauss_vector_conjugated_heat_sq_global q w hw hwU z]
    rw [show Real.exp (2 * φ z) = Real.exp (φ z) ^ 2 by
      rw [show 2 * φ z = φ z + φ z by ring, Real.exp_add, pow_two]]
    ring
  rw [heq]
  exact hint

/-- Each scalar conjugated heat energy is integrable. -/
theorem gauss_component_conjugated_heat_integrable (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 *
      carlemanConj (gaussCarlemanPhase q)
        (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  let φ := gaussCarlemanPhase q
  let L : ParabolicPoint → ℝ := fun z =>
    timePartial (fun y => w y i) z + scalarLaplacian (fun y => w y i) z
  have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => w z i) := by
    fun_prop
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := by
    have ht := CKN.contDiff_timePartial hwi
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => scalarLaplacian (fun y => w y i) z) := by
      unfold scalarLaplacian
      apply ContDiff.sum
      intro j hj
      exact CKN.spatialPartial_contDiff
        (CKN.spatialPartial_contDiff hwi j) j
    exact ht.add hs
  have hLzero (z : ParabolicPoint) (hz : z ∉ tsupport w) : L z = 0 := by
    obtain ⟨_, ht, hs⟩ := gauss_component_zero_outside w z hz i
    dsimp [L, scalarLaplacian]
    simp [ht, fun j => (hs j).2]
  have hLs : tsupport (fun z => L z ^ 2) ⊆ tsupport w := by
    apply closure_minimal _ (isClosed_tsupport w)
    intro z hz
    by_contra hnot
    exact hz (by simp [hLzero z hnot])
  have hLc : HasCompactSupport (fun z => L z ^ 2) :=
    hwc.isCompact.of_isClosed_subset (isClosed_tsupport _) hLs
  have hint : Integrable (fun z : Vec3 × ℝ =>
      (z.2 ^ 2 * Real.exp (2 * φ z)) * L z ^ 2) volume :=
    integrable_mul_of_tsupport hU (gauss_phase_energy_coefficient_contDiffOn q)
      (hL.pow 2) hLc (hLs.trans hwU)
  have heq : (fun z : Vec3 × ℝ => z.2 ^ 2 *
      carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2) =
      (fun z : Vec3 × ℝ => (z.2 ^ 2 * Real.exp (2 * φ z)) * L z ^ 2) := by
    funext z
    rw [gauss_component_conjugation_global q w hw hwU i z]
    rw [show Real.exp (2 * φ z) = Real.exp (φ z) ^ 2 by
      rw [show 2 * φ z = φ z + φ z by ring, Real.exp_add, pow_two]]
    ring
  rw [heq]
  exact hint

/-- The Gaussian commutator mass density is integrable for a smooth
compactly supported scalar field. -/
theorem gauss_mass_integrable (q : ℝ) (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport (show Vec3 × ℝ → ℝ from v)) :
    Integrable (fun z : Vec3 × ℝ => q / 3 * z.2 * v z ^ 2) volume := by
  have hcont : Continuous (fun z : Vec3 × ℝ => q / 3 * z.2 * v z ^ 2) := by
    fun_prop
  have hsupp : tsupport (fun z : Vec3 × ℝ => v z ^ 2) ⊆
      tsupport (show Vec3 × ℝ → ℝ from v) := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro z hz
    by_contra hnot
    have hv0 : v z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from v) hnot
    exact hz (by simp [hv0])
  have hv2c : HasCompactSupport (fun z : Vec3 × ℝ => v z ^ 2) := by
    exact hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hcompact : HasCompactSupport
      (fun z : Vec3 × ℝ => q / 3 * z.2 * v z ^ 2) := by
    exact hv2c.mul_left
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The Gaussian cross integral satisfies the sharp Young form of the
Cauchy–Schwarz bound from `eq:carleman-E`. -/
theorem gauss_cross_integral_le (q : ℝ) (hq : 1 ≤ q)
    (v L : ParabolicPoint → ℝ)
    (hvU : tsupport (show Vec3 × ℝ → ℝ from v) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (hC : Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * v z * L z) volume)
    (hI : Integrable (fun z : Vec3 × ℝ => q / 3 * z.2 * v z ^ 2) volume)
    (hP : Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * L z ^ 2) volume) :
    |∫ z : Vec3 × ℝ, z.2 ^ 2 * v z * L z ∂volume| ≤
      Real.sqrt 6 / 2 *
        ((∫ z : Vec3 × ℝ, q / 3 * z.2 * v z ^ 2 ∂volume) +
          ∫ z : Vec3 × ℝ, z.2 ^ 2 * L z ^ 2 ∂volume) := by
  have hright : Integrable (fun z : Vec3 × ℝ =>
      Real.sqrt 6 / 2 *
        (q / 3 * z.2 * v z ^ 2 + z.2 ^ 2 * L z ^ 2)) volume :=
    (hI.add hP).const_mul _
  have hpoint (z : Vec3 × ℝ) :
      |z.2 ^ 2 * v z * L z| ≤ Real.sqrt 6 / 2 *
        (q / 3 * z.2 * v z ^ 2 + z.2 ^ 2 * L z ^ 2) := by
    by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
    · exact gaussCarleman_cross_pointwise hq hz.2.1 hz.2.2
    · have hnot : z ∉ tsupport (show Vec3 × ℝ → ℝ from v) :=
        fun h => hz (hvU h)
      have hv0 : v z = 0 :=
        image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from v) hnot
      simpa [hv0] using
        (mul_nonneg (div_nonneg (Real.sqrt_nonneg (6 : ℝ))
          (show (0 : ℝ) ≤ 2 by norm_num))
          (mul_nonneg (sq_nonneg z.2) (sq_nonneg (L z))))
  calc
    |∫ z : Vec3 × ℝ, z.2 ^ 2 * v z * L z ∂volume| ≤
        ∫ z : Vec3 × ℝ, |z.2 ^ 2 * v z * L z| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z : Vec3 × ℝ, Real.sqrt 6 / 2 *
        (q / 3 * z.2 * v z ^ 2 + z.2 ^ 2 * L z ^ 2) ∂volume :=
      integral_mono hC.abs hright hpoint
    _ = _ := by rw [integral_const_mul, integral_add hI hP]

/-- The Gaussian cross density is integrable for a smooth scalar field
supported in the positive-time cylinder. -/
theorem gauss_cross_integrable (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v)
    (hvU : tsupport v ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * v z *
      carlemanConj (gaussCarlemanPhase q) v z) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 ^ 2) := by fun_prop
  have hbase : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 ^ 2 * v z) := ht.mul hv
  have hcompact : HasCompactSupport
      (fun z : ParabolicPoint => z.2 ^ 2 * v z) :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _)
      tsupport_mul_subset_right
  have hsubset : tsupport (fun z : ParabolicPoint => z.2 ^ 2 * v z) ⊆ U :=
    tsupport_mul_subset_right.trans hvU
  have hint := integrable_mul_of_tsupport hU
    (contDiffOn_carlemanConj hU hφ hv) hbase hcompact hsubset
  have heq : (fun z : Vec3 × ℝ => z.2 ^ 2 * v z *
      carlemanConj (gaussCarlemanPhase q) v z) =
      (fun z : Vec3 × ℝ => carlemanConj (gaussCarlemanPhase q) v z *
        (z.2 ^ 2 * v z)) := by funext z; ring
  rw [heq]
  exact hint

/-- The phase potential term in the Gaussian integrated gradient identity
is integrable. -/
theorem gauss_potential_integrable (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v)
    (hvU : tsupport v ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * v z ^ 2 *
      (scalarGradSq (gaussCarlemanPhase q) z -
        timePartial (gaussCarlemanPhase q) z)) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  let B : ParabolicPoint → ℝ := fun z => z.2 ^ 2 * v z ^ 2
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by
    dsimp [B]
    fun_prop
  have hBs : tsupport B ⊆ tsupport v := by
    apply closure_minimal _ (isClosed_tsupport v)
    intro z hz
    by_contra hnot
    have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact hz (by simp [B, hv0])
  have hBc : HasCompactSupport B :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hBs
  have hgrad : ContDiffOn ℝ (⊤ : ℕ∞)
      (scalarGradSq (gaussCarlemanPhase q)) U :=
    contDiffOn_scalarGradSq hU hφ
  have htime : ContDiffOn ℝ (⊤ : ℕ∞)
      (timePartial (gaussCarlemanPhase q)) U :=
    contDiffOn_timePartial hU hφ
  have hcoef : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => scalarGradSq (gaussCarlemanPhase q) z -
        timePartial (gaussCarlemanPhase q) z) U :=
    hgrad.sub htime
  have hint := integrable_mul_of_tsupport hU
    hcoef hB hBc (hBs.trans hvU)
  have heq : (fun z : Vec3 × ℝ => z.2 ^ 2 * v z ^ 2 *
      (scalarGradSq (gaussCarlemanPhase q) z -
        timePartial (gaussCarlemanPhase q) z)) =
      (fun z : Vec3 × ℝ =>
        (scalarGradSq (gaussCarlemanPhase q) z -
          timePartial (gaussCarlemanPhase q) z) * B z) := by
    funext z
    ring
  rw [heq]
  exact hint

/-- The phase-gradient part of the Gaussian energy is integrable. -/
theorem gauss_phase_gradient_mass_integrable (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v)
    (hvU : tsupport v ⊆ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * v z ^ 2 *
      scalarGradSq (gaussCarlemanPhase q) z) volume := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  let B : ParabolicPoint → ℝ := fun z => z.2 ^ 2 * v z ^ 2
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by
    dsimp [B]
    fun_prop
  have hBs : tsupport B ⊆ tsupport v := by
    apply closure_minimal _ (isClosed_tsupport v)
    intro z hz
    by_contra hnot
    have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact hz (by simp [B, hv0])
  have hBc : HasCompactSupport B :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hBs
  have hgrad : ContDiffOn ℝ (⊤ : ℕ∞)
      (scalarGradSq (gaussCarlemanPhase q)) U :=
    contDiffOn_scalarGradSq hU hφ
  have hint := integrable_mul_of_tsupport hU hgrad hB hBc (hBs.trans hvU)
  have heq : (fun z : Vec3 × ℝ => z.2 ^ 2 * v z ^ 2 *
      scalarGradSq (gaussCarlemanPhase q) z) =
      (fun z : Vec3 × ℝ => scalarGradSq (gaussCarlemanPhase q) z * B z) := by
    funext z
    ring
  rw [heq]
  exact hint

/-- The squared scalar gradient of a smooth compactly supported field is
integrable after multiplication by `t²`. -/
theorem gauss_scalar_gradient_integrable
    (v : ParabolicPoint → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v) :
    Integrable (fun z : Vec3 × ℝ => z.2 ^ 2 * scalarGradSq v z) volume := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (scalarGradSq v) := by
    unfold scalarGradSq
    exact ContDiff.sum (fun i _ => (CKN.spatialPartial_contDiff hv i).pow 2)
  have hgs : tsupport (scalarGradSq v) ⊆ tsupport v := by
    apply closure_minimal _ (isClosed_tsupport v)
    intro z hz
    by_contra hnot
    have hsp (i : Fin 3) : spatialPartial v i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport hnot i
    have hzero : scalarGradSq v z = 0 := by
      simp [scalarGradSq, hsp]
    exact hz (by simp [hzero])
  have hgc : HasCompactSupport (scalarGradSq v) :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hgs
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun z : ParabolicPoint => z.2 ^ 2) := by
    fun_prop
  exact integrable_mul_of_tsupport isOpen_univ ht.contDiffOn
    hgrad hgc (subset_univ _)

end ESS
