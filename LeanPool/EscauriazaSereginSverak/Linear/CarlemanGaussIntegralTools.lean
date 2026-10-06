/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanGaussVectorEstimate
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Support and integral forms of the Gaussian commutator

The density identity from `eq:carleman-I` extends across the complement of
the test field's support, which permits whole-space integration.
-/

public section


open CKN CKN.Foundation.Parabolic Set MeasureTheory

noncomputable section

namespace ESS

local instance gaussIntegralToolsNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance gaussIntegralToolsNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The Gaussian commutator identity holds globally for a field supported in
the positive-time cylinder. -/
theorem gauss_commutatorDensity_global (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hvU : tsupport (show Vec3 × ℝ → ℝ from v) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) (z : ParabolicPoint) :
    carlemanCommutatorDensity (gaussCarlemanPhase q) v z =
      q / 3 * z.2 * v z ^ 2 := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · exact gaussCarleman_commutatorDensity q v z hz.2.1
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → ℝ from v) :=
      fun h => hz (hvU h)
    have hv0 : v z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from v) hnot
    have hgrad (i : Fin 3) : spatialPartial v i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport hnot i
    unfold carlemanCommutatorDensity scalarGradSq
    simp [hv0, hgrad]

/-- The Gaussian commutator integral is its explicit positive density. -/
theorem gauss_commutator_integral_eq (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hvU : tsupport (show Vec3 × ℝ → ℝ from v) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z : ParabolicPoint,
      carlemanCommutatorDensity (gaussCarlemanPhase q) v z) =
        ∫ z : ParabolicPoint, q / 3 * z.2 * v z ^ 2 := by
  apply integral_congr_ae
  filter_upwards [] with z
  exact gauss_commutatorDensity_global q v hvU z


/-- The Gaussian phase potential can be rewritten wherever the field is
supported, and both sides vanish elsewhere. -/
theorem gauss_potential_times_field_global (q : ℝ)
    (v : ParabolicPoint → ℝ)
    (hvU : tsupport (show Vec3 × ℝ → ℝ from v) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) (z : ParabolicPoint) :
    v z ^ 2 * (scalarGradSq (gaussCarlemanPhase q) z -
      timePartial (gaussCarlemanPhase q) z) =
      v z ^ 2 * (-scalarGradSq (gaussCarlemanPhase q) z +
        q * (1 / z.2 - 1 / 3)) := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · rw [gaussCarlemanPhase_potential q z hz.2.1]
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → ℝ from v) :=
      fun h => hz (hvU h)
    have hv0 : v z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from v) hnot
    simp [hv0]

/-- The coefficient in the Gaussian integrated gradient identity is bounded
by the commutator density. -/
theorem gauss_coefficient_times_field_le (q : ℝ) (hq : 0 ≤ q)
    (v : ParabolicPoint → ℝ)
    (hvU : tsupport (show Vec3 × ℝ → ℝ from v) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) (z : ParabolicPoint) :
    (-z.2 + q * z.2 ^ 2 * (1 / z.2 - 1 / 3)) * v z ^ 2 ≤
      q * z.2 * v z ^ 2 := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · exact mul_le_mul_of_nonneg_right
      (gaussCarleman_coefficient_le hq hz.2.1) (sq_nonneg _)
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → ℝ from v) :=
      fun h => hz (hvU h)
    have hv0 : v z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → ℝ from v) hnot
    simp [hv0]

/-- The weighted field and gradient density vanishes outside the test
field's supporting cylinder. -/
theorem gauss_original_energy_zero_outside (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (z : ParabolicPoint) (hz : z ∉ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
          spatialGradientSq w (spatialGradient w) z) = 0 := by
  have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
    fun h => hz (hwU h)
  have hw0 : w z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → Vec3 from w) hnot
  have hgrad : spatialGradientSq w (spatialGradient w) z = 0 := by
    unfold spatialGradientSq spatialGradient
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [(gauss_component_zero_outside w z hnot i).2.2 j |>.1]
    norm_num
  rw [hw0, vec3EuclideanNorm_zero, hgrad]
  ring

/-- The weighted heat density vanishes outside the test field's supporting
cylinder. -/
theorem gauss_original_heat_zero_outside (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (z : ParabolicPoint) (hz : z ∉ spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 = 0 := by
  have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
    fun h => hz (hwU h)
  have hheat : (fun i : Fin 3 => timePartial (fun y => w y i) z +
      ∑ j, spatialSecondPartial (fun y => w y i) j j z) = 0 := by
    funext i
    obtain ⟨_, ht, hs⟩ := gauss_component_zero_outside w z hnot i
    simp [ht, fun j => (hs j).2]
  rw [hheat, vec3EuclideanNorm_zero]
  ring

/-- The original energy integral over the cylinder equals the whole-space
integral of its zero extension. -/
theorem gauss_original_energy_setIntegral_eq_integral (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z in spaceTimeSet univ (Ioo (0 : ℝ) 2),
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
            spatialGradientSq w (spatialGradient w) z)) =
      ∫ z : ParabolicPoint,
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
            (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
              spatialGradientSq w (spatialGradient w) z) := by
  apply gauss_setIntegral_eq_integral_of_zero_outside
  intro z hz
  exact gauss_original_energy_zero_outside a w hwU z hz

/-- The original heat integral over the cylinder equals the whole-space
integral of its zero extension. -/
theorem gauss_original_heat_setIntegral_eq_integral (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2)) :
    (∫ z in spaceTimeSet univ (Ioo (0 : ℝ) 2),
      (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) =
      ∫ z : ParabolicPoint,
        (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
            vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
              ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  apply gauss_setIntegral_eq_integral_of_zero_outside
  intro z hz
  exact gauss_original_heat_zero_outside a w hwU z hz

/-- The vector conjugation identity extends globally because both sides
vanish off the field's support. -/
theorem gauss_vector_conjugated_heat_sq_global (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (z : ParabolicPoint) :
    (∑ i : Fin 3, carlemanConj (gaussCarlemanPhase q)
      (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z ^ 2) =
      Real.exp (gaussCarlemanPhase q z) ^ 2 *
        vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · exact gauss_vector_conjugated_heat_sq q w hw z hz
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
      fun h => hz (hwU h)
    have hheat : (fun i : Fin 3 => timePartial (fun y => w y i) z +
        ∑ j, spatialSecondPartial (fun y => w y i) j j z) = 0 := by
      funext i
      obtain ⟨_, ht, hs⟩ := gauss_component_zero_outside w z hnot i
      simp [ht, fun j => (hs j).2]
    have hconj (i : Fin 3) : carlemanConj (gaussCarlemanPhase q)
        (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z = 0 := by
      let vi : Vec3 × ℝ → ℝ := fun y =>
        Real.exp (gaussCarlemanPhase q y) * w y i
      have hsuppWi : tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) ⊆
          tsupport (show Vec3 × ℝ → Vec3 from w) :=
        tsupport_comp_subset (g := fun x : Vec3 => x i) rfl
          (show Vec3 × ℝ → Vec3 from w)
      have hsuppVi : tsupport vi ⊆
          tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) :=
        tsupport_mul_subset_right
      have hnotVi : z ∉ tsupport vi := fun h => hnot (hsuppWi (hsuppVi h))
      have hvi0 : vi z = 0 := image_eq_zero_of_notMem_tsupport hnotVi
      have hdt : timePartial vi z = 0 := CKN.timePartial_eq_zero_off_tsupport hnotVi
      have hsp (j : Fin 3) : spatialPartial vi j z = 0 :=
        CKN.spatialPartial_eq_zero_off_tsupport hnotVi j
      have hss (j : Fin 3) : spatialSecondPartial vi j j z = 0 :=
        CKN.spatialSecondPartial_eq_zero_off_tsupport hnotVi j j
      change carlemanConj (gaussCarlemanPhase q) vi z = 0
      unfold carlemanConj scalarLaplacian
      simp [hvi0, hdt, hsp, hss]
    simp [hconj, hheat, vec3EuclideanNorm_zero]

/-- Scalar Gaussian conjugation holds globally for each component of a
supported vector field. -/
theorem gauss_component_conjugation_global (q : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (i : Fin 3) (z : ParabolicPoint) :
    carlemanConj (gaussCarlemanPhase q)
        (fun y => Real.exp (gaussCarlemanPhase q y) * w y i) z =
      Real.exp (gaussCarlemanPhase q z) *
        (timePartial (fun y => w y i) z +
          scalarLaplacian (fun y => w y i) z) := by
  let U : Set ParabolicPoint := spaceTimeSet univ (Ioo (0 : ℝ) 2)
  have hU : IsOpen U := by
    change IsOpen (univ ×ˢ Ioo (0 : ℝ) 2)
    exact isOpen_univ.prod isOpen_Ioo
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) (gaussCarlemanPhase q) U :=
    gaussCarlemanPhase_contDiffOn q
  have hwi : ContDiff ℝ (⊤ : ℕ∞) (fun y : ParabolicPoint => w y i) := by
    fun_prop
  have hsuppWi : tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) ⊆
      tsupport (show Vec3 × ℝ → Vec3 from w) :=
    tsupport_comp_subset (g := fun x : Vec3 => x i) rfl
      (show Vec3 × ℝ → Vec3 from w)
  by_cases hz : z ∈ U
  · exact carlemanConj_exp_mul hU hφ hwi hz
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
      fun h => hz (hwU h)
    have hwi0 := gauss_component_zero_outside w z hnot i
    let vi : Vec3 × ℝ → ℝ := fun y =>
      Real.exp (gaussCarlemanPhase q y) * w y i
    have hsuppVi : tsupport vi ⊆
        tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) :=
      tsupport_mul_subset_right
    have hnotVi : z ∉ tsupport vi := fun h => hnot (hsuppWi (hsuppVi h))
    have hvi0 : vi z = 0 := image_eq_zero_of_notMem_tsupport hnotVi
    have hdt : timePartial vi z = 0 := CKN.timePartial_eq_zero_off_tsupport hnotVi
    have hsp (j : Fin 3) : spatialPartial vi j z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport hnotVi j
    have hss (j : Fin 3) : spatialSecondPartial vi j j z = 0 :=
      CKN.spatialSecondPartial_eq_zero_off_tsupport hnotVi j j
    change carlemanConj (gaussCarlemanPhase q) vi z = _
    unfold carlemanConj scalarLaplacian
    simp [hvi0, hdt, hsp, hss, hwi0.2.1, fun j => (hwi0.2.2 j).2]

/-- The pointwise vector energy comparison holds globally after extension by
zero outside the supporting cylinder. -/
theorem gauss_vector_weighted_energy_le_global (a : ℝ)
    (w : ParabolicPoint → Vec3) (ha : 0 < a)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (z : ParabolicPoint) :
    (gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
      Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
        (a / z.2 * vec3EuclideanNorm (w z) ^ 2 +
          spatialGradientSq w (spatialGradient w) z) ≤
      Real.exp (2 / 3 : ℝ) *
        ((a + 1) * z.2 *
            vec3EuclideanNorm (fun i =>
              Real.exp (gaussCarlemanPhase (a + 1) z) * w z i) ^ 2 +
          2 * z.2 ^ 2 *
            ((∑ i : Fin 3, scalarGradSq
                (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z) +
              vec3EuclideanNorm (fun i =>
                Real.exp (gaussCarlemanPhase (a + 1) z) * w z i) ^ 2 *
                scalarGradSq (gaussCarlemanPhase (a + 1)) z)) := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · exact gauss_vector_weighted_energy_le a w ha hw z hz
  · have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
      fun h => hz (hwU h)
    have hleft := gauss_original_energy_zero_outside a w hwU z hz
    have hw0 : w z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := show Vec3 × ℝ → Vec3 from w) hnot
    have hV : (fun i : Fin 3 =>
        Real.exp (gaussCarlemanPhase (a + 1) z) * w z i) = 0 := by
      funext i
      simp [hw0]
    have hG (i : Fin 3) : scalarGradSq
        (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z = 0 := by
      let vi : Vec3 × ℝ → ℝ := fun y =>
        Real.exp (gaussCarlemanPhase (a + 1) y) * w y i
      have hsuppWi : tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) ⊆
          tsupport (show Vec3 × ℝ → Vec3 from w) :=
        tsupport_comp_subset (g := fun x : Vec3 => x i) rfl
          (show Vec3 × ℝ → Vec3 from w)
      have hsuppVi : tsupport vi ⊆
          tsupport (show Vec3 × ℝ → ℝ from fun y => w y i) :=
        tsupport_mul_subset_right
      have hnotVi : z ∉ tsupport vi := fun h => hnot (hsuppWi (hsuppVi h))
      have hsp (j : Fin 3) : spatialPartial vi j z = 0 :=
        CKN.spatialPartial_eq_zero_off_tsupport hnotVi j
      change scalarGradSq vi z = 0
      simp [scalarGradSq, hsp]
    rw [hleft, hV, vec3EuclideanNorm_zero]
    simp [hG]

/-- The conjugated heat energy comparison holds across the complement of the
supporting cylinder. -/
theorem gauss_vector_operator_energy_le_global (a : ℝ)
    (w : ParabolicPoint → Vec3)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwU : tsupport (show Vec3 × ℝ → Vec3 from w) ⊆
      spaceTimeSet univ (Ioo (0 : ℝ) 2))
    (z : ParabolicPoint) :
    z.2 ^ 2 * (∑ i : Fin 3,
      carlemanConj (gaussCarlemanPhase (a + 1))
        (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z ^ 2) ≤
      Real.exp (2 / 3 : ℝ) *
        ((gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
          Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2))) *
          vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) := by
  by_cases hz : z ∈ spaceTimeSet univ (Ioo (0 : ℝ) 2)
  · exact gauss_vector_operator_energy_le a w hw z hz
  · have hleft : (∑ i : Fin 3,
        carlemanConj (gaussCarlemanPhase (a + 1))
          (fun y => Real.exp (gaussCarlemanPhase (a + 1) y) * w y i) z ^ 2) =
          0 := by
      rw [gauss_vector_conjugated_heat_sq_global (a + 1) w hw hwU z]
      have hnot : z ∉ tsupport (show Vec3 × ℝ → Vec3 from w) :=
        fun h => hz (hwU h)
      have hheat : (fun i : Fin 3 => timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) = 0 := by
        funext i
        obtain ⟨_, ht, hs⟩ := gauss_component_zero_outside w z hnot i
        simp [ht, fun j => (hs j).2]
      simp [hheat, vec3EuclideanNorm_zero]
    rw [hleft, gauss_original_heat_zero_outside a w hwU z hz]
    norm_num

end ESS
