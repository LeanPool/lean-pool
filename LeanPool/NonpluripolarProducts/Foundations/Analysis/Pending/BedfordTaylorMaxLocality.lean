/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.JointDecreasingMaxWeight
public import LeanPool.NonpluripolarProducts.Foundations.FiniteTuple

/-!
# Plurifine locality of Bedford–Taylor measures for a maximum with a constant

Let `u' = max(u, c)` in one slot. With decreasing smooth approximations `f_j` of
`u` and the scaled regularized maxima `g_j = c + ε_j P((f_j - c)/ε_j)` of
`max(u, c)`, the mixed densities of the two families agree where `f_j > c + ε_j`,
while the weight `g_j - c` is at most `ε_j` elsewhere. Weighted convergence
therefore gives `(max(u, c) - c) μ = (max(u, c) - c) μ'`, and dividing by the
positive weight on `{u > c}` gives `μ = μ'` there.

Source: Bedford–Taylor locality in the plurifine topology, as invoked in BEGZ §1.2.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

/-- **Weighted locality.** Replacing one slot `u i₀` by `max(u i₀, c)` does not
change the limit measure weighted by `max(u i₀, c) - c`. -/
theorem integral_mul_maxWeight_eq {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) (c : ℝ) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) c) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, χ z * (max (u i₀ z) c - c) ∂μ = ∫ z, χ z * (max (u i₀ z) c - c) ∂μ' := by
  have hconst : IsSmoothPsdOn U (fun _ => c) :=
    ⟨contDiffOn_const, fun z _ => by rw [complexHessian_const]; exact Matrix.PosSemidef.zero⟩
  exact JointDecreasingMaxWeight.integral_mul_jointMaxWeight_eq i₀
    (isDecApprox_const hconst) hμc hμf hμ hμ'c hμ'f hμ' hex hχ hχc hχU

open scoped Distributions in
/-- If the measures agree against tests weighted by `max a b - b`, division by the
weight recovers their restrictions to the strict locus `{b < a} ∩ U`. -/
theorem restrict_eq_of_max_weight_test_integral_eq {U : Opens (ComplexModel n)}
    {a b : ComplexModel n → ℝ} {μ μ' : Measure (ComplexModel n)}
    (hP : MeasurableSet {z | z ∈ U ∧ b z < a z})
    (hfm : ∀ ν : Measure (ComplexModel n),
      AEMeasurable (fun z => ENNReal.ofReal (max (a z) (b z) - b z)) (ν.restrict U))
    (ha : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ z ∈ K, |a z| ≤ C)
    (hb : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ z ∈ K, |b z| ≤ C)
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (heq : ∀ φ : 𝓓(U, ℝ),
      (∫ z, φ z * (max (a z) (b z) - b z) ∂μ) = ∫ z, φ z * (max (a z) (b z) - b z) ∂μ') :
    μ.restrict {z | z ∈ U ∧ b z < a z} = μ'.restrict {z | z ∈ U ∧ b z < a z} := by
  let P : Set (ComplexModel n) := {z | z ∈ U ∧ b z < a z}
  have hPU : P ⊆ U := fun _ hz => hz.1
  have hUm := U.isOpen.measurableSet
  let f := fun z => ENNReal.ofReal (max (a z) (b z) - b z)
  let ρ := (μ.restrict U).withDensity f
  let ρ' := (μ'.restrict U).withDensity f
  have hfin (ν : Measure (ComplexModel n)) (hf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ U → (ν.restrict U).withDensity f K < ⊤ := by
    intro K hK hKU
    obtain ⟨C, hC⟩ := ha K hK hKU
    obtain ⟨D, hD⟩ := hb K hK hKU
    rw [withDensity_apply _ hK.measurableSet]
    calc
      ∫⁻ z in K, f z ∂ν.restrict U ≤ ∫⁻ _ in K, ENNReal.ofReal (C + D) ∂ν.restrict U := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
        refine Eventually.of_forall fun z hz => ENNReal.ofReal_le_ofReal ?_
        rcases le_total (a z) (b z) with h | h
        · rw [max_eq_right h, sub_self]
          linarith [hC z hz, hD z hz, abs_nonneg (a z), abs_nonneg (b z)]
        · rw [max_eq_left h]
          linarith [hC z hz, hD z hz, le_abs_self (a z), neg_abs_le (b z)]
      _ = ENNReal.ofReal (C + D) * ν.restrict U K := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt (hf K hK hKU))
  have hint (ν : Measure (ComplexModel n)) (φ : 𝓓(U, ℝ)) :
      ∫ z, φ z ∂(ν.restrict U).withDensity f = ∫ z, φ z * (max (a z) (b z) - b z) ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hfm ν)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      simp [image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)]]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (sub_nonneg.2 (le_max_right _ _)), smul_eq_mul, mul_comm]
  have hρ : ρ.restrict U = ρ'.restrict U :=
    restrict_eq_of_testFunction_integral_eq (hfin μ hμf) (hfin μ' hμ'f) fun φ => by
      rw [hint μ φ, hint μ' φ]
      exact heq φ
  have hself (ν : Measure (ComplexModel n)) :
      ((ν.restrict U).withDensity f).restrict U = (ν.restrict U).withDensity f := by
    rw [restrict_withDensity hUm, Measure.restrict_restrict hUm, inter_self]
  rw [hself, hself] at hρ
  have hinv (ν : Measure (ComplexModel n)) :
      ν.restrict P = (((ν.restrict U).withDensity f).restrict P).withDensity
        fun z => (f z)⁻¹ := by
    rw [restrict_withDensity hP, withDensity_inv_same₀ ((hfm ν).mono_measure
      Measure.restrict_le_self)]
    · rw [Measure.restrict_restrict_of_subset hPU]
    · filter_upwards [ae_restrict_mem hP] with z hz
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact lt_max_of_lt_left hz.2
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  rw [hinv μ, hinv μ', hρ]

/-- Borel strict comparison is constructed from the original two finite limits. -/
theorem measurableSet_lt_of_joint_decApprox {U : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} {F G : ℕ → ComplexModel n → ℝ}
    (hF : IsDecApprox U u F) (hG : IsDecApprox U v G) :
    MeasurableSet {z | z ∈ U ∧ v z < u z} := by
  classical
  have hmeas {w : ComplexModel n → ℝ} {H : ℕ → ComplexModel n → ℝ}
      (hH : IsDecApprox U w H) :
      Measurable ((U : Set (ComplexModel n)).piecewise w (fun _ ↦ 0)) := by
    refine measurable_of_tendsto_metrizable
      (f := fun j ↦ (U : Set (ComplexModel n)).piecewise (H j) (fun _ ↦ 0))
      (fun j ↦ ((hH.1 j).1.continuousOn).measurable_piecewise
        continuousOn_const U.isOpen.measurableSet) (tendsto_pi_nhds.2 fun z ↦ ?_)
    by_cases hz : z ∈ (U : Set (ComplexModel n))
    · simpa only [Set.piecewise, ite_eq_left hz] using hH.2.2.1 z hz
    · simp only [Set.piecewise, ite_eq_right hz]
      exact tendsto_const_nhds
  have hlt := measurableSet_lt (hmeas hG) (hmeas hF)
  have heq : {z | z ∈ U ∧ v z < u z} = (U : Set (ComplexModel n)) ∩
      {z | (U : Set (ComplexModel n)).piecewise v (fun _ ↦ 0) z <
        (U : Set (ComplexModel n)).piecewise u (fun _ ↦ 0) z} := by
    ext z
    change (z ∈ (U : Set (ComplexModel n)) ∧ v z < u z) ↔
      (z ∈ (U : Set (ComplexModel n)) ∧
        (U : Set (ComplexModel n)).piecewise v (fun _ ↦ 0) z <
          (U : Set (ComplexModel n)).piecewise u (fun _ ↦ 0) z)
    by_cases hz : z ∈ (U : Set (ComplexModel n)) <;> simp [hz]
  rw [heq]
  exact U.isOpen.measurableSet.inter hlt

/-- The original positive comparison gap internally yields maximum slot locality. -/
theorem restrict_eq_of_joint_max_slot {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    {J : ℕ → ComplexModel n → ℝ} (hg : IsDecApprox U g J) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) (g z)) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) :
    μ.restrict {z | z ∈ U ∧ g z < u i₀ z} = μ'.restrict {z | z ∈ U ∧ g z < u i₀ z} := by
  classical
  obtain ⟨F, hF⟩ := id hex
  have hGw := hF.1 i₀
  set P := {z | z ∈ U ∧ g z < u i₀ z}
  have hPm : MeasurableSet P := measurableSet_lt_of_joint_decApprox hGw hg
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) (g z) - g z)
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) (J j z) - J j z) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact (((hGw.1 j).1.continuousOn.sup (hg.1 j).1.continuousOn).sub
        (hg.1 j).1.continuousOn).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max (hg.2.2.1 z hz)).sub (hg.2.2.1 z hz)
  refine restrict_eq_of_max_weight_test_integral_eq hPm hfm ?_ ?_ hμf hμ'f ?_
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    exact ⟨C, fun _ hz => hGw.abs_le_of_mem hKU hC hz⟩
  · intro K hK hKU
    obtain ⟨D, hD⟩ := hg.exists_abs_le hK hKU
    exact ⟨D, fun _ hz => hg.abs_le_of_mem hKU hD hz⟩
  · intro φ
    exact JointDecreasingMaxWeight.integral_mul_jointMaxWeight_eq i₀ hg hμc hμf hμ hμ'c hμ'f hμ' hex
      φ.continuous φ.hasCompactSupport φ.tsupport_subset

/-- **Locality for one slot.** On `{u i₀ > c}` the limit measures for `u` and for
`u` with `max(u i₀, c)` in slot `i₀` coincide. -/
theorem restrict_eq_of_max_slot {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) (c : ℝ) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) c) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) :
    μ.restrict {z | z ∈ U ∧ c < u i₀ z} = μ'.restrict {z | z ∈ U ∧ c < u i₀ z} := by
  have hconst : IsSmoothPsdOn U (fun _ => c) :=
    ⟨contDiffOn_const, fun z _ => by rw [complexHessian_const]; exact Matrix.PosSemidef.zero⟩
  exact restrict_eq_of_joint_max_slot i₀ (isDecApprox_const hconst)
    hμc hμf hμ hμ'c hμ'f hμ' hex

/-- The tuple with `max(·, g i)` applied in the slots of index below `k`. -/
def maxTupleObstacle (u g : Fin n → ComplexModel n → ℝ) (k : ℕ) :
    Fin n → ComplexModel n → ℝ :=
  fun i ↦ if i.val < k then fun z ↦ max (u i z) (g i z) else u i

theorem maxTupleObstacle_zero (u g : Fin n → ComplexModel n → ℝ) :
    maxTupleObstacle u g 0 = u :=
  FiniteTuple.replacePrefix_zero u (fun i z ↦ max (u i z) (g i z))

theorem maxTupleObstacle_succ (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g (k + 1) =
      Function.update (maxTupleObstacle u g k) ⟨k, hk⟩
        (fun z ↦ max (maxTupleObstacle u g k ⟨k, hk⟩ z) (g ⟨k, hk⟩ z)) := by
  have hslot : maxTupleObstacle u g k ⟨k, hk⟩ = u ⟨k, hk⟩ := by simp [maxTupleObstacle]
  rw [hslot]
  exact FiniteTuple.replacePrefix_succ u (fun i z ↦ max (u i z) (g i z)) hk

theorem maxTupleObstacle_apply_self (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g k ⟨k, hk⟩ = u ⟨k, hk⟩ := by
  simp [maxTupleObstacle]

/-- The tuple with `max(·, c)` applied in the slots of index below `k`. -/
abbrev maxTuple (u : Fin n → ComplexModel n → ℝ) (c : ℝ) (k : ℕ) :
    Fin n → ComplexModel n → ℝ :=
  maxTupleObstacle u (fun _ _ => c) k

theorem maxTuple_zero (u : Fin n → ComplexModel n → ℝ) (c : ℝ) : maxTuple u c 0 = u :=
  maxTupleObstacle_zero u (fun _ _ ↦ c)

theorem maxTuple_succ (u : Fin n → ComplexModel n → ℝ) (c : ℝ) {k : ℕ} (hk : k < n) :
    maxTuple u c (k + 1) =
      Function.update (maxTuple u c k) ⟨k, hk⟩ fun z ↦ max (maxTuple u c k ⟨k, hk⟩ z) c :=
  maxTupleObstacle_succ u (fun _ _ ↦ c) hk

theorem maxTuple_apply_self (u : Fin n → ComplexModel n → ℝ) (c : ℝ) {k : ℕ} (hk : k < n) :
    maxTuple u c k ⟨k, hk⟩ = u ⟨k, hk⟩ :=
  maxTupleObstacle_apply_self u (fun _ _ ↦ c) hk

/-- Actual joint stages supply every intermediate maximum tuple. -/
theorem exists_isAdmissible_joint_maxTuple {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    {J : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (hJ : ∀ i, IsDecApprox U (g i) (J i)) (k : ℕ) :
    ∃ F', IsAdmissible n U (maxTupleObstacle u g k) F' := by
  classical
  refine ⟨fun i ↦ if i.val < k then
    (fun j ↦ scaledSmoothMax (maxScale j) (F i j) (J i j)) else F i,
    fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i.val < k
  · simpa [maxTupleObstacle, h] using
      JointDecreasingSmoothMax.isDecApprox_joint_scaledSmoothMax (hF.1 i) (hJ i)
  · simpa [maxTupleObstacle, h] using hF.1 i

theorem exists_isAdmissible_maxTuple {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (c : ℝ) (k : ℕ) : ∃ F', IsAdmissible n U (maxTuple u c k) F' := by
  have hconst : IsSmoothPsdOn U (fun _ => c) :=
    ⟨contDiffOn_const, fun z _ => by rw [complexHessian_const]; exact Matrix.PosSemidef.zero⟩
  exact exists_isAdmissible_joint_maxTuple hF (fun _ ↦ isDecApprox_const hconst) k

/-- A tuple comparison follows from the one-slot comparisons on sets containing `P`. -/
theorem restrict_eq_of_tuple_steps {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    {P : Set (ComplexModel n)} (hPU : P ⊆ U)
    (v : ℕ → Fin n → ComplexModel n → ℝ) (hzero : v 0 = u)
    {S : Fin n → Set (ComplexModel n)} (hPS : ∀ i, P ⊆ S i)
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F)
    (hstep : ∀ k (hk : k < n) (μ₀ μ₁ : Measure (ComplexModel n)),
      μ₀ (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ₀ K < ⊤) →
      (∀ F, IsAdmissible n U (v k) F → TendstoMixed U F μ₀) →
      μ₁ (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ₁ K < ⊤) →
      (∀ F, IsAdmissible n U (v (k + 1)) F → TendstoMixed U F μ₁) →
      μ₀.restrict (S ⟨k, hk⟩) = μ₁.restrict (S ⟨k, hk⟩)) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (v k) F → TendstoMixed U F μ') →
      μ'.restrict P = μ.restrict P := by
  intro k
  induction k with
  | zero =>
    intro _ μ' _ hμ'f hμ'
    rw [hzero] at hμ'
    have h := restrict_eq_of_claims le_rfl hμ'f hμf hμ' hμ hex
    rw [← Measure.restrict_restrict_of_subset hPU, h, Measure.restrict_restrict_of_subset hPU]
  | succ k ih =>
    intro hk μ' hμ'c hμ'f hμ'
    have hkn : k < n := hk
    obtain ⟨μk, hμkc, hμkf, hμkT⟩ := pClaim_all (n := n) U (v k)
    have hIH := ih hkn.le μk hμkc hμkf hμkT
    have hslot := hstep k hkn μk μ' hμkc hμkf hμkT hμ'c hμ'f hμ'
    have hsub := hPS ⟨k, hkn⟩
    rw [← hIH, ← Measure.restrict_restrict_of_subset hsub, ← hslot,
      Measure.restrict_restrict_of_subset hsub]

/-- Finite-slot comparison on the original common strict-superlevel set. -/
theorem restrict_eq_joint_maxTuple {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {J : Fin n → ℕ → ComplexModel n → ℝ}
    (hJ : ∀ i, IsDecApprox U (g i) (J i))
    {μ : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTupleObstacle u g k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} =
        μ.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} := by
  obtain ⟨F, hF⟩ := hex
  refine restrict_eq_of_tuple_steps (U := U) (P := {z | z ∈ U ∧ ∀ i, g i z < u i z})
    (S := fun i => {z | z ∈ U ∧ g i z < maxTupleObstacle u g i i z})
    (fun _ hz => hz.1) (maxTupleObstacle u g) (maxTupleObstacle_zero u g) ?_ hμf hμ ⟨F, hF⟩ ?_
  · intro i z hz
    exact ⟨hz.1, by rw [maxTupleObstacle_apply_self]; exact hz.2 i⟩
  · intro k hk μk μ' hμkc hμkf hμkT hμ'c hμ'f hμ'
    rw [maxTupleObstacle_succ u g hk] at hμ'
    exact restrict_eq_of_joint_max_slot
      (u := maxTupleObstacle u g k) ⟨k, hk⟩ (hJ ⟨k, hk⟩) hμkc hμkf hμkT hμ'c hμ'f hμ'
      (exists_isAdmissible_joint_maxTuple hF hJ k)

/-- **Locality in all slots on a relatively compact set.** -/
theorem restrict_eq_maxTuple {U : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (c : ℝ) {μ : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTuple u c k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, c < u i z} = μ.restrict {z | z ∈ U ∧ ∀ i, c < u i z} := by
  have hconst : IsSmoothPsdOn U (fun _ => c) :=
    ⟨contDiffOn_const, fun z _ => by rw [complexHessian_const]; exact Matrix.PosSemidef.zero⟩
  exact restrict_eq_joint_maxTuple (fun _ ↦ isDecApprox_const hconst) hμf hμ hex

theorem IsDecApprox.congr {U : Opens (ComplexModel n)} {w w' : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (h : EqOn w w' U) :
    IsDecApprox U w' G := by
  refine ⟨hG.1, hG.2.1, fun z hz ↦ h hz ▸ hG.2.2.1 z hz, fun K hK hKU ↦ ?_⟩
  rw [← (h.mono hKU).image_eq]
  exact hG.2.2.2 K hK hKU

/-- Restriction equalities for local mixed limits pass to an open exhaustion. The two
tuples defining the second limit may be identified by equality on the open set. -/
theorem restrict_eq_of_relativelyCompact_model {Ω : Opens (ComplexModel n)}
    {v w model : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (P : Set (ComplexModel n))
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤)
    (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hμT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ)
    (hνT : ∀ U, RelativelyCompactIn U Ω → ∃ G, IsAdmissible n U w G ∧ TendstoMixed U G ν)
    (hmodel : ∀ i, EqOn (w i) (model i) Ω)
    (hlocal : ∀ (V : Opens (ComplexModel n)), RelativelyCompactIn V Ω →
      ∀ (μV νV : Measure (ComplexModel n)),
      (∀ K, IsCompact K → K ⊆ V → μV K < ⊤) →
      (∀ F, IsAdmissible n V v F → TendstoMixed V F μV) →
      (∃ F, IsAdmissible n V v F) →
      νV (V : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ V → νV K < ⊤) →
      (∀ G, IsAdmissible n V model G → TendstoMixed V G νV) →
      νV.restrict {z | z ∈ V ∧ z ∈ P} = μV.restrict {z | z ∈ V ∧ z ∈ P}) :
    ν.restrict {z | z ∈ Ω ∧ z ∈ P} = μ.restrict {z | z ∈ Ω ∧ z ∈ P} := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (j : ℕ) : U j ≤ Ω := subset_closure.trans (hUrc j).2
  have hcover : {z | z ∈ Ω ∧ z ∈ P} = ⋃ j, {z | z ∈ U j ∧ z ∈ P} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hzΩ, hz⟩
      obtain ⟨j, hj⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hzΩ)
      exact ⟨j, hj rfl, hz⟩
    · rintro ⟨j, hzj, hz⟩
      exact ⟨hUΩ j hzj, hz⟩
  rw [hcover, Measure.restrict_iUnion_congr]
  intro j
  set V := U j
  have hPV : {z | z ∈ V ∧ z ∈ P} ⊆ (V : Set (ComplexModel n)) := fun _ hz ↦ hz.1
  have hfin (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ρ K < ⊤ := fun K hK hKV ↦ hρ K hK (hKV.trans (hUΩ j))
  obtain ⟨F, hF, hFT⟩ := hμT V (hUrc j)
  obtain ⟨μV, -, hμVf, hμVT⟩ := pClaim_all (n := n) V v
  have hμeq : μ.restrict V = μV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfin μ hμf) hμVf fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hμVT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  obtain ⟨G, hG, hGT⟩ := hνT V (hUrc j)
  have hG' : IsAdmissible n V model G :=
    ⟨fun i ↦ (hG.1 i).congr ((hmodel i).mono (hUΩ j)), hG.2⟩
  obtain ⟨νV, hνVc, hνVf, hνVT⟩ := pClaim_all (n := n) V model
  have hνeq : ν.restrict V = νV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfin ν hνf) hνVf fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hνVT G hG' φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hchain := hlocal V (hUrc j) μV νV hμVf hμVT ⟨F, hF⟩ hνVc hνVf hνVT
  rw [← Measure.restrict_restrict_of_subset hPV, hνeq, Measure.restrict_restrict_of_subset hPV,
    hchain, ← Measure.restrict_restrict_of_subset hPV, ← hμeq,
    Measure.restrict_restrict_of_subset hPV]

/-- **Max-constant locality on an open set.** For measures that are limits of
mixed densities of decreasing approximations on every relatively compact open
subset, replacing every slot `v i` by `max(v i, c)` does not change the measure
on the common strict superlevel set. -/
theorem restrict_eq_of_max_const {Ω : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    (c : ℝ) {μ ν : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hμT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ)
    (hνT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U w F ∧ TendstoMixed U F ν)
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} = μ.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} := by
  refine restrict_eq_of_relativelyCompact_model (model := maxTuple v c n)
    {z | ∀ i, c < v i z} hμf hνf hμT hνT ?_ ?_
  · intro i z hz
    simpa [maxTupleObstacle] using hmax i hz
  · intro V hV μV νV hμVf hμVT hF hνVc hνVf hνVT
    exact restrict_eq_maxTuple c hμVf hμVT hF n le_rfl νV hνVc hνVf hνVT

/-- **Scalar max-constant locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalBedfordTaylorMeasure.restrict_max_const
    {Ω : Opens (ComplexModel n)} {v w : ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : EqOn w (fun z => max (v z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ c < v z} = μ.restrict {z | z ∈ Ω ∧ c < v z} := by
  have h := restrict_eq_of_max_const (v := fun _ ↦ v) (w := fun _ ↦ w) c hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) fun _ ↦ hmax
  have hS : {z | z ∈ Ω ∧ c < v z} ⊆ {z | z ∈ Ω ∧ ∀ _ : Fin n, c < v z} :=
    fun z hz ↦ ⟨hz.1, fun _ ↦ hz.2⟩
  rw [← Measure.restrict_restrict_of_subset hS, h, Measure.restrict_restrict_of_subset hS]

/-- **Mixed max-constant locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalMixedBedfordTaylorMeasure.restrict_max_const
    {Ω : Opens (ComplexModel n)} {v w : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : ∀ i, EqOn (w i) (fun z => max (v i z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} = μ.restrict {z | z ∈ Ω ∧ ∀ i, c < v i z} :=
  restrict_eq_of_max_const c hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) hmax

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
