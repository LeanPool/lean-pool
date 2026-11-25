/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorGauge

/-!
# Additivity of the mixed Bedford–Taylor measure in one slot

If one slot of the tuple is a sum `a + b` of two locally bounded plurisubharmonic
functions, the mixed Bedford–Taylor measure is the sum of the two measures
obtained by putting `a`, respectively `b`, in that slot. Adding the smooth
approximations of `a` and `b` gives an admissible family for `a + b`, and the
mixed densities are additive in each slot, so the three weak limits are related
by the same identity.

This is the measure-level form of slot additivity in the algebra of bounded
Bedford–Taylor products (BEGZ §1.2, Demailly III.3).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Sums of decreasing smooth approximations approximate the sum. -/
theorem IsDecApprox.add {U : Opens (ComplexModel n)} {a b : ComplexModel n → ℝ}
    {A B : ℕ → ComplexModel n → ℝ} (hA : IsDecApprox U a A) (hB : IsDecApprox U b B) :
    IsDecApprox U (fun z ↦ a z + b z) (fun k z ↦ A k z + B k z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun k ↦ ⟨(hA.1 k).1.add (hB.1 k).1, fun z hz ↦ ?_⟩, fun z hz k l hkl ↦ ?_,
    fun z hz ↦ (hA.2.2.1 z hz).add (hB.2.2.1 z hz), fun K hK hKU ↦ ?_⟩
  · have hAz : ContDiffAt ℝ 2 (A k) z := ((hA.1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
    have hBz : ContDiffAt ℝ 2 (B k) z := ((hB.1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
    change (complexHessian (A k + B k) z).PosSemidef
    rw [complexHessian_add hAz hBz]
    exact ((hA.1 k).2 z hz).add ((hB.1 k).2 z hz)
  · exact add_le_add (hA.2.1 z hz hkl) (hB.2.1 z hz hkl)
  · obtain ⟨ma, hma⟩ := hA.2.2.2 K hK hKU
    obtain ⟨mb, hmb⟩ := hB.2.2.2 K hK hKU
    refine ⟨ma + mb, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact add_le_add (hma ⟨z, hz, rfl⟩) (hmb ⟨z, hz, rfl⟩)

/-- Replacing one slot by a sum of two admissible families gives an admissible
family for the tuple with the sum in that slot. -/
theorem IsAdmissible.update_add {U : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {a b : ComplexModel n → ℝ} (i₀ : Fin n)
    {F : Fin n → ℕ → ComplexModel n → ℝ} {B : ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U (Function.update v i₀ a) F) (hb : IsDecApprox U b B) :
    IsAdmissible n U (Function.update v i₀ fun z ↦ a z + b z)
      (Function.update F i₀ fun k z ↦ F i₀ k z + B k z) := by
  classical
  refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i = i₀
  · subst h
    have ha : IsDecApprox U a (F i) := by simpa using hF.1 i
    simpa using ha.add hb
  · simpa [Function.update_of_ne h] using hF.1 i

/-- The mixed densities of the three families are additive in the chosen slot. -/
theorem mixedDensity_update_add {f : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a b : ComplexModel n → ℝ}
    {z : ComplexModel n} (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z) :
    mixedDensity (Function.update f i₀ fun y ↦ a y + b y) z =
      mixedDensity (Function.update f i₀ a) z + mixedDensity (Function.update f i₀ b) z := by
  have h := mixedDensity_update_add_smul (f := f) i₀ ha hb 1
  simpa using h

/-- **Slot additivity of the limit measures.** If `μ`, `μa` and `μb` are the
mixed limits for the tuples with `a + b`, `a` and `b` in slot `i₀`, then
`μ = μa + μb`. -/
theorem restrict_eq_of_add_slot {U : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {a b : ComplexModel n → ℝ}
    {μ μa μb : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμaf : ∀ K, IsCompact K → K ⊆ U → μa K < ⊤)
    (hμbf : ∀ K, IsCompact K → K ⊆ U → μb K < ⊤)
    (hμ : ∀ F, IsAdmissible n U (Function.update v i₀ fun z ↦ a z + b z) F → TendstoMixed U F μ)
    (hμa : ∀ F, IsAdmissible n U (Function.update v i₀ a) F → TendstoMixed U F μa)
    (hμb : ∀ F, IsAdmissible n U (Function.update v i₀ b) F → TendstoMixed U F μb)
    (hexa : ∃ F, IsAdmissible n U (Function.update v i₀ a) F)
    (hexb : ∃ B, IsDecApprox U b B) :
    μ.restrict (U : Set (ComplexModel n)) = (μa + μb).restrict (U : Set (ComplexModel n)) := by
  classical
  obtain ⟨F, hF⟩ := hexa
  obtain ⟨B, hB⟩ := hexb
  set F' : Fin n → ℕ → ComplexModel n → ℝ :=
    Function.update F i₀ (fun k z ↦ F i₀ k z + B k z) with hF'_def
  have hF' : IsAdmissible n U (Function.update v i₀ fun z ↦ a z + b z) F' :=
    IsAdmissible.update_add i₀ hF hB
  set G : Fin n → ℕ → ComplexModel n → ℝ := Function.update F i₀ B with hG_def
  have hG : IsAdmissible n U (Function.update v i₀ b) G := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h; simpa [hG_def] using hB
    · simpa [hG_def, Function.update_of_ne h] using hF.1 i
  have hfinite (ν : Measure (ComplexModel n)) (hν : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ U → ν K < ⊤ := hν
  refine restrict_eq_of_testFunction_integral_eq hμf (fun K hK hKU ↦ ?_) fun φ ↦ ?_
  · rw [add_apply]
    exact ENNReal.add_lt_top.2 ⟨hμaf K hK hKU, hμbf K hK hKU⟩
  · have hφU := φ.tsupport_subset
    have h1 := hμ F' hF' φ φ.continuous φ.hasCompactSupport hφU
    have h2 := hμa F hF φ φ.continuous φ.hasCompactSupport hφU
    have h3 := hμb G hG φ φ.continuous φ.hasCompactSupport hφU
    have hdens (k : ℕ) (z : ComplexModel n) (hz : z ∈ (U : Set (ComplexModel n))) :
        mixedDensity (fun i ↦ F' i k) z =
          mixedDensity (fun i ↦ F i k) z + mixedDensity (fun i ↦ G i k) z := by
      have h2' : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
      have hAz : ContDiffAt ℝ 2 (F i₀ k) z :=
        (((hF.1 i₀).1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2'
      have hBz : ContDiffAt ℝ 2 (B k) z :=
        (((hB.1 k).1).contDiffAt (U.isOpen.mem_nhds hz)).of_le h2'
      have hupd (H : Fin n → ℕ → ComplexModel n → ℝ) (c : ℕ → ComplexModel n → ℝ) :
          (fun i ↦ (Function.update H i₀ c) i k) = Function.update (fun i ↦ H i k) i₀ (c k) := by
        funext i
        by_cases h : i = i₀
        · subst h; simp
        · simp [Function.update_of_ne h]
      have hadd := mixedDensity_update_add (f := fun i ↦ F i k) i₀ hAz hBz
      rw [Function.update_eq_self] at hadd
      rw [hF'_def, hG_def, hupd F (fun k z ↦ F i₀ k z + B k z), hupd F B]
      exact hadd
    have hsum (k : ℕ) : ∫ z, φ z * mixedDensity (fun i ↦ F' i k) z =
        (∫ z, φ z * mixedDensity (fun i ↦ F i k) z) +
          ∫ z, φ z * mixedDensity (fun i ↦ G i k) z := by
      have hI1 : Integrable fun z ↦ φ z * mixedDensity (fun i ↦ F i k) z :=
        integrable_mul_of_continuousOn (continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1)
          φ.continuous φ.hasCompactSupport hφU
      have hI2 : Integrable fun z ↦ φ z * mixedDensity (fun i ↦ G i k) z :=
        integrable_mul_of_continuousOn (continuousOn_mixedDensity fun i ↦ ((hG.1 i).1 k).1)
          φ.continuous φ.hasCompactSupport hφU
      rw [← integral_add hI1 hI2]
      congr 1
      funext z
      by_cases hz : z ∈ (U : Set (ComplexModel n))
      · rw [hdens k z hz]; ring
      · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]
    rw [integral_add_measure]
    · exact tendsto_nhds_unique (by simpa only [hsum] using h1) (h2.add h3)
    · exact integrable_of_bounded_of_support (isClosed_tsupport φ).measurableSet
        (hμaf _ φ.hasCompactSupport hφU) φ.continuous.stronglyMeasurable
        (exists_bound_of_continuous_of_hasCompactSupport φ.continuous
          φ.hasCompactSupport).choose_spec.2
        fun z hz ↦ image_eq_zero_of_notMem_tsupport hz
    · exact integrable_of_bounded_of_support (isClosed_tsupport φ).measurableSet
        (hμbf _ φ.hasCompactSupport hφU) φ.continuous.stronglyMeasurable
        (exists_bound_of_continuous_of_hasCompactSupport φ.continuous
          φ.hasCompactSupport).choose_spec.2
        fun z hz ↦ image_eq_zero_of_notMem_tsupport hz

/-- **Slot additivity of Bedford–Taylor limits.** The limit for the tuple with
`a + b` in slot `i₀` is the sum of the limits for `a` and for `b` in that slot. -/
theorem IsBTLimit.add_slot {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) {a b : ComplexModel n → ℝ} {μ μa μb : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (Function.update v i₀ fun z ↦ a z + b z) μ)
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa)
    (hμb : IsBTLimit Ω (Function.update v i₀ b) μb) :
    μ = μa + μb := by
  classical
  have hsum_compl : (μa + μb) (Ω : Set (ComplexModel n))ᶜ = 0 := by
    rw [add_apply, hμa.1, hμb.1, add_zero]
  have hself (ν : Measure (ComplexModel n)) (hν : ν (Ω : Set (ComplexModel n))ᶜ = 0) :
      ν.restrict (Ω : Set (ComplexModel n)) = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν)
  rw [← hself μ hμ.1, ← hself _ hsum_compl]
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hcover : (Ω : Set (ComplexModel n)) = ⋃ m, ((U m : Set (ComplexModel n))) := by
    ext z
    simp only [mem_iUnion]
    constructor
    · intro hz
      obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hz)
      exact ⟨m, hm rfl⟩
    · rintro ⟨m, hm⟩
      exact hUΩ m hm
  rw [hcover, Measure.restrict_iUnion_congr]
  intro m
  set V := U m with hV_def
  have hVrc : RelativelyCompactIn V Ω := hUrc m
  have hfin (ν : Measure (ComplexModel n)) (hν : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ν K < ⊤ := fun K hK hKV ↦ hν K hK (hKV.trans (hUΩ m))
  obtain ⟨F, hF, hFT⟩ := hμa.2.2 V hVrc
  obtain ⟨G, hG, hGT⟩ := hμb.2.2 V hVrc
  obtain ⟨F₁, hF₁, hF₁T⟩ := hμ.2.2 V hVrc
  have hB : IsDecApprox V b (G i₀) := by simpa using hG.1 i₀
  obtain ⟨ν₁, -, hν₁f, hν₁T⟩ := pClaim_all (n := n) V (Function.update v i₀ fun z ↦ a z + b z)
  obtain ⟨ν₂, -, hν₂f, hν₂T⟩ := pClaim_all (n := n) V (Function.update v i₀ a)
  obtain ⟨ν₃, -, hν₃f, hν₃T⟩ := pClaim_all (n := n) V (Function.update v i₀ b)
  have e1 : μ.restrict V = ν₁.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfin μ hμ.2.1) hν₁f fun φ ↦
      tendsto_nhds_unique (hF₁T φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hν₁T F₁ hF₁ φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have e2 : μa.restrict V = ν₂.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfin μa hμa.2.1) hν₂f fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hν₂T F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have e3 : μb.restrict V = ν₃.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfin μb hμb.2.1) hν₃f fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hν₃T G hG φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hadd := restrict_eq_of_add_slot (v := v) i₀ hν₁f hν₂f hν₃f hν₁T hν₂T hν₃T
    ⟨F, hF⟩ ⟨G i₀, hB⟩
  have hVeq : μ.restrict (V : Set (ComplexModel n)) = (μa + μb).restrict V :=
    calc μ.restrict (V : Set (ComplexModel n)) = ν₁.restrict V := e1
      _ = (ν₂ + ν₃).restrict V := hadd
      _ = ν₂.restrict V + ν₃.restrict V := Measure.restrict_add _ _ _
      _ = μa.restrict V + μb.restrict V := by rw [e2, e3]
      _ = (μa + μb).restrict V := (Measure.restrict_add _ _ _).symm
  exact hVeq

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
