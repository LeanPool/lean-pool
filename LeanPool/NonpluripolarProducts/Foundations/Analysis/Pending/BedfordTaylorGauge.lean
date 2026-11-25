/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MeasureLocality

/-!
# Bedford–Taylor limit measures under pluriharmonic gauge changes

A measure is a *Bedford–Taylor limit* for a tuple on an open set when, on every
relatively compact open subset, some decreasing smooth approximation of the
tuple has mixed densities converging to it. Such a measure is unique, it is
unchanged when a smooth function with vanishing complex Hessian is added to the
slots (the approximations shift and their densities do not change), and the
max-constant locality then extends to a maximum with a pluriharmonic obstacle.

These are the ingredients for the invariance of the non-pluripolar truncation
limits under a change of local potential.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- `μ` is the Bedford–Taylor limit of the tuple `u` on `Ω`. -/
def IsBTLimit (Ω : Opens (ComplexModel n)) (u : Fin n → ComplexModel n → ℝ)
    (μ : Measure (ComplexModel n)) : Prop :=
  μ (Ω : Set (ComplexModel n))ᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
    ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U u F ∧ TendstoMixed U F μ

theorem exists_isBTLimit {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hadm : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U u F) :
    ∃ μ, IsBTLimit Ω u μ := by
  obtain ⟨μ, hμc, hμf, hμT⟩ := exists_measure_tendstoMixed_of_exists hadm
  exact ⟨μ, hμc, hμf, fun U hU ↦ (hadm U hU).imp fun F hF ↦ ⟨hF, hμT U hU F hF⟩⟩

/-- **Uniqueness** of Bedford–Taylor limits. -/
theorem IsBTLimit.unique {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ) (hν : IsBTLimit Ω u ν) : μ = ν := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hunion : (⋃ m, (U m : Set (ComplexModel n))) = Ω := by
    refine subset_antisymm (iUnion_subset hUΩ) fun z hz ↦ ?_
    obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hz)
    exact mem_iUnion.2 ⟨m, hm rfl⟩
  have hloc (m : ℕ) : μ.restrict (U m) = ν.restrict (U m) := by
    obtain ⟨μU, -, hμUf, hμUT⟩ := pClaim_all (n := n) (U m) u
    have hfin (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
        ∀ K, IsCompact K → K ⊆ U m → ρ K < ⊤ := fun K hK hKU ↦ hρ K hK (hKU.trans (hUΩ m))
    have e (ρ : Measure (ComplexModel n)) (hρ : IsBTLimit Ω u ρ) :
        ρ.restrict (U m) = μU.restrict (U m) := by
      obtain ⟨F, hF, hFT⟩ := hρ.2.2 (U m) (hUrc m)
      exact restrict_eq_of_testFunction_integral_eq (hfin ρ hρ.2.1) hμUf fun φ ↦
        tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
          (hμUT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
    rw [e μ hμ, e ν hν]
  have hself (ρ : Measure (ComplexModel n)) (hρ : ρ (Ω : Set (ComplexModel n))ᶜ = 0) :
      ρ.restrict Ω = ρ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hρ)
  rw [← hself μ hμ.1, ← hself ν hν.1, ← hunion]
  exact Measure.restrict_iUnion_congr.2 hloc

/-- Every admissible family on a relatively compact subset converges to a
Bedford–Taylor limit. -/
theorem IsBTLimit.tendstoMixed {Ω U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (hU : RelativelyCompactIn U Ω) {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) : TendstoMixed U F μ := by
  obtain ⟨μ', hμ'c, hμ'f, hμ'T⟩ := exists_measure_tendstoMixed_of_exists
    (Ω := Ω) (u := u) fun V hV ↦ (hμ.2.2 V hV).imp fun _ h ↦ h.1
  have h' : IsBTLimit Ω u μ' :=
    ⟨hμ'c, hμ'f, fun V hV ↦ (hμ.2.2 V hV).imp fun G hG ↦ ⟨hG.1, hμ'T V hV G hG.1⟩⟩
  rw [← h'.unique hμ]
  exact hμ'T U hU F hF

theorem IsBTLimit.congr {Ω : Opens (ComplexModel n)} {u v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ) (h : ∀ i, EqOn (u i) (v i) Ω) :
    IsBTLimit Ω v μ := by
  refine ⟨hμ.1, hμ.2.1, fun U hU ↦ (hμ.2.2 U hU).imp fun F hF ↦ ⟨⟨fun i ↦ ?_, hF.1.2⟩, hF.2⟩⟩
  exact (hF.1.1 i).congr ((h i).mono (subset_closure.trans hU.2))

theorem IsLocalMixedBedfordTaylorMeasure.isBTLimit {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ) : IsBTLimit Ω v μ :=
  ⟨hμ.2.1, hμ.2.2.1, fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed
    hμ hU⟩

theorem IsLocalBedfordTaylorMeasure.isBTLimit {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ) : IsBTLimit Ω (fun _ ↦ v) μ :=
  ⟨hμ.2.1, hμ.2.2.1, fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU⟩

/-- Smooth on `Ω` with vanishing complex Hessian. -/
def IsSmoothPluriharmonicOn (Ω : Opens (ComplexModel n)) (h : ComplexModel n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h Ω ∧ ∀ z ∈ Ω, complexHessian h z = 0

theorem IsSmoothPluriharmonicOn.mono {Ω U : Opens (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hh : IsSmoothPluriharmonicOn Ω h) (hU : U ≤ Ω) : IsSmoothPluriharmonicOn U h :=
  ⟨hh.1.mono hU, fun z hz ↦ hh.2 z (hU hz)⟩

theorem complexHessian_add_of_isSmoothPluriharmonicOn {Ω : Opens (ComplexModel n)}
    {f h : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (hh : IsSmoothPluriharmonicOn Ω h)
    {z : ComplexModel n} (hz : z ∈ Ω) :
    complexHessian (fun y ↦ f y + h y) z = complexHessian f z := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [show (fun y ↦ f y + h y) = f + h from rfl,
    complexHessian_add ((hf.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le h2)
      ((hh.1.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le h2), hh.2 z hz, add_zero]

theorem IsSmoothPluriharmonicOn.neg {Ω : Opens (ComplexModel n)} {h : ComplexModel n → ℝ}
    (hh : IsSmoothPluriharmonicOn Ω h) : IsSmoothPluriharmonicOn Ω fun z ↦ -h z := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨hh.1.neg, fun z hz ↦ ?_⟩
  have := complexHessian_smul ((hh.1.contDiffAt (Ω.isOpen.mem_nhds hz)).of_le h2) (-1)
  rw [show (fun y ↦ -h y) = (-1 : ℝ) • h by funext y; simp, this, hh.2 z hz, smul_zero]

theorem IsDecApprox.add_pluriharmonic {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {h : ComplexModel n → ℝ}
    (hh : IsSmoothPluriharmonicOn U h) :
    IsDecApprox U (fun z ↦ w z + h z) (fun k z ↦ G k z + h z) := by
  refine ⟨fun k ↦ ⟨(hG.1 k).1.add hh.1, fun z hz ↦ ?_⟩, fun z hz k l hkl ↦ ?_,
    fun z hz ↦ (hG.2.2.1 z hz).add_const _, fun K hK hKU ↦ ?_⟩
  · rw [complexHessian_add_of_isSmoothPluriharmonicOn (hG.1 k).1 hh hz]
    exact (hG.1 k).2 z hz
  · simpa using hG.2.1 z hz hkl
  · obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
    obtain ⟨m', hm'⟩ := (hK.image_of_continuousOn (hh.1.continuousOn.mono hKU)).bddBelow
    exact ⟨m + m', by
      rintro _ ⟨z, hz, rfl⟩
      exact add_le_add (hm ⟨z, hz, rfl⟩) (hm' ⟨z, hz, rfl⟩)⟩

/-- **Gauge invariance.** Adding smooth functions with vanishing complex Hessian
to the slots does not change the Bedford–Taylor limit. -/
theorem IsBTLimit.add_pluriharmonic {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    {h : Fin n → ComplexModel n → ℝ} (hh : ∀ i, IsSmoothPluriharmonicOn Ω (h i)) :
    IsBTLimit Ω (fun i z ↦ u i z + h i z) μ := by
  refine ⟨hμ.1, hμ.2.1, fun U hU ↦ ?_⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 U hU
  refine ⟨fun i k z ↦ F i k z + h i z, ⟨fun i ↦ (hF.1 i).add_pluriharmonic ((hh i).mono hUΩ),
    fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩, fun φ hφ hφc hφU ↦ ?_⟩
  refine (hFT φ hφ hφc hφU).congr fun k ↦ ?_
  congr 1; funext z
  by_cases hz : z ∈ (U : Set (ComplexModel n))
  · rw [mixedDensity_congr_hessian fun i ↦
      complexHessian_add_of_isSmoothPluriharmonicOn ((hF.1 i).1 k).1 ((hh i).mono hUΩ) hz]
  · simp [image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hφU h')]

theorem IsBTLimit.exists_add_pluriharmonic {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    {h : Fin n → ComplexModel n → ℝ} (hh : ∀ i, IsSmoothPluriharmonicOn Ω (h i))
    (c : ℝ) : ∃ ν, IsBTLimit Ω (fun i z ↦ max (u i z + h i z) c) ν := by
  refine exists_isBTLimit fun U hU ↦ ?_
  obtain ⟨F, hF, -⟩ := (hμ.add_pluriharmonic hh).2.2 U hU
  obtain ⟨F', hF'⟩ := exists_isAdmissible_maxTuple hF c n
  refine ⟨F', fun i ↦ ?_, hF'.2⟩
  simpa [maxTupleObstacle] using hF'.1 i

/-- **Locality for a pluriharmonic obstacle.** -/
theorem IsBTLimit.restrict_max_pluriharmonic {Ω : Opens (ComplexModel n)}
    {v w φ : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω v μ) (hν : IsBTLimit Ω w ν) (hφ : ∀ i, IsSmoothPluriharmonicOn Ω (φ i))
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) (φ i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, φ i z < v i z} = μ.restrict {z | z ∈ Ω ∧ ∀ i, φ i z < v i z} := by
  have hμ' := hμ.add_pluriharmonic fun i ↦ (hφ i).neg
  have hν' := hν.add_pluriharmonic fun i ↦ (hφ i).neg
  have h := restrict_eq_of_max_const (v := fun i z ↦ v i z + -φ i z)
    (w := fun i z ↦ w i z + -φ i z) 0 hμ'.2.1 hν'.2.1 hμ'.2.2 hν'.2.2 fun i z hz ↦ by
      simp only [hmax i hz, ← sub_eq_add_neg]
      rw [← max_sub_sub_right, sub_self]
  have hset : {z | z ∈ Ω ∧ ∀ i, (0 : ℝ) < v i z + -φ i z} = {z | z ∈ Ω ∧ ∀ i, φ i z < v i z} := by
    ext z; simp [← sub_eq_add_neg, sub_pos]
  rwa [hset] at h

/-- Restriction of a Bedford–Taylor limit to an open subset. -/
theorem IsBTLimit.restrict_opens {Ω V : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ) (hVΩ : V ≤ Ω) :
    IsBTLimit V u (μ.restrict V) := by
  refine ⟨by rw [Measure.restrict_apply' V.isOpen.measurableSet]; simp,
    MeasureLocality.finiteOnCompacts_restrict hμ.2.1 hVΩ,
    fun U hU ↦ ?_⟩
  have hUΩ : RelativelyCompactIn U Ω := ⟨hU.1, hU.2.trans hVΩ⟩
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 U hUΩ
  refine ⟨F, hF, fun φ hφ hφc hφU ↦ ?_⟩
  rw [MeasureLocality.integral_restrict_eq_of_tsupport_subset
    (hφU.trans (subset_closure.trans hU.2))]
  exact hFT φ hφ hφc hφU

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
