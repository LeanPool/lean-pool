/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.UniformBoundedGlobalMass
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GlobalMeasureInvariance

/-!
# Compact integration by parts for bounded global mixed measures

For bounded `η`-PSH potentials on a compact complex manifold carrying a Kähler
form `κ`, replacing the potential of one slot by another bounded one does not
change the total mass of the global mixed measure. This is the compact form of
`∫ ddᶜ(a - b) ∧ T = 0`.

The regularized slot defect `ddᶜf ∧ T` of a chart-smooth `f` is made *global*
from the start: it is the pair of global measures `T(f)`, `T(0)` whose slot
`i₀` carries the background `η i₀ + C κ` and the potential `f`, respectively
`0`. Both are glued by the existing construction, so no chart covariance of the
defect has to be proved. In a chart the slot functions are `f + p` and `p`, for
`p` the local potential of `η i₀ + C κ`, and
`Pending.BedfordTaylorSlotStokes` gives, for a partition-of-unity function `χ_b`,

  `∫ χ_b dμ_a - ∫ χ_b dμ_v = ∫ g dT(χ_b) - ∫ g dT(0)`,     `g = a - v i₀`,

where `μ_a` carries `a` in slot `i₀` and `μ_v` the original tuple.

Summing over `b`, the right-hand sides telescope: chartwise
`Σ_b μ(χ_b + p) = μ(1 + m p) = μ(m p) = m μ(p)`, so `Σ_b T(χ_b) = m T(0)`.
-/

@[expose] public section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.GlobalSlotStokes

open FirstPass FirstPass.GlobalPotentialPatches FirstPass.PositiveClasses
open MixedNonPluripolar MixedMongeAmpere GlobalNonPluripolar BoundedGlobalProduct
open BedfordTaylor FirstPass.MongeAmpere

noncomputable section

/-- Two measures on a second-countable space agreeing on every member of an open
cover are equal. -/
theorem measure_eq_of_restrict_eq_of_openCover {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] {ι : Type*} (S : ι → Set X)
    (hS : ∀ i, IsOpen (S i)) (hcover : ∀ x, ∃ i, x ∈ S i) {μ ν : Measure X}
    (h : ∀ i, μ.restrict (S i) = ν.restrict (S i)) : μ = ν := by
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable S hS
  have : Countable T := hTc.to_subtype
  have huniv : (⋃ i : T, S i) = univ := by
    refine eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨i, hi⟩ := hcover x
    have hx : x ∈ ⋃ i ∈ T, S i := hTU ▸ mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨j, hjT, hxj⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨j, hjT⟩, hxj⟩
  have := Measure.restrict_iUnion_congr.mpr fun i : T => h i
  rwa [huniv, Measure.restrict_univ, Measure.restrict_univ] at this

/-- A Bedford–Taylor limit restricts to a Bedford–Taylor limit on a smaller open
set. -/
theorem _root_.SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsBTLimit.restrict_open {n : ℕ} {Ω
    U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (hU : U ≤ Ω) : IsBTLimit U u (μ.restrict (U : Set (ComplexModel n))) := by
  refine ⟨?_, fun K hK hKU => ?_, fun V hV => ?_⟩
  · rw [Measure.restrict_apply' U.isOpen.measurableSet]; simp
  · exact lt_of_le_of_lt (Measure.restrict_le_self K) (hμ.2.1 K hK (hKU.trans hU))
  · have hVΩ : RelativelyCompactIn V Ω := ⟨hV.1, hV.2.trans hU⟩
    obtain ⟨F, hF, hT⟩ := hμ.2.2 V hVΩ
    refine ⟨F, hF, fun φ hφ hφc hφV => ?_⟩
    have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) := hφV.trans (subset_closure.trans hV.2)
    have hint : (∫ z, φ z ∂(μ.restrict (U : Set (ComplexModel n)))) = ∫ z, φ z ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
    rw [hint]
    exact hT φ hφ hφc hφV

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Chart-smooth functions are continuous. -/
theorem ChartSmooth.continuous {f : M → ℝ} (hf : ChartSmooth (n := n) f) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hc : ContinuousAt (fun z => f (e.val.symm z)) (e.val x) :=
    ((hf e).continuousOn).continuousAt (e.val.open_target.mem_nhds hz)
  have hcomp : ContinuousAt ((fun z => f (e.val.symm z)) ∘ e.val) x :=
    hc.comp (e.val.continuousAt hx)
  refine hcomp.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, e.val.left_inv hy]

section Transport

variable [MeasurableSpace M] [BorelSpace M]
  {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}

/-- **Integrals against a transported patch measure** are coordinate integrals. -/
theorem
    _root_.SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches.Patch.integral_pushMeasure
    (P : Patch θ u) {μ : Measure (ComplexModel n)}
    (hμ : μ (P.domain : Set (ComplexModel n))ᶜ = 0) (F : M → ℝ) :
    ∫ x, F x ∂(P.pushMeasure μ) = ∫ z, F (P.chart.val.symm z) ∂μ := by
  rw [Patch.pushMeasure, P.measurableEmbedding_toManifold.integral_map]
  have h := integral_subtype_comap (μ := μ) P.domain.isOpen.measurableSet
    (fun z => F (P.chart.val.symm z))
  refine h.trans ?_
  rw [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)]

end Transport

/-! ### Charts carrying all the local potentials -/

/-- A coordinate domain on which every background `η i` and the Kähler form `κ`
have smooth local potentials. Unlike a `Patch` it involves no potential of `M`,
so it serves every tuple and every regularized background at once. -/
structure SlotChart (η : Fin n → ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm n M) where
  /-- The chart in which all backgrounds have local potentials. -/
  chart : ComplexChart n M
  /-- The common coordinate domain of the local potentials. -/
  domain : Opens (ComplexModel n)
  domain_le_target : (domain : Set (ComplexModel n)) ⊆ chart.val.target
  /-- The local potentials for the slot backgrounds. -/
  potential : Fin n → ComplexModel n → ℝ
  localPotential : ∀ i, IsSmoothLocalPotential (η i).val chart domain (potential i)
  /-- The local potential of the Kähler form. -/
  kahler : ComplexModel n → ℝ
  kahlerLocal : IsSmoothLocalPotential κ.val chart domain kahler

namespace SlotChart

variable {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}

/-- The manifold neighbourhood of the coordinate domain. -/
def source (J : SlotChart η κ) : Opens M :=
  ⟨J.chart.val.source ∩ J.chart.val ⁻¹' J.domain,
    J.chart.val.isOpen_inter_preimage J.domain.isOpen⟩

/-- Slot charts cover the manifold. -/
theorem exists_mem_source (η : Fin n → ClosedRealOneOneForm n M)
    (κ : ClosedRealOneOneForm n M) (x : M) : ∃ J : SlotChart η κ, x ∈ J.source := by
  classical
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  choose W ρ hmem hloc using fun i =>
    LocalPotentials.closedRealOneOne_hasLocalPotentials (η i) e (e.val x) hz
  obtain ⟨Wκ, σ, hmemκ, hlocκ⟩ :=
    LocalPotentials.closedRealOneOne_hasLocalPotentials κ e (e.val x) hz
  let D : Opens (ComplexModel n) :=
    ⟨e.val.target ∩ (Wκ ∩ ⋂ i, W i),
      e.val.open_target.inter (hlocκ.1.inter (isOpen_iInter_of_finite fun i => (hloc i).1))⟩
  have hDW (i : Fin n) : (D : Set (ComplexModel n)) ⊆ W i :=
    fun _ hy => mem_iInter.mp hy.2.2 i
  have hDκ : (D : Set (ComplexModel n)) ⊆ Wκ := fun _ hy => hy.2.1
  refine ⟨{
    chart := e
    domain := D
    domain_le_target := inter_subset_left
    potential := ρ
    localPotential := fun i => (hloc i).mono D.isOpen (hDW i)
    kahler := σ
    kahlerLocal := hlocκ.mono D.isOpen hDκ }, ?_⟩
  exact ⟨hx, hz, hmemκ, mem_iInter.mpr hmem⟩

/-- The patch of a tuple of `η`-PSH potentials on a slot chart. -/
def patch (J : SlotChart η κ) (u : Fin n → M → EReal)
    (hu : ∀ i, ThetaPlurisubharmonic (η i).val (u i)) : Patch η u where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_le_target
  potential := J.potential
  localPotential := J.localPotential
  plurisubharmonic i :=
    BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn (hu i) J.chart
      (J.localPotential i)

/-- The regularized backgrounds: slot `i₀` gets `η i₀ + C κ`. -/
def regForms (η : Fin n → ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm n M)
    (i₀ : Fin n) (C : ℝ) : Fin n → ClosedRealOneOneForm n M :=
  Function.update η i₀ (η i₀ + C • κ)

/-- The same chart, read for the regularized backgrounds. -/
def lift (J : SlotChart η κ) (i₀ : Fin n) (C : ℝ) : SlotChart (regForms η κ i₀ C) κ where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_le_target
  potential := Function.update J.potential i₀ fun z => J.potential i₀ z + C • J.kahler z
  localPotential i := by
    classical
    by_cases h : i = i₀
    · subst h
      simp only [regForms, Function.update_self]
      exact FirstPass.LocalPotentials.localPotential_add (J.localPotential i)
        (FirstPass.LocalPotentials.localPotential_smul J.kahlerLocal C)
    · simp only [regForms, Function.update_of_ne h]
      exact J.localPotential i
  kahler := J.kahler
  kahlerLocal := J.kahlerLocal

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The local model of a bounded global measure.** On a slot chart the global
mixed measure of a bounded tuple is the transported Bedford–Taylor limit of the
real corrected potentials. -/
theorem exists_isBTLimit (J : SlotChart η κ) {u : Fin n → M → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic (η i).val (u i)) (hb : ∀ i, IsBoundedPotential (u i)) :
    ∃ μ : Measure (ComplexModel n),
      IsBTLimit J.domain (fun i z => (u i (J.chart.val.symm z)).toReal + J.potential i z) μ ∧
      (globalMixedMeasure η u hu).restrict (J.source : Set M) = (J.patch u hu).pushMeasure μ := by
  set P := J.patch u hu
  refine ⟨canonicalMixedBedfordTaylorMeasure P.domain (correctedReal P)
    (correctedReal_isLocallyBoundedMixedPshOn hb P), ?_,
    globalMixedMeasure_restrict_patch_eq_canonical hu hb P⟩
  have h := IsLocalMixedBedfordTaylorMeasure.isBTLimit
    (canonicalMixedBedfordTaylorMeasure_spec P.domain (correctedReal P)
      (correctedReal_isLocallyBoundedMixedPshOn hb P))
  exact h.congr fun i z _ => correctedReal_eq (hb i) P z

end SlotChart

/-! ### The global regularized slot defect -/

section Defect

variable {η : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}

/-- The tuple with the real function `f` in slot `i₀`. -/
def slotTuple (v : Fin n → M → EReal) (i₀ : Fin n) (f : M → ℝ) : Fin n → M → EReal :=
  Function.update v i₀ fun x => ((f x : ℝ) : EReal)

theorem slotTuple_thetaPlurisubharmonic {v : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i)) (i₀ : Fin n) (C : ℝ) {f : M → ℝ}
    (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f x : ℝ) : EReal)) :
    ∀ i, ThetaPlurisubharmonic (SlotChart.regForms η κ i₀ C i).val (slotTuple v i₀ f i) := by
  classical
  intro i
  by_cases h : i = i₀
  · subst h; simpa [slotTuple, SlotChart.regForms] using hf
  · simpa [slotTuple, SlotChart.regForms, Function.update_of_ne h] using hv i

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
theorem slotTuple_isBoundedPotential [CompactSpace M] {v : Fin n → M → EReal}
    (hb : ∀ i, IsBoundedPotential (v i)) (i₀ : Fin n) {f : M → ℝ} (hfc : Continuous f) :
    ∀ i, IsBoundedPotential (slotTuple v i₀ f i) := by
  classical
  intro i
  by_cases h : i = i₀
  · subst h
    obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn hfc.continuousOn
    refine ⟨-Q, Q, fun x => ?_⟩
    have hx := abs_le.mp (by simpa [Real.norm_eq_abs] using hQ x (mem_univ x))
    simp only [slotTuple, Function.update_self]
    exact ⟨EReal.coe_le_coe_iff.mpr hx.1, EReal.coe_le_coe_iff.mpr hx.2⟩
  · simpa [slotTuple, Function.update_of_ne h] using hb i

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- **The regularized defect measure** `T(f)`: slot `i₀` carries the background
`η i₀ + C κ` and the potential `f`. -/
def defectMeasure {v : Fin n → M → EReal} (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
    (i₀ : Fin n) (C : ℝ) (f : M → ℝ)
    (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f x : ℝ) : EReal)) : Measure M :=
  globalMixedMeasure (SlotChart.regForms η κ i₀ C) (slotTuple v i₀ f)
    (slotTuple_thetaPlurisubharmonic hv i₀ C hf)

namespace SlotChart

/-- The real corrected potentials of `v` on a slot chart. -/
def localSlots (J : SlotChart η κ) (v : Fin n → M → EReal) : Fin n → ComplexModel n → ℝ :=
  fun i z => (v i (J.chart.val.symm z)).toReal + J.potential i z

/-- The local regularizer: the potential of `η i₀ + C κ`. -/
def regularizer (J : SlotChart η κ) (i₀ : Fin n) (C : ℝ) : ComplexModel n → ℝ :=
  fun z => J.potential i₀ z + C • J.kahler z

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem localSlots_update (J : SlotChart η κ) (v : Fin n → M → EReal) (i₀ : Fin n)
    (a : M → EReal) :
    (fun i z => (Function.update v i₀ a i (J.chart.val.symm z)).toReal + J.potential i z) =
      Function.update (J.localSlots v) i₀
        fun z => (a (J.chart.val.symm z)).toReal + J.potential i₀ z := by
  classical
  funext i z
  by_cases h : i = i₀
  · subst h; simp
  · simp [localSlots, Function.update_of_ne h]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem localSlots_lift (J : SlotChart η κ) (v : Fin n → M → EReal) (i₀ : Fin n) (C : ℝ)
    (f : M → ℝ) :
    (fun i z => (slotTuple v i₀ f i ((J.lift i₀ C).chart.val.symm z)).toReal +
        (J.lift i₀ C).potential i z) =
      Function.update (J.localSlots v) i₀
        fun z => f (J.chart.val.symm z) + J.regularizer i₀ C z := by
  classical
  funext i z
  by_cases h : i = i₀
  · subst h; simp [slotTuple, lift, regularizer]
  · simp [slotTuple, lift, localSlots, Function.update_of_ne h]

/-- The local model of a defect measure. -/
theorem exists_isBTLimit_defect (J : SlotChart η κ) {v : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i)) (hb : ∀ i, IsBoundedPotential (v i))
    (i₀ : Fin n) (C : ℝ) {f : M → ℝ}
    (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f x : ℝ) : EReal))
    (hfc : Continuous f) :
    ∃ μ : Measure (ComplexModel n),
      IsBTLimit J.domain (Function.update (J.localSlots v) i₀
        fun z => f (J.chart.val.symm z) + J.regularizer i₀ C z) μ ∧
      (defectMeasure hv i₀ C f hf).restrict (J.source : Set M) =
        ((J.lift i₀ C).patch (slotTuple v i₀ f)
          (slotTuple_thetaPlurisubharmonic hv i₀ C hf)).pushMeasure μ := by
  obtain ⟨μ, hμ, heq⟩ := (J.lift i₀ C).exists_isBTLimit
    (slotTuple_thetaPlurisubharmonic hv i₀ C hf) (slotTuple_isBoundedPotential hb i₀ hfc)
  refine ⟨μ, ?_, heq⟩
  rw [← localSlots_lift J v i₀ C f]
  exact hμ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **A chart-supported function read in coordinates** is a compactly supported
smooth function on the model space, supported in the chart domain. -/
theorem exists_coordinate_test (J : SlotChart η κ) {f : M → ℝ} (hfs : ChartSmooth (n := n) f)
    (hfJ : tsupport f ⊆ (J.source : Set M)) (hfK : IsCompact (tsupport f)) :
    ∃ φ : ComplexModel n → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ (J.domain : Set (ComplexModel n)) ∧
      EqOn φ (fun z => f (J.chart.val.symm z)) J.domain ∧
      ∀ x ∈ tsupport f, J.chart.val x ∈ tsupport φ := by
  classical
  set e := J.chart with he
  have hsrc : tsupport f ⊆ e.val.source := fun x hx => (hfJ hx).1
  set K : Set (ComplexModel n) := e.val '' tsupport f with hK
  have hKc : IsCompact K := hfK.image_of_continuousOn (e.val.continuousOn.mono hsrc)
  have hKD : K ⊆ (J.domain : Set (ComplexModel n)) := by
    rintro _ ⟨x, hx, rfl⟩; exact (hfJ hx).2
  have hDt : (J.domain : Set (ComplexModel n)) ⊆ e.val.target := J.domain_le_target
  set φ : ComplexModel n → ℝ := fun z => if z ∈ e.val.target then f (e.val.symm z) else 0
    with hφ
  have hzero : ∀ z ∉ K, φ z = 0 := by
    intro z hz
    by_cases ht : z ∈ e.val.target
    · simp only [hφ, ite_eq_left ht]
      by_contra hne
      exact hz ⟨e.val.symm z, subset_tsupport f hne, e.val.right_inv ht⟩
    · simp [hφ, ite_eq_right ht]
  have hsupp : tsupport φ ⊆ K :=
    closure_minimal (fun z hz => by_contra fun h => hz (hzero z h)) hKc.isClosed
  have hsmooth : ContDiff ℝ ∞ φ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases ht : z ∈ e.val.target
    · refine ((hfs e).contDiffAt (e.val.open_target.mem_nhds ht)).congr_of_eventuallyEq ?_
      filter_upwards [e.val.open_target.mem_nhds ht] with y hy
      simp [hφ, ite_eq_left hy]
    · have hzK : z ∉ K := fun h => ht (hDt (hKD h))
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hzK] with y hy
      exact hzero y hy
  refine ⟨φ, hsmooth, hKc.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hKD,
    fun z hz => by simp [hφ, ite_eq_left (hDt hz)], fun x hx => ?_⟩
  have himg : e.val '' Function.support f ⊆ Function.support φ := by
    rintro _ ⟨y, hy, rfl⟩
    have hys : y ∈ e.val.source := hsrc (subset_tsupport f hy)
    simp only [Function.mem_support, hφ, ite_eq_left (e.val.map_source hys), e.val.left_inv hys]
    exact hy
  exact closure_mono himg (mem_closure_image (e.val.continuousAt (hsrc hx)) hx)

end SlotChart

variable {v : Fin n → M → EReal} (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i))
  (hb : ∀ i, IsBoundedPotential (v i)) (i₀ : Fin n) (C : ℝ)

include hb in
/-- **Locality of the defect.** Where `f` vanishes, `T(f)` and `T(0)` agree. -/
theorem defectMeasure_restrict_eq {f : M → ℝ}
    (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f x : ℝ) : EReal))
    (hfc : Continuous f)
    (h0 : ThetaPlurisubharmonic (η i₀ + C • κ).val fun _ => (((0 : ℝ) : ℝ) : EReal))
    {W : Set M} (hW : IsOpen W) (hfW : ∀ x ∈ W, f x = 0) :
    (defectMeasure hv i₀ C f hf).restrict W =
      (defectMeasure hv i₀ C (fun _ => 0) h0).restrict W := by
  refine measure_eq_of_restrict_eq_of_openCover (fun J : SlotChart η κ => (J.source : Set M))
    (fun J => J.source.isOpen) (fun x => SlotChart.exists_mem_source η κ x) fun J => ?_
  rw [Measure.restrict_comm J.source.isOpen.measurableSet,
    Measure.restrict_comm J.source.isOpen.measurableSet]
  obtain ⟨μf, hμf, hfeq⟩ := J.exists_isBTLimit_defect hv hb i₀ C hf hfc
  obtain ⟨μ0, hμ0, h0eq⟩ := J.exists_isBTLimit_defect hv hb i₀ C h0 continuous_const
  rw [hfeq, h0eq]
  set D' : Opens (ComplexModel n) :=
    ⟨J.domain ∩ J.chart.val.symm ⁻¹' W,
      (J.chart.val.symm.continuousOn.mono J.domain_le_target).isOpen_inter_preimage
        J.domain.isOpen hW⟩ with hD'
  have hD'le : D' ≤ J.domain := fun _ hz => hz.1
  have hloc : μf.restrict (D' : Set (ComplexModel n)) = μ0.restrict (D' : Set (ComplexModel n))
    := by
    refine ((hμf.restrict_open hD'le).congr fun i z hz => ?_).unique (hμ0.restrict_open hD'le)
    classical
    by_cases h : i = i₀
    · subst h
      simp [hfW _ hz.2]
    · simp [Function.update_of_ne h]
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Patch.pushMeasure_apply,
    Patch.pushMeasure_apply]
  have hset : ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' (s ∩ W)) =
      J.chart.val.symm ⁻¹' s ∩ (D' : Set (ComplexModel n)) := by
    ext z
    simp only [mem_inter_iff, mem_preimage, hD', Opens.coe_mk]
    tauto
  change μf ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' (s ∩ W)) =
    μ0 ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' (s ∩ W))
  rw [hset, ← Measure.restrict_apply' D'.isOpen.measurableSet,
    ← Measure.restrict_apply' D'.isOpen.measurableSet, hloc]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
theorem restrict_finset_sum {ι : Type*} (t : Finset ι) (μ : ι → Measure M) (S : Set M) :
    (∑ i ∈ t, μ i).restrict S = ∑ i ∈ t, (μ i).restrict S := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.restrict_add, ih]

include hb in
/-- **The defects of a partition of unity telescope.** If `Σ_b χ_b = 1`, then
`Σ_b T(χ_b) = Σ_b T(0)`: chartwise `Σ_b μ(χ_b + p) = μ(1 + Σ_b p) = Σ_b μ(p)`. -/
theorem sum_defectMeasure_eq {N : ℕ} {χ : Fin (N + 1) → M → ℝ}
    (hχ : ∀ b, ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((χ b x : ℝ) : EReal))
    (hχc : ∀ b, Continuous (χ b)) (hsum : ∀ x, ∑ b, χ b x = 1)
    (h0 : ThetaPlurisubharmonic (η i₀ + C • κ).val fun _ => (((0 : ℝ) : ℝ) : EReal)) :
    ∑ b, defectMeasure hv i₀ C (χ b) (hχ b) =
      ∑ _b : Fin (N + 1), defectMeasure hv i₀ C (fun _ => 0) h0 := by
  refine measure_eq_of_restrict_eq_of_openCover (fun J : SlotChart η κ => (J.source : Set M))
    (fun J => J.source.isOpen) (fun x => SlotChart.exists_mem_source η κ x) fun J => ?_
  choose μ hμ heq using fun b => J.exists_isBTLimit_defect hv hb i₀ C (hχ b) (hχc b)
  obtain ⟨μ0, hμ0, h0eq⟩ := J.exists_isBTLimit_defect hv hb i₀ C h0 continuous_const
  rw [restrict_finset_sum, restrict_finset_sum]
  simp only [heq, h0eq]
  -- the local identity
  have hsumμ := IsBTLimit.sum_slot i₀
    (s := fun b z => χ b (J.chart.val.symm z) + J.regularizer i₀ C z) hμ
  have hsum0 := IsBTLimit.sum_slot i₀ (N := N)
    (s := fun _ z => (fun _ : M => (0 : ℝ)) (J.chart.val.symm z) + J.regularizer i₀ C z)
    (ν := fun _ => μ0) fun _ => hμ0
  have hloc : ∑ b, μ b = ∑ _b : Fin (N + 1), μ0 := by
    refine (hsumμ.congr fun i z _ => ?_).unique (hsum0.update_const_add i₀ 1)
    classical
    by_cases h : i = i₀
    · subst h
      simp only [Function.update_self]
      rw [Finset.sum_add_distrib, hsum, Finset.sum_add_distrib]
      simp
    · simp [Function.update_of_ne h]
  ext s hs
  simp only [FunLike.coe_sum, Finset.sum_apply, Patch.pushMeasure_apply]
  have e1 := congrArg (fun ρ : Measure (ComplexModel n) =>
    ρ ((J.domain : Set (ComplexModel n)) ∩ J.chart.val.symm ⁻¹' s)) hloc
  simp only [FunLike.coe_sum, Finset.sum_apply] at e1
  exact e1

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem IsBoundedPotential.exists_abs_toReal_le {u : M → EReal} (hu : IsBoundedPotential u) :
    ∃ Q : ℝ, ∀ x, |(u x).toReal| ≤ Q := by
  obtain ⟨lo, hi, h⟩ := hu
  refine ⟨max |lo| |hi|, fun x => ?_⟩
  have hcoe : (((u x).toReal : ℝ) : EReal) = u x :=
    EReal.coe_toReal (IsBoundedPotential.ne_top ⟨lo, hi, h⟩ x)
      (IsBoundedPotential.ne_bot ⟨lo, hi, h⟩ x)
  have h1 : lo ≤ (u x).toReal := EReal.coe_le_coe_iff.mp (hcoe ▸ (h x).1)
  have h2 : (u x).toReal ≤ hi := EReal.coe_le_coe_iff.mp (hcoe ▸ (h x).2)
  refine abs_le.mpr ⟨?_, h2.trans ((le_abs_self hi).trans (le_max_right _ _))⟩
  linarith [neg_abs_le lo, le_max_left |lo| |hi|]

omit [CompactSpace M] in
theorem ThetaPlurisubharmonic.measurable_toReal {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) : Measurable fun x => (u x).toReal :=
  hu.quasiPlurisubharmonic.upperSemicontinuous.measurable.ereal_toReal

include hb in
/-- **Integration by parts on one slot chart.** For a chart-smooth `f` supported
in a slot chart,
`∫ f dμ(v with a in slot i₀) - ∫ f dμ(v) = ∫ (a - v i₀) dT(f) - ∫ (a - v i₀) dT(0)`. -/
theorem integral_sub_eq_defect {a : M → EReal}
    (hva : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update v i₀ a i))
    (ha : IsBoundedPotential a) (J : SlotChart η κ) {f : M → ℝ}
    (hfs : ChartSmooth (n := n) f) (hfJ : tsupport f ⊆ (J.source : Set M))
    (hfK : IsCompact (tsupport f))
    (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val fun x => ((f x : ℝ) : EReal))
    (h0 : ThetaPlurisubharmonic (η i₀ + C • κ).val fun _ => (((0 : ℝ) : ℝ) : EReal)) :
    (∫ x, f x ∂(globalMixedMeasure η (Function.update v i₀ a) hva)) -
        ∫ x, f x ∂(globalMixedMeasure η v hv) =
      (∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C f hf)) -
        ∫ x, ((a x).toReal - (v i₀ x).toReal) ∂(defectMeasure hv i₀ C (fun _ => 0) h0) := by
  classical
  set e := J.chart with he
  set D := J.domain with hD
  set S : Set M := (J.source : Set M) with hS
  have hDt : (D : Set (ComplexModel n)) ⊆ e.val.target := J.domain_le_target
  have hbva : ∀ i, IsBoundedPotential (Function.update v i₀ a i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa using ha
    · simpa [Function.update_of_ne h] using hb i
  -- local models
  obtain ⟨μa, hμa, heqa⟩ := J.exists_isBTLimit hva hbva
  rw [J.localSlots_update v i₀ a] at hμa
  obtain ⟨μv, hμv, heqv⟩ := J.exists_isBTLimit hv hb
  have hμv' : IsBTLimit D (Function.update (J.localSlots v) i₀ (J.localSlots v i₀)) μv := by
    rw [Function.update_eq_self]; exact hμv
  obtain ⟨ν₁, hν₁, heq1⟩ := J.exists_isBTLimit_defect hv hb i₀ C hf (ChartSmooth.continuous hfs)
  obtain ⟨ν₂, hν₂, heq2⟩ := J.exists_isBTLimit_defect hv hb i₀ C h0 continuous_const
  obtain ⟨φ, hφs, hφc, hφD, hφeq, hφsupp⟩ := J.exists_coordinate_test hfs hfJ hfK
  have hν₁' : IsBTLimit D (Function.update (J.localSlots v) i₀ fun z =>
      φ z + ((fun _ : M => (0 : ℝ)) (e.val.symm z) + J.regularizer i₀ C z)) ν₁ := by
    refine hν₁.congr fun i z hz => ?_
    by_cases h : i = i₀
    · subst h; simp [hφeq hz]
    · simp [Function.update_of_ne h]
  obtain ⟨χ, hχs, hχc, hχD, hχ1, hibp⟩ :=
    exists_integral_sub_eq_slotDefect i₀ hμa hμv' hν₁' hν₂ hφs hφc hφD
  have hsrc : ∀ x ∈ S, x ∈ e.val.source := fun x hx => hx.1
  have hae : ∀ {μ : Measure (ComplexModel n)}, μ (D : Set (ComplexModel n))ᶜ = 0 →
      ∀ F G : ComplexModel n → ℝ, EqOn F G D → ∫ z, F z ∂μ = ∫ z, G z ∂μ := by
    intro μ hμ F G h
    refine integral_congr_ae ?_
    rw [EventuallyEq, ae_iff]
    have hsub : {z | F z ≠ G z} ⊆ (D : Set (ComplexModel n))ᶜ :=
      fun _ hz hzD => hz (h hzD)
    exact measure_mono_null hsub hμ
  -- the left-hand side in coordinates
  have hfS : ∀ x ∉ S, f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hfJ h)
  have hleft_a : ∫ x, f x ∂(globalMixedMeasure η (Function.update v i₀ a) hva) =
      ∫ z, φ z ∂μa := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfS, hS, heqa,
      Patch.integral_pushMeasure _ hμa.1]
    exact hae hμa.1 _ _ fun z hz => (hφeq hz).symm
  have hleft_v : ∫ x, f x ∂(globalMixedMeasure η v hv) = ∫ z, φ z ∂μv := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfS, hS, heqv,
      Patch.integral_pushMeasure _ hμv.1]
    exact hae hμv.1 _ _ fun z hz => (hφeq hz).symm
  -- the right-hand side on the manifold
  set g : M → ℝ := fun x => (a x).toReal - (v i₀ x).toReal with hg
  set χh : M → ℝ := ChartPartition.chartExtend e χ with hχh
  have hχhs : ChartSmooth (n := n) χh :=
    ChartPartition.chartSmooth_chartExtend e hχs hχc (hχD.trans hDt)
  have hχhS : ∀ x ∉ S, χh x * g x = 0 := by
    intro x hx
    by_cases hxs : x ∈ e.val.source
    · have hxD : e.val x ∉ (D : Set (ComplexModel n)) := fun h => hx ⟨hxs, h⟩
      rw [hχh, ChartPartition.chartExtend_of_mem hxs,
        image_eq_zero_of_notMem_tsupport fun h => hxD (hχD h), zero_mul]
    · rw [hχh, ChartPartition.chartExtend_of_notMem hxs, zero_mul]
  have hχhz : ∀ z ∈ (D : Set (ComplexModel n)),
      χ z * ((a (e.val.symm z)).toReal + J.potential i₀ z - J.localSlots v i₀ z) =
        χh (e.val.symm z) * g (e.val.symm z) := by
    intro z hz
    rw [hχh, ChartPartition.chartExtend_of_mem (e.val.map_target (hDt hz)),
      e.val.right_inv (hDt hz)]
    simp only [hg, SlotChart.localSlots]
    ring
  have hright₁ : (∫ z, χ z * ((a (e.val.symm z)).toReal + J.potential i₀ z -
      J.localSlots v i₀ z) ∂ν₁) = ∫ x, χh x * g x ∂(defectMeasure hv i₀ C f hf) := by
    rw [hae hν₁.1 _ _ hχhz, ← setIntegral_eq_integral_of_forall_compl_eq_zero hχhS, hS, heq1,
      Patch.integral_pushMeasure _ hν₁.1]
    rfl
  have hright₂ : (∫ z, χ z * ((a (e.val.symm z)).toReal + J.potential i₀ z -
      J.localSlots v i₀ z) ∂ν₂) =
        ∫ x, χh x * g x ∂(defectMeasure hv i₀ C (fun _ => 0) h0) := by
    rw [hae hν₂.1 _ _ hχhz, ← setIntegral_eq_integral_of_forall_compl_eq_zero hχhS, hS, heq2,
      Patch.integral_pushMeasure _ hν₂.1]
    rfl
  -- removing the cutoff: `T(f)` and `T(0)` agree off the support of `f`
  have hfc : Continuous f := ChartSmooth.continuous hfs
  have hfin₁ : IsFiniteMeasure (defectMeasure hv i₀ C f hf) :=
    globalMixedMeasure_isFiniteMeasure_of_bounded _ (slotTuple_isBoundedPotential hb i₀ hfc)
  have hfin₂ : IsFiniteMeasure (defectMeasure hv i₀ C (fun _ => 0) h0) :=
    globalMixedMeasure_isFiniteMeasure_of_bounded _
      (slotTuple_isBoundedPotential hb i₀ continuous_const)
  have hameas : Measurable fun x => (a x).toReal :=
    ThetaPlurisubharmonic.measurable_toReal (by simpa using hva i₀)
  have hgmeas : Measurable g := hameas.sub (ThetaPlurisubharmonic.measurable_toReal (hv i₀))
  obtain ⟨Qa, hQa⟩ := IsBoundedPotential.exists_abs_toReal_le ha
  obtain ⟨Qv, hQv⟩ := IsBoundedPotential.exists_abs_toReal_le (hb i₀)
  have hgb : ∀ x, |g x| ≤ Qa + Qv := fun x =>
    (abs_sub _ _).trans (add_le_add (hQa x) (hQv x))
  have hInt : ∀ F : M → ℝ, Continuous F → ∀ (μ : Measure M) [IsFiniteMeasure μ],
      Integrable (fun x => F x * g x) μ := by
    intro F hF μ _
    obtain ⟨QF, hQF⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
    refine Integrable.of_bound (hF.measurable.mul hgmeas).aestronglyMeasurable (QF * (Qa + Qv))
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hQF x (mem_univ x)) (hgb x)
      (abs_nonneg _) ((abs_nonneg _).trans (hQF x (mem_univ x)))
  have hχhc : Continuous χh := ChartSmooth.continuous hχhs
  have hone : ∀ x ∈ tsupport f, χh x = 1 := by
    intro x hx
    rw [hχh, ChartPartition.chartExtend_of_mem (hfJ hx).1]
    exact hχ1.self_of_nhdsSet _ (hφsupp x hx)
  have hrest := defectMeasure_restrict_eq hv hb i₀ C hf hfc h0 (isClosed_tsupport f).isOpen_compl
    fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hsplit : ∀ (μ : Measure M) [IsFiniteMeasure μ],
      ∫ x, g x ∂μ = (∫ x, χh x * g x ∂μ) + ∫ x, (1 - χh x) * g x ∂μ := by
    intro μ _
    rw [← integral_add (hInt χh hχhc μ) (hInt (fun x => 1 - χh x) (continuous_const.sub hχhc) μ)]
    congr 1; funext x; ring
  have hcomp : ∀ x ∉ (tsupport f)ᶜ, (1 - χh x) * g x = 0 := by
    intro x hx
    rw [hone x (not_not.mp hx), sub_self, zero_mul]
  have hR : ∫ x, (1 - χh x) * g x ∂(defectMeasure hv i₀ C f hf) =
      ∫ x, (1 - χh x) * g x ∂(defectMeasure hv i₀ C (fun _ => 0) h0) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcomp, hrest]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hcomp
  rw [hleft_a, hleft_v, hibp, hright₁, hright₂, hsplit (defectMeasure hv i₀ C f hf),
    hsplit (defectMeasure hv i₀ C (fun _ => 0) h0), hR]
  ring

end Defect

/-! ### One-slot mass invariance -/

section Mass

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] [CompactSpace M] in
theorem integrable_of_measurable_bounded {F : M → ℝ} (hF : Measurable F) {Q : ℝ}
    (hQ : ∀ x, |F x| ≤ Q) (μ : Measure M) [IsFiniteMeasure μ] : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable Q (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hQ x)

/-- **One-slot mass invariance for bounded potentials** on a compact Kähler
manifold: replacing the potential in one slot of a bounded `η`-PSH tuple by
another bounded `η`-PSH potential does not change the total mass of the global
mixed measure. -/
theorem globalMixedMeasure_update_univ_eq (omega : KahlerBackground n M)
    {η : Fin n → ClosedRealOneOneForm n M} {v : Fin n → M → EReal}
    (hv : ∀ i, ThetaPlurisubharmonic (η i).val (v i)) (hb : ∀ i, IsBoundedPotential (v i))
    (i₀ : Fin n) {a : M → EReal}
    (hva : ∀ i, ThetaPlurisubharmonic (η i).val (Function.update v i₀ a i))
    (ha : IsBoundedPotential a) :
    globalMixedMeasure η (Function.update v i₀ a) hva univ = globalMixedMeasure η v hv univ := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM => simp [Set.univ_eq_empty_iff.mpr hM]
  | inr hM =>
  obtain ⟨x₀⟩ := hM
  set κ := omega.form with hκ
  choose J hJ using SlotChart.exists_mem_source η κ
  obtain ⟨m, χ, idx, hsm, -, hsupp, hcpt, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n)
      (fun x => (J x).source) fun x => ⟨x, hJ x⟩
  have hm : m ≠ 0 := by
    rintro rfl
    simpa using hsum x₀
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨C, -, hsemi, hpsh⟩ :=
    SmoothDDCForm.exists_pos_thetaPlurisubharmonic_smooth omega (fun _ : Fin (N + 1) => η i₀) χ hsm
  have h0 : ThetaPlurisubharmonic (η i₀ + C • κ).val fun _ => (((0 : ℝ) : ℝ) : EReal) :=
    thetaPlurisubharmonic_const (η i₀ + C • κ) (hsemi 0) 0
  have hχc : ∀ b, Continuous (χ b) := fun b => ChartSmooth.continuous (hsm b)
  have hbva : ∀ i, IsBoundedPotential (Function.update v i₀ a i) := by
    intro i
    by_cases h : i = i₀
    · subst h; simpa using ha
    · simpa [Function.update_of_ne h] using hb i
  have hfa := globalMixedMeasure_isFiniteMeasure_of_bounded hva hbva
  have hfv := globalMixedMeasure_isFiniteMeasure_of_bounded hv hb
  -- the mass as a partition sum
  have hmass : ∀ (μ : Measure M) [IsFiniteMeasure μ], μ.real univ = ∑ b, ∫ x, χ b x ∂μ := by
    intro μ _
    have hint : ∀ b ∈ (Finset.univ : Finset (Fin (N + 1))), Integrable (χ b) μ := by
      intro b _
      obtain ⟨Q, hQ⟩ := isCompact_univ.exists_bound_of_continuousOn (hχc b).continuousOn
      exact integrable_of_measurable_bounded (hχc b).measurable
        (fun x => by simpa [Real.norm_eq_abs] using hQ x (mem_univ x)) μ
    rw [← integral_finsetSum _ hint]
    simp [hsum]
  -- the defect pairing
  set g : M → ℝ := fun x => (a x).toReal - (v i₀ x).toReal with hg
  have hgmeas : Measurable g :=
    (ThetaPlurisubharmonic.measurable_toReal (by simpa using hva i₀)).sub
      (ThetaPlurisubharmonic.measurable_toReal (hv i₀))
  obtain ⟨Qa, hQa⟩ := IsBoundedPotential.exists_abs_toReal_le ha
  obtain ⟨Qv, hQv⟩ := IsBoundedPotential.exists_abs_toReal_le (hb i₀)
  have hgb : ∀ x, |g x| ≤ Qa + Qv := fun x =>
    (abs_sub _ _).trans (add_le_add (hQa x) (hQv x))
  have hgint : ∀ {f : M → ℝ} (hf : ThetaPlurisubharmonic (η i₀ + C • κ).val
      fun x => ((f x : ℝ) : EReal)), Continuous f →
        Integrable g (defectMeasure hv i₀ C f hf) := by
    intro f hf hfc
    have : IsFiniteMeasure (defectMeasure hv i₀ C f hf) :=
      globalMixedMeasure_isFiniteMeasure_of_bounded
      (slotTuple_thetaPlurisubharmonic hv i₀ C hf) (slotTuple_isBoundedPotential hb i₀ hfc)
    exact integrable_of_measurable_bounded hgmeas hgb _
  have hchart : ∀ b, (∫ x, χ b x ∂(globalMixedMeasure η (Function.update v i₀ a) hva)) -
      ∫ x, χ b x ∂(globalMixedMeasure η v hv) =
        (∫ x, g x ∂(defectMeasure hv i₀ C (χ b) (hpsh b))) -
          ∫ x, g x ∂(defectMeasure hv i₀ C (fun _ => 0) h0) := fun b =>
    integral_sub_eq_defect hv hb i₀ C hva ha (J (idx b)) (hsm b) (hsupp b) (hcpt b) (hpsh b) h0
  have htel := sum_defectMeasure_eq hv hb i₀ C hpsh hχc hsum h0
  have hsumeq : (∑ b, ∫ x, χ b x ∂(globalMixedMeasure η (Function.update v i₀ a) hva)) -
      ∑ b, ∫ x, χ b x ∂(globalMixedMeasure η v hv) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simp only [hchart]
    rw [Finset.sum_sub_distrib,
      ← integral_finsetSum_measure fun b _ => hgint (hpsh b) (hχc b),
      ← integral_finsetSum_measure fun _ _ => hgint h0 continuous_const, htel, sub_self]
  have hreal : (globalMixedMeasure η (Function.update v i₀ a) hva).real univ =
      (globalMixedMeasure η v hv).real univ := by
    rw [hmass, hmass]
    linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end Mass

end

end SGPT.Foundations.Analysis.Pending.GlobalSlotStokes
