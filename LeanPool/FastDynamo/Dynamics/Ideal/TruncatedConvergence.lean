/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.Ideal.TruncatedTransport
public import LeanPool.FastDynamo.Dynamics.Ideal.CauchyOperator

/-!
# The truncated Cauchy transport converges to the Cauchy transport

The paper proves that the Cauchy formula preserves the divergence constraint by testing
against `∇ψ` and extending to `ψ ∘ Φ_t ∈ H¹` by density (the divergence-constraint paragraph of
the proof of `cor:ideal-growth`); it uses no truncation.  The formalisation instead compares the
truncated transport `𝒯₀^{(N)}(t)` of `FastDynamo/Dynamics/Ideal/TruncatedTransport.lean` with
the full transport `𝒯₀(t)` of `FastDynamo/Dynamics/Ideal/CauchyOperator.lean`.  The two differ
only on the *tail*

```
  E_N = { x : Torus 3 | the transverse representative of x lies in a buffer disc of index ≥ N }
```

because off the discarded buffer discs the truncated flow, its axial shift and both their
differentials coincide with the untruncated ones.  This module builds that comparison and
concludes the `L²` convergence `𝒯₀^{(N)}(t)B → 𝒯₀(t)B`, which is what lets
`idealTransport_mem_literalSolenoidalSubspace`
(`FastDynamo/Dynamics/Ideal/SolenoidalInvariance.lean`) transfer the solenoidality of
`𝒯₀^{(N)}(t)B` (proved through the smooth truncated flow and
`inner_gradient_mFourier_comp_eq_zero_of_mem_literalSolenoidalSubspace` of
`FastDynamo/Dynamics/Ideal/GradientOrthogonality.lean`) to `𝒯₀(t)B` by closedness of
`literalSolenoidalSubspace`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

/-- **Uniqueness of the `(0,1]` representative, coordinatewise**: a lift whose `j`th coordinate
already lies in `(0,1]` is the canonical representative there. -/
theorem literalIocRepresentative_apply_of_mem_Ioc {a : R3} (j : Fin 3)
    (ha : a j ∈ Set.Ioc (0 : ℝ) 1) :
    literalIocRepresentative (literalTorusPoint a) j = a j := by
  obtain ⟨k, hk⟩ := exists_intCast_add_of_literalTorusPoint_eq
    (literalTorusPoint_literalIocRepresentative (literalTorusPoint a)) j
  have hb := literalIocRepresentative_mem_Ioc (literalTorusPoint a) j
  rw [Set.mem_Ioc, hk] at hb
  rw [Set.mem_Ioc] at ha
  have hlt : ((k : ℤ) : ℝ) < 1 := by linarith [hb.2, ha.1]
  have hgt : ((-1 : ℤ) : ℝ) < ((k : ℤ) : ℝ) := by push_cast; linarith [hb.1, ha.2]
  have hk1 : k < 1 := by exact_mod_cast hlt
  have hk2 : (-1 : ℤ) < k := by exact_mod_cast hgt
  have hk0 : k = 0 := by omega
  rw [hk, hk0]
  simp

namespace ScaleFamily.TorusCellPlacement

open UnitBoxPeriodization

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-! ## Recentring inside the fundamental box -/

/-- **On the fundamental box, recentring by the active translate cannot enter the placement
chart unless it is the trivial translate.**  For `q ∈ (0,1]²` the second index is always `0`, and
the first is `0` or `1`; in the latter case `(q - c).1 ≤ 0`, which is outside the chart's first
interval `(0, 1/4)`. -/
theorem sub_chartTranslation_eq_self_of_mem_placementChart {q : ℝ × ℝ} (hq : q ∈ pairUnitIocBox)
    (hsub : q - chartTranslation q ∈ ScaleFamily.placementChart) :
    q - chartTranslation q = q := by
  obtain ⟨hq1, hq2⟩ := hq
  rw [Set.mem_Ioc] at hq1 hq2
  obtain ⟨hc1, hc2⟩ := hsub
  rw [Set.mem_Ioo] at hc1 hc2
  have hval1 : (q - chartTranslation q).1 = q.1 - ((⌈q.1 + 1 / 8⌉ - 1 : ℤ) : ℝ) := rfl
  have hval2 : (q - chartTranslation q).2 = q.2 - ((⌈q.2⌉ - 1 : ℤ) : ℝ) := rfl
  rw [hval1] at hc1
  rw [hval2] at hc2
  have hceil1 : ⌈q.1 + 1 / 8⌉ = 1 := by
    by_contra hcon
    have hcases : ⌈q.1 + 1 / 8⌉ ≤ 0 ∨ 2 ≤ ⌈q.1 + 1 / 8⌉ := by omega
    rcases hcases with hle | hge
    · have hr : ((⌈q.1 + 1 / 8⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
      have hcl := Int.le_ceil (q.1 + 1 / 8)
      linarith [hq1.1]
    · have hr : (2 : ℝ) ≤ ((⌈q.1 + 1 / 8⌉ : ℤ) : ℝ) := by exact_mod_cast hge
      have hlt := hc1.1
      push_cast at hlt
      linarith [hq1.2]
  have hceil2 : ⌈q.2⌉ = 1 := by
    by_contra hcon
    have hcases : ⌈q.2⌉ ≤ 0 ∨ 2 ≤ ⌈q.2⌉ := by omega
    rcases hcases with hle | hge
    · have hr : ((⌈q.2⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
      have hcl := Int.le_ceil q.2
      linarith [hq2.1]
    · have hr : (2 : ℝ) ≤ ((⌈q.2⌉ : ℤ) : ℝ) := by exact_mod_cast hge
      have hlt := hc2.1
      push_cast at hlt
      linarith [hq2.2]
  have hzero : chartTranslation q = 0 := by
    have hidx : localTranslationIndex q = 0 := by
      refine Prod.ext ?_ ?_
      · change ⌈q.1 + 1 / 8⌉ - 1 = 0
        omega
      · change ⌈q.2⌉ - 1 = 0
        omega
    rw [chartTranslation, hidx]
    simp
  rw [hzero, sub_zero]

/-- **Recentring inside the fundamental box does not create tail membership.** -/
theorem not_mem_bufferDisk_sub_chartTranslation {q : ℝ × ℝ} (hq : q ∈ pairUnitIocBox) {N : ℕ}
    (hx : ∀ n : ℕ, N ≤ n → q ∉ P.scaleFamily.bufferDisk n) (n : ℕ) (hn : N ≤ n) :
    q - chartTranslation q ∉ P.scaleFamily.bufferDisk n := by
  intro hmem
  have hchart : q - chartTranslation q ∈ ScaleFamily.placementChart :=
    P.bufferDisk_subset_chart n hmem
  rw [sub_chartTranslation_eq_self_of_mem_placementChart hq hchart] at hmem
  exact hx n hn hmem

/-! ## The truncation tail on the torus -/

/-- **The tail of the `N`-truncation**: the torus points whose transverse representative lies in
one of the *discarded* buffer discs.  Off this set the truncated and the untruncated objects
coincide; the sets decrease to the empty set because the buffer discs are pairwise disjoint. -/
def truncationTailSet (N : ℕ) : Set (Torus 3) :=
  {x : Torus 3 | ∃ n : ℕ, N ≤ n ∧ literalIocPair x ∈ P.scaleFamily.bufferDisk n}

/-- The tail is measurable: a countable union of preimages of open discs under the measurable
canonical section. -/
theorem measurableSet_truncationTailSet (N : ℕ) :
    MeasurableSet (truncationTailSet h P N) := by
  have hrw : truncationTailSet h P N =
      ⋃ n : ℕ, ⋃ _ : N ≤ n, literalIocPair ⁻¹' P.scaleFamily.bufferDisk n := by
    ext x
    constructor
    · rintro ⟨n, hn, hmem⟩
      exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨hn, hmem⟩⟩
    · intro hmem
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
      obtain ⟨hn', hmem'⟩ := Set.mem_iUnion.1 hn
      exact ⟨n, hn', hmem'⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦
    measurable_literalIocPair (isOpen_bufferDisk h P n).measurableSet

/-- **Every point leaves the tail**: the buffer discs are pairwise disjoint, so a point lies in at
most one of them and hence in no tail of large enough index. -/
theorem not_mem_truncationTailSet_of_le (x : Torus 3) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → x ∉ truncationTailSet h P N := by
  by_cases hbuf : ∃ k : ℕ, literalIocPair x ∈ P.scaleFamily.bufferDisk k
  · obtain ⟨k, hk⟩ := hbuf
    refine ⟨k + 1, fun N hN hmem ↦ ?_⟩
    obtain ⟨n, hn, hn'⟩ := hmem
    have hne : k ≠ n := by omega
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hlt)) hk hn'
    · exact (Set.disjoint_left.mp (P.disjoint_bufferDisk hgt)) hn' hk
  · exact ⟨0, fun N _ hmem ↦ hbuf ⟨hmem.choose, hmem.choose_spec.2⟩⟩

/-! ## The transverse representative of a flowed point -/

/-- The transverse representative of `Φ_t x` is the periodised plane flow of that of `x`. -/
theorem literalIocPair_literalFlow (t : ℝ) (x : Torus 3) :
    literalIocPair (literalFlow h P angularSpeed axialSpeed tau t x) =
      planePeriodizedTransverseFlow h P angularSpeed t (literalIocPair x) := by
  set a := literalIocRepresentative x with ha
  have hx : literalTorusPoint a = x := literalTorusPoint_literalIocRepresentative x
  have hbox := planePeriodizedTransverseFlow_mem_pairUnitIocBox h P angularSpeed t
    (literalIocPair_mem_pairUnitIocBox x)
  have hflow : literalFlow h P angularSpeed axialSpeed tau t x =
      literalTorusPoint (literalFlowLift h P angularSpeed axialSpeed tau t a) := by
    rw [← hx, literalTorusPoint_literalFlowLift]
  rw [hflow, literalIocPair,
    literalIocRepresentative_apply_of_mem_Ioc 0 hbox.1,
    literalIocRepresentative_apply_of_mem_Ioc 1 hbox.2]
  exact literalFlowLift_pair h P angularSpeed axialSpeed tau t a

/-! ## Invariance of the tail -/

/-- **The tail is invariant under the full flow.** -/
theorem literalFlow_mem_truncationTailSet_iff (N : ℕ) (t : ℝ) (x : Torus 3) :
    literalFlow h P angularSpeed axialSpeed tau t x ∈ truncationTailSet h P N ↔
      x ∈ truncationTailSet h P N := by
  have hstep : ∀ (s : ℝ) (y : Torus 3), y ∈ truncationTailSet h P N →
      literalFlow h P angularSpeed axialSpeed tau s y ∈ truncationTailSet h P N := by
    rintro s y ⟨n, hn, hmem⟩
    refine ⟨n, hn, ?_⟩
    rw [literalIocPair_literalFlow,
      planePeriodizedTransverseFlow_eq_of_mem_pairUnitIocBox h P angularSpeed s
        (literalIocPair_mem_pairUnitIocBox y)]
    exact planeTransverseFlow_mem_bufferDisk h P angularSpeed s hmem
  refine ⟨fun hmem ↦ ?_, hstep t x⟩
  have hback := hstep (-t) _ hmem
  rwa [literalFlow_neg_literalFlow] at hback

/-! ## Agreement of the truncated and the full objects off the tail -/

/-- Off the tail the two periodised plane flows agree at the transverse representative. -/
theorem planePeriodizedTruncatedFlow_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    planePeriodizedTruncatedFlow h P angularSpeed N t (literalIocPair x) =
      planePeriodizedTransverseFlow h P angularSpeed t (literalIocPair x) := by
  have hout : ∀ n : ℕ, N ≤ n → literalIocPair x ∉ P.scaleFamily.bufferDisk n :=
    fun n hn hmem ↦ hx ⟨n, hn, hmem⟩
  rw [planePeriodizedTruncatedFlow_eq, planePeriodizedTransverseFlow_eq,
    planeTruncatedTransverseFlow_eq_planeTransverseFlow h P angularSpeed N t
      (not_mem_bufferDisk_sub_chartTranslation h P (literalIocPair_mem_pairUnitIocBox x) hout)]

/-- Off the tail the two periodised axial shifts agree at the transverse representative. -/
theorem planePeriodizedTruncatedShift_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    planePeriodizedTruncatedShift h P axialSpeed tau N t (literalIocPair x) =
      planePeriodizedAxialShift h P axialSpeed tau t (literalIocPair x) := by
  have hout : ∀ n : ℕ, N ≤ n → literalIocPair x ∉ P.scaleFamily.bufferDisk n :=
    fun n hn hmem ↦ hx ⟨n, hn, hmem⟩
  rw [planePeriodizedTruncatedShift_eq, planePeriodizedAxialShift_eq,
    planeTruncatedAxialShift_eq_planeAxialShift h P axialSpeed tau N t
      (not_mem_bufferDisk_sub_chartTranslation h P (literalIocPair_mem_pairUnitIocBox x) hout)]

/-- **Off the tail the truncated flow is the full flow.** -/
theorem literalTruncatedFlow_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    literalTruncatedFlow h P angularSpeed axialSpeed tau N t x =
      literalFlow h P angularSpeed axialSpeed tau t x := by
  have hpt := transverseTorusPoint_literalIocPair x
  have hflow : torusTruncatedFlow h P angularSpeed N t (fun j : Fin 2 ↦ x j.castSucc) =
      torusTransverseFlow h P angularSpeed t (fun j : Fin 2 ↦ x j.castSucc) := by
    rw [← hpt, torusTruncatedFlow_transverseTorusPoint, torusTransverseFlow_transverseTorusPoint,
      planePeriodizedTruncatedFlow_eq_of_not_mem_tail h P angularSpeed N t hx]
  have hshift : torusTruncatedShift h P axialSpeed tau N t (fun j : Fin 2 ↦ x j.castSucc) =
      torusAxialShift h P axialSpeed tau t (fun j : Fin 2 ↦ x j.castSucc) := by
    rw [← hpt, torusTruncatedShift_transverseTorusPoint, torusAxialShift_transverseTorusPoint,
      planePeriodizedTruncatedShift_eq_of_not_mem_tail h P axialSpeed tau N t hx]
  exact (truncatedFlowData h P angularSpeed axialSpeed tau N).literalFlow_eq_of
    (fullFlowData h P angularSpeed axialSpeed tau) hflow hshift

/-- **Off the tail the truncated derivative flow is the full derivative flow.** -/
theorem truncatedFlowFDeriv_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    truncatedFlowFDeriv h P angularSpeed axialSpeed tau N t x =
      flowFDeriv h P angularSpeed axialSpeed tau t x := by
  have hout : ∀ n : ℕ, N ≤ n → literalIocPair x ∉ P.scaleFamily.bufferDisk n :=
    fun n hn hmem ↦ hx ⟨n, hn, hmem⟩
  have hsub := not_mem_bufferDisk_sub_chartTranslation h P
    (literalIocPair_mem_pairUnitIocBox x) hout
  rw [truncatedFlowFDeriv_eq, flowFDeriv_eq, truncatedFlowFDerivPlane_eq,
    flowFDerivPlane_eq,
    fderiv_planePeriodizedTruncatedFlow, fderiv_planePeriodizedTransverseFlow,
    fderiv_planePeriodizedTruncatedShift, fderiv_planePeriodizedAxialShift,
    fderiv_planeTruncatedTransverseFlow_eq h P angularSpeed N t hsub,
    fderiv_planeTruncatedAxialShift_eq h P axialSpeed tau N t hsub]

/-- Off the tail the complexified derivatives agree. -/
theorem truncatedFlowFDerivC_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    truncatedFlowFDerivC h P angularSpeed axialSpeed tau N t x =
      flowFDerivC h P angularSpeed axialSpeed tau t x := by
  rw [truncatedFlowFDerivC_eq, flowFDerivC_eq,
    truncatedFlowFDeriv_eq_of_not_mem_tail h P angularSpeed axialSpeed tau N t hx]

/-- **Off the tail the two Cauchy symbols agree.** -/
theorem truncatedSymbol_eq_of_not_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∉ truncationTailSet h P N) :
    truncatedSymbol h P angularSpeed axialSpeed tau N t x =
      idealSymbol h P angularSpeed axialSpeed tau t x := by
  have hback : literalTruncatedFlow h P angularSpeed axialSpeed tau N (-t) x =
      literalFlow h P angularSpeed axialSpeed tau (-t) x :=
    literalTruncatedFlow_eq_of_not_mem_tail h P angularSpeed axialSpeed tau N (-t) hx
  have hmem : literalFlow h P angularSpeed axialSpeed tau (-t) x ∉ truncationTailSet h P N := by
    intro hcon
    exact hx ((literalFlow_mem_truncationTailSet_iff h P angularSpeed axialSpeed tau N (-t) x).1
      hcon)
  rw [truncatedSymbol_eq, idealSymbol_eq, hback,
    truncatedFlowFDerivC_eq_of_not_mem_tail h P angularSpeed axialSpeed tau N t hmem]

/-- **On the tail the truncated flow is the identity**: a discarded buffer disc meets no retained
one, so the truncated displacement and the truncated axial shift both vanish there. -/
theorem literalTruncatedFlow_eq_self_of_mem_tail (N : ℕ) (t : ℝ) {x : Torus 3}
    (hx : x ∈ truncationTailSet h P N) :
    literalTruncatedFlow h P angularSpeed axialSpeed tau N t x = x := by
  obtain ⟨n, hn, hmem⟩ := hx
  have hout : ∀ m : ℕ, m < N → literalIocPair x ∉ P.scaleFamily.bufferDisk m :=
    not_mem_bufferDisk_of_le_of_mem h P hn hmem
  have hbox := literalIocPair_mem_pairUnitIocBox x
  have hpt := transverseTorusPoint_literalIocPair x
  have hflow : torusTruncatedFlow h P angularSpeed N t (fun j : Fin 2 ↦ x j.castSucc) =
      fun j : Fin 2 ↦ x j.castSucc := by
    rw [← hpt, torusTruncatedFlow_transverseTorusPoint,
      planePeriodizedTruncatedFlow_eq_of_mem_pairUnitIocBox h P angularSpeed N t hbox,
      planeTruncatedTransverseFlow_eq_self h P angularSpeed N t hout]
  have hshift : torusTruncatedShift h P axialSpeed tau N t (fun j : Fin 2 ↦ x j.castSucc) = 0 := by
    rw [← hpt, torusTruncatedShift_transverseTorusPoint, planePeriodizedTruncatedShift,
      periodization_eq_self_of_mem_Ioc
        (supportedInPlacementChart_planeTruncatedAxialShift h P axialSpeed tau N
          t).supportedInOpenUnitBox hbox.1 hbox.2,
      planeTruncatedAxialShift_eq_zero h P axialSpeed tau N t hout]
  exact (truncatedFlowData h P angularSpeed axialSpeed tau N).literalFlow_eq_self hflow hshift

/-! ## The `L²` convergence of the truncated transport -/

/-- **The dominating function of the comparison**: twice the square of the uniform symbol bound
times the sum of the squared norms of `B` and of `B ∘ Φ_{-t}`.  It is integrable and dominates
the pointwise difference of the two transports on the tail. -/
def truncationDominant (t : ℝ) (B : LiteralC3L2) (x : Torus 3) : ℝ :=
  2 * flowComplexDerivativeBound h P angularSpeed axialSpeed tau t ^ 2 *
    (‖(B : Torus 3 → C3) x‖ ^ 2 +
      ‖(B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)‖ ^ 2)

/-- The dominating function is nonnegative. -/
theorem truncationDominant_nonneg (t : ℝ) (B : LiteralC3L2) (x : Torus 3) :
    0 ≤ truncationDominant h P angularSpeed axialSpeed tau t B x := by
  rw [truncationDominant]
  positivity

/-- The dominating function is integrable: both summands are squared norms of `L²` fields. -/
theorem integrable_truncationDominant (t : ℝ) (B : LiteralC3L2) :
    Integrable (truncationDominant h P angularSpeed axialSpeed tau t B)
      (volume : Measure (Torus 3)) := by
  have hmp := measurePreserving_literalFlow h P angularSpeed axialSpeed tau (-t)
  have hintV : Integrable
      (fun x : Torus 3 ↦
        ‖(B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)‖ ^ 2)
      (volume : Measure (Torus 3)) := by
    refine (integrable_sq_norm_literalC3L2
      ((Lp.compMeasurePreservingₗᵢ ℂ (literalFlow h P angularSpeed axialSpeed tau (-t))
        hmp).toContinuousLinearMap B)).congr ?_
    filter_upwards [coeFn_compMeasurePreservingCLM hmp B] with x hx
    rw [hx]
  exact ((integrable_sq_norm_literalC3L2 B).add hintV).const_mul _

/-- **The pointwise comparison of the two transports.**  Off the tail they agree; on the tail the
truncated flow is the identity, so both terms are bounded by the uniform symbol bound times the
value of `B` at a point of the tail. -/
theorem norm_sq_idealTruncatedTransport_sub_le (htau : 0 ≤ tau) (N : ℕ) (t : ℝ)
    (B : LiteralC3L2) :
    ∀ᵐ x : Torus 3,
      ‖((idealTruncatedTransport h P angularSpeed axialSpeed tau N t B -
          idealTransport h P angularSpeed axialSpeed tau t B : LiteralC3L2) :
          Torus 3 → C3) x‖ ^ 2 ≤
        Set.indicator (truncationTailSet h P N)
          (truncationDominant h P angularSpeed axialSpeed tau t B) x := by
  filter_upwards [Lp.coeFn_sub (idealTruncatedTransport h P angularSpeed axialSpeed tau N t B)
      (idealTransport h P angularSpeed axialSpeed tau t B),
    idealTruncatedTransport_coe_ae h P angularSpeed axialSpeed tau htau N t B,
    idealTransport_coe_ae h P angularSpeed axialSpeed tau htau t B] with x hxs hx1 hx2
  rw [hxs]
  change ‖((idealTruncatedTransport h P angularSpeed axialSpeed tau N t B : LiteralC3L2) :
      Torus 3 → C3) x - ((idealTransport h P angularSpeed axialSpeed tau t B : LiteralC3L2) :
      Torus 3 → C3) x‖ ^ 2 ≤ _
  rw [hx1, hx2]
  by_cases hmem : x ∈ truncationTailSet h P N
  · rw [Set.indicator_of_mem hmem, truncationDominant,
      literalTruncatedFlow_eq_self_of_mem_tail h P angularSpeed axialSpeed tau N (-t) hmem]
    have hb1 : ‖truncatedSymbol h P angularSpeed axialSpeed tau N t x
        ((B : Torus 3 → C3) x)‖ ≤
        flowComplexDerivativeBound h P angularSpeed axialSpeed tau t *
          ‖(B : Torus 3 → C3) x‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (norm_truncatedSymbol_le h P angularSpeed axialSpeed tau htau N t x) (norm_nonneg _))
    have hb2 : ‖idealSymbol h P angularSpeed axialSpeed tau t x
        ((B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x))‖ ≤
        flowComplexDerivativeBound h P angularSpeed axialSpeed tau t *
          ‖(B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (norm_idealSymbol_le h P angularSpeed axialSpeed tau htau t x) (norm_nonneg _))
    have hsum := (norm_sub_le
      (truncatedSymbol h P angularSpeed axialSpeed tau N t x ((B : Torus 3 → C3) x))
      (idealSymbol h P angularSpeed axialSpeed tau t x
        ((B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)))).trans
      (add_le_add hb1 hb2)
    refine (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans ?_
    nlinarith [sq_nonneg (‖(B : Torus 3 → C3) x‖ -
        ‖(B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x)‖),
      sq_nonneg (flowComplexDerivativeBound h P angularSpeed axialSpeed tau t),
      norm_nonneg ((B : Torus 3 → C3) x),
      norm_nonneg ((B : Torus 3 → C3) (literalFlow h P angularSpeed axialSpeed tau (-t) x))]
  · rw [Set.indicator_of_notMem hmem,
      truncatedSymbol_eq_of_not_mem_tail h P angularSpeed axialSpeed tau N t hmem,
      literalTruncatedFlow_eq_of_not_mem_tail h P angularSpeed axialSpeed tau N (-t) hmem,
      sub_self, norm_zero]
    norm_num

/-- **The tail integrals of the dominating function tend to zero**, by dominated convergence: the
tails decrease to the empty set because the buffer discs are pairwise disjoint. -/
theorem tendsto_integral_indicator_truncationTailSet (t : ℝ) (B : LiteralC3L2) :
    Tendsto (fun N : ℕ ↦ ∫ x : Torus 3,
        Set.indicator (truncationTailSet h P N)
          (truncationDominant h P angularSpeed axialSpeed tau t B) x)
      atTop (𝓝 0) := by
  have hG := integrable_truncationDominant h P angularSpeed axialSpeed tau t B
  have hdom := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (Torus 3)))
    (F := fun N : ℕ ↦ Set.indicator (truncationTailSet h P N)
      (truncationDominant h P angularSpeed axialSpeed tau t B))
    (f := fun _ : Torus 3 ↦ (0 : ℝ))
    (bound := truncationDominant h P angularSpeed axialSpeed tau t B)
    (fun N ↦ hG.aestronglyMeasurable.indicator (measurableSet_truncationTailSet h P N)) hG ?_ ?_
  · simpa using hdom
  · intro N
    filter_upwards with x
    by_cases hx : x ∈ truncationTailSet h P N
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (truncationDominant_nonneg h P angularSpeed axialSpeed tau t B x)]
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact truncationDominant_nonneg h P angularSpeed axialSpeed tau t B x
  · filter_upwards with x
    obtain ⟨N₀, hN₀⟩ := not_mem_truncationTailSet_of_le h P x
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact (Set.indicator_of_notMem (hN₀ N hN) _).symm

/-- **`𝒯₀^{(N)}(t)B → 𝒯₀(t)B` in `L²`**.  This is what lets
`idealTransport_mem_literalSolenoidalSubspace`
(`FastDynamo/Dynamics/Ideal/SolenoidalInvariance.lean`) transfer the solenoidality of the
truncated transports — provable through the smooth truncated flow and
`sum_inner_flatTorus3FourierBasis_eq_zero` — to `𝒯₀(t)B`, using that
`literalSolenoidalSubspace` is closed. -/
theorem tendsto_idealTruncatedTransport (htau : 0 ≤ tau) (t : ℝ) (B : LiteralC3L2) :
    Tendsto (fun N : ℕ ↦ idealTruncatedTransport h P angularSpeed axialSpeed tau N t B)
      atTop (𝓝 (idealTransport h P angularSpeed axialSpeed tau t B)) := by
  have hG := integrable_truncationDominant h P angularSpeed axialSpeed tau t B
  have hbound : ∀ N : ℕ,
      ‖idealTruncatedTransport h P angularSpeed axialSpeed tau N t B -
          idealTransport h P angularSpeed axialSpeed tau t B‖ ^ 2 ≤
        ∫ x : Torus 3, Set.indicator (truncationTailSet h P N)
          (truncationDominant h P angularSpeed axialSpeed tau t B) x := by
    intro N
    rw [sq_norm_literalC3L2_eq_integral]
    exact integral_mono_ae (integrable_sq_norm_literalC3L2 _)
      (hG.indicator (measurableSet_truncationTailSet h P N))
      (norm_sq_idealTruncatedTransport_sub_le h P angularSpeed axialSpeed tau htau N t B)
  have hvnn : ∀ N : ℕ, 0 ≤ ∫ x : Torus 3, Set.indicator (truncationTailSet h P N)
      (truncationDominant h P angularSpeed axialSpeed tau t B) x :=
    fun N ↦ le_trans (sq_nonneg _) (hbound N)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N ↦ norm_nonneg _)
    (fun N ↦ (Real.le_sqrt (norm_nonneg _) (hvnn N)).2 (hbound N)) ?_
  have hc := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_integral_indicator_truncationTailSet h P angularSpeed axialSpeed tau t B)
  rw [Real.sqrt_zero] at hc
  exact hc

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
