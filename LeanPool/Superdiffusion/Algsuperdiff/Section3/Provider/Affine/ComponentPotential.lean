/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.KuhnWeakGradient
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.PotentialSolenoidal
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.Basic

/-!
# ComponentPotential

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A zero-trace potential for one affine component correction

This file packages the explicitly zero-extended finite Kuhn interpolation of
`competitorVertexData C p - linearFn p`.  On the open root cube it is exactly
`globalCompetitor m s C p - linearFn p`; outside the component's common coarse
mesh it vanishes.  The resulting compactly supported `H¹` function implements
the component slope correction as an `H¹₀` potential field locally.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open Filter Function HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The vertex datum for the scalar correction `ℓ̂_p - ℓ_p`. -/
def componentCorrectionDatum (C : Set (TriadicCube d)) (p : Vec d) : Vec d → ℝ :=
  fun x => competitorVertexData C p x - linearFn p x

/-- The scalar component correction, using the root mesh on the open root and
the literal zero representative away from that finite mesh. -/
def componentCorrectionPotential (m s : ℤ) (C : Set (TriadicCube d)) (p : Vec d) :
    Vec d → ℝ :=
  zeroExtendedKuhnAffine (rootCoarseMesh m s) (componentCorrectionDatum C p)

/-- The finite closed-cell carrier of the part of the common coarse mesh
subordinate to a component neighborhood. -/
def commonCoarseMeshClosedCarrier (N : Finset (TriadicCube d)) (s : ℤ) : Set (Vec d) :=
  ⋃ T ∈ (commonCoarseMesh N s : Set (KuhnCell d)), T.closedCarrier

/-- On a closed root-mesh cell, the explicit zero extension is the difference
between the global competitor and the linear function. -/
theorem componentCorrectionPotential_eqOn_globalCompetitor_sub_linearFn_closedCarrier
    {m s : ℤ} (hsm : s ≤ m) (C : Set (TriadicCube d)) (p : Vec d)
    {T : KuhnCell d} (hT : T ∈ rootCoarseMesh (d := d) m s) :
    Set.EqOn (componentCorrectionPotential m s C p)
      (fun x => globalCompetitor m s C p x - linearFn p x) T.closedCarrier := by
  intro x hx
  rw [componentCorrectionPotential,
    zeroExtendedKuhnAffine_of_mem_closedCarrier
      (fun U hU => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU)
      (componentCorrectionDatum C p) hT hx]
  change kuhnInterp T
      (fun y => competitorVertexData C p y - linearFn p y) x = _
  calc
    kuhnInterp T (fun y => competitorVertexData C p y - linearFn p y) x =
        kuhnInterp T
          (fun y => competitorVertexData C p y + (-1 : ℝ) * linearFn p y) x := by
            congr 2
            funext y
            ring
    _ = kuhnInterp T (competitorVertexData C p) x +
          kuhnInterp T (fun y => (-1 : ℝ) * linearFn p y) x := by
          rw [kuhnInterp_add]
    _ = kuhnInterp T (competitorVertexData C p) x +
          (-1 : ℝ) * kuhnInterp T (linearFn p) x := by
          rw [kuhnInterp_smul]
    _ = kuhnInterp T (competitorVertexData C p) x - linearFn p x := by
          rw [kuhnInterp_linearFn]
          ring
    _ = globalCompetitor m s C p x - linearFn p x := by
          rw [globalCompetitor,
            gluedKuhnAffine_of_mem_closedCarrier
              (fun U hU => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU)
              (competitorVertexData C p) hT hx]

/-- On the root cube, the component potential is the raw scalar correction. -/
theorem componentCorrectionPotential_eqOn_globalCompetitor_sub_linearFn
    {m s : ℤ} (hsm : s ≤ m) (C : Set (TriadicCube d)) (p : Vec d) :
    Set.EqOn (componentCorrectionPotential m s C p)
      (fun x => globalCompetitor m s C p x - linearFn p x)
      (cubeSet (originCube d m)) := by
  intro x hx
  obtain ⟨T, hT, hxT⟩ := by
    simpa only [Set.mem_iUnion] using
      cubeSet_originCube_subset_iUnion_closedCarrier_rootCoarseMesh hsm hx
  exact componentCorrectionPotential_eqOn_globalCompetitor_sub_linearFn_closedCarrier
    hsm C p hT hxT

/-- Closed balls of scale descendants are contained in the ancestor's closed
ball. -/
theorem closedBall_supportCube_subset_closedBall_of_mem_descendantsAtScale
    {Q R : TriadicCube d} {s : ℤ} (hR : R ∈ descendantsAtScale Q s) :
    Metric.closedBall (cubeCenter R) (HCPolySupport.cubeRadius R) ⊆
      Metric.closedBall (cubeCenter Q) (HCPolySupport.cubeRadius Q) := by
  by_cases hs : s ≤ Q.scale
  · rw [descendantsAtScale_eq_descendantsAtDepth Q hs] at hR
    exact closedBall_subset_closedBall_of_mem_descendantsAtDepth hR
  · rw [descendantsAtScale_eq_empty Q (by omega)] at hR
    exact absurd hR (Finset.notMem_empty _)

/-- The common-mesh closed carrier is compact. -/
theorem isCompact_commonCoarseMeshClosedCarrier
    (N : Finset (TriadicCube d)) (s : ℤ) :
    IsCompact (commonCoarseMeshClosedCarrier N s) := by
  exact (commonCoarseMesh N s).finite_toSet.isCompact_biUnion
    fun T _ => by
      rw [closedCarrier_eq_convexHull_vertexSet T]
      exact (Set.finite_range T.vertex).isCompact_convexHull (𝕜 := ℝ)

/-- If every window cube belongs to the Whitney partition, the common-mesh
closed carrier lies strictly inside the open root cube. -/
theorem commonCoarseMeshClosedCarrier_subset_openCubeSet
    {m s : ℤ} {hn : ℕ → ℕ} {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn) :
    commonCoarseMeshClosedCarrier N s ⊆ openCubeSet (originCube d m) := by
  intro x hx
  obtain ⟨T, hT, hxT⟩ := by
    simpa only [commonCoarseMeshClosedCarrier, Set.mem_iUnion] using hx
  obtain ⟨Q, hQN, hTQ⟩ := mem_commonCoarseMesh_iff.mp hT
  obtain ⟨n, hQn⟩ := hNsub Q hQN
  exact closedBall_subset_openCubeSet_of_mem_whitneyLayer hQn
    (closedBall_supportCube_subset_closedBall_of_mem_descendantsAtScale hTQ hxT.1)

/-- The correction potential vanishes away from the finite common-mesh
carrier.  Root cells omitted from the common mesh carry exactly the linear
vertex datum, so their scalar correction is zero. -/
theorem componentCorrectionPotential_eq_zero_of_notMem_commonCoarseMeshClosedCarrier
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) {x : Vec d}
    (hx : x ∉ commonCoarseMeshClosedCarrier N s) :
    componentCorrectionPotential m s C p x = 0 := by
  by_cases hroot : ∃ T ∈ rootCoarseMesh (d := d) m s, x ∈ T.closedCarrier
  · obtain ⟨T, hT, hxT⟩ := hroot
    have hTnot : T ∉ commonCoarseMesh N s := by
      intro hTcommon
      exact hx (Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hTcommon, hxT⟩⟩)
    rw [componentCorrectionPotential_eqOn_globalCompetitor_sub_linearFn_closedCarrier
      hsm C p hT hxT]
    change globalCompetitor m s C p x - linearFn p x = 0
    rw [
      globalCompetitor_eqOn_linearFn_closedCarrier_of_notMem_commonCoarseMesh
        hsm hC hN hs p hT hTnot hxT,
      sub_self]
  · push Not at hroot
    exact zeroExtendedKuhnAffine_of_forall_notMem
      (rootCoarseMesh m s) (componentCorrectionDatum C p) hroot

/-- The component correction is continuous as an ambient function.  On the
open root it is the continuous global correction; away from the compact
common-mesh carrier it is locally zero. -/
theorem continuous_componentCorrectionPotential
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    Continuous (componentCorrectionPotential m s C p) := by
  let K := commonCoarseMeshClosedCarrier N s
  have hK : IsCompact K := isCompact_commonCoarseMeshClosedCarrier N s
  have hKU : K ⊆ openCubeSet (originCube d m) :=
    commonCoarseMeshClosedCarrier_subset_openCubeSet hNsub
  have hzero : ∀ x, x ∉ K → componentCorrectionPotential m s C p x = 0 :=
    fun _ hx => componentCorrectionPotential_eq_zero_of_notMem_commonCoarseMeshClosedCarrier
      hsm hC hN hs p hx
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ openCubeSet (originCube d m)
  · have hxcube : x ∈ cubeSet (originCube d m) := openCubeSet_subset_cubeSet _ hxU
    have hrawWithin : ContinuousWithinAt
        (fun y => globalCompetitor m s C p y - linearFn p y)
        (cubeSet (originCube d m)) x :=
      (continuousOn_globalCompetitor hsm C p x hxcube).sub
        (continuous_linearFn p).continuousAt.continuousWithinAt
    have hcube_nhds : cubeSet (originCube d m) ∈ 𝓝 x :=
      Filter.mem_of_superset ((isOpen_openCubeSet _).mem_nhds hxU)
        (openCubeSet_subset_cubeSet _)
    refine (hrawWithin.continuousAt hcube_nhds).congr_of_eventuallyEq ?_
    filter_upwards [hcube_nhds] with y hy
    exact componentCorrectionPotential_eqOn_globalCompetitor_sub_linearFn hsm C p hy
  · have hxK : x ∉ K := fun hxK => hxU (hKU hxK)
    refine (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.eventually_mem hxK] with y hy
    exact hzero y hy

/-- One component correction has compact support as an ambient function. -/
theorem hasCompactSupport_componentCorrectionPotential
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    HasCompactSupport (componentCorrectionPotential m s C p) := by
  exact HasCompactSupport.intro (isCompact_commonCoarseMeshClosedCarrier N s)
    fun x hx => componentCorrectionPotential_eq_zero_of_notMem_commonCoarseMeshClosedCarrier
      hsm hC hN hs p hx

/-- The scalar correction is square-integrable in ambient space. -/
theorem memL2_componentCorrectionPotential
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    MemLp (componentCorrectionPotential m s C p) 2 volume :=
  (continuous_componentCorrectionPotential hsm hC hNsub hN hs p).memLp_of_hasCompactSupport
    (hasCompactSupport_componentCorrectionPotential hsm hC hN hs p)

/-- The coordinatewise weak-gradient representative for one zero-extended
component correction. -/
noncomputable def componentCorrectionWeakGradient [NeZero d]
    (m s : ℤ) (C : Set (TriadicCube d)) (p : Vec d) : Vec d → Vec d := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      exact fun x i => zeroExtendedKuhnAffineCoordDeriv (rootCoarseMesh m s)
        (componentCorrectionDatum C p) i x

/-- The canonical `H¹` realization of one finite component correction. -/
noncomputable def componentCorrectionH1Function
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    H1Function (openCubeSet (originCube d m)) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      let cells : Finset (KuhnCell (n + 1)) := rootCoarseMesh m s
      let datum : Vec (n + 1) → ℝ := componentCorrectionDatum C p
      let u : Vec (n + 1) → ℝ := componentCorrectionPotential m s C p
      let Du : Vec (n + 1) → Vec (n + 1) := componentCorrectionWeakGradient m s C p
      have hscale : ∀ T ∈ cells, T.supportCube.scale = s :=
        fun T hT => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hT
      have hucont : Continuous u :=
        continuous_componentCorrectionPotential hsm hC hNsub hN hs p
      exact
        { toFun := u
          grad := Du
          memL2 :=
            (memL2_componentCorrectionPotential hsm hC hNsub hN hs p).mono_measure
              Measure.restrict_le_self
          gradMemL2 := by
            intro i
            change MemLp (zeroExtendedKuhnAffineCoordDeriv cells datum i) 2
              (volume.restrict (openCubeSet (originCube (n + 1) m)))
            refine MemLp.of_bound
              (measurable_zeroExtendedKuhnAffineCoordDeriv cells datum hucont
                i).aestronglyMeasurable
              (zeroExtendedKuhnAffineCoordBound cells datum i) ?_
            exact Eventually.of_forall fun x =>
              norm_zeroExtendedKuhnAffineCoordDeriv_le cells datum hscale hucont i x
          hasWeakGradient := by
            intro i
            have hweak := hasWeakPartialDerivOn_univ_zeroExtendedKuhnAffine
              cells datum hscale hucont i
            have hrestrict := hweak.restrict
              (isOpen_openCubeSet (originCube (n + 1) m)) (Set.subset_univ _)
            simpa only [u, Du, cells, datum, componentCorrectionPotential,
              componentCorrectionWeakGradient] using hrestrict }

@[simp]
theorem componentCorrectionH1Function_toFun
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    (componentCorrectionH1Function hsm hC hNsub hN hs p).toFun =
      componentCorrectionPotential m s C p := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

@[simp]
theorem componentCorrectionH1Function_grad
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    (componentCorrectionH1Function hsm hC hNsub hN hs p).grad =
      componentCorrectionWeakGradient m s C p := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- Compact support inside the open root upgrades the component correction to
`H¹₀`. -/
theorem memH10_componentCorrectionPotential
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    MemH10 (openCubeSet (originCube d m)) (componentCorrectionPotential m s C p) := by
  let u := componentCorrectionH1Function hsm hC hNsub hN hs p
  rw [← componentCorrectionH1Function_toFun hsm hC hNsub hN hs p]
  refine memH10_of_compactSupport
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) u
    (isCompact_commonCoarseMeshClosedCarrier N s)
    (commonCoarseMeshClosedCarrier_subset_openCubeSet hNsub) ?_
  intro x hx
  rw [show u.toFun = componentCorrectionPotential m s C p from
    componentCorrectionH1Function_toFun hsm hC hNsub hN hs p]
  exact componentCorrectionPotential_eq_zero_of_notMem_commonCoarseMeshClosedCarrier
    hsm hC hN hs p hx

/-! ## Identification with the component slope field -/

/-- The open cells of a uniform root mesh cover the open root cube up to a
Lebesgue-null set. -/
theorem volume_openCubeSet_diff_iUnion_openCarrier_rootCoarseMesh
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) :
    volume (openCubeSet (originCube d m) \
      ⋃ T ∈ (rootCoarseMesh (d := d) m s : Set (KuhnCell d)), T.openCarrier) = 0 := by
  have hsub :
      openCubeSet (originCube d m) \
          (⋃ T ∈ (rootCoarseMesh (d := d) m s : Set (KuhnCell d)), T.openCarrier) ⊆
        ⋃ T ∈ (rootCoarseMesh (d := d) m s : Set (KuhnCell d)),
          (T.carrier \ T.openCarrier) := by
    intro x hx
    have hxcube : x ∈ cubeSet (originCube d m) := openCubeSet_subset_cubeSet _ hx.1
    rw [cubeSet_eq_iUnion_triadicSimplexPartition (originCube d m) hsm] at hxcube
    obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hxcube
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxT, ?_⟩⟩
    intro hxopen
    exact hx.2 (Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨hT, hxopen⟩⟩)
  refine measure_mono_null hsub ?_
  refine measure_biUnion_null_iff (Set.to_countable _) |>.mpr ?_
  intro T _
  exact volume_carrier_diff_openCarrier T

/-- On every open root-mesh cell, the weak-gradient representative is exactly
the component slope correction `∇ℓ̂_p - p`. -/
theorem componentCorrectionWeakGradient_eq_globalCompetitorSlope_sub
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) (C : Set (TriadicCube d))
    (p : Vec d) {x : Vec d}
    (hx : x ∈ ⋃ T ∈ (rootCoarseMesh (d := d) m s : Set (KuhnCell d)),
      T.openCarrier) :
    componentCorrectionWeakGradient m s C p x =
      globalCompetitorSlope m s C p x - p := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      obtain ⟨T, hT, hxT⟩ := by simpa only [Set.mem_iUnion] using hx
      funext i
      change zeroExtendedKuhnAffineCoordDeriv (rootCoarseMesh m s)
          (componentCorrectionDatum C p) i x =
        globalCompetitorSlope m s C p x i - p i
      rw [zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier
          (fun U hU => supportCube_scale_eq_of_mem_rootCoarseMesh hsm hU) hT hxT i]
      change kuhnSlope T
          (fun y => competitorVertexData C p y - linearFn p y) i =
        globalCompetitorSlope m s C p x i - p i
      rw [kuhnSlope_sub,
        globalCompetitorSlope_of_mem_openCarrier hsm C p hT hxT,
        kuhnSlope_linearFn]
      rfl

/-- The weak-gradient representative agrees almost everywhere on the open
root with the existing piecewise-constant component slope correction. -/
theorem componentCorrectionWeakGradient_ae_eq_globalCompetitorSlope_sub
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) (C : Set (TriadicCube d))
    (p : Vec d) :
    componentCorrectionWeakGradient m s C p =ᵐ[volume.restrict
        (openCubeSet (originCube d m))]
      fun x => globalCompetitorSlope m s C p x - p := by
  refine (MeasureTheory.ae_restrict_iff'
    (measurableSet_openCubeSet (originCube d m))).2 ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (volume_openCubeSet_diff_iUnion_openCarrier_rootCoarseMesh hsm)] with x hxnull hxU
  apply componentCorrectionWeakGradient_eq_globalCompetitorSlope_sub hsm C p
  by_contra hxopen
  exact hxnull ⟨hxU, hxopen⟩

/-- The canonical weak-gradient representative is an internal zero-trace
potential field. -/
theorem isPotentialZeroTraceOn_componentCorrectionWeakGradient
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d m))
      (componentCorrectionWeakGradient m s C p) := by
  let U := openCubeSet (originCube d m)
  let u : H1Function U := componentCorrectionH1Function hsm hC hNsub hN hs p
  obtain ⟨w, hw⟩ := memH10_componentCorrectionPotential hsm hC hNsub hN hs p
  have hwu : w.toH1Function.toFun = u.toFun := by
    rw [hw, show u.toFun = componentCorrectionPotential m s C p from
      componentCorrectionH1Function_toFun hsm hC hNsub hN hs p]
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hcoord : ∀ i : Fin d,
      (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict U]
        fun x => u.grad x i := by
    intro i
    have hweak := w.toH1Function.hasWeakGradient i
    rw [hwu] at hweak
    exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet (originCube d m))
      (hloc _ i) (hloc _ i) hweak (u.hasWeakGradient i)
  have hgrad : w.toH1Function.grad =ᵐ[volume.restrict U] u.grad := by
    filter_upwards [Filter.eventually_all.2 hcoord] with x hx
    funext i
    exact hx i
  have hpot : IsPotentialZeroTraceOn U u.grad :=
    IsPotentialZeroTraceOn.congr_ae hgrad ⟨w, rfl⟩
  rw [show u.grad = componentCorrectionWeakGradient m s C p from
    componentCorrectionH1Function_grad hsm hC hNsub hN hs p] at hpot
  exact hpot

/-- The existing component slope correction is an internal zero-trace
potential field. -/
theorem isPotentialZeroTraceOn_globalCompetitorSlope_sub
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d m))
      (fun x => globalCompetitorSlope m s C p x - p) :=
  IsPotentialZeroTraceOn.congr_ae
    (componentCorrectionWeakGradient_ae_eq_globalCompetitorSlope_sub hsm C p)
    (isPotentialZeroTraceOn_componentCorrectionWeakGradient hsm hC hNsub hN hs p)

/-- Public Chapter 1 packaging of the component zero-trace potential field. -/
theorem potentialZeroTraceFieldOn_globalCompetitorSlope_sub
    [NeZero d] {m s : ℤ} (hsm : s ≤ m) {hn : ℕ → ℕ}
    {C : Set (TriadicCube d)} (hC : C ⊆ whitneyPartition m hn)
    {N : Finset (TriadicCube d)}
    (hNsub : ∀ Q ∈ N, Q ∈ whitneyPartition m hn)
    (hN : ∀ Q ∈ whitneyPartition m hn, (∃ R ∈ C, CubeTouch Q R) → Q ∈ N)
    (hs : ∀ Q ∈ N, s ≤ Q.scale) (p : Vec d) :
    HCPolySupport.Book.Ch01.PotentialZeroTraceFieldOn
      (openCubeSet (originCube d m))
      (fun x => globalCompetitorSlope m s C p x - p) := by
  rcases isPotentialZeroTraceOn_globalCompetitorSlope_sub
    hsm hC hNsub hN hs p with ⟨u, hu⟩
  have hpublic := HCPolySupport.Book.Ch01.potentialZeroTraceFieldOn_of_h10 u
  rw [hu] at hpublic
  exact hpublic

end

end Algsuperdiff.Section3.Provider.Affine
