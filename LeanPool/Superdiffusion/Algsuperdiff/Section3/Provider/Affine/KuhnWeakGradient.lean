/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Affine.GlobalGluing
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.SimplexDomains
public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FaceReflectionMain
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# KuhnWeakGradient

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak gradients of finite Kuhn-affine zero extensions

This file proves the finite-mesh analytic bridge needed for one component of
the Section 3 piecewise-affine competitor.  `zeroExtendedKuhnAffine` agrees
with the proved Kuhn interpolant on a finite equal-scale mesh and is literally
zero off the closed-cell union.  Coordinate slicing gives a bounded classical
line derivative away from finitely many endpoints; one-dimensional integration
by parts and Fubini then identify an ambient weak derivative.

Everything here is restated and reproved at this repository's `KuhnCell`,
`kuhnInterp`, and `gluedKuhnAffine` carriers.
-/

namespace Algsuperdiff.Section3.Provider.Affine

open Filter Function HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
open scoped ENNReal Interval

noncomputable section

variable {n : ℕ}

/-- Parameters at which a coordinate line meets one closed Kuhn cell. -/
def kuhnCellCoordSlice (T : KuhnCell (n + 1)) (i : Fin (n + 1))
    (z : Vec n) : Set ℝ :=
  {t | i.insertNth t z ∈ T.closedCarrier}

/-- A closed Kuhn cell is compact. -/
theorem isCompact_kuhnCell_closedCarrier (T : KuhnCell (n + 1)) :
    IsCompact T.closedCarrier := by
  rw [closedCarrier_eq_convexHull_vertexSet T]
  exact (Set.finite_range T.vertex).isCompact_convexHull ℝ

/-- Inserting the varying coordinate into a fixed coordinate line is an isometry. -/
theorem isometry_finInsertNth_line (i : Fin (n + 1)) (z : Vec n) :
    Isometry (fun t : ℝ => (i.insertNth t z : Vec (n + 1))) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [Fin.dist_insertNth_insertNth, dist_self, max_eq_left dist_nonneg]

/-- A coordinate slice of a closed Kuhn cell is compact. -/
theorem isCompact_kuhnCellCoordSlice (T : KuhnCell (n + 1))
    (i : Fin (n + 1)) (z : Vec n) : IsCompact (kuhnCellCoordSlice T i z) := by
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · exact (isClosed_closedCarrier T).preimage (isometry_finInsertNth_line i z).continuous
  · exact (isometry_finInsertNth_line i z).antilipschitzWith.isBounded_preimage
      ((isCompact_kuhnCell_closedCarrier T).isBounded)

/-- A coordinate slice of a closed Kuhn cell is convex. -/
theorem convex_kuhnCellCoordSlice (T : KuhnCell (n + 1))
    (i : Fin (n + 1)) (z : Vec n) : Convex ℝ (kuhnCellCoordSlice T i z) := by
  have hT : Convex ℝ T.closedCarrier := by
    rw [closedCarrier_eq_convexHull_vertexSet T]
    exact convex_convexHull ℝ _
  let p0 : Vec (n + 1) := i.insertNth 0 z
  let p1 : Vec (n + 1) := i.insertNth 1 z
  let L : ℝ →ᵃ[ℝ] Vec (n + 1) := AffineMap.lineMap p0 p1
  have hL (t : ℝ) : L t = (i.insertNth t z : Vec (n + 1)) := by
    funext j
    rcases eq_or_ne j i with hji | hji
    · subst j
      simp [L, p0, p1, AffineMap.lineMap_apply]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp [L, p0, p1, AffineMap.lineMap_apply, Fin.insertNth_apply_succAbove]
  have hslice : kuhnCellCoordSlice T i z = L ⁻¹' T.closedCarrier := by
    ext t
    simp only [kuhnCellCoordSlice, Set.mem_ofPred_eq, Set.mem_preimage, hL]
  rw [hslice]
  exact hT.affine_preimage L

/-- A nonempty coordinate slice is the interval between its extrema. -/
theorem kuhnCellCoordSlice_eq_Icc (T : KuhnCell (n + 1))
    (i : Fin (n + 1)) (z : Vec n) (hne : (kuhnCellCoordSlice T i z).Nonempty) :
    kuhnCellCoordSlice T i z =
      Set.Icc (sInf (kuhnCellCoordSlice T i z)) (sSup (kuhnCellCoordSlice T i z)) := by
  exact eq_Icc_of_connected_compact
    ⟨hne, (convex_kuhnCellCoordSlice T i z).isPreconnected⟩
      (isCompact_kuhnCellCoordSlice T i z)

/-- The at-most-two endpoints of one coordinate slice. -/
def kuhnCellCoordSliceEndpoints (T : KuhnCell (n + 1))
    (i : Fin (n + 1)) (z : Vec n) : Finset ℝ := by
  classical
  exact if (kuhnCellCoordSlice T i z).Nonempty then
    {sInf (kuhnCellCoordSlice T i z), sSup (kuhnCellCoordSlice T i z)} else ∅

/-- Away from the endpoints, slice membership is locally constant. -/
theorem eventually_mem_kuhnCellCoordSlice_iff (T : KuhnCell (n + 1))
    (i : Fin (n + 1)) (z : Vec n) {t : ℝ}
    (ht : t ∉ kuhnCellCoordSliceEndpoints T i z) :
    ∀ᶠ s in 𝓝 t, (s ∈ kuhnCellCoordSlice T i z ↔ t ∈ kuhnCellCoordSlice T i z) := by
  classical
  by_cases hne : (kuhnCellCoordSlice T i z).Nonempty
  · have htinf : t ≠ sInf (kuhnCellCoordSlice T i z) := by
      intro h
      apply ht
      simp [kuhnCellCoordSliceEndpoints, hne, h]
    have htsup : t ≠ sSup (kuhnCellCoordSlice T i z) := by
      intro h
      apply ht
      simp [kuhnCellCoordSliceEndpoints, hne, h]
    rw [kuhnCellCoordSlice_eq_Icc T i z hne]
    by_cases htmem : t ∈ Set.Icc (sInf (kuhnCellCoordSlice T i z))
        (sSup (kuhnCellCoordSlice T i z))
    · have hinf : sInf (kuhnCellCoordSlice T i z) < t :=
        lt_of_le_of_ne htmem.1 htinf.symm
      have hsup : t < sSup (kuhnCellCoordSlice T i z) :=
        lt_of_le_of_ne htmem.2 htsup
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hinf, hsup⟩] with s hs
      exact iff_of_true ⟨hs.1.le, hs.2.le⟩ htmem
    · simp only [Set.mem_Icc, not_and_or, not_le] at htmem
      rcases htmem with htleft | htright
      · filter_upwards [isOpen_Iio.mem_nhds htleft] with s hs
        exact iff_of_false (fun h => (not_le_of_gt hs) h.1)
          (fun h => (not_le_of_gt htleft) h.1)
      · filter_upwards [isOpen_Ioi.mem_nhds htright] with s hs
        exact iff_of_false (fun h => (not_le_of_gt hs) h.2)
          (fun h => (not_le_of_gt htright) h.2)
  · have hempty : kuhnCellCoordSlice T i z = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact Filter.Eventually.of_forall fun s => by simp [hempty]

/-- The finite endpoint set contributed by every cell in a finite mesh. -/
def kuhnCellSliceEndpoints (cells : Finset (KuhnCell (n + 1)))
    (i : Fin (n + 1)) (z : Vec n) : Finset ℝ := by
  classical
  exact cells.biUnion fun T => kuhnCellCoordSliceEndpoints T i z

/-- Off the endpoint set, membership in every mesh cell is locally constant. -/
theorem eventually_forall_mem_coordSlice_iff
    (cells : Finset (KuhnCell (n + 1))) (i : Fin (n + 1)) (z : Vec n) {t : ℝ}
    (ht : t ∉ kuhnCellSliceEndpoints cells i z) :
    ∀ᶠ s in 𝓝 t, ∀ T ∈ cells,
      (s ∈ kuhnCellCoordSlice T i z ↔ t ∈ kuhnCellCoordSlice T i z) := by
  classical
  apply cells.eventually_all.2
  intro T hT
  apply eventually_mem_kuhnCellCoordSlice_iff T i z
  intro htT
  apply ht
  simp only [kuhnCellSliceEndpoints, Finset.mem_biUnion]
  exact ⟨T, hT, htT⟩

/-! ## The zero-off-mesh representative and its line derivatives -/

open Classical in
/-- The zero extension of a finite Kuhn gluing.  Unlike `gluedKuhnAffine`,
which returns its datum off the mesh, this is the representative needed for a
compactly supported component correction. -/
def zeroExtendedKuhnAffine {d : ℕ} (cells : Finset (KuhnCell d))
    (g : Vec d → ℝ) (x : Vec d) : ℝ :=
  if ∃ T ∈ cells, x ∈ T.closedCarrier then gluedKuhnAffine cells g x else 0

/-- On a selected closed cell, the zero extension is that cell's interpolant. -/
theorem zeroExtendedKuhnAffine_of_mem_closedCarrier
    {d : ℕ} {cells : Finset (KuhnCell d)} {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (g : Vec d → ℝ) {T : KuhnCell d} (hT : T ∈ cells)
    {x : Vec d} (hx : x ∈ T.closedCarrier) :
    zeroExtendedKuhnAffine cells g x = kuhnInterp T g x := by
  rw [zeroExtendedKuhnAffine, ite_eq_left ⟨T, hT, hx⟩,
    gluedKuhnAffine_of_mem_closedCarrier hscale g hT hx]

/-- Off every selected closed cell, the zero extension is zero. -/
theorem zeroExtendedKuhnAffine_of_forall_notMem
    {d : ℕ} (cells : Finset (KuhnCell d)) (g : Vec d → ℝ)
    {x : Vec d} (hx : ∀ T ∈ cells, x ∉ T.closedCarrier) :
    zeroExtendedKuhnAffine cells g x = 0 := by
  rw [zeroExtendedKuhnAffine, ite_eq_right]
  rintro ⟨T, hT, hxT⟩
  exact hx T hT hxT

/-- The selected coordinate slope along a line, with value zero off the mesh. -/
def zeroExtendedKuhnAffineLineSlope
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (i : Fin (n + 1)) (z : Vec n) (t : ℝ) : ℝ := by
  classical
  exact if h : ∃ T ∈ cells, i.insertNth t z ∈ T.closedCarrier then
    kuhnSlope (Classical.choose h) g i else 0

/-- A uniform bound for all selected slopes in one coordinate. -/
def zeroExtendedKuhnAffineCoordBound
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  ∑ T ∈ cells, ‖kuhnSlope T g i‖

/-- The coordinate-slope bound is nonnegative. -/
theorem zeroExtendedKuhnAffineCoordBound_nonneg
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (i : Fin (n + 1)) : 0 ≤ zeroExtendedKuhnAffineCoordBound cells g i := by
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem hasDerivAt_kuhnInterp_insertNth (T : KuhnCell (n + 1))
    (g : Vec (n + 1) → ℝ) (i : Fin (n + 1)) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => kuhnInterp T g (i.insertNth s z)) (kuhnSlope T g i) t := by
  let L : ℝ →ᵃ[ℝ] Vec (n + 1) :=
    AffineMap.lineMap (i.insertNth (0 : ℝ) z : Vec (n + 1))
      (i.insertNth (1 : ℝ) z : Vec (n + 1))
  have hL (s : ℝ) : L s = (i.insertNth s z : Vec (n + 1)) := by
    funext j
    rcases eq_or_ne j i with hji | hji
    · subst j
      simp [L, AffineMap.lineMap_apply]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp [L, AffineMap.lineMap_apply, Fin.insertNth_apply_succAbove]
  have hderiv :
      HasDerivAt ((kuhnInterpAffine T g).comp L)
        (((kuhnInterpAffine T g).comp L).linear 1) t :=
    ((kuhnInterpAffine T g).comp L).hasDerivAt
  have hlinear : L.linear 1 = basisVec i := by
    change
      (AffineMap.lineMap (i.insertNth (0 : ℝ) z : Vec (n + 1))
        (i.insertNth (1 : ℝ) z : Vec (n + 1))).linear 1 = basisVec i
    funext j
    rcases eq_or_ne j i with hji | hji
    · subst j
      simp [basisVec]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simp [basisVec]
  have hslope : ((kuhnInterpAffine T g).comp L).linear 1 = kuhnSlope T g i := by
    rw [AffineMap.comp_linear, LinearMap.comp_apply, kuhnInterpAffine_linear_apply,
      hlinear, vecDot_basisVec_right]
  rw [hslope] at hderiv
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [] with s
  change kuhnInterp T g (i.insertNth s z) = kuhnInterp T g (L s)
  rw [hL]

/-- Away from slice endpoints, the coordinate-line derivative is the selected slope. -/
theorem hasDerivAt_zeroExtendedKuhnAffine_insertNth_of_not_mem_endpoints
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (i : Fin (n + 1)) (z : Vec n) {t : ℝ}
    (ht : t ∉ kuhnCellSliceEndpoints cells i z) :
    HasDerivAt (fun s : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth s z))
      (zeroExtendedKuhnAffineLineSlope cells g i z t) t := by
  classical
  have hstable := eventually_forall_mem_coordSlice_iff cells i z ht
  by_cases hmem : ∃ T ∈ cells, i.insertNth t z ∈ T.closedCarrier
  · let T : KuhnCell (n + 1) := Classical.choose hmem
    have hT : T ∈ cells ∧ i.insertNth t z ∈ T.closedCarrier := Classical.choose_spec hmem
    have hnear : ∀ᶠ s in 𝓝 t, i.insertNth s z ∈ T.closedCarrier :=
      hstable.mono fun s hs => (hs T hT.1).2 hT.2
    have heq :
        (fun s : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth s z)) =ᶠ[𝓝 t]
          fun s : ℝ => kuhnInterp T g (i.insertNth s z) :=
      hnear.mono fun _ hs => zeroExtendedKuhnAffine_of_mem_closedCarrier hscale g hT.1 hs
    have hderiv := (hasDerivAt_kuhnInterp_insertNth T g i z t).congr_of_eventuallyEq heq
    simpa only [zeroExtendedKuhnAffineLineSlope, dite_eq_left hmem, T] using hderiv
  · have hnear : ∀ᶠ s in 𝓝 t,
        ¬ ∃ T ∈ cells, i.insertNth s z ∈ T.closedCarrier :=
      hstable.mono fun s hs h => hmem <| by
        obtain ⟨T, hT, hx⟩ := h
        exact ⟨T, hT, (hs T hT).1 hx⟩
    have heq :
        (fun s : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth s z)) =ᶠ[𝓝 t]
          fun _ : ℝ => 0 :=
      hnear.mono fun s hs => zeroExtendedKuhnAffine_of_forall_notMem cells g
        (fun T hT hx => hs ⟨T, hT, hx⟩)
    have hderiv : HasDerivAt
        (fun s : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth s z)) 0 t :=
      (hasDerivAt_const t 0).congr_of_eventuallyEq heq
    simpa only [zeroExtendedKuhnAffineLineSlope, dite_eq_right hmem] using hderiv

/-- Every selected line slope is bounded by the finite coordinate sum. -/
theorem norm_zeroExtendedKuhnAffineLineSlope_le
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (i : Fin (n + 1)) (z : Vec n) (t : ℝ) :
    ‖zeroExtendedKuhnAffineLineSlope cells g i z t‖ ≤
      zeroExtendedKuhnAffineCoordBound cells g i := by
  classical
  by_cases hmem : ∃ T ∈ cells, i.insertNth t z ∈ T.closedCarrier
  · rw [zeroExtendedKuhnAffineLineSlope, dite_eq_left hmem]
    exact Finset.single_le_sum (fun T _ => norm_nonneg (kuhnSlope T g i))
      (Classical.choose_spec hmem).1
  · rw [zeroExtendedKuhnAffineLineSlope, dite_eq_right hmem, norm_zero]
    exact zeroExtendedKuhnAffineCoordBound_nonneg cells g i

private theorem intervalIntegrable_deriv_zeroExtendedKuhnAffine_line
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (i : Fin (n + 1)) (z : Vec n) (a b : ℝ) :
    IntervalIntegrable
      (deriv fun t : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth t z))
      volume a b := by
  let f : ℝ → ℝ := fun t => zeroExtendedKuhnAffine cells g (i.insertNth t z)
  let B : ℝ := zeroExtendedKuhnAffineCoordBound cells g i
  have hmeas : AEStronglyMeasurable (deriv f) volume :=
    (measurable_deriv f).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume, ‖deriv f t‖ ≤ B := by
    filter_upwards [(kuhnCellSliceEndpoints cells i z).countable_toSet.ae_notMem
      (volume : Measure ℝ)] with t ht
    have hd := hasDerivAt_zeroExtendedKuhnAffine_insertNth_of_not_mem_endpoints
      cells g hscale i z ht
    rw [show deriv f t = zeroExtendedKuhnAffineLineSlope cells g i z t from hd.deriv]
    exact norm_zeroExtendedKuhnAffineLineSlope_le cells g i z t
  rw [intervalIntegrable_iff']
  exact Measure.integrableOn_of_bounded isCompact_uIcc.measure_lt_top.ne hmeas
    (ae_restrict_of_ae hbound)

/-- A continuous finite equal-scale zero extension is Lipschitz on every coordinate line. -/
theorem lipschitzWith_zeroExtendedKuhnAffine_insertNth
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells g))
    (i : Fin (n + 1)) (z : Vec n) :
    LipschitzWith ⟨zeroExtendedKuhnAffineCoordBound cells g i,
      zeroExtendedKuhnAffineCoordBound_nonneg cells g i⟩
      (fun t : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth t z)) := by
  let f : ℝ → ℝ := fun t => zeroExtendedKuhnAffine cells g (i.insertNth t z)
  let B : ℝ := zeroExtendedKuhnAffineCoordBound cells g i
  have hfcont : Continuous f := hcontinuous.comp <|
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth i z t).continuousAt
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hFTC : ∫ t in a..b, deriv f t = f b - f a := by
    apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable f (deriv f)
      (kuhnCellSliceEndpoints cells i z).countable_toSet hfcont.continuousOn
    · intro t ht
      have hd := hasDerivAt_zeroExtendedKuhnAffine_insertNth_of_not_mem_endpoints
        cells g hscale i z ht.2
      simpa only [f, hd.deriv] using hd
    · exact intervalIntegrable_deriv_zeroExtendedKuhnAffine_line
        cells g hscale i z a b
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι a b → ‖deriv f t‖ ≤ B := by
    filter_upwards [(kuhnCellSliceEndpoints cells i z).countable_toSet.ae_notMem
      (volume : Measure ℝ)] with t ht _htI
    have hd := hasDerivAt_zeroExtendedKuhnAffine_insertNth_of_not_mem_endpoints
      cells g hscale i z ht
    rw [show deriv f t = zeroExtendedKuhnAffineLineSlope cells g i z t from hd.deriv]
    exact norm_zeroExtendedKuhnAffineLineSlope_le cells g i z t
  calc
    dist (f a) (f b) = ‖f b - f a‖ := by rw [dist_comm, dist_eq_norm]
    _ = ‖∫ t in a..b, deriv f t‖ := by rw [hFTC]
    _ ≤ B * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const_ae hbound
    _ = B * dist a b := by rw [Real.dist_eq, abs_sub_comm]
    _ = ((⟨B, zeroExtendedKuhnAffineCoordBound_nonneg cells g i⟩ : NNReal) : ℝ) *
        dist a b := rfl

/-- The ambient representative of the coordinate-line derivative. -/
def zeroExtendedKuhnAffineCoordDeriv
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (i : Fin (n + 1)) (x : Vec (n + 1)) : ℝ :=
  deriv (fun t : ℝ => zeroExtendedKuhnAffine cells g (i.insertNth t (i.removeNth x))) (x i)

/-- The coordinate-line derivative representative is measurable. -/
theorem measurable_zeroExtendedKuhnAffineCoordDeriv
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells g))
    (i : Fin (n + 1)) : Measurable (zeroExtendedKuhnAffineCoordDeriv cells g i) := by
  let f : Vec n → ℝ → ℝ := fun z t => zeroExtendedKuhnAffine cells g (i.insertNth t z)
  have hf : Continuous f.uncurry := by
    have hins : Continuous (fun p : Vec n × ℝ =>
        (i.insertNth p.2 p.1 : Vec (n + 1))) := by
      exact Continuous.finInsertNth i continuous_snd continuous_fst
    exact hcontinuous.comp hins
  have hderiv : Measurable (fun p : Vec n × ℝ => deriv (f p.1) p.2) :=
    measurable_deriv_with_param hf
  have hremove : Continuous (fun x : Vec (n + 1) => i.removeNth x) :=
    continuous_pi fun j => continuous_apply (i.succAbove j)
  have hparam : Measurable (fun x : Vec (n + 1) => (i.removeNth x, x i)) :=
    (hremove.prodMk (continuous_apply i)).measurable
  simpa only [zeroExtendedKuhnAffineCoordDeriv, f] using! hderiv.comp hparam

/-- The ambient derivative representative obeys the finite coordinate bound. -/
theorem norm_zeroExtendedKuhnAffineCoordDeriv_le
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells g))
    (i : Fin (n + 1)) (x : Vec (n + 1)) :
    ‖zeroExtendedKuhnAffineCoordDeriv cells g i x‖ ≤
      zeroExtendedKuhnAffineCoordBound cells g i := by
  unfold zeroExtendedKuhnAffineCoordDeriv
  exact norm_deriv_le_of_lipschitz <|
    lipschitzWith_zeroExtendedKuhnAffine_insertNth cells g hscale hcontinuous i (i.removeNth x)

/-! ## One-dimensional integration by parts -/

private theorem integral_mul_deriv_eq_neg_of_hasDerivAt_off_finite
    {u φ dφ : ℝ → ℝ} (S : Finset ℝ) (K : NNReal)
    (hucont : Continuous u) (hulip : LipschitzWith K u)
    (hu : ∀ t, t ∉ S → HasDerivAt u (deriv u t) t)
    (hφ : ∀ t, HasDerivAt φ (dφ t) t)
    (hdφcont : Continuous dφ) (hφc : HasCompactSupport φ) :
    (∫ t, u t * dφ t) = -∫ t, deriv u t * φ t := by
  have hφcont : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hdφ_eq : dφ = deriv φ := by
    funext t
    exact (hφ t).deriv.symm
  have hdφc : HasCompactSupport dφ := by
    rw [hdφ_eq]
    exact hφc.deriv
  have hF_int : Integrable (fun t => u t * dφ t) :=
    (hucont.mul hdφcont).integrable_of_hasCompactSupport hdφc.mul_left
  have hdu_meas : AEStronglyMeasurable (deriv u) volume :=
    (measurable_deriv u).aestronglyMeasurable
  have hdu_bound : ∀ t, ‖deriv u t‖ ≤ (K : ℝ) :=
    fun t => norm_deriv_le_of_lipschitz hulip
  have hφ_int : Integrable φ := hφcont.integrable_of_hasCompactSupport hφc
  have hG_int : Integrable (fun t => deriv u t * φ t) :=
    hφ_int.bdd_mul hdu_meas (Eventually.of_forall hdu_bound)
  obtain ⟨R₀, hR₀⟩ := hφc.isBounded.subset_closedBall (0 : ℝ)
  set R := |R₀| + 1 with hRdef
  have hR_pos : 0 < R := by rw [hRdef]; positivity
  have hsub_Icc : tsupport φ ⊆ Icc (-|R₀|) |R₀| := by
    intro t ht
    have hball := hR₀ ht
    rw [Real.closedBall_eq_Icc] at hball
    simp only [zero_sub, zero_add] at hball
    exact ⟨le_trans (neg_le_neg (le_abs_self R₀)) hball.1,
      le_trans hball.2 (le_abs_self R₀)⟩
  have hR₀_lt : |R₀| < R := by rw [hRdef]; linarith
  have hnotin : ∀ y : ℝ, |R₀| < |y| → y ∉ tsupport φ := by
    intro y hy hymem
    have hyIcc := hsub_Icc hymem
    have habs : |y| ≤ |R₀| := abs_le.2 hyIcc
    linarith
  have hφR : φ R = 0 := image_eq_zero_of_notMem_tsupport <|
    hnotin R (by rw [abs_of_pos hR_pos]; exact hR₀_lt)
  have hφnegR : φ (-R) = 0 := image_eq_zero_of_notMem_tsupport <|
    hnotin (-R) (by rw [abs_neg, abs_of_pos hR_pos]; exact hR₀_lt)
  have hdφ_zero : ∀ t, t ∉ tsupport φ → dφ t = 0 := by
    intro t ht
    have hev : φ =ᶠ[𝓝 t] 0 :=
      (isClosed_tsupport φ).isOpen_compl.eventually_mem ht |>.mono
        fun y hy => image_eq_zero_of_notMem_tsupport hy
    have hzero : HasDerivAt φ 0 t := (hasDerivAt_const t 0).congr_of_eventuallyEq hev
    exact (hφ t).unique hzero
  have hIoc : ∀ (F : ℝ → ℝ), (∀ t, t ∉ tsupport φ → F t = 0) →
      Function.support F ⊆ Ioc (-R) R := by
    intro F hF t ht
    have htmem : t ∈ tsupport φ := by
      by_contra hnot
      exact ht (hF t hnot)
    have htIcc := hsub_Icc htmem
    exact ⟨by linarith [htIcc.1, hR₀_lt], le_of_lt (lt_of_le_of_lt htIcc.2 hR₀_lt)⟩
  have hFsupp : Function.support (fun t => u t * dφ t) ⊆ Ioc (-R) R :=
    hIoc _ fun t ht => by simp [hdφ_zero t ht]
  have hGsupp : Function.support (fun t => deriv u t * φ t) ⊆ Ioc (-R) R :=
    hIoc _ fun t ht => by simp [image_eq_zero_of_notMem_tsupport ht]
  have hFII : IntervalIntegrable (fun t => u t * dφ t) volume (-R) R :=
    hF_int.intervalIntegrable
  have hGII : IntervalIntegrable (fun t => deriv u t * φ t) volume (-R) R :=
    hG_int.intervalIntegrable
  have hFTC :
      (∫ t in (-R)..R, deriv u t * φ t + u t * dφ t) =
        u R * φ R - u (-R) * φ (-R) := by
    apply MeasureTheory.integral_eq_of_hasDerivAt_off_countable
      (fun t => u t * φ t) (fun t => deriv u t * φ t + u t * dφ t)
      S.countable_toSet (hucont.mul hφcont).continuousOn
    · intro t ht
      exact (hu t ht.2).mul (hφ t)
    · exact hGII.add hFII
  have hinterval :
      (∫ t in (-R)..R, u t * dφ t) = -∫ t in (-R)..R, deriv u t * φ t := by
    rw [intervalIntegral.integral_add hGII hFII, hφR, hφnegR] at hFTC
    linarith
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hFsupp,
    ← intervalIntegral.integral_eq_integral_of_support_subset hGsupp]
  exact hinterval

/-- Coordinate-line integration by parts for the zero-extended gluing. -/
theorem integral_zeroExtendedKuhnAffine_mul_testCoordDeriv_eq_neg
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells g))
    {φ : Vec (n + 1) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin (n + 1)) (z : Vec n) :
    (∫ t, zeroExtendedKuhnAffine cells g (i.insertNth t z) *
      (fderiv ℝ φ (i.insertNth t z)) (basisVec i)) =
      -∫ t, deriv (fun s => zeroExtendedKuhnAffine cells g (i.insertNth s z)) t *
        φ (i.insertNth t z) := by
  let u : ℝ → ℝ := fun t => zeroExtendedKuhnAffine cells g (i.insertNth t z)
  let φL : ℝ → ℝ := fun t => φ (i.insertNth t z)
  let dφL : ℝ → ℝ := fun t => (fderiv ℝ φ (i.insertNth t z)) (basisVec i)
  have hucont : Continuous u := hcontinuous.comp <|
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth i z t).continuousAt
  have hulip : LipschitzWith
      ⟨zeroExtendedKuhnAffineCoordBound cells g i,
        zeroExtendedKuhnAffineCoordBound_nonneg cells g i⟩ u :=
    lipschitzWith_zeroExtendedKuhnAffine_insertNth cells g hscale hcontinuous i z
  have hu : ∀ t, t ∉ kuhnCellSliceEndpoints cells i z →
      HasDerivAt u (deriv u t) t := by
    intro t ht
    have hd := hasDerivAt_zeroExtendedKuhnAffine_insertNth_of_not_mem_endpoints
      cells g hscale i z ht
    exact hd.congr_deriv hd.deriv.symm
  have hφdiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφL : ∀ t, HasDerivAt φL (dφL t) t :=
    fun t => hasDerivAt_comp_insertNth hφdiff i z t
  have hdφLcont : Continuous dφL :=
    ((hφ.continuous_fderiv (by simp)).comp
      (continuous_iff_continuousAt.2 fun t =>
        (hasDerivAt_insertNth i z t).continuousAt)).clm_apply continuous_const
  have hφLc : HasCompactSupport φL := hasCompactSupport_insertNth_line hφc i z
  exact integral_mul_deriv_eq_neg_of_hasDerivAt_off_finite
    (kuhnCellSliceEndpoints cells i z)
    ⟨zeroExtendedKuhnAffineCoordBound cells g i,
      zeroExtendedKuhnAffineCoordBound_nonneg cells g i⟩
    hucont hulip hu hφL hdφLcont hφLc

/-! ## Ambient weak derivatives -/

/-- The coordinate-line representative is a weak partial derivative on ambient space. -/
theorem hasWeakPartialDerivOn_univ_zeroExtendedKuhnAffine
    (cells : Finset (KuhnCell (n + 1))) (g : Vec (n + 1) → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells g))
    (i : Fin (n + 1)) :
    HasWeakPartialDerivOn univ i (zeroExtendedKuhnAffine cells g)
      (zeroExtendedKuhnAffineCoordDeriv cells g i) := by
  intro φ hφ hφc _hφsub
  have hφf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hDφcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    hφf.clm_apply continuous_const
  have hDφc : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hF_int : Integrable
      (fun x => zeroExtendedKuhnAffine cells g x * (fderiv ℝ φ x) (basisVec i))
      (volume : Measure (Vec (n + 1))) :=
    (hcontinuous.mul hDφcont).integrable_of_hasCompactSupport hDφc.mul_left
  have hφ_int : Integrable φ (volume : Measure (Vec (n + 1))) :=
    hφ.continuous.integrable_of_hasCompactSupport hφc
  have hG_int : Integrable
      (fun x => zeroExtendedKuhnAffineCoordDeriv cells g i x * φ x)
      (volume : Measure (Vec (n + 1))) :=
    hφ_int.bdd_mul
      (measurable_zeroExtendedKuhnAffineCoordDeriv cells g hcontinuous i).aestronglyMeasurable
      (Eventually.of_forall fun x =>
        norm_zeroExtendedKuhnAffineCoordDeriv_le cells g hscale hcontinuous i x)
  rw [MeasureTheory.setIntegral_univ, MeasureTheory.setIntegral_univ,
    integral_peel_coord i hF_int, integral_peel_coord i hG_int, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simpa only [zeroExtendedKuhnAffineCoordDeriv, Fin.removeNth_insertNth,
    Fin.insertNth_apply_same] using
    integral_zeroExtendedKuhnAffine_mul_testCoordDeriv_eq_neg
      cells g hscale hcontinuous hφ hφc i z

/-- On the interior of a mesh cell, the line-derivative representative is the
literal Kuhn slope coordinate. -/
theorem zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier
    {cells : Finset (KuhnCell (n + 1))} {g : Vec (n + 1) → ℝ} {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale = scale)
    {T : KuhnCell (n + 1)} (hT : T ∈ cells) {x : Vec (n + 1)}
    (hx : x ∈ T.openCarrier) (i : Fin (n + 1)) :
    zeroExtendedKuhnAffineCoordDeriv cells g i x = kuhnSlope T g i := by
  let line : ℝ → Vec (n + 1) := fun t => i.insertNth t (i.removeNth x)
  have hline_cont : Continuous line :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_insertNth i (i.removeNth x) t).continuousAt
  have hxline : line (x i) = x := by
    exact Fin.insertNth_self_removeNth i x
  have hnear : ∀ᶠ t in 𝓝 (x i), line t ∈ T.openCarrier := by
    have hopen : T.openCarrier ∈ 𝓝 x := (isOpen_openCarrier T).mem_nhds hx
    rw [← hxline] at hopen
    exact hline_cont.continuousAt hopen
  have heq :
      (fun t : ℝ => zeroExtendedKuhnAffine cells g (line t)) =ᶠ[𝓝 (x i)]
        fun t : ℝ => kuhnInterp T g (line t) :=
    hnear.mono fun _ ht => zeroExtendedKuhnAffine_of_mem_closedCarrier hscale g hT
      (T.openCarrier_subset_closedCarrier ht)
  have hd := (hasDerivAt_kuhnInterp_insertNth T g i (i.removeNth x) (x i)).congr_of_eventuallyEq
    heq
  exact hd.deriv

end

end Algsuperdiff.Section3.Provider.Affine
