/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedFiveTermSplit
public import LeanPool.HighContrastHomogenization.Provider.Response.LinearOscillationDuality
public import LeanPool.HighContrastHomogenization.Provider.Response.NestedAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungProjectionFatou
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRowPartialDischarge

/-!
# High-contrast homogenization: Provider.Response.PreYoungPrimalProjectionGeometry

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-!
The primal cutoff oscillation is first estimated against finite-depth cube
projections of the optimizer field.  The projection expansion is reindexed by
adapted nested cells, and its limit is identified with the physical pairing.
-/

theorem sum_range_eq_sum_Ico_descending (s : ℤ) (N : ℕ)
    (F : ℤ → ℝ) :
    (∑ j ∈ Finset.range N, F (s - ((j + 1 : ℕ) : ℤ))) =
      ∑ k ∈ Finset.Ico (s - (N : ℤ)) s, F k := by
  classical
  refine Finset.sum_bij (fun j _ ↦ s - ((j + 1 : ℕ) : ℤ)) ?_ ?_ ?_ ?_
  · intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    simp only [Finset.mem_Ico]
    constructor <;> omega
  · intro j₁ hj₁ j₂ hj₂ heq
    have heq' : s - ((j₁ + 1 : ℕ) : ℤ) =
        s - ((j₂ + 1 : ℕ) : ℤ) := by
      simpa using heq
    have hcast : (j₁ : ℤ) = (j₂ : ℤ) := by omega
    exact_mod_cast hcast
  · intro k hk
    have hlow : s - (N : ℤ) ≤ k := (Finset.mem_Ico.mp hk).1
    have hhigh : k < s := (Finset.mem_Ico.mp hk).2
    let j : ℕ := Int.toNat (s - k - 1)
    have hjcast : (j : ℤ) = s - k - 1 := by
      dsimp only [j]
      rw [Int.toNat_of_nonneg]
      omega
    refine ⟨j, Finset.mem_range.mpr ?_, ?_⟩
    · exact_mod_cast (show (j : ℤ) < (N : ℤ) by omega)
    · omega
  · intro j hj
    rfl

theorem integrableOn_diagonalWeakState_fst_component_of_aligned
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) (i : Fin d) :
    IntegrableOn (fun x ↦ (diagonalWeakState hq t a p r x).1 i)
      (adaptedCellAt q k w) volume := by
  obtain ⟨hgrad, _hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hi := integrableOn_component (U := adaptedDomain hq t) hgrad i
  simpa only [adaptedDomain_carrier] using
    hi.mono_set (adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw)

theorem integrableOn_vecDot_diagonalWeakState_pullback
    {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (a : CoeffSpace d) (p r Qcen : Vec d) :
    IntegrableOn (fun y ↦ vecDot Qcen
        (diagonalWeakState hq t a p r (matVecMul q y)).1)
      (cubeSet (translateCube z (originCube d s))) volume := by
  let R : TriadicCube d := translateCube z (originCube d s)
  obtain ⟨hgrad, _hflux⟩ := diagonalWeakState_memVectorL2 hq t a p r
  have hsub := adaptedCellAt_subset_of_mem_alignedIndex hq hst hz
  have hqdet : IsUnit q.det :=
    (Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit
  have hU : MeasurableSet (adaptedCellAt q s z) :=
    (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq s z).isOpen.measurableSet
  have hpull := memVectorL2_affinePullback hqdet hU
    (memVectorL2_mono hsub hgrad)
  rw [matImage_inv_adaptedCellAt_eq hq s z] at hpull
  have hidentityCell : adaptedCellAt (1 : Mat d) s z = openCubeSet R := by
    dsimp only [R]
    rw [Recurrence.adaptedCellAt_eq_image]
    have hone : matVecMul (1 : Mat d) = id :=
      funext fun x ↦ matVecMul_one x
    rw [hone, Set.image_id]
    rfl
  have hi : ∀ i, IntegrableOn (fun y ↦
      (diagonalWeakState hq t a p r (matVecMul q y)).1 i)
      (cubeSet R) volume := by
    intro i
    have hiOpen := integrableOn_component
      (U := adaptedDomainAt Matrix.PosDef.one s z) hpull i
    change Integrable (fun y ↦
      (diagonalWeakState hq t a p r (matVecMul q y)).1 i)
      (volume.restrict (cubeSet R))
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    simpa only [adaptedDomainAt_carrier, hidentityCell] using! hiOpen
  simpa only [vecDot] using! integrable_finsetSum
    (s := (Finset.univ : Finset (Fin d)))
    (fun i hiMem ↦ (hi i).const_mul (Qcen i))

private theorem avsum_comm
    {ι κ : Type*} (Z : Finset ι) (W : Finset κ) (f : ι → κ → ℝ) :
    avsum Z (fun z ↦ avsum W (fun w ↦ f z w)) =
      avsum W (fun w ↦ avsum Z (fun z ↦ f z w)) := by
  unfold avsum
  simp only
  calc
    (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, (W.card : ℝ)⁻¹ * ∑ w ∈ W, f z w =
        ((Z.card : ℝ)⁻¹ * (W.card : ℝ)⁻¹) *
          ∑ z ∈ Z, ∑ w ∈ W, f z w := by
      rw [← Finset.mul_sum]
      ring
    _ = ((W.card : ℝ)⁻¹ * (Z.card : ℝ)⁻¹) *
          ∑ w ∈ W, ∑ z ∈ Z, f z w := by
      rw [Finset.sum_comm]
      ring
    _ = (W.card : ℝ)⁻¹ * ∑ w ∈ W, (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, f z w := by
      rw [← Finset.mul_sum]
      ring

theorem abs_avsum_le_avsum_abs {ι : Type*} (Z : Finset ι)
    (f : ι → ℝ) :
    |avsum Z f| ≤ avsum Z (fun z ↦ |f z|) := by
  unfold avsum
  rw [abs_mul, abs_of_nonneg (by positivity :
    0 ≤ ((Z.card : ℝ))⁻¹)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (by positivity)

theorem avsum_finset_sum {ι κ : Type*} (Z : Finset ι)
    (W : Finset κ) (f : ι → κ → ℝ) :
    avsum Z (fun z ↦ ∑ w ∈ W, f z w) =
      ∑ w ∈ W, avsum Z (fun z ↦ f z w) := by
  unfold avsum
  rw [Finset.sum_comm, Finset.mul_sum]

theorem integral_double_avsum_le_of_half_integral_row_bounds
    {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α}
    (Z : Finset ι) (W : Finset κ) (pair : ι → κ → α → ℝ)
    (energy load : κ → ℝ)
    (hint : ∀ z ∈ Z, ∀ w ∈ W, Integrable (pair z w) μ)
    (hrow : ∀ w ∈ W,
      avsum Z (fun z ↦ (1 / 2 : ℝ) * ∫ a, pair z w a ∂μ) ≤
        energy w * load w) :
    ∫ a, avsum Z (fun z ↦ avsum W (fun w ↦ pair z w a)) ∂μ ≤
      2 * avsum W (fun w ↦ energy w * load w) := by
  have hintW : ∀ z ∈ Z,
      Integrable (fun a ↦ avsum W (fun w ↦ pair z w a)) μ := by
    intro z hz
    unfold avsum
    exact (integrable_finsetSum W fun w hw ↦ hint z hz w hw).const_mul _
  have hterm : ∀ w ∈ W,
      avsum Z (fun z ↦ ∫ a, pair z w a ∂μ) ≤
        2 * (energy w * load w) := by
    intro w hw
    have hhalf := hrow w hw
    rw [avsum_const_mul] at hhalf
    linarith only [hhalf]
  calc
    ∫ a, avsum Z (fun z ↦ avsum W (fun w ↦ pair z w a)) ∂μ =
        avsum Z (fun z ↦
          ∫ a, avsum W (fun w ↦ pair z w a) ∂μ) :=
      integral_avsum_eq_avsum_integral Z _ hintW
    _ = avsum Z (fun z ↦ avsum W (fun w ↦ ∫ a, pair z w a ∂μ)) := by
      unfold avsum
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      simpa only [avsum] using
        (integral_avsum_eq_avsum_integral W _
          (fun w hw ↦ hint z hz w hw))
    _ = avsum W (fun w ↦ avsum Z (fun z ↦ ∫ a, pair z w a ∂μ)) :=
      avsum_comm Z W _
    _ ≤ avsum W (fun w ↦ 2 * (energy w * load w)) :=
      avsum_le_avsum hterm
    _ = 2 * avsum W (fun w ↦ energy w * load w) :=
      avsum_const_mul W 2 _

theorem descendantsAtDepth_translated_root_eq_nested_labels
    {q : Mat d} (hq : q.PosDef) {k s : ℤ} (hks : k ≤ s)
    (z : Fin d → ℤ) :
    descendantsAtDepth (translateCube z (originCube d s))
        (Int.toNat (s - k)) =
      (alignedIndex q k s).image (fun w ↦
        translateCube (nestedLabel k s z w) (originCube d k)) := by
  classical
  let n : ℕ := Int.toNat (s - k)
  have hn : (n : ℤ) = s - k := by
    dsimp only [n]
    omega
  rw [descendantsAtDepth_translateCube]
  rw [← image_translateCube_alignedIndex_one_eq_descendantsAtDepth d s n]
  rw [Finset.image_image]
  have hscale : s - (n : ℤ) = k := by omega
  rw [hscale, alignedIndex_one_eq hq hks]
  apply Finset.image_congr
  intro w hw
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    simp only [translateCube, originCube,
      descendantTranslationShift, nestedLabel]
    ring

theorem cubeBesovCircDepthAverage_pullback_eq_nested_avsum
    {q : Mat d} (hq : q.PosDef) {k s : ℤ} (hks : k ≤ s)
    (z : Fin d → ℤ) (g : Vec d → ℝ) :
    cubeBesovCircDepthAverage (translateCube z (originCube d s)) 1
        (fun y ↦ g (matVecMul q y)) (Int.toNat (s - k)) =
      avsum (alignedIndex q k s) (fun w ↦
        |volumeAverage (adaptedCellAt q k (nestedLabel k s z w)) g|) := by
  classical
  let Z := alignedIndex q k s
  let phi : (Fin d → ℤ) → TriadicCube d := fun w ↦
    translateCube (nestedLabel k s z w) (originCube d k)
  have hphi : Function.Injective phi := by
    intro w v hwv
    funext i
    have hi := congrArg (fun R : TriadicCube d ↦ R.index i) hwv
    dsimp only [phi, translateCube, originCube, nestedLabel] at hi
    simp only [Pi.zero_apply, zero_add] at hi
    exact add_left_cancel hi
  rw [cubeBesovCircDepthAverage]
  unfold descendantsAverage
  rw [descendantsAtDepth_translated_root_eq_nested_labels hq hks z]
  change ((((Z.image phi).card : ℝ))⁻¹ *
      ∑ R ∈ Z.image phi,
        ‖cubeAverage R (fun y ↦ g (matVecMul q y))‖ ^ (1 : ENNReal).toReal) = _
  rw [Finset.card_image_of_injective _ hphi]
  rw [Finset.sum_image hphi.injOn]
  rw [avsum_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  rw [show (1 : ENNReal).toReal = 1 by norm_num, Real.rpow_one,
    Real.norm_eq_abs]
  exact congrArg abs
    (volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq k
      (nestedLabel k s z w) g).symm

theorem volumeAverage_vecDot_fst_eq_vecDot_blockCellAverage
    (U : Set (Vec d)) (F : Vec d → BlockVec d) (Qcen : Vec d)
    (hF : ∀ i, IntegrableOn (fun x ↦ (F x).1 i) U volume) :
    volumeAverage U (fun x ↦ vecDot Qcen (F x).1) =
      vecDot Qcen (blockCellAverage U F).1 := by
  rw [blockCellAverage_fst]
  change volumeAverage U (fun x ↦ vecDot Qcen (F x).1) =
    vecDot Qcen (fun i ↦ volumeAverage U (fun x ↦ (F x).1 i))
  exact volumeAverage_vecDot_left (U := U) Qcen (fun x ↦ (F x).1) hF

theorem cubeBesovCircDepthAverage_primal_eq_nested_cellPair_avsum
    {q : Mat d} (hq : q.PosDef) {k s : ℤ} (hks : k ≤ s)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Qcen : Vec d)
    (hF : ∀ w ∈ alignedIndex q k s, ∀ i,
      IntegrableOn (fun x ↦ (F x).1 i)
        (adaptedCellAt q k (nestedLabel k s z w)) volume) :
    cubeBesovCircDepthAverage (translateCube z (originCube d s)) 1
        (fun y ↦ vecDot Qcen (F (matVecMul q y)).1)
        (Int.toNat (s - k)) =
      avsum (alignedIndex q k s) (fun w ↦
        |vecDot Qcen
          (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w)) F).1|) := by
  rw [cubeBesovCircDepthAverage_pullback_eq_nested_avsum hq hks z
    (fun x ↦ vecDot Qcen (F x).1)]
  unfold avsum
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  exact congrArg abs
    (volumeAverage_vecDot_fst_eq_vecDot_blockCellAverage
      (adaptedCellAt q k (nestedLabel k s z w)) F Qcen
      (hF w hw))

theorem abs_cubeBesovPairing_cubeProjection_le_depth_sum
    (Q : TriadicCube d) (f G : Vec d → ℝ) (N : ℕ) (K : ℕ → ℝ)
    (hGInt : IntegrableOn G (cubeSet Q) volume)
    (hf : MemLp f 1 (normalizedCubeMeasure Q))
    (hfTop : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MemLp (cubeFluctuation R f) (⊤ : ENNReal) (normalizedCubeMeasure R))
    (hmean : cubeAverage Q f = 0)
    (hres : ∀ j < N, ∀ x ∈ cubeSet Q,
      |cubeProjectionResidual Q j f x| ≤ K j) :
    |cubeBesovPairing Q f (cubeProjection Q N G)| ≤
      ∑ j ∈ Finset.range N, K j * cubeBesovCircDepthAverage Q 1 G (j + 1) := by
  classical
  have hconj : cubeBesovConjExponent (⊤ : ENNReal) = 1 := by
    simp [cubeBesovConjExponent, ENNReal.conjExponent]
  have hgProj : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MemLp (cubeProjection Q (j + 1) G)
        (cubeBesovConjExponent (⊤ : ENNReal))
        (normalizedCubeMeasure R) := by
    intro j hj R hR
    rw [hconj]
    exact cubeProjection_succ_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) 1 G hR
  have hid :=
    cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
      (Q := Q) (p := (⊤ : ENNReal)) (f := f) (g := G) (N := N)
      hGInt hfTop hgProj le_top
  rw [hid, hmean, zero_mul, zero_add]
  have hterm : ∀ j ∈ Finset.range N,
      |cubeAverage Q (fun x ↦ cubeProjection Q (j + 1) G x *
        cubeProjectionResidual Q j f x)| ≤
      K j * cubeBesovCircDepthAverage Q 1 G (j + 1) := by
    intro j hj
    exact abs_cubeAverage_cubeProjection_mul_cubeProjectionResidual_le
      Q f G j hf (hres j (Finset.mem_range.mp hj))
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)

theorem cutoff_projectionResidual_le_sharp
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (j : ℕ) {x : Vec d}
    (hx : x ∈ cubeSet (translateCube z (originCube d s))) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    |cubeProjectionResidual R j f x| ≤
      32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-((t - s) + (j : ℤ))) := by
  dsimp only
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  have hphiCont : Continuous phi :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.comp (continuous_matVecMul q)
  obtain ⟨T, hT, hxT⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
  have hphiTopT : MemLp phi (⊤ : ENNReal) (normalizedCubeMeasure T) := by
    apply memLp_top_of_bound hphiCont.aestronglyMeasurable 2
    exact _root_.Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (adaptedPreYoungCutoff_nonneg hq t _)]
      exact adaptedPreYoungCutoff_le_two hq t _
  have hphiTwoT : MemLp phi 2 (normalizedCubeMeasure T) :=
    hphiTopT.mono_exponent (by norm_num)
  have hTscale : T.scale = s - (j : ℤ) := by
    simpa only [R] using! scale_eq_sub_of_mem_descendantsAtDepth hT
  have hosc := adaptedPreYoungCutoff_pullback_sub_cubeAverage_sharp
    (s := s - (j : ℤ)) (t := t) (H := (t - s) + (j : ℤ))
    hq hTscale (by omega) hxT
  unfold cubeProjectionResidual
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hT hxT]
  have havg : cubeAverage T f = cubeAverage T phi - cubeAverage R phi := by
    simpa only [f] using
      cubeAverage_sub_const_of_memLp_two T hphiTwoT (cubeAverage R phi)
  rw [havg]
  calc
    |(phi x - cubeAverage R phi) -
        (cubeAverage T phi - cubeAverage R phi)| =
        |cubeAverage T phi - phi x| := by
      rw [show (phi x - cubeAverage R phi) -
          (cubeAverage T phi - cubeAverage R phi) =
            -(cubeAverage T phi - phi x) by ring, abs_neg]
    _ ≤ 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
        (3 : ℝ) ^ (-((t - s) + (j : ℤ))) := by
      simpa only [phi] using hosc

theorem abs_cutoff_projected_primal_pairing_le_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Qcen : Vec d)
    (N : ℕ)
    (hGInt : IntegrableOn (fun y ↦ vecDot Qcen (F (matVecMul q y)).1)
      (cubeSet (translateCube z (originCube d s))) volume) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦
      vecDot Qcen (F (matVecMul q y)).1
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            cubeBesovCircDepthAverage R 1 G (j + 1) := by
  dsimp only
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
  have hphiCont : Continuous phi :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.comp (continuous_matVecMul q)
  have hphiInt : IntegrableOn phi (cubeSet R) volume :=
    (hphiCont.continuousOn.integrableOn_compact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hphiAvg0 : 0 ≤ cubeAverage R phi :=
    le_cubeAverage_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_nonneg hq t _)
  have hphiAvg2 : cubeAverage R phi ≤ 2 :=
    cubeAverage_le_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_le_two hq t _)
  have hfTopR : MemLp f (⊤ : ENNReal) (normalizedCubeMeasure R) := by
    apply memLp_top_of_bound (hphiCont.sub continuous_const).aestronglyMeasurable 2
    exact _root_.Filter.Eventually.of_forall fun y ↦ by
      have h1 : 0 ≤ adaptedPreYoungCutoff q hq t (matVecMul q y) :=
        adaptedPreYoungCutoff_nonneg hq t _
      have h2 : adaptedPreYoungCutoff q hq t (matVecMul q y) ≤ 2 :=
        adaptedPreYoungCutoff_le_two hq t _
      rw [Real.norm_eq_abs, abs_le]
      constructor <;>
        simp only [phi, Pi.sub_apply] <;>
        linarith only [h1, h2, hphiAvg0, hphiAvg2]
  have hf : MemLp f 1 (normalizedCubeMeasure R) :=
    hfTopR.mono_exponent (by norm_num)
  have hfFluct : ∀ j : ℕ, ∀ T ∈ descendantsAtDepth R j,
      MemLp (cubeFluctuation T f) (⊤ : ENNReal)
        (normalizedCubeMeasure T) := by
    intro j T hT
    change MemLp (f - fun x ↦ cubeAverage T f) (⊤ : ENNReal)
      (normalizedCubeMeasure T)
    exact (memLp_on_descendant_of_memLp hT hfTopR).sub
      (memLp_const (cubeAverage T f))
  have hmean : cubeAverage R f = 0 := by
    simpa only [f, cubeFluctuation] using! cubeAverage_cubeFluctuation R phi
  exact abs_cubeBesovPairing_cubeProjection_le_depth_sum R f G N
    (fun j ↦ 32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
      (3 : ℝ) ^ (-((t - s) + (j : ℤ))))
    hGInt hf (fun j _ ↦ hfFluct j) hmean
    (fun j _ x hx ↦ by
      simpa only [R, phi, f] using
        cutoff_projectionResidual_le_sharp hq s t z j hx)

theorem abs_cutoff_projected_primal_pairing_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (z : Fin d → ℤ) (F : Vec d → BlockVec d) (Qcen : Vec d)
    (N : ℕ)
    (hGInt : IntegrableOn (fun y ↦ vecDot Qcen (F (matVecMul q y)).1)
      (cubeSet (translateCube z (originCube d s))) volume)
    (hF : ∀ j < N, ∀ w ∈ alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s,
      ∀ i, IntegrableOn (fun x ↦ (F x).1 i)
        (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
          (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) volume) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦
      vecDot Qcen (F (matVecMul q y)).1
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Qcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) F).1|) := by
  dsimp only
  have hbase := abs_cutoff_projected_primal_pairing_le_depth_sum
    hq s t z F Qcen N hGInt
  refine hbase.trans_eq ?_
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hks : s - ((j + 1 : ℕ) : ℤ) ≤ s := by omega
  have hdepth := cubeBesovCircDepthAverage_primal_eq_nested_cellPair_avsum
    hq hks z F Qcen (hF j (Finset.mem_range.mp hj))
  have hnat : Int.toNat (s - (s - ((j + 1 : ℕ) : ℤ))) = j + 1 := by
    omega
  rw [hnat] at hdepth
  exact hdepth

theorem abs_cutoff_projected_primal_pairing_subSkew_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Qcen : Vec d) (N : ℕ) :
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d := diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    |cubeBesovPairing R f (cubeProjection R N G)| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Qcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w)) F).1|) := by
  dsimp only
  apply abs_cutoff_projected_primal_pairing_le_nested_depth_sum
    hq s t z (diagonalWeakState hq t (a.subSkew g hg) p r) Qcen N
  · exact integrableOn_vecDot_diagonalWeakState_pullback
      hq hst hz (a.subSkew g hg) p r Qcen
  · intro j hj w hw i
    have hks : s - ((j + 1 : ℕ) : ℤ) ≤ s := by omega
    have hmem := nestedLabel_mem_alignedIndex hq hks hst hw hz
    exact integrableOn_diagonalWeakState_fst_component_of_aligned
      hq (hks.trans hst) hmem (a.subSkew g hg) p r i

@[expose]
def primal_projected_oscillation [NeZero d]
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f (cubeProjection R N G)

@[expose]
def primal_physical_oscillation [NeZero d]
    {q : Mat d} (hq : q.PosDef) (s t : ℤ)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (a : CoeffSpace d) : ℝ :=
  avsum (alignedIndex q s t) fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f G

theorem abs_primal_projected_oscillation_le_nested_depth_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (N : ℕ) (a : CoeffSpace d) :
    |primal_projected_oscillation hq s t g hg p r Qcen N a| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q s t) (fun z ↦
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Qcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakState hq t (a.subSkew g hg) p r)).1|)) := by
  let Z := alignedIndex q s t
  let pair : (Fin d → ℤ) → ℝ := fun z ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f (cubeProjection R N G)
  have hcell : ∀ z ∈ Z, |pair z| ≤
      ∑ j ∈ Finset.range N,
        (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
          (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
            avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
              (fun w ↦ |vecDot Qcen
                (blockCellAverage
                  (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                    (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                  (diagonalWeakState hq t (a.subSkew g hg) p r)).1|) := by
    intro z hz
    simpa only [pair] using
      abs_cutoff_projected_primal_pairing_subSkew_le_nested_depth_sum
        hq hst hz g hg a p r Qcen N
  change |avsum Z pair| ≤ _
  calc
    |avsum Z pair| ≤ avsum Z (fun z ↦ |pair z|) :=
      abs_avsum_le_avsum_abs Z pair
    _ ≤ avsum Z (fun z ↦ ∑ j ∈ Finset.range N,
          (32 * (d : ℝ) ^ 2 * smoothTransitionProfile.derivBound *
            (3 : ℝ) ^ (-((t - s) + (j : ℤ)))) *
              avsum (alignedIndex q (s - ((j + 1 : ℕ) : ℤ)) s)
                (fun w ↦ |vecDot Qcen
                  (blockCellAverage
                    (adaptedCellAt q (s - ((j + 1 : ℕ) : ℤ))
                      (nestedLabel (s - ((j + 1 : ℕ) : ℤ)) s z w))
                    (diagonalWeakState hq t (a.subSkew g hg) p r)).1|)) :=
      avsum_le_avsum hcell
    _ = _ := by
      rw [avsum_finset_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [avsum_const_mul]

theorem primal_cutoff_oscillation_eq_unprojected_pairing
    [NeZero d] {q : Mat d} (hq : q.PosDef) (s t : ℤ) (w : Fin d → ℤ)
    (F : Vec d → BlockVec d) (Qcen : Vec d) :
    let R : TriadicCube d := translateCube w (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦
      vecDot Qcen (F (matVecMul q y)).1
    volumeAverage (adaptedCellAt q s w) (fun x ↦
        (adaptedPreYoungCutoff q hq t x -
          volumeAverage (adaptedCellAt q s w)
            (adaptedPreYoungCutoff q hq t)) *
          vecDot Qcen (F x).1) =
      cubeBesovPairing R f G := by
  dsimp only
  rw [volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq,
    volumeAverage_adaptedCellAt_eq_cubeAverage_pullback hq]
  rfl

theorem projected_primal_pairing_tendsto_physical
    (Q : TriadicCube d) (f G : Vec d → ℝ) (C : ℝ)
    (hGInt : IntegrableOn G (cubeSet Q) volume)
    (hfInt : IntegrableOn f (cubeSet Q) volume)
    (hC : 0 ≤ C)
    (hfBound : ∀ x ∈ cubeSet Q, |f x| ≤ C) :
    _root_.Filter.Tendsto
        (fun n ↦ cubeBesovPairing Q f (cubeProjection Q (n + 1) G))
        _root_.Filter.atTop (nhds (cubeBesovPairing Q f G)) := by
  have hlim :=
    tendsto_cubeBesovPairing_projection_left_of_integrableOn_of_bounded
      Q G f C hGInt hfInt hC hfBound
  have hswap : ∀ n : ℕ,
      cubeBesovPairing Q (cubeProjection Q (n + 1) G) f =
        cubeBesovPairing Q f (cubeProjection Q (n + 1) G) := by
    intro n
    simp only [cubeBesovPairing]
    exact congrArg (cubeAverage Q) (funext fun x ↦ mul_comm _ _)
  have htarget : cubeBesovPairing Q G f = cubeBesovPairing Q f G := by
    simp only [cubeBesovPairing]
    exact congrArg (cubeAverage Q) (funext fun x ↦ mul_comm _ _)
  rw [← htarget]
  exact hlim.congr fun n ↦ hswap n

end

end HCPolySupport.HighContrast.Response
