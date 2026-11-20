/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.WholePlaneLocalC2
public import LeanPool.FastDynamo.Global.HorizontalTransportSkewness

/-!
# Fibre transfer on the whole plane and the plane-side quotient identity

The paper works with the two-component induction operator, while the
repository's whole-plane layer (`Operator/WholePlaneLocal.lean`) is hard-wired to the
three-component fibre `ℂ³`.  This module supplies the whole-plane counterpart of the transverse
fibre calculus of `Operator/HorizontalSector.lean` and `Global/HorizontalTransportSkewness.lean`:

* a *generic* fibre functor.  A bounded map `L : F →L[ℂ] G` of fibres acts on whole-plane `L²`
  by `L.compLpL`, on tempered distributions by postcomposition, and — because those two actions
  agree and postcomposition commutes with line differentiation — on the weak `H²` jet graph.
* the two instances used in the formalised proof: the horizontal projection
  `π_⊥ : ℂ³ ↠ ℂ²` of `Operator/WholePlaneLocalC2.lean` and the isometric zero extension
  `ι_⊥ : ℂ² ↪ ℂ³` of `Global/HorizontalTransportSkewness.lean`.
* the **plane-side quotient identity** `π_⊥ ∘ A₃ = A₂ ∘ π_⊥` between
  the actions `selectedWholePlaneInductionAction` (a three-component version of
  `eq:selected-whole-plane-operator`) and `selectedWholePlaneC2InductionAction` (two
  components, as in the paper).  This is the
  whole-plane analogue of the torus block relation
  `horizontalProjL2_reducedInductionAction`
  (`Operator/HorizontalSector.lean`): the stretching term is the only mixing term, and the
  projection turns its `ℂ³`-valued coefficient `∂_j v` into the horizontal coefficient
  `(∂_j v)_⊥`.  The zero extension does **not** intertwine the two actions: the `(3,⊥)` block
  `h ↦ ∑_j h_j ∂_j v₃` is nonzero, so `ℂ²` is a quotient, not a subrepresentation.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv

namespace WholePlaneHorizontalFibre

/-! ## The generic fibre functor -/

section Generic

variable {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] [CompleteSpace G] in
/-- A pointwise isometric fibre map induces an isometry of whole-plane `L²`. -/
theorem norm_fibreL2_apply (L : F →L[ℂ] G) (hL : ∀ v : F, ‖L v‖ = ‖v‖)
    (f : WholePlaneL2 F) : ‖fibreL2 L f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [fibreL2_coe_ae L f] with x hx
  rw [hx, hL]

omit [CompleteSpace F] [CompleteSpace G] in
/-- A pointwise contractive fibre map induces a contraction of whole-plane `L²`. -/
theorem norm_fibreL2_apply_le (L : F →L[ℂ] G) (hL : ∀ v : F, ‖L v‖ ≤ ‖v‖)
    (f : WholePlaneL2 F) : ‖fibreL2 L f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) ?_
  refine eLpNorm_mono_ae (Lp.aestronglyMeasurable _) ?_
  filter_upwards [fibreL2_coe_ae L f] with x hx
  rw [hx]
  exact hL _

omit [CompleteSpace F] [CompleteSpace G] in
/-- A pointwise fibre map commutes with multiplication by a scalar `L∞` coefficient. -/
theorem fibreL2_scalarVectorMulL2 (L : F →L[ℂ] G)
    (a : WholePlaneScalarLInf) (f : WholePlaneL2 F) :
    fibreL2 L (scalarVectorMulL2 (E := F) volume a f) =
      scalarVectorMulL2 (E := G) volume a (fibreL2 L f) := by
  apply Lp.ext
  filter_upwards [fibreL2_coe_ae L (scalarVectorMulL2 (E := F) volume a f),
    scalarVectorMulL2_coe_ae (E := F) volume a f,
    scalarVectorMulL2_coe_ae (E := G) volume a (fibreL2 L f),
    fibreL2_coe_ae L f] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4, map_smul]

omit [CompleteSpace F] [CompleteSpace G] in
/-- A pointwise fibre map turns a vector-valued `L∞` coefficient into its image. -/
theorem fibreL2_vectorScalarMulL2 (L : F →L[ℂ] G)
    (a : WholePlaneLInf F) (g : WholePlaneScalarL2) :
    fibreL2 L (vectorScalarMulL2 (E := F) volume a g) =
      vectorScalarMulL2 (E := G) volume (L.compLpL ∞ volume a) g := by
  apply Lp.ext
  filter_upwards [fibreL2_coe_ae L (vectorScalarMulL2 (E := F) volume a g),
    vectorScalarMulL2_coe_ae (E := F) volume a g,
    vectorScalarMulL2_coe_ae (E := G) volume (L.compLpL ∞ volume a) g,
    L.coeFn_compLpL a] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2, hx3, hx4, map_smul]

/-- The ambient second-order jet obtained by applying a fibre map in every slot. -/
def fibreH2Ambient (L : F →L[ℂ] G) :
    WholePlaneH2 F →L[ℂ] WholePlaneH2Ambient G :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet2Index ↦ WholePlaneL2 G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q ↦ q.elim
      (fun s ↦ s.elim ((fibreL2 L).comp (wholePlaneH2Embedding F))
        (fun j ↦ (fibreL2 L).comp (wholePlaneH2FirstDerivative F j)))
      (fun jk ↦ (fibreL2 L).comp (wholePlaneH2SecondDerivative F jk.1 jk.2)))

omit [CompleteSpace G] in
/-- The value slot of the transported jet. -/
@[simp] theorem fibreH2Ambient_value (L : F →L[ℂ] G) (u : WholePlaneH2 F) :
    fibreH2Ambient L u (Sum.inl none) = fibreL2 L (wholePlaneH2Embedding F u) :=
  rfl

omit [CompleteSpace G] in
/-- The first-derivative slots of the transported jet. -/
@[simp] theorem fibreH2Ambient_firstDerivative (L : F →L[ℂ] G) (u : WholePlaneH2 F)
    (j : Fin 2) :
    fibreH2Ambient L u (Sum.inl (some j)) =
      fibreL2 L (wholePlaneH2FirstDerivative F j u) :=
  rfl

omit [CompleteSpace G] in
/-- The second-derivative slots of the transported jet. -/
@[simp] theorem fibreH2Ambient_secondDerivative (L : F →L[ℂ] G) (u : WholePlaneH2 F)
    (j k : Fin 2) :
    fibreH2Ambient L u (Sum.inr (j, k)) =
      fibreL2 L (wholePlaneH2SecondDerivative F j k u) :=
  rfl

/-- A bounded fibre map acting on the whole-plane weak `H²` jet graph. -/
def fibreH2 (L : F →L[ℂ] G) : WholePlaneH2 F →L[ℂ] WholePlaneH2 G :=
  (fibreH2Ambient L).codRestrict (wholePlaneH2Graph G) (fun u ↦ by
    rw [mem_wholePlaneH2Graph_iff]
    constructor
    · intro j
      simp only [fibreH2Ambient_value, fibreH2Ambient_firstDerivative]
      rw [← fibreTempered_l2, ← fibreTempered_l2, ← fibreTempered_lineDeriv,
        wholePlaneH2_firstDerivative_distribution]
    · intro j k
      simp only [fibreH2Ambient_firstDerivative, fibreH2Ambient_secondDerivative]
      rw [← fibreTempered_l2, ← fibreTempered_l2, ← fibreTempered_lineDeriv,
        wholePlaneH2_secondDerivative_distribution])

/-- The fibre map commutes with each stored ordered second weak derivative. -/
theorem wholePlaneH2SecondDerivative_fibreH2 (L : F →L[ℂ] G) (j k : Fin 2)
    (u : WholePlaneH2 F) :
    wholePlaneH2SecondDerivative G j k (fibreH2 L u) =
      fibreL2 L (wholePlaneH2SecondDerivative F j k u) :=
  rfl

/-- The fibre map commutes with the transverse Laplacian. -/
theorem wholePlaneLaplacian_fibreH2 (L : F →L[ℂ] G) (u : WholePlaneH2 F) :
    wholePlaneLaplacian G (fibreH2 L u) = fibreL2 L (wholePlaneLaplacian F u) := by
  rw [wholePlaneLaplacian_apply, wholePlaneLaplacian_apply, map_add,
    wholePlaneH2SecondDerivative_fibreH2, wholePlaneH2SecondDerivative_fibreH2]

end Generic

/-! ## The two fibre maps of the formalised proof -/

/-- The pointwise zero extension is an isometry `ℂ² → ℂ³`. -/
theorem norm_verticalZeroExtendPoint (v : C2) :
    ‖verticalZeroExtendPoint v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_three]
  have h0 : ‖verticalZeroExtendPoint v 0‖ = ‖v 0‖ :=
    congrArg norm (verticalZeroExtendPoint_apply_castSucc v 0)
  have h1 : ‖verticalZeroExtendPoint v 1‖ = ‖v 1‖ :=
    congrArg norm (verticalZeroExtendPoint_apply_castSucc v 1)
  have h2 : ‖verticalZeroExtendPoint v 2‖ = 0 := by
    rw [verticalZeroExtendPoint_apply_two, norm_zero]
  rw [h0, h1, h2]
  norm_num

/-- The horizontal projection on whole-plane `L²`. -/
def wholePlaneHorizontalProjL2 : WholePlaneC3L2 →L[ℂ] WholePlaneC2L2 :=
  fibreL2 horizontalProjPoint

/-- The horizontal projection on the whole-plane weak `H²` graph. -/
def wholePlaneHorizontalProjH2 : WholePlaneC3H2 →L[ℂ] WholePlaneC2H2 :=
  fibreH2 horizontalProjPoint

/-- The axial zero extension on whole-plane `L²`. -/
def wholePlaneVerticalZeroExtendL2 : WholePlaneC2L2 →L[ℂ] WholePlaneC3L2 :=
  fibreL2 verticalZeroExtendPoint

/-- The axial zero extension on the whole-plane weak `H²` graph. -/
def wholePlaneVerticalZeroExtendH2 : WholePlaneC2H2 →L[ℂ] WholePlaneC3H2 :=
  fibreH2 verticalZeroExtendPoint

/-- Almost-everywhere representative of the whole-plane horizontal projection. -/
theorem wholePlaneHorizontalProjL2_coe_ae (f : WholePlaneC3L2) :
    (wholePlaneHorizontalProjL2 f : WholePlane → C2) =ᵐ[volume]
      fun x ↦ horizontalProjPoint ((f : WholePlane → C3) x) :=
  fibreL2_coe_ae _ f

/-- Almost-everywhere representative of the whole-plane axial zero extension. -/
theorem wholePlaneVerticalZeroExtendL2_coe_ae (f : WholePlaneC2L2) :
    (wholePlaneVerticalZeroExtendL2 f : WholePlane → C3) =ᵐ[volume]
      fun x ↦ verticalZeroExtendPoint ((f : WholePlane → C2) x) :=
  fibreL2_coe_ae _ f

/-- Projecting a zero-extended whole-plane field returns it. -/
@[simp] theorem wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2
    (f : WholePlaneC2L2) :
    wholePlaneHorizontalProjL2 (wholePlaneVerticalZeroExtendL2 f) = f := by
  apply Lp.ext
  filter_upwards [wholePlaneHorizontalProjL2_coe_ae (wholePlaneVerticalZeroExtendL2 f),
    wholePlaneVerticalZeroExtendL2_coe_ae f] with x h1 h2
  rw [h1, h2]
  exact horizontalProjPoint_verticalZeroExtendPoint _

/-- Projecting a zero-extended whole-plane `H²` field returns it. -/
@[simp] theorem wholePlaneHorizontalProjH2_wholePlaneVerticalZeroExtendH2
    (h : WholePlaneC2H2) :
    wholePlaneHorizontalProjH2 (wholePlaneVerticalZeroExtendH2 h) = h := by
  apply Subtype.ext
  apply PiLp.ext
  intro q
  rcases q with s | jk
  · rcases s with _ | j
    · exact wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2
        (wholePlaneH2Embedding C2 h)
    · exact wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2
        (wholePlaneH2FirstDerivative C2 j h)
  · exact wholePlaneHorizontalProjL2_wholePlaneVerticalZeroExtendL2
      (wholePlaneH2SecondDerivative C2 jk.1 jk.2 h)

/-- The whole-plane axial zero extension is an `L²` isometry. -/
@[simp] theorem norm_wholePlaneVerticalZeroExtendL2 (f : WholePlaneC2L2) :
    ‖wholePlaneVerticalZeroExtendL2 f‖ = ‖f‖ :=
  norm_fibreL2_apply _ norm_verticalZeroExtendPoint f

/-- The whole-plane horizontal projection is an `L²` contraction. -/
theorem norm_wholePlaneHorizontalProjL2_apply_le (f : WholePlaneC3L2) :
    ‖wholePlaneHorizontalProjL2 f‖ ≤ ‖f‖ :=
  norm_fibreL2_apply_le _ norm_horizontalProjPoint_le f

/-- The `H²` zero extension lies over the `L²` one. -/
theorem wholePlaneH2Embedding_wholePlaneVerticalZeroExtendH2 (h : WholePlaneC2H2) :
    wholePlaneH2Embedding C3 (wholePlaneVerticalZeroExtendH2 h) =
      wholePlaneVerticalZeroExtendL2 (wholePlaneH2Embedding C2 h) :=
  rfl

/-- The `H²` horizontal projection lies over the `L²` one. -/
theorem wholePlaneH2Embedding_wholePlaneHorizontalProjH2 (b : WholePlaneC3H2) :
    wholePlaneH2Embedding C2 (wholePlaneHorizontalProjH2 b) =
      wholePlaneHorizontalProjL2 (wholePlaneH2Embedding C3 b) :=
  rfl

/-- The `H²` horizontal projection commutes with each stored first weak derivative. -/
theorem wholePlaneH2FirstDerivative_wholePlaneHorizontalProjH2
    (j : Fin 2) (b : WholePlaneC3H2) :
    wholePlaneH2FirstDerivative C2 j (wholePlaneHorizontalProjH2 b) =
      wholePlaneHorizontalProjL2 (wholePlaneH2FirstDerivative C3 j b) :=
  rfl

/-- Coordinate extraction after the horizontal projection is coordinate extraction. -/
theorem wholePlaneC2CoordL2_wholePlaneHorizontalProjL2 (j : Fin 2) (f : WholePlaneC3L2) :
    wholePlaneC2CoordL2 j (wholePlaneHorizontalProjL2 f) =
      wholePlaneCoordL2 j.castSucc f := by
  apply Lp.ext
  have h1 := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL
    (p := 2) (μ := (volume : Measure WholePlane)) (wholePlaneHorizontalProjL2 f)
  have h2 := (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL
    (p := 2) (μ := (volume : Measure WholePlane)) f
  filter_upwards [h1, h2, wholePlaneHorizontalProjL2_coe_ae f] with x hx1 hx2 hx3
  rw [show (wholePlaneC2CoordL2 j (wholePlaneHorizontalProjL2 f) : WholePlane → ℂ) x =
    (EuclideanSpace.proj (𝕜 := ℂ) j)
      ((wholePlaneHorizontalProjL2 f : WholePlane → C2) x) from hx1,
    show (wholePlaneCoordL2 j.castSucc f : WholePlane → ℂ) x =
      (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc) ((f : WholePlane → C3) x) from hx2, hx3]
  exact horizontalProjPoint_apply _ j

/-! ## The plane-side quotient identity `π_⊥ ∘ A₃ = A₂ ∘ π_⊥` -/

section Quotient

variable (v : WholePlaneVelocityCoefficients)

/-- The horizontal projection intertwines the two fixed-wavenumber diffusions. -/
theorem wholePlaneHorizontalProjL2_wholePlaneLocalDiffusion (N : ℝ) (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (wholePlaneLocalDiffusion N b) =
      wholePlaneC2LocalDiffusion N (wholePlaneHorizontalProjH2 b) := by
  have hlap : wholePlaneHorizontalProjL2 (wholePlaneLaplacian C3 b) =
      wholePlaneLaplacian C2 (wholePlaneHorizontalProjH2 b) :=
    (wholePlaneLaplacian_fibreH2 horizontalProjPoint b).symm
  rw [wholePlaneLocalDiffusion_apply, wholePlaneC2LocalDiffusion_apply, map_sub, map_smul,
    hlap, wholePlaneH2Embedding_wholePlaneHorizontalProjH2]

/-- The horizontal projection intertwines the two transverse transport terms: the scalar
velocity coefficients are the same, and a scalar multiplier acts diagonally in the fibre. -/
theorem wholePlaneHorizontalProjL2_wholePlaneLocalTransport (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (wholePlaneLocalTransport v b) =
      wholePlaneC2LocalTransport v (wholePlaneHorizontalProjH2 b) := by
  rw [wholePlaneLocalTransport_apply, wholePlaneC2LocalTransport_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show wholePlaneHorizontalProjL2 (scalarVectorMulL2 (E := C3) volume
        (wholePlaneCoordLInf j.castSucc v.value) (wholePlaneH2FirstDerivative C3 j b)) =
      scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf j.castSucc v.value)
        (wholePlaneHorizontalProjL2 (wholePlaneH2FirstDerivative C3 j b)) from
    fibreL2_scalarVectorMulL2 _ _ _,
    wholePlaneH2FirstDerivative_wholePlaneHorizontalProjH2]

/-- The horizontal projection intertwines the two axial transport terms. -/
theorem wholePlaneHorizontalProjL2_wholePlaneLocalAxialTransport (N : ℝ) (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (wholePlaneLocalAxialTransport v N b) =
      wholePlaneC2LocalAxialTransport v N (wholePlaneHorizontalProjH2 b) := by
  rw [wholePlaneLocalAxialTransport_apply, wholePlaneC2LocalAxialTransport_apply, map_smul,
    show wholePlaneHorizontalProjL2 (scalarVectorMulL2 (E := C3) volume
        (wholePlaneCoordLInf (2 : Fin 3) v.value) (wholePlaneH2Embedding C3 b)) =
      scalarVectorMulL2 (E := C2) volume (wholePlaneCoordLInf (2 : Fin 3) v.value)
        (wholePlaneHorizontalProjL2 (wholePlaneH2Embedding C3 b)) from
    fibreL2_scalarVectorMulL2 _ _ _,
    wholePlaneH2Embedding_wholePlaneHorizontalProjH2]

/-- The horizontal projection intertwines the two stretching terms.  This is the only mixing
term: the projection replaces the `ℂ³`-valued coefficient `∂_j v` by its horizontal part
`(∂_j v)_⊥`, which is exactly the coefficient of the two-component operator. -/
theorem wholePlaneHorizontalProjL2_wholePlaneLocalStretching (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (wholePlaneLocalStretching v b) =
      wholePlaneC2LocalStretching v (wholePlaneHorizontalProjH2 b) := by
  rw [wholePlaneLocalStretching_apply, wholePlaneC2LocalStretching_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcoord : wholePlaneCoordL2 j.castSucc (wholePlaneH2Embedding C3 b) =
      wholePlaneC2CoordL2 j
        (wholePlaneH2Embedding C2 (wholePlaneHorizontalProjH2 b)) := by
    rw [wholePlaneH2Embedding_wholePlaneHorizontalProjH2,
      wholePlaneC2CoordL2_wholePlaneHorizontalProjL2]
  have hmul : wholePlaneHorizontalProjL2 (vectorScalarMulL2 (E := C3) volume (v.deriv j)
        (wholePlaneCoordL2 j.castSucc (wholePlaneH2Embedding C3 b))) =
      vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j)
        (wholePlaneCoordL2 j.castSucc (wholePlaneH2Embedding C3 b)) :=
    fibreL2_vectorScalarMulL2 horizontalProjPoint (v.deriv j) _
  refine hmul.trans ?_
  exact congrArg
    (fun x ↦ vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j) x) hcoord

/-- The horizontal projection intertwines the three-component local generator and the
two-component local generator of `eq:local-generator`. -/
theorem wholePlaneHorizontalProjL2_wholePlaneLocalAction
    (delta N : ℝ) (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (wholePlaneLocalAction v delta N b) =
      wholePlaneC2LocalAction v delta N (wholePlaneHorizontalProjH2 b) := by
  have hdiff := wholePlaneHorizontalProjL2_wholePlaneLocalDiffusion N b
  have htransport := wholePlaneHorizontalProjL2_wholePlaneLocalTransport v b
  have haxial := wholePlaneHorizontalProjL2_wholePlaneLocalAxialTransport v N b
  have hstretch := wholePlaneHorizontalProjL2_wholePlaneLocalStretching v b
  change wholePlaneHorizontalProjL2 ((delta : ℂ) • wholePlaneLocalDiffusion N b -
      wholePlaneLocalTransport v b - wholePlaneLocalAxialTransport v N b +
        wholePlaneLocalStretching v b) = _
  simp only [map_add, map_sub, map_smul, hdiff, htransport, haxial, hstretch]
  rfl

/-- The horizontal projection intertwines the constant axial shifts. -/
theorem wholePlaneHorizontalProjL2_selectedWholePlaneAxialShift
    (K : ℤ) (a : ℝ) (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (selectedWholePlaneAxialShift K a b) =
      selectedWholePlaneC2AxialShift K a (wholePlaneHorizontalProjH2 b) := by
  rw [selectedWholePlaneAxialShift_apply, selectedWholePlaneC2AxialShift_apply, map_smul,
    wholePlaneH2Embedding_wholePlaneHorizontalProjH2]

/-- **The plane-side quotient identity.**  The horizontal projection intertwines the
three-component version of the selected whole-plane action of
`eq:selected-whole-plane-operator` with its two-component counterpart (the paper's operator). -/
theorem wholePlaneHorizontalProjL2_selectedWholePlaneInductionAction
    (epsilon : ℝ) (K : ℤ) (a : ℝ) (b : WholePlaneC3H2) :
    wholePlaneHorizontalProjL2 (selectedWholePlaneInductionAction v epsilon K a b) =
      selectedWholePlaneC2InductionAction v epsilon K a (wholePlaneHorizontalProjH2 b) := by
  have haction := wholePlaneHorizontalProjL2_wholePlaneLocalAction v epsilon
    (wholePlaneAxialWavenumber K) b
  have hshift := wholePlaneHorizontalProjL2_selectedWholePlaneAxialShift K a b
  change wholePlaneHorizontalProjL2 (wholePlaneLocalAction v epsilon
      (wholePlaneAxialWavenumber K) b - selectedWholePlaneAxialShift K a b) = _
  rw [map_sub, haction, hshift]
  rfl

end Quotient

end WholePlaneHorizontalFibre

end

end FastDynamo
