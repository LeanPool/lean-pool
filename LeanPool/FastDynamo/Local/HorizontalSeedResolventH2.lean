/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.HorizontalFormStrongIdentification
public import LeanPool.FastDynamo.Local.HorizontalModeContour
public import LeanPool.FastDynamo.Local.HorizontalSmoothedVelocity
public import LeanPool.FastDynamo.Global.WholePlaneScaledLocalResolvent

/-!
# The uniform `L² → H²` resolvent bound on the contour `Γ`

The statement of `prop:local-seed`, with `eq:local-continuation-bound`: *"`Γ ⊂ ρ(𝓛_δ)` for
every `δ ∈ I`, and `sup_{δ∈I, z∈Γ} ‖(z - 𝓛_δ)^{-1}‖_{L² → H¹} < ∞`."*

**Lean proves more than the paper asks.**  The paper's
`eq:local-continuation-bound` is the `L² → H¹` bound; what this module states and proves is the
`L² → H²` bound, of which the paper's is a corollary through `H² ↪ H¹`.  That is not extra
work: the Lean `𝓛_δ` is a
`DomainOperator` with bundled domain `H²(ℝ²; ℂ²)` — the domain identification the paper's
proof of `prop:local-seed` performs too — and `HasResolventOn` stores a domain-valued inverse
`L² → H²`,
so the `H²` operator norm is the only norm available at that type.  Only the `L²` and gradient
halves are ever consumed downstream, which is exactly the `H¹` content.

The `L² → H¹` half is the graph-norm bound of `Local/HorizontalFormResolvent.lean`.  This
module supplies the upgrade to `H²`, in three steps.

1. **Quantitative whole-plane elliptic regularity.**  The pair space
   `{(b₀, lap) ∈ L² × L² : Δ b₀ = lap}` is a closed subspace of `L² × L²`, and
   `h ↦ (h, Δh)` is a continuous linear bijection from `H²(ℝ²; F)` onto it
   (`exists_wholePlaneH2_of_laplacian_eq_l2` is the surjectivity).  Banach's isomorphism
   theorem therefore produces a *bounded* reconstruction map `wholePlaneH2OfPair`, i.e. the
   estimate `‖h‖_{H²} ≤ C(‖h‖₂ + ‖Δ h‖₂)`.  The library has
   no Fourier proof of this inequality; the open-mapping route gives it with no symbol
   calculus at all, at the price of an unspecified constant.
2. **The strong resolvent.**  Given a form resolvent for any form `a` agreeing with
   `𝔩_{w,δ}`, the `H²` field attached to `R_a(z)f` by the domain identification of
   `Local/HorizontalFormStrongIdentification.lean` is `wholePlaneH2OfPair` applied to the pair
   `(j b, δ⁻¹(A b + 𝔡 b))`, a bounded function of `R_a(z)`.  This is a
   `HasResolventOn (horizontalLocalOperator N δ v) S`, `ContinuousOn` included.
3. **The bound.**  On a compact parameter set the composite bound is
   `‖wholePlaneH2OfPair‖ · ‖pair map‖ · sup_{z∈S}‖R_a(z)‖`, which is the shape
   `WholePlaneLocalResolventBound` of `Global/WholePlaneScaledLocalResolvent.lean`.

**Which velocity.**  The strong operator `𝓛_δ` only exists on `H²` for a velocity with an
`L^∞` weak gradient (the stretching term is `(b·∇_⊥)v_⊥`).  The paper's `v = v_h` is
smooth, and `wholePlaneSchwartzVelocityCoefficients (parameterizedSmoothedVelocity h Ω U)`
carries the certificate.  The *jump* reference `V⁰` does **not**: its transverse gradient is a
surface measure.  This is why the bound is proved for `v_h` only, and why
the unperturbed contour data of `Local/HorizontalModeContour.lean` is used here only through
the `V⁰` form operator, never through a strong `V⁰` operator.

## Contents

* `wholePlaneLaplacianPair` and `wholePlaneH2OfPair`.
* `horizontalAssociatedOperator` and `horizontalStrongResolvent`.
* `HorizontalMode.smoothedModeCoefficients` and its weak-gradient certificate
  `HorizontalMode.smoothedModeCoefficients_hasWeakGradient`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

-- The graph domain is a submodule of a product of `Lp` quotients; its normed-space instance
-- is one synthesis step beyond the default pending depth.

/-! ## The `L²` Laplacian pair space -/

section Pair

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The distributional Laplacian on tempered distributions, bundled as a continuous linear
map.  Only the bundling is new; the value is `Laplacian.laplacian`. -/
def wholePlaneTemperedLaplacian :
    TemperedDistribution WholePlane F →L[ℂ] TemperedDistribution WholePlane F :=
  LineDeriv.laplacianCLM ℂ WholePlane (TemperedDistribution WholePlane F)

omit [CompleteSpace F] in
/-- The bundled distributional Laplacian is the distributional Laplacian. -/
@[simp] theorem wholePlaneTemperedLaplacian_apply (T : TemperedDistribution WholePlane F) :
    wholePlaneTemperedLaplacian F T = Laplacian.laplacian T :=
  TemperedDistribution.laplacianCLM_apply T

/-- The map `(b₀, lap) ↦ Δ b₀` on `L² × L²`, valued in tempered distributions. -/
def wholePlaneLaplacianPairLeft :
    (WholePlaneL2 F × WholePlaneL2 F) →L[ℂ] TemperedDistribution WholePlane F :=
  (wholePlaneTemperedLaplacian F).comp
    ((wholePlaneL2ToTempered F).comp
      (ContinuousLinearMap.fst ℂ (WholePlaneL2 F) (WholePlaneL2 F)))

/-- The map `(b₀, lap) ↦ lap` on `L² × L²`, valued in tempered distributions. -/
def wholePlaneLaplacianPairRight :
    (WholePlaneL2 F × WholePlaneL2 F) →L[ℂ] TemperedDistribution WholePlane F :=
  (wholePlaneL2ToTempered F).comp
    (ContinuousLinearMap.snd ℂ (WholePlaneL2 F) (WholePlaneL2 F))

/-- **The `L²` Laplacian pair space** `{(b₀, lap) : Δ b₀ = lap}`.  It is closed because it is
the equaliser of two continuous linear maps into a Hausdorff space of distributions. -/
def wholePlaneLaplacianPair : Submodule ℂ (WholePlaneL2 F × WholePlaneL2 F) :=
  (wholePlaneLaplacianPairLeft F).toLinearMap.eqLocus
    (wholePlaneLaplacianPairRight F).toLinearMap

/-- The pair space is a closed subspace of `L² × L²`, hence a Banach space. -/
instance wholePlaneLaplacianPairCompleteSpace :
    CompleteSpace (wholePlaneLaplacianPair F) :=
  ContinuousLinearMap.completeSpace_eqLocus _ _

/-- Membership in the pair space is the distributional Laplacian identity. -/
theorem mem_wholePlaneLaplacianPair_iff (p : WholePlaneL2 F × WholePlaneL2 F) :
    p ∈ wholePlaneLaplacianPair F ↔
      Laplacian.laplacian (wholePlaneL2ToTempered F p.1) = wholePlaneL2ToTempered F p.2 := by
  rw [wholePlaneLaplacianPair, LinearMap.mem_eqLocus]
  constructor
  · intro h
    have h' : wholePlaneLaplacianPairLeft F p = wholePlaneLaplacianPairRight F p := h
    rw [wholePlaneLaplacianPairLeft, wholePlaneLaplacianPairRight] at h'
    simpa using h'
  · intro h
    change wholePlaneLaplacianPairLeft F p = wholePlaneLaplacianPairRight F p
    rw [wholePlaneLaplacianPairLeft, wholePlaneLaplacianPairRight]
    simpa using h

/-- The value-and-Laplacian pair of an `H²` field. -/
def wholePlaneH2PairFun : WholePlaneH2 F →L[ℂ] (WholePlaneL2 F × WholePlaneL2 F) :=
  (wholePlaneH2Embedding F).prod (wholePlaneLaplacian F)

/-- Value of the value-and-Laplacian pair. -/
@[simp] theorem wholePlaneH2PairFun_apply (h : WholePlaneH2 F) :
    wholePlaneH2PairFun F h = (wholePlaneH2Embedding F h, wholePlaneLaplacian F h) := rfl

/-- The value-and-Laplacian pair of an `H²` field lies in the pair space. -/
theorem wholePlaneH2PairFun_mem (h : WholePlaneH2 F) :
    wholePlaneH2PairFun F h ∈ wholePlaneLaplacianPair F := by
  rw [mem_wholePlaneLaplacianPair_iff, wholePlaneH2PairFun_apply]
  exact (wholePlaneLaplacian_toTempered F h).symm

/-- The value-and-Laplacian pair, corestricted to the pair space. -/
def wholePlaneH2ToPair : WholePlaneH2 F →L[ℂ] wholePlaneLaplacianPair F :=
  (wholePlaneH2PairFun F).codRestrict (wholePlaneLaplacianPair F) (wholePlaneH2PairFun_mem F)

/-- Value of the corestricted pair map. -/
@[simp] theorem wholePlaneH2ToPair_coe (h : WholePlaneH2 F) :
    ((wholePlaneH2ToPair F h : wholePlaneLaplacianPair F) :
        WholePlaneL2 F × WholePlaneL2 F) =
      (wholePlaneH2Embedding F h, wholePlaneLaplacian F h) := rfl

/-- The pair map is injective: an `H²` field is determined by its `L²` value. -/
theorem wholePlaneH2ToPair_injective : Function.Injective (wholePlaneH2ToPair F) := by
  intro x y hxy
  apply wholePlaneH2Embedding_injective F
  have h := congrArg (fun q : wholePlaneLaplacianPair F =>
    (q : WholePlaneL2 F × WholePlaneL2 F).1) hxy
  exact h

/-- The pair map is surjective: this is whole-plane elliptic regularity
(`exists_wholePlaneH2_of_laplacian_eq_l2`). -/
theorem wholePlaneH2ToPair_surjective : Function.Surjective (wholePlaneH2ToPair F) := by
  rintro ⟨p, hp⟩
  rw [mem_wholePlaneLaplacianPair_iff] at hp
  obtain ⟨h, hemb, hlap⟩ := exists_wholePlaneH2_of_laplacian_eq_l2 F p.1 p.2 hp
  refine ⟨h, ?_⟩
  apply Subtype.ext
  rw [wholePlaneH2ToPair_coe, hemb, hlap]

/-- **Banach's isomorphism theorem for the `H²` graph.**  `h ↦ (h, Δ h)` is a continuous linear
isomorphism from `H²(ℝ²; F)` onto the `L²` Laplacian pair space. -/
def wholePlaneH2PairEquiv : WholePlaneH2 F ≃L[ℂ] wholePlaneLaplacianPair F :=
  ContinuousLinearEquiv.ofBijective (wholePlaneH2ToPair F)
    (LinearMap.ker_eq_bot.mpr (wholePlaneH2ToPair_injective F))
    (LinearMap.range_eq_top.mpr (wholePlaneH2ToPair_surjective F))

/-- **The bounded `H²` reconstruction map.**  An `L²` field together with an `L²` distributional
Laplacian determines an `H²` field, boundedly. -/
def wholePlaneH2OfPair : wholePlaneLaplacianPair F →L[ℂ] WholePlaneH2 F :=
  (wholePlaneH2PairEquiv F).symm.toContinuousLinearMap

/-- The reconstruction map inverts the pair map. -/
@[simp] theorem wholePlaneH2OfPair_wholePlaneH2ToPair (h : WholePlaneH2 F) :
    wholePlaneH2OfPair F (wholePlaneH2ToPair F h) = h :=
  (wholePlaneH2PairEquiv F).symm_apply_apply h

/-- The `L²` value of a reconstructed `H²` field is the first component of the pair. -/
theorem wholePlaneH2Embedding_wholePlaneH2OfPair (p : wholePlaneLaplacianPair F) :
    wholePlaneH2Embedding F (wholePlaneH2OfPair F p) =
      (p : WholePlaneL2 F × WholePlaneL2 F).1 := by
  have h : wholePlaneH2ToPair F (wholePlaneH2OfPair F p) = p :=
    (wholePlaneH2PairEquiv F).apply_symm_apply p
  have h1 := congrArg (fun q : wholePlaneLaplacianPair F =>
    (q : WholePlaneL2 F × WholePlaneL2 F).1) h
  exact h1

end Pair

/-! ## Post-composition and corestriction of operator families -/

section OperatorFamilies

variable {M E G : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Post-composition with the inclusion undoes a corestriction. -/
theorem subtypeL_comp_codRestrict (p : Submodule ℂ E) (f : M →L[ℂ] E) (h : ∀ x, f x ∈ p) :
    p.subtypeL.comp (f.codRestrict p h) = f :=
  ContinuousLinearMap.ext fun _ => rfl

/-- Post-composition with a fixed bounded operator preserves continuity of an operator
family. -/
theorem continuousOn_comp_left (A : E →L[ℂ] G) {S : Set ℂ} {T : ℂ → (M →L[ℂ] E)}
    (hT : ContinuousOn T S) : ContinuousOn (fun z => A.comp (T z)) S :=
  (ContinuousLinearMap.compL ℂ M E G A).continuous.comp_continuousOn hT

/-- A corestricted operator family is continuous as soon as the family itself is. -/
theorem continuousOn_codRestrict (p : Submodule ℂ E) {S : Set ℂ} {T : ℂ → (M →L[ℂ] E)}
    (h : ∀ z, ∀ x, T z x ∈ p) (hT : ContinuousOn T S) :
    ContinuousOn (fun z => (T z).codRestrict p (h z)) S := by
  rw [← (isometry_subtypeL_comp (M := M) p).comp_continuousOn_iff]
  refine hT.congr fun z _ => ?_
  exact (subtypeL_comp_codRestrict p (T z) (h z)).symm

end OperatorFamilies

/-! ## The strong resolvent attached to a form resolvent -/

namespace HorizontalWeakForm

/-- The `L²` operator associated with an arbitrary sesquilinear form on `H¹(ℝ²; ℂ²)`.  Both
`horizontalFormOperator N w` and `horizontalFormDeltaOperator N δ w` are instances of it, so
stating the construction here avoids a spurious distinction between the two graph domains. -/
def horizontalAssociatedOperator (a : ComplexForm WholePlaneC2H1) :
    DomainOperator WholePlaneC2L2 (AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :=
  associatedFormProdOperator (wholePlaneH1Embedding C2) wholePlaneC2H1Embedding_injective
    denseRange_wholePlaneC2H1Embedding a

/-- The `H¹` coordinate of a graph element, as a bounded map. -/
def formProdFst (a : ComplexForm WholePlaneC2H1) :
    AssociatedFormProdDomain (wholePlaneH1Embedding C2) a →L[ℂ] WholePlaneC2H1 :=
  (ContinuousLinearMap.fst ℂ WholePlaneC2H1 WholePlaneC2L2).comp
    (AssociatedFormProdDomain (wholePlaneH1Embedding C2) a).subtypeL

/-- Value of the `H¹` coordinate map. -/
@[simp] theorem formProdFst_apply (a : ComplexForm WholePlaneC2H1)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) : formProdFst a u = u.1.1 := rfl

variable (N delta : ℝ) (v : WholePlaneVelocityCoefficients) (a : ComplexForm WholePlaneC2H1)

/-- Every graph element of a form agreeing with `𝔩_{w,δ}` solves the weak seed equation. -/
theorem horizontalAssociatedDomain_weakDelta
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) (phi : WholePlaneC2H1) :
    horizontalWeakFormDelta N delta v.value u.1.1 phi =
      -inner ℂ (wholePlaneH1Embedding C2 phi) ((horizontalAssociatedOperator a).op u) := by
  have hop : (horizontalAssociatedOperator a).op u = -u.1.2 :=
    associatedFormProdOperator_op_apply (wholePlaneH1Embedding C2)
      wholePlaneC2H1Embedding_injective denseRange_wholePlaneC2H1Embedding a u
  calc horizontalWeakFormDelta N delta v.value u.1.1 phi
      = a u.1.1 phi := (hform u.1.1 phi).symm
    _ = inner ℂ (wholePlaneH1Embedding C2 phi) u.1.2 :=
        associatedFormProdDomain_relation_apply (wholePlaneH1Embedding C2) a u phi
    _ = -inner ℂ (wholePlaneH1Embedding C2 phi) (-u.1.2) := by
        simp only [inner_neg_right, neg_neg]
    _ = -inner ℂ (wholePlaneH1Embedding C2 phi) ((horizontalAssociatedOperator a).op u) :=
        congrArg (fun t => -inner ℂ (wholePlaneH1Embedding C2 phi) t) hop.symm

/-- Every `H²` field carries a graph element of any form agreeing with `𝔩_{w,δ}`. -/
theorem exists_horizontalAssociatedDomain_of_wholePlaneC2H2 (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (h : WholePlaneC2H2) :
    ∃ u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a,
      u.1.1 = wholePlaneC2H2ToH1 h ∧
        (horizontalAssociatedOperator a).op u = wholePlaneC2LocalAction v delta N h := by
  refine ⟨⟨(wholePlaneC2H2ToH1 h, -(wholePlaneC2LocalAction v delta N h)), ?_⟩, rfl, ?_⟩
  · rw [mem_associatedFormProdDomain_iff_forall]
    intro phi
    calc a (wholePlaneC2H2ToH1 h) phi
        = horizontalWeakFormDelta N delta v.value (wholePlaneC2H2ToH1 h) phi :=
          hform (wholePlaneC2H2ToH1 h) phi
      _ = -inner ℂ (wholePlaneH1Embedding C2 phi) (wholePlaneC2LocalAction v delta N h) :=
          horizontalWeakFormDelta_h2ToH1_eq N delta v hv h phi
      _ = inner ℂ (wholePlaneH1Embedding C2 phi)
            (-(wholePlaneC2LocalAction v delta N h)) := by rw [inner_neg_right]
  · change -(-(wholePlaneC2LocalAction v delta N h)) = wholePlaneC2LocalAction v delta N h
    rw [neg_neg]

/-- The `L² × L²` pair `(j b, δ⁻¹(A b + 𝔡 b))` attached to a graph element: its first entry is
the `L²` value of the solution, its second the `L²` field representing `Δ_⊥ b`. -/
def horizontalStrongPairMap :
    AssociatedFormProdDomain (wholePlaneH1Embedding C2) a →L[ℂ]
      (WholePlaneC2L2 × WholePlaneC2L2) :=
  ((wholePlaneH1Embedding C2).comp (formProdFst a)).prod
    (((delta : ℂ)⁻¹) • ((horizontalAssociatedOperator a).op +
      (horizontalLaplacianDatum N delta v).comp (formProdFst a)))

/-- Value of the pair map. -/
@[simp] theorem horizontalStrongPairMap_apply
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    horizontalStrongPairMap N delta v a u =
      (wholePlaneH1Embedding C2 u.1.1,
        ((delta : ℂ)⁻¹) • ((horizontalAssociatedOperator a).op u +
          horizontalLaplacianDatum N delta v u.1.1)) := rfl

/-- The pair attached to a graph element lies in the `L²` Laplacian pair space. -/
theorem horizontalStrongPairMap_mem (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    horizontalStrongPairMap N delta v a u ∈ wholePlaneLaplacianPair C2 := by
  rw [mem_wholePlaneLaplacianPair_iff]
  exact laplacian_toTempered_of_horizontalWeak N delta hdelta v hv u.1.1
    ((horizontalAssociatedOperator a).op u)
    (horizontalAssociatedDomain_weakDelta N delta v a hform u)

variable {S : Set ℂ}

/-- The `H²` field attached to a graph element by the domain identification. -/
def horizontalStrongLift (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) : WholePlaneC2H2 :=
  wholePlaneH2OfPair C2 ⟨horizontalStrongPairMap N delta v a u,
    horizontalStrongPairMap_mem N delta v a hdelta hv hform u⟩

/-- The lifted field has the `L²` value of the graph element. -/
theorem wholePlaneH2Embedding_horizontalStrongLift (hdelta : delta ≠ 0)
    (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    wholePlaneH2Embedding C2 (horizontalStrongLift N delta v a hdelta hv hform u) =
      wholePlaneH1Embedding C2 u.1.1 :=
  wholePlaneH2Embedding_wholePlaneH2OfPair C2 _

/-- The lifted field solves the strong equation of the graph element. -/
theorem horizontalStrongLift_action (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (u : AssociatedFormProdDomain (wholePlaneH1Embedding C2) a) :
    wholePlaneC2LocalAction v delta N (horizontalStrongLift N delta v a hdelta hv hform u) =
      (horizontalAssociatedOperator a).op u := by
  have hex : ∃ h : WholePlaneC2H2, wholePlaneC2H2ToH1 h = u.1.1 ∧
      wholePlaneC2LocalAction v delta N h = (horizontalAssociatedOperator a).op u :=
    exists_wholePlaneC2H2_of_horizontalWeak N delta hdelta v hv u.1.1
      ((horizontalAssociatedOperator a).op u)
      (horizontalAssociatedDomain_weakDelta N delta v a hform u)
  obtain ⟨h, htrace, haction⟩ := hex
  have heq : horizontalStrongLift N delta v a hdelta hv hform u = h := by
    apply wholePlaneH2Embedding_injective C2
    calc wholePlaneH2Embedding C2 (horizontalStrongLift N delta v a hdelta hv hform u)
        = wholePlaneH1Embedding C2 u.1.1 :=
          wholePlaneH2Embedding_horizontalStrongLift N delta v a hdelta hv hform u
      _ = wholePlaneH1Embedding C2 (wholePlaneC2H2ToH1 h) :=
          congrArg (fun t => wholePlaneH1Embedding C2 t) htrace.symm
      _ = wholePlaneH2Embedding C2 h := by rw [wholePlaneH1Embedding_H2ToH1]
  exact (congrArg (fun t => wholePlaneC2LocalAction v delta N t) heq).trans haction

/-- The `L² → H²` resolvent family, before composing with the reconstruction map. -/
def horizontalStrongPairCod (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) (z : ℂ) :
    WholePlaneC2L2 →L[ℂ] wholePlaneLaplacianPair C2 :=
  ((horizontalStrongPairMap N delta v a).comp (hres.inv z)).codRestrict
    (wholePlaneLaplacianPair C2)
    (fun f => horizontalStrongPairMap_mem N delta v a hdelta hv hform (hres.inv z f))

/-- The corestricted pair family has the norm of the uncorestricted one. -/
theorem norm_horizontalStrongPairCod (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) (z : ℂ) :
    ‖horizontalStrongPairCod N delta v a hdelta hv hform hres z‖ =
      ‖(horizontalStrongPairMap N delta v a).comp (hres.inv z)‖ := by
  have h1 : (wholePlaneLaplacianPair C2).subtypeL.comp
      (horizontalStrongPairCod N delta v a hdelta hv hform hres z) =
      (horizontalStrongPairMap N delta v a).comp (hres.inv z) :=
    subtypeL_comp_codRestrict (wholePlaneLaplacianPair C2)
      ((horizontalStrongPairMap N delta v a).comp (hres.inv z))
      (fun f => horizontalStrongPairMap_mem N delta v a hdelta hv hform (hres.inv z f))
  calc ‖horizontalStrongPairCod N delta v a hdelta hv hform hres z‖
      = ‖(wholePlaneLaplacianPair C2).subtypeL.comp
          (horizontalStrongPairCod N delta v a hdelta hv hform hres z)‖ :=
        (norm_subtypeL_comp (wholePlaneLaplacianPair C2)
          (horizontalStrongPairCod N delta v a hdelta hv hform hres z)).symm
    _ = ‖(horizontalStrongPairMap N delta v a).comp (hres.inv z)‖ :=
        congrArg (fun T => ‖T‖) h1

/-- The candidate `L² → H²` resolvent family. -/
def horizontalStrongInv (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) (z : ℂ) :
    WholePlaneC2L2 →L[ℂ] WholePlaneC2H2 :=
  (wholePlaneH2OfPair C2).comp (horizontalStrongPairCod N delta v a hdelta hv hform hres z)

/-- The candidate resolvent is a right inverse of the strong pencil. -/
theorem horizontalStrongInv_right (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) {z : ℂ} (hz : z ∈ S)
    (f : WholePlaneC2L2) :
    (horizontalLocalOperator N delta v).pencil z
        (horizontalStrongInv N delta v a hdelta hv hform hres z f) = f := by
  have hr : (horizontalAssociatedOperator a).pencil z (hres.inv z f) = f :=
    congrArg (fun T => T f) (hres.right_inv z hz)
  have h1 : wholePlaneH2Embedding C2
        (horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)) =
      wholePlaneH1Embedding C2 (hres.inv z f).1.1 :=
    wholePlaneH2Embedding_horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)
  have h2 : wholePlaneC2LocalAction v delta N
        (horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)) =
      (horizontalAssociatedOperator a).op (hres.inv z f) :=
    horizontalStrongLift_action N delta v a hdelta hv hform (hres.inv z f)
  calc (horizontalLocalOperator N delta v).pencil z
        (horizontalStrongInv N delta v a hdelta hv hform hres z f)
      = z • wholePlaneH2Embedding C2
            (horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)) -
          wholePlaneC2LocalAction v delta N
            (horizontalStrongLift N delta v a hdelta hv hform (hres.inv z f)) := rfl
    _ = z • wholePlaneH1Embedding C2 (hres.inv z f).1.1 -
          (horizontalAssociatedOperator a).op (hres.inv z f) :=
        congrArg₂ (fun x y => z • x - y) h1 h2
    _ = (horizontalAssociatedOperator a).pencil z (hres.inv z f) := rfl
    _ = f := hr

/-- The candidate resolvent is a left inverse of the strong pencil. -/
theorem horizontalStrongInv_left (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) {z : ℂ} (hz : z ∈ S)
    (h : WholePlaneC2H2) :
    horizontalStrongInv N delta v a hdelta hv hform hres z
        ((horizontalLocalOperator N delta v).pencil z h) = h := by
  obtain ⟨u, hu1, hu2⟩ :=
    exists_horizontalAssociatedDomain_of_wholePlaneC2H2 N delta v a hv hform h
  have hpencil : (horizontalAssociatedOperator a).pencil z u =
      (horizontalLocalOperator N delta v).pencil z h := by
    calc (horizontalAssociatedOperator a).pencil z u
        = z • wholePlaneH1Embedding C2 u.1.1 - (horizontalAssociatedOperator a).op u := rfl
      _ = z • wholePlaneH1Embedding C2 (wholePlaneC2H2ToH1 h) -
            wholePlaneC2LocalAction v delta N h :=
          congrArg₂ (fun x y => z • wholePlaneH1Embedding C2 x - y) hu1 hu2
      _ = z • wholePlaneH2Embedding C2 h - wholePlaneC2LocalAction v delta N h := by
          rw [wholePlaneH1Embedding_H2ToH1]
      _ = (horizontalLocalOperator N delta v).pencil z h := rfl
  have hinv0 : hres.inv z ((horizontalAssociatedOperator a).pencil z u) = u :=
    congrArg (fun T => T u) (hres.left_inv z hz)
  have hinv : hres.inv z ((horizontalLocalOperator N delta v).pencil z h) = u :=
    (congrArg (fun t => hres.inv z t) hpencil).symm.trans hinv0
  apply wholePlaneH2Embedding_injective C2
  calc wholePlaneH2Embedding C2 (horizontalStrongInv N delta v a hdelta hv hform hres z
          ((horizontalLocalOperator N delta v).pencil z h))
      = wholePlaneH2Embedding C2 (horizontalStrongLift N delta v a hdelta hv hform
          (hres.inv z ((horizontalLocalOperator N delta v).pencil z h))) := rfl
    _ = wholePlaneH2Embedding C2 (horizontalStrongLift N delta v a hdelta hv hform u) :=
        congrArg (fun t => wholePlaneH2Embedding C2
          (horizontalStrongLift N delta v a hdelta hv hform t)) hinv
    _ = wholePlaneH1Embedding C2 u.1.1 :=
        wholePlaneH2Embedding_horizontalStrongLift N delta v a hdelta hv hform u
    _ = wholePlaneH1Embedding C2 (wholePlaneC2H2ToH1 h) :=
        congrArg (fun t => wholePlaneH1Embedding C2 t) hu1
    _ = wholePlaneH2Embedding C2 h := by rw [wholePlaneH1Embedding_H2ToH1]

/-- The candidate resolvent family is continuous on the parameter set. -/
theorem continuousOn_horizontalStrongInv (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) :
    ContinuousOn (horizontalStrongInv N delta v a hdelta hv hform hres) S := by
  have h1 : ContinuousOn
      (fun z : ℂ => (horizontalStrongPairMap N delta v a).comp (hres.inv z)) S :=
    continuousOn_comp_left (M := WholePlaneC2L2) (horizontalStrongPairMap N delta v a)
      hres.continuousOn
  have h2 : ContinuousOn
      (fun z : ℂ => horizontalStrongPairCod N delta v a hdelta hv hform hres z) S :=
    continuousOn_codRestrict (wholePlaneLaplacianPair C2) _ h1
  exact continuousOn_comp_left (wholePlaneH2OfPair C2) h2

/--
**The strong resolvent.**  A form resolvent of any form agreeing with `𝔩_{w,δ}` induces an
`L² → H²` resolvent of the strong local generator `𝓛_δ` on the same parameter set.
This is the domain identification in the proof of `prop:local-seed`.
-/
def horizontalStrongResolvent (hdelta : delta ≠ 0) (hv : v.HasWeakGradient)
    (hform : ∀ b phi : WholePlaneC2H1,
      a b phi = horizontalWeakFormDelta N delta v.value b phi)
    (hres : HasResolventOn (horizontalAssociatedOperator a) S) :
    HasResolventOn (horizontalLocalOperator N delta v) S where
  inv := horizontalStrongInv N delta v a hdelta hv hform hres
  left_inv := fun _ hz => ContinuousLinearMap.ext fun h =>
    horizontalStrongInv_left N delta v a hdelta hv hform hres hz h
  right_inv := fun _ hz => ContinuousLinearMap.ext fun f =>
    horizontalStrongInv_right N delta v a hdelta hv hform hres hz f
  continuousOn := continuousOn_horizontalStrongInv N delta v a hdelta hv hform hres

end HorizontalWeakForm

/-! ## The seed contour: the conditional statement consumed by the Riesz-perturbation step -/

namespace HorizontalMode

open HorizontalWeakForm PonomarenkoFreeOmegaInterface

/-- The velocity coefficients of the smoothed seed velocity `v_h`.  Unlike the jump reference
`V⁰`, this velocity is smooth and therefore admits the `L^∞` weak gradient that the strong
generator `𝓛_δ` needs. -/
def smoothedModeCoefficients (N Omega : ℝ) (h : PonomarenkoSmoothingWidth) :
    WholePlaneVelocityCoefficients :=
  wholePlaneSchwartzVelocityCoefficients
    (parameterizedSmoothedVelocity h Omega (jumpAxialSpeed N Omega))

/-- The smoothed seed coefficients carry the paper's velocity `v_h`. -/
@[simp] theorem smoothedModeCoefficients_value (N Omega : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    (smoothedModeCoefficients N Omega h).value = horizontalSmoothedModeVelocity N Omega h := rfl

/-- The smoothed seed coefficients have an `L^∞` weak gradient. -/
theorem smoothedModeCoefficients_hasWeakGradient (N Omega : ℝ)
    (h : PonomarenkoSmoothingWidth) :
    (smoothedModeCoefficients N Omega h).HasWeakGradient :=
  parameterizedSmoothedVelocity_coefficients_hasWeakGradient h Omega (jumpAxialSpeed N Omega)

end HorizontalMode

end

end FastDynamo
