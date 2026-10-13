/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifiedDecorrelation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# StationaryCarrierTransport

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Transporting the stationary potential projection along an equivariant factor map

Two stationary carriers can present *the same* random field.  In this
repository the fresh-shell forcing is read both on CoarseGraining's
regular-field carrier `RegCoeffField d` — where the frozen assumption (J4)
states the corrector energy — and on the continuous-path carrier `C(Vec d, Mat
d)` — where the corrector limit `l.corrector.limit` is proved, because that
carrier alone supports the joint measurability of the translation action.  The
two stationary `L²` layers sit over different `σ`-algebras, so the two
canonical Helmholtz correctors are *a priori* unrelated.

This file supplies the missing comparison in complete generality.  Let
`Φ : Ω₂ → Ω₁` be measurable, equivariant for the two real translation actions,
and push the second law forward to the first.  Write

* `carrierTransport E hΦ : L²(Ω₁) →L L²(Ω₂)` for the Koopman isometry `u ↦ u ∘ Φ`;
* `carrierTransportAdj E hΦ` for its Hilbert adjoint.

Both maps intertwine the two Koopman families — the transport by construction,
its adjoint by taking adjoints in the intertwining relation and using the proved
Koopman adjoint identity `inner_koopman_left` of
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`.
Consequently **both** map horizontal gradients to
horizontal gradients, hence both map stationary potential subspace into
stationary potential subspace (`mem_stationaryPotentialSubspace_carrierTransport`
and `mem_stationaryPotentialSubspace_carrierTransportAdj`).  That two-sided
invariance is exactly what makes the two orthogonal projections correspond:

`stationaryPotentialProjection (carrierTransport F) = carrierTransport
  (stationaryPotentialProjection F)`,

and therefore the two projected energies agree
(`norm_stationaryPotentialProjection_carrierTransport`).

**No** identification of the two `σ`-algebras is used, and the transport is not
assumed surjective: the adjoint direction replaces both.

## Main results

* `hasHorizontalGradient_of_intertwine` — a bounded pair of maps intertwining the
  translation actions and compatible with coordinates carries horizontal
  gradients to horizontal gradients.
* `stationaryPotentialProjection_carrierTransport` — the projections correspond.
* `norm_stationaryPotentialProjection_carrierTransport` — the projected energies
  agree.

**Disclosure.**  Nothing in this file realizes any source node: it is a
Hilbert-space comparison of two carrier presentations of one stationary field.
It consumes only Mathlib, `Algsuperdiff.Probability.StationaryProjection` and the
Koopman algebra of `MollifiedDecorrelation.lean`.
No draft theorem, in particular not `Frozen.External.calderon_zygmund`, is used.
-/

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Probability.Stationary

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### Intertwining maps preserve horizontal gradients -/

section Intertwine

variable {d : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'}
variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
  [VAddInvariantMeasure (Vec d) Ω μ]
variable [AddAction (Vec d) Ω'] [MeasurableConstVAdd (Vec d) Ω']
  [VAddInvariantMeasure (Vec d) Ω' ν]

/-- A bounded pair of maps that intertwines the two translation actions and is
compatible with taking coordinates carries horizontal gradients to horizontal
gradients. -/
theorem hasHorizontalGradient_of_intertwine
    {Sscal : ScalarL2 μ →L[ℝ] ScalarL2 ν} {Svec : VectorL2 d μ →L[ℝ] VectorL2 d ν}
    (hcomm : ∀ (x : Vec d) (φ : ScalarL2 μ),
      Sscal (koopman (μ := μ) (d := d) x φ) = koopman (μ := ν) (d := d) x (Sscal φ))
    (hcoord : ∀ (i : Fin d) (F : VectorL2 d μ),
      vectorL2Coord (μ := ν) i (Svec F) = Sscal (vectorL2Coord (μ := μ) i F))
    {φ : ScalarL2 μ} {F : VectorL2 d μ}
    (hφ : HasHorizontalGradient (μ := μ) φ F) :
    HasHorizontalGradient (μ := ν) (Sscal φ) (Svec F) := by
  intro i
  rw [hcoord i F]
  have hcomp : (fun t : ℝ ↦ koopman (μ := ν) (d := d) (t • (Pi.single i 1 : Vec d)) (Sscal φ))
      = fun t : ℝ ↦ Sscal (koopman (μ := μ) (d := d) (t • (Pi.single i 1 : Vec d)) φ) := by
    funext t
    exact (hcomm _ φ).symm
  rw [hcomp]
  exact (Sscal.hasFDerivAt (x := koopman (μ := μ) (d := d)
    ((0 : ℝ) • (Pi.single i 1 : Vec d)) φ)).comp_hasDerivAt 0 (hφ i)

theorem mem_horizontalGradientRange_of_intertwine
    {Sscal : ScalarL2 μ →L[ℝ] ScalarL2 ν} {Svec : VectorL2 d μ →L[ℝ] VectorL2 d ν}
    (hcomm : ∀ (x : Vec d) (φ : ScalarL2 μ),
      Sscal (koopman (μ := μ) (d := d) x φ) = koopman (μ := ν) (d := d) x (Sscal φ))
    (hcoord : ∀ (i : Fin d) (F : VectorL2 d μ),
      vectorL2Coord (μ := ν) i (Svec F) = Sscal (vectorL2Coord (μ := μ) i F))
    {F : VectorL2 d μ} (hF : F ∈ horizontalGradientRange (μ := μ) (d := d)) :
    Svec F ∈ horizontalGradientRange (μ := ν) (d := d) := by
  obtain ⟨φ, hφ⟩ := hF
  exact ⟨Sscal φ, hasHorizontalGradient_of_intertwine hcomm hcoord hφ⟩

theorem mem_stationaryPotentialSubspace_of_intertwine
    {Sscal : ScalarL2 μ →L[ℝ] ScalarL2 ν} {Svec : VectorL2 d μ →L[ℝ] VectorL2 d ν}
    (hcomm : ∀ (x : Vec d) (φ : ScalarL2 μ),
      Sscal (koopman (μ := μ) (d := d) x φ) = koopman (μ := ν) (d := d) x (Sscal φ))
    (hcoord : ∀ (i : Fin d) (F : VectorL2 d μ),
      vectorL2Coord (μ := ν) i (Svec F) = Sscal (vectorL2Coord (μ := μ) i F))
    {F : VectorL2 d μ} (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    Svec F ∈ stationaryPotentialSubspace (μ := ν) (d := d) := by
  have hsub : horizontalGradientRange (μ := μ) (d := d) ≤
      Submodule.comap (Svec : VectorL2 d μ →ₗ[ℝ] VectorL2 d ν)
        (stationaryPotentialSubspace (μ := ν) (d := d)) := by
    intro G hG
    exact Submodule.le_topologicalClosure _
      (mem_horizontalGradientRange_of_intertwine hcomm hcoord hG)
  have hclosed : IsClosed
      ((Submodule.comap (Svec : VectorL2 d μ →ₗ[ℝ] VectorL2 d ν)
        (stationaryPotentialSubspace (μ := ν) (d := d))) : Set (VectorL2 d μ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage Svec.continuous
  exact Submodule.topologicalClosure_minimal _ hsub hclosed hF

end Intertwine

/-! ### The transport along an equivariant factor map, and its adjoint -/

section Transport

variable {d : ℕ} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
variable [AddAction (Vec d) Ω₁] [MeasurableConstVAdd (Vec d) Ω₁]
  [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
variable [AddAction (Vec d) Ω₂] [MeasurableConstVAdd (Vec d) Ω₂]
  [VAddInvariantMeasure (Vec d) Ω₂ μ₂]

section Defs

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Transport of the stationary `L²` layer along a measure-preserving map:
`u ↦ u ∘ Φ`. -/
def carrierTransport {Φ : Ω₂ → Ω₁} (hΦ : MeasurePreserving Φ μ₂ μ₁) :
    Lp E 2 μ₁ →L[ℝ] Lp E 2 μ₂ :=
  (Lp.compMeasurePreservingₗᵢ ℝ Φ hΦ).toContinuousLinearMap

/-- The Hilbert adjoint of the transport. -/
def carrierTransportAdj [CompleteSpace E] {Φ : Ω₂ → Ω₁}
    (hΦ : MeasurePreserving Φ μ₂ μ₁) :
    Lp E 2 μ₂ →L[ℝ] Lp E 2 μ₁ :=
  ContinuousLinearMap.adjoint (carrierTransport E hΦ)

end Defs

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {Φ : Ω₂ → Ω₁}

theorem coeFn_carrierTransport (hΦ : MeasurePreserving Φ μ₂ μ₁) (g : Lp E 2 μ₁) :
    carrierTransport E hΦ g =ᵐ[μ₂] g ∘ Φ :=
  Lp.coeFn_compMeasurePreserving g hΦ

theorem norm_carrierTransport (hΦ : MeasurePreserving Φ μ₂ μ₁) (g : Lp E 2 μ₁) :
    ‖carrierTransport E hΦ g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g hΦ

/-- The defining adjunction. -/
theorem inner_carrierTransportAdj_left [CompleteSpace E]
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (w : Lp E 2 μ₂) (v : Lp E 2 μ₁) :
    (inner ℝ (carrierTransportAdj E hΦ w) v : ℝ)
      = inner ℝ w (carrierTransport E hΦ v) :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Transport commutes with the pointwise action of a continuous linear map. -/
theorem carrierTransport_compLpL (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (L : E →L[ℝ] F) (g : Lp E 2 μ₁) :
    carrierTransport F hΦ (L.compLpL 2 μ₁ g) = L.compLpL 2 μ₂ (carrierTransport E hΦ g) := by
  have h₁ : (carrierTransport F hΦ (L.compLpL 2 μ₁ g) : Ω₂ → F)
      =ᵐ[μ₂] fun ω ↦ L ((g : Ω₁ → E) (Φ ω)) := by
    refine (coeFn_carrierTransport hΦ (L.compLpL 2 μ₁ g)).trans ?_
    have h := ContinuousLinearMap.coeFn_compLpL (μ := μ₁) (p := 2) L g
    exact h.comp_tendsto hΦ.quasiMeasurePreserving.tendsto_ae
  have h₂ : (L.compLpL 2 μ₂ (carrierTransport E hΦ g) : Ω₂ → F)
      =ᵐ[μ₂] fun ω ↦ L ((g : Ω₁ → E) (Φ ω)) := by
    refine (ContinuousLinearMap.coeFn_compLpL (μ := μ₂) (p := 2) L
      (carrierTransport E hΦ g)).trans ?_
    filter_upwards [coeFn_carrierTransport hΦ g] with ω hω
    exact congrArg L hω
  exact Lp.ext (h₁.trans h₂.symm)

/-- Pointwise application of a continuous linear map is adjoint to pointwise
application of its adjoint. -/
theorem inner_compLpL_left [CompleteSpace E] [CompleteSpace F]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (L : E →L[ℝ] F) (u : Lp E 2 μ) (v : Lp F 2 μ) :
    (inner ℝ (L.compLpL 2 μ u) v : ℝ)
      = inner ℝ u ((ContinuousLinearMap.adjoint L).compLpL 2 μ v) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (μ := μ) (p := 2) L u,
    ContinuousLinearMap.coeFn_compLpL (μ := μ) (p := 2)
      (ContinuousLinearMap.adjoint L) v] with ω h₁ h₂
  rw [h₁, h₂]
  exact (ContinuousLinearMap.adjoint_inner_right L (u ω) (v ω)).symm

/-- The adjoint transport also commutes with the pointwise action of a
continuous linear map. -/
theorem carrierTransportAdj_compLpL [CompleteSpace E] [CompleteSpace F]
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (L : E →L[ℝ] F) (w : Lp E 2 μ₂) :
    carrierTransportAdj F hΦ (L.compLpL 2 μ₂ w)
      = L.compLpL 2 μ₁ (carrierTransportAdj E hΦ w) := by
  refine ext_inner_right ℝ fun v ↦ ?_
  calc (inner ℝ (carrierTransportAdj F hΦ (L.compLpL 2 μ₂ w)) v : ℝ)
      = inner ℝ (L.compLpL 2 μ₂ w) (carrierTransport F hΦ v) :=
        inner_carrierTransportAdj_left hΦ _ _
    _ = inner ℝ w ((ContinuousLinearMap.adjoint L).compLpL 2 μ₂
          (carrierTransport F hΦ v)) := inner_compLpL_left L w _
    _ = inner ℝ w (carrierTransport E hΦ
          ((ContinuousLinearMap.adjoint L).compLpL 2 μ₁ v)) := by
        rw [carrierTransport_compLpL hΦ (ContinuousLinearMap.adjoint L) v]
    _ = inner ℝ (carrierTransportAdj E hΦ w)
          ((ContinuousLinearMap.adjoint L).compLpL 2 μ₁ v) :=
        (inner_carrierTransportAdj_left hΦ _ _).symm
    _ = inner ℝ (L.compLpL 2 μ₁ (carrierTransportAdj E hΦ w)) v :=
        (inner_compLpL_left L _ v).symm

/-- The transport intertwines the two Koopman families, provided the factor map
is equivariant. -/
theorem carrierTransport_koopman (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    (x : Vec d) (g : Lp E 2 μ₁) :
    carrierTransport E hΦ (koopman (μ := μ₁) (d := d) x g)
      = koopman (μ := μ₂) (d := d) x (carrierTransport E hΦ g) := by
  have hvadd : MeasurePreserving (fun ω : Ω₂ ↦ x +ᵥ ω) μ₂ μ₂ :=
    measurePreserving_const_vadd (μ := μ₂) x
  have h₁ : (carrierTransport E hΦ (koopman (μ := μ₁) (d := d) x g) : Ω₂ → E)
      =ᵐ[μ₂] fun ω ↦ (g : Ω₁ → E) (x +ᵥ Φ ω) := by
    refine (coeFn_carrierTransport hΦ _).trans ?_
    have hg : (koopman (μ := μ₁) (d := d) x g : Ω₁ → E)
        =ᵐ[μ₁] fun ω ↦ (g : Ω₁ → E) (x +ᵥ ω) :=
      Lp.coeFn_compMeasurePreserving _ (measurePreserving_const_vadd (μ := μ₁) x)
    exact hg.comp_tendsto hΦ.quasiMeasurePreserving.tendsto_ae
  have h₂ : (koopman (μ := μ₂) (d := d) x (carrierTransport E hΦ g) : Ω₂ → E)
      =ᵐ[μ₂] fun ω ↦ (g : Ω₁ → E) (x +ᵥ Φ ω) := by
    refine (Lp.coeFn_compMeasurePreserving _ hvadd).trans ?_
    have := (coeFn_carrierTransport hΦ g).comp_tendsto
      hvadd.quasiMeasurePreserving.tendsto_ae
    refine this.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
    exact congrArg (g : Ω₁ → E) (hequiv x ω)
  exact Lp.ext (h₁.trans h₂.symm)

/-- The adjoint transport intertwines the two Koopman families as well. -/
theorem carrierTransportAdj_koopman [CompleteSpace E] (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    (x : Vec d) (w : Lp E 2 μ₂) :
    carrierTransportAdj E hΦ (koopman (μ := μ₂) (d := d) x w)
      = koopman (μ := μ₁) (d := d) x (carrierTransportAdj E hΦ w) := by
  refine ext_inner_right ℝ fun v ↦ ?_
  calc (inner ℝ (carrierTransportAdj E hΦ (koopman (μ := μ₂) (d := d) x w)) v : ℝ)
      = inner ℝ (koopman (μ := μ₂) (d := d) x w) (carrierTransport E hΦ v) :=
        inner_carrierTransportAdj_left hΦ _ _
    _ = inner ℝ w (koopman (μ := μ₂) (d := d) (-x) (carrierTransport E hΦ v)) :=
        inner_koopman_left x w _
    _ = inner ℝ w (carrierTransport E hΦ (koopman (μ := μ₁) (d := d) (-x) v)) := by
        rw [carrierTransport_koopman hΦ hequiv (-x) v]
    _ = inner ℝ (carrierTransportAdj E hΦ w) (koopman (μ := μ₁) (d := d) (-x) v) :=
        (inner_carrierTransportAdj_left hΦ _ _).symm
    _ = inner ℝ (koopman (μ := μ₁) (d := d) x (carrierTransportAdj E hΦ w)) v :=
        (inner_koopman_left x _ v).symm

/-! ### Both directions preserve the stationary potential subspace -/

omit [AddAction (Vec d) Ω₁] [MeasurableConstVAdd (Vec d) Ω₁]
  [VAddInvariantMeasure (Vec d) Ω₁ μ₁] [AddAction (Vec d) Ω₂]
  [MeasurableConstVAdd (Vec d) Ω₂] [VAddInvariantMeasure (Vec d) Ω₂ μ₂] in
theorem vectorL2Coord_carrierTransport (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (i : Fin d) (G : VectorL2 d μ₁) :
    vectorL2Coord (μ := μ₂) i (carrierTransport (HilbertVec d) hΦ G)
      = carrierTransport ℝ hΦ (vectorL2Coord (μ := μ₁) i G) :=
  (carrierTransport_compLpL hΦ (PiLp.proj (p := 2) (β := fun _ : Fin d ↦ ℝ) i) G).symm

omit [AddAction (Vec d) Ω₁] [MeasurableConstVAdd (Vec d) Ω₁]
  [VAddInvariantMeasure (Vec d) Ω₁ μ₁] [AddAction (Vec d) Ω₂]
  [MeasurableConstVAdd (Vec d) Ω₂] [VAddInvariantMeasure (Vec d) Ω₂ μ₂] in
theorem vectorL2Coord_carrierTransportAdj (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (i : Fin d) (G : VectorL2 d μ₂) :
    vectorL2Coord (μ := μ₁) i (carrierTransportAdj (HilbertVec d) hΦ G)
      = carrierTransportAdj ℝ hΦ (vectorL2Coord (μ := μ₂) i G) :=
  (carrierTransportAdj_compLpL hΦ (PiLp.proj (p := 2) (β := fun _ : Fin d ↦ ℝ) i) G).symm

theorem mem_stationaryPotentialSubspace_carrierTransport
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    {G : VectorL2 d μ₁} (hG : G ∈ stationaryPotentialSubspace (μ := μ₁) (d := d)) :
    carrierTransport (HilbertVec d) hΦ G ∈
      stationaryPotentialSubspace (μ := μ₂) (d := d) :=
  mem_stationaryPotentialSubspace_of_intertwine
    (Sscal := carrierTransport ℝ hΦ) (Svec := carrierTransport (HilbertVec d) hΦ)
    (fun x φ ↦ carrierTransport_koopman hΦ hequiv x φ)
    (fun i G' ↦ vectorL2Coord_carrierTransport hΦ i G') hG

theorem mem_stationaryPotentialSubspace_carrierTransportAdj
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    {G : VectorL2 d μ₂} (hG : G ∈ stationaryPotentialSubspace (μ := μ₂) (d := d)) :
    carrierTransportAdj (HilbertVec d) hΦ G ∈
      stationaryPotentialSubspace (μ := μ₁) (d := d) :=
  mem_stationaryPotentialSubspace_of_intertwine
    (Sscal := carrierTransportAdj ℝ hΦ) (Svec := carrierTransportAdj (HilbertVec d) hΦ)
    (fun x φ ↦ carrierTransportAdj_koopman hΦ hequiv x φ)
    (fun i G' ↦ vectorL2Coord_carrierTransportAdj hΦ i G') hG

/-! ### The two stationary potential projections correspond -/

/-- **The stationary potential projection is natural under an equivariant factor
map.**  No identification of the two carrier `σ`-algebras is used, and the
transport is not assumed surjective. -/
theorem stationaryPotentialProjection_carrierTransport
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    (G : VectorL2 d μ₁) :
    stationaryPotentialProjection (μ := μ₂)
        (carrierTransport (HilbertVec d) hΦ G)
      = carrierTransport (HilbertVec d) hΦ
          (stationaryPotentialProjection (μ := μ₁) G) := by
  refine (eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    (mem_stationaryPotentialSubspace_carrierTransport hΦ hequiv
      (stationaryPotentialProjection_mem (μ := μ₁) G)) ?_).symm
  have hsub : carrierTransport (HilbertVec d) hΦ G
      - carrierTransport (HilbertVec d) hΦ (stationaryPotentialProjection (μ := μ₁) G)
      = carrierTransport (HilbertVec d) hΦ
          (G - stationaryPotentialProjection (μ := μ₁) G) :=
    (map_sub (carrierTransport (HilbertVec d) hΦ) _ _).symm
  rw [hsub]
  rw [stationarySolenoidalSubspace, Submodule.mem_orthogonal]
  intro v hv
  have hAv : carrierTransportAdj (HilbertVec d) hΦ v ∈
      stationaryPotentialSubspace (μ := μ₁) (d := d) :=
    mem_stationaryPotentialSubspace_carrierTransportAdj hΦ hequiv hv
  have hperp := sub_stationaryPotentialProjection_mem_orthogonal (μ := μ₁) G
  rw [stationarySolenoidalSubspace, Submodule.mem_orthogonal] at hperp
  have := hperp _ hAv
  rw [← inner_carrierTransportAdj_left hΦ v
    (G - stationaryPotentialProjection (μ := μ₁) G)]
  exact this

/-- **The two projected energies agree.** -/
theorem norm_stationaryPotentialProjection_carrierTransport
    (hΦ : MeasurePreserving Φ μ₂ μ₁)
    (hequiv : ∀ (x : Vec d) (ω : Ω₂), Φ (x +ᵥ ω) = x +ᵥ Φ ω)
    (G : VectorL2 d μ₁) :
    ‖stationaryPotentialProjection (μ := μ₂) (carrierTransport (HilbertVec d) hΦ G)‖
      = ‖stationaryPotentialProjection (μ := μ₁) G‖ := by
  rw [stationaryPotentialProjection_carrierTransport hΦ hequiv G]
  exact norm_carrierTransport hΦ _

end Transport

end

end Algsuperdiff.Section3.Provider.Corrector
