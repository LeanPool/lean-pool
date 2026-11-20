/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.TorusHelicalSource
public import LeanPool.FastDynamo.Global.TorusChartEmbedding
public import LeanPool.FastDynamo.Analysis.WeakLeibnizVelocity

/-!
# Measurable quotient-chart transfer for placed Euclidean sources

A placed Euclidean cell source must be carried onto the transverse torus
before it can become part of the global periodic velocity.  This module
performs every step of that transfer which does not require a weak chain
rule: it periodizes the placed field in a quotient-safe way, and it
carries `EuclideanCellSourceCertificate` through the chart construction.

A field supported in one Euclidean buffer disc has at most one representative
in the fixed placement chart, so its torus field is defined by that
representative and pulled back along the coordinatewise quotient map; the
pullback is exactly one-periodic in each coordinate, with no
differentiability of a quotient chart and no infinite-sum API.  A canonical
measurable representative in `(0,1]²` then removes the arbitrary-choice
obstacle in `torusPeriodizedExtension`, so the descended source and its two
displayed derivatives are measurable, bounded, real, supported in the torus
core, periodic after pullback, pointwise divergence free, and bundled as
real `L∞` fields.

## Organisation

* Quotient-safe periodization on the transverse torus: the support and
  descent certificates for the placed representative and its periodic
  pullback.
* Measurable quotient-chart transfer for placed Euclidean sources: the
  canonical measurable representative, and the certified descended source
  with its local classical chain rule.
-/

@[expose] public section

/-!
## Quotient-safe periodization on the transverse torus

The exact finite-on-support form of periodization needed for a placed local
field is recorded here.  A field supported in one Euclidean buffer disc has
at most one representative in the fixed placement chart.  We therefore
define its torus field by that representative and pull it back along the
coordinatewise quotient map.  The pullback is exactly one-periodic in each
coordinate, without using differentiability of a quotient chart or an
infinite-sum API.

Differentiability is not addressed in this section: the statements here are
the support and descent certificates on which the weak-derivative identities of
`Global/TorusChartFourierWeakTransfer.lean` build.
-/

namespace FastDynamo

noncomputable section

open Set

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-- The unique Euclidean representative selected from a placed buffer disc. -/
def periodizationRepresentative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) (hq : q ∈ P.torusBufferDisk n) : ℝ × ℝ :=
  Classical.choose hq

/-- The Euclidean representative selected for a torus point of the `n`-th placed buffer image lies
in the Euclidean buffer disc `P.scaleFamily.bufferDisk n`.
-/
theorem periodizationRepresentative_mem
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) (hq : q ∈ P.torusBufferDisk n) :
    P.periodizationRepresentative n q hq ∈ P.scaleFamily.bufferDisk n :=
  (Classical.choose_spec hq).1

/-- Projecting the selected Euclidean representative back through the coordinatewise torus quotient
recovers the original torus point.
-/
theorem transverseTorusPoint_periodizationRepresentative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) (hq : q ∈ P.torusBufferDisk n) :
    transverseTorusPoint (P.periodizationRepresentative n q hq) = q :=
  (Classical.choose_spec hq).2

/-- A chosen buffer representative agrees with every other buffer
representative of the same torus point. -/
theorem periodizationRepresentative_unique
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) (hq : q ∈ P.torusBufferDisk n)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n)
    (hxq : transverseTorusPoint x = q) :
    P.periodizationRepresentative n q hq = x := by
  apply transverseTorusPoint_injectiveOn_placementChart
  · exact P.bufferDisk_subset_chart n
      (P.periodizationRepresentative_mem n q hq)
  · exact P.bufferDisk_subset_chart n hx
  · exact (P.transverseTorusPoint_periodizationRepresentative n q hq).trans
      hxq.symm

/-- Descent of a Euclidean field supported in a placed buffer disc to the
actual transverse torus.  Outside that image it is defined to be zero. -/
def torusPeriodizedExtension
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E) : TransverseTorus → E := by
  classical
  exact fun q => if hq : q ∈ P.torusBufferDisk n then
    v (P.periodizationRepresentative n q hq)
  else 0

/-- The periodic Euclidean pullback of the descended field. -/
def periodizedExtension
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E) : ℝ × ℝ → E :=
  fun x => P.torusPeriodizedExtension n v (transverseTorusPoint x)

/-- On the original Euclidean buffer disc, descent followed by pullback is
the original field exactly. -/
theorem periodizedExtension_eq_source
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E)
    {x : ℝ × ℝ} (hx : x ∈ P.scaleFamily.bufferDisk n) :
    P.periodizedExtension n v x = v x := by
  classical
  rw [periodizedExtension, torusPeriodizedExtension,
    dite_eq_left ⟨x, hx, rfl⟩]
  congr 1
  exact P.periodizationRepresentative_unique n (transverseTorusPoint x)
    ⟨x, hx, rfl⟩ hx rfl

/-- The descended field is zero off its placed torus-buffer image. -/
theorem torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E)
    {q : TransverseTorus} (hq : q ∉ P.torusBufferDisk n) :
    P.torusPeriodizedExtension n v q = 0 := by
  classical
  rw [torusPeriodizedExtension, dite_eq_right hq]

/-- If a Euclidean source vanishes off its core disc, then its descended
torus field vanishes off the corresponding torus-core image. -/
theorem torusPeriodizedExtension_eq_zero_of_not_mem_torusLocalCoreDisk
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E)
    (hv : ∀ x, x ∉ P.scaleFamily.localCoreDisk supportRadius n → v x = 0)
    {q : TransverseTorus} (hq : q ∉ P.torusLocalCoreDisk n) :
    P.torusPeriodizedExtension n v q = 0 := by
  classical
  by_cases hbuffer : q ∈ P.torusBufferDisk n
  · rw [torusPeriodizedExtension, dite_eq_left hbuffer]
    apply hv
    intro hcore
    exact hq ⟨P.periodizationRepresentative n q hbuffer, hcore,
      P.transverseTorusPoint_periodizationRepresentative n q hbuffer⟩
  · exact P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n v
      hbuffer

end ScaleFamily.TorusCellPlacement

end

end FastDynamo

/-!
## Measurable quotient-chart transfer for placed Euclidean sources

This part carries `EuclideanCellSourceCertificate` through every piece of the
transverse-torus chart construction that does not require a weak chain
rule.  A canonical measurable representative in `(0,1]²` removes the
arbitrary-choice obstacle in `torusPeriodizedExtension`.  Consequently the
descended source and its two displayed derivatives are measurable, bounded,
real, supported in the torus core, periodic after pullback, and pointwise
(hence almost-everywhere) divergence free.  They are also bundled as
real `L∞` fields.

The further step toward `TransverseRealW1Inf` is to prove
that the two bundled derivative fields satisfy
`HasTransverseFourierDerivative` for the bundled value field.  The local
classical chain rule proved below identifies the derivatives on the original
buffer; converting that local identity (or its periodic pullback) into the
Fourier integration-by-parts identity on `UnitAddTorus` is done in
`Global/TorusChartFourierWeakTransfer.lean`, not here, and no such identity is assumed here.

That conversion is proved in `Global/TorusChartFourierWeakTransfer.lean`, and
the resulting global velocity is built in `Global/TorusFullVelocityConcrete.lean`;
see `FastDynamo/MainTheorem.lean`.
-/

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set WithLp
open scoped ENNReal Topology

/-! ## A canonical measurable representative -/

/-- The coordinatewise representative of a torus point in `(0,1]²`. -/
def transverseIocRepresentative (q : TransverseTorus) : ℝ × ℝ :=
  ((AddCircle.equivIoc 1 0 (q 0) : ℝ),
    (AddCircle.equivIoc 1 0 (q 1) : ℝ))

/-- First coordinate of the canonical `(0,1]²` representative: it is the `AddCircle.equivIoc`
representative of the zeroth torus coordinate. -/
@[simp] theorem transverseIocRepresentative_fst (q : TransverseTorus) :
    (transverseIocRepresentative q).1 =
      (AddCircle.equivIoc 1 0 (q 0) : ℝ) :=
  rfl

/-- Second coordinate of the canonical `(0,1]²` representative: it is the `AddCircle.equivIoc`
representative of the first torus coordinate. -/
@[simp] theorem transverseIocRepresentative_snd (q : TransverseTorus) :
    (transverseIocRepresentative q).2 =
      (AddCircle.equivIoc 1 0 (q 1) : ℝ) :=
  rfl

/-- The canonical representative maps back to the original torus point. -/
@[simp] theorem transverseTorusPoint_transverseIocRepresentative
    (q : TransverseTorus) :
    transverseTorusPoint (transverseIocRepresentative q) = q := by
  funext i
  fin_cases i <;> simp [transverseTorusPoint, transverseIocRepresentative]

/-- The canonical representative is Borel measurable. -/
theorem measurable_transverseIocRepresentative :
    Measurable transverseIocRepresentative := by
  have hzero : Measurable
      (fun q : TransverseTorus ↦
        (AddCircle.equivIoc 1 0 (q 0) : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc 1 0).measurable.comp
        (measurable_pi_apply (0 : Fin 2)))
  have hone : Measurable
      (fun q : TransverseTorus ↦
        (AddCircle.equivIoc 1 0 (q 1) : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc 1 0).measurable.comp
        (measurable_pi_apply (1 : Fin 2)))
  exact hzero.prodMk hone

/-- A Euclidean point already lying coordinatewise in `(0,1]` is recovered
exactly after quotienting and taking the canonical representative. -/
theorem transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc
    {x : ℝ × ℝ} (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    transverseIocRepresentative (transverseTorusPoint x) = x := by
  apply Prod.ext
  · simpa [transverseIocRepresentative, transverseTorusPoint] using
      (AddCircle.equivIoc_coe_of_mem hxzero)
  · simpa [transverseIocRepresentative, transverseTorusPoint] using
      (AddCircle.equivIoc_coe_of_mem hxone)

/-- On the fixed placement chart, the canonical representative is exactly
the original Euclidean point. -/
theorem transverseIocRepresentative_transverseTorusPoint_of_mem_placementChart
    {x : ℝ × ℝ} (hx : x ∈ ScaleFamily.placementChart) :
    transverseIocRepresentative (transverseTorusPoint x) = x := by
  have hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · exact hx.1.1
    · linarith [hx.1.2]
  have hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · linarith [hx.2.1]
    · linarith [hx.2.2]
  exact transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc
    hxzero hxone

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p} {supportRadius : ℝ}

/-- Membership in a torus buffer is detected measurably by the canonical
`(0,1]²` representative. -/
theorem mem_torusBufferDisk_iff_transverseIocRepresentative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) :
    q ∈ P.torusBufferDisk n ↔
      transverseIocRepresentative q ∈ P.scaleFamily.bufferDisk n := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [transverseIocRepresentative_transverseTorusPoint_of_mem_placementChart
      (P.bufferDisk_subset_chart n hx)] using hx
  · intro hq
    exact ⟨transverseIocRepresentative q, hq,
      transverseTorusPoint_transverseIocRepresentative q⟩

/-- The chosen periodization representative agrees with the canonical
measurable representative inside a placed buffer. -/
theorem periodizationRepresentative_eq_transverseIocRepresentative
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    (q : TransverseTorus) (hq : q ∈ P.torusBufferDisk n) :
    P.periodizationRepresentative n q hq = transverseIocRepresentative q := by
  apply P.periodizationRepresentative_unique n q hq
  · exact (P.mem_torusBufferDisk_iff_transverseIocRepresentative n q).mp hq
  · exact transverseTorusPoint_transverseIocRepresentative q

/-- Extension written using only the measurable canonical representative
and a measurable membership test. -/
def canonicalRepresentativeExtension
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E) : TransverseTorus → E := by
  classical
  exact fun q ↦
    if transverseIocRepresentative q ∈ P.scaleFamily.bufferDisk n then
      v (transverseIocRepresentative q)
    else 0

/-- Formula equating the descended extension with its canonical measurable
representative expression. -/
theorem torusPeriodizedExtension_eq_canonicalRepresentativeExtension
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] (v : ℝ × ℝ → E) :
    P.torusPeriodizedExtension n v =
      P.canonicalRepresentativeExtension n v := by
  funext q
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [torusPeriodizedExtension, dite_eq_left hq,
      canonicalRepresentativeExtension,
      ite_eq_left ((P.mem_torusBufferDisk_iff_transverseIocRepresentative n q).mp hq),
      P.periodizationRepresentative_eq_transverseIocRepresentative n q hq]
  · have hrep : transverseIocRepresentative q ∉
        P.scaleFamily.bufferDisk n := by
      intro hrep
      exact hq
        ((P.mem_torusBufferDisk_iff_transverseIocRepresentative n q).2 hrep)
    rw [torusPeriodizedExtension, dite_eq_right hq,
      canonicalRepresentativeExtension, ite_eq_right hrep]

/-- A measurable Euclidean field has a measurable torus periodization. -/
theorem measurable_torusPeriodizedExtension
    (P : TorusCellPlacement (r := r) supportRadius) (n : ℕ)
    {E : Type*} [Zero E] [MeasurableSpace E]
    (v : ℝ × ℝ → E) (hv : Measurable v) :
    Measurable (P.torusPeriodizedExtension n v) := by
  classical
  have hbuffer : MeasurableSet
      (transverseIocRepresentative ⁻¹' P.scaleFamily.bufferDisk n) :=
    measurableSet_ball.preimage measurable_transverseIocRepresentative
  have hite : Measurable (P.canonicalRepresentativeExtension n v) := by
    unfold canonicalRepresentativeExtension
    exact
    (hv.comp measurable_transverseIocRepresentative).ite
      hbuffer measurable_const
  rw [P.torusPeriodizedExtension_eq_canonicalRepresentativeExtension n v]
  exact hite

namespace EuclideanCellSourceCertificate

variable {P : TorusCellPlacement (r := r) supportRadius} {n : ℕ}

/-- The certified Euclidean source vanishes pointwise off its local core. -/
theorem source_eq_zero_of_not_mem_localCoreDisk
    (C : EuclideanCellSourceCertificate P n) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk supportRadius n) :
    C.source x = 0 := by
  by_contra hzero
  exact hx (C.source_support hzero)

/-- Each certified Euclidean derivative vanishes pointwise off the same
local core. -/
theorem firstDerivative_eq_zero_of_not_mem_localCoreDisk
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∉ P.scaleFamily.localCoreDisk supportRadius n) :
    C.firstDerivative j x = 0 := by
  by_contra hzero
  exact hx (C.firstDerivative_support j hzero)

/-- The stored first derivative is the ordinary `fderiv` applied to the
corresponding pair-coordinate basis vector. -/
theorem firstDerivative_eq_fderiv_apply_pairBasis
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) (x : ℝ × ℝ) :
    C.firstDerivative j x = fderiv ℝ C.source x (pairBasis j) := by
  rw [(C.source_hasFDerivAt x).fderiv]
  exact (C.sourceFDeriv_apply_pairBasis x j).symm

/-- The certified Euclidean source is measurable. -/
theorem measurable_source (C : EuclideanCellSourceCertificate P n) :
    Measurable C.source := by
  have hd : Differentiable ℝ C.source :=
    fun x ↦ (C.source_hasFDerivAt x).differentiableAt
  exact hd.continuous.measurable

/-- The stored coordinate derivatives are measurable, as applications of
the measurable Fréchet derivative. -/
theorem measurable_firstDerivative
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    Measurable (C.firstDerivative j) := by
  have hmeas := measurable_fderiv_apply_const ℝ C.source (pairBasis j)
  convert hmeas using 1
  funext x
  exact C.firstDerivative_eq_fderiv_apply_pairBasis j x

/-! ### Raw torus and periodic representatives -/

/-- The certified source descended to the transverse torus. -/
def torusSource (C : EuclideanCellSourceCertificate P n) :
    TransverseTorus → C3 :=
  P.torusPeriodizedExtension n C.source

/-- The two certified source derivatives descended separately to the torus. -/
def torusFirstDerivative (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) : TransverseTorus → C3 :=
  P.torusPeriodizedExtension n (C.firstDerivative j)

/-- The one-periodic Euclidean pullback of the descended source. -/
def periodicSource (C : EuclideanCellSourceCertificate P n) :
    ℝ × ℝ → C3 :=
  P.periodizedExtension n C.source

/-- The one-periodic Euclidean pullback of one descended derivative. -/
def periodicFirstDerivative (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) : ℝ × ℝ → C3 :=
  P.periodizedExtension n (C.firstDerivative j)

/-- The descended source is measurable. -/
theorem measurable_torusSource
    (C : EuclideanCellSourceCertificate P n) :
    Measurable C.torusSource :=
  P.measurable_torusPeriodizedExtension n C.source C.measurable_source

/-- Each descended derivative representative is measurable. -/
theorem measurable_torusFirstDerivative
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    Measurable (C.torusFirstDerivative j) :=
  P.measurable_torusPeriodizedExtension n (C.firstDerivative j)
    (C.measurable_firstDerivative j)

/-- The torus source is supported in the image of the local core. -/
theorem torusSource_eq_zero_of_not_mem_torusLocalCoreDisk
    (C : EuclideanCellSourceCertificate P n) {q : TransverseTorus}
    (hq : q ∉ P.torusLocalCoreDisk n) :
    C.torusSource q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusLocalCoreDisk n
    C.source (fun _ hx ↦ C.source_eq_zero_of_not_mem_localCoreDisk hx) hq

/-- Each torus derivative representative has the same core support. -/
theorem torusFirstDerivative_eq_zero_of_not_mem_torusLocalCoreDisk
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2)
    {q : TransverseTorus} (hq : q ∉ P.torusLocalCoreDisk n) :
    C.torusFirstDerivative j q = 0 :=
  P.torusPeriodizedExtension_eq_zero_of_not_mem_torusLocalCoreDisk n
    (C.firstDerivative j)
    (fun _ hx ↦ C.firstDerivative_eq_zero_of_not_mem_localCoreDisk j hx) hq

/-- The torus source remains pointwise real in every component. -/
theorem torusSource_pointwiseReal
    (C : EuclideanCellSourceCertificate P n)
    (q : TransverseTorus) (i : Fin 3) :
    (C.torusSource q i).im = 0 := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [torusSource, torusPeriodizedExtension, dite_eq_left hq]
    exact C.source_pointwiseReal _ i
  · rw [torusSource, torusPeriodizedExtension, dite_eq_right hq]
    simp

/-- The torus derivative representatives remain pointwise real. -/
theorem torusFirstDerivative_pointwiseReal
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2)
    (q : TransverseTorus) (i : Fin 3) :
    (C.torusFirstDerivative j q i).im = 0 := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [torusFirstDerivative, torusPeriodizedExtension, dite_eq_left hq]
    exact C.firstDerivative_pointwiseReal j _ i
  · rw [torusFirstDerivative, torusPeriodizedExtension, dite_eq_right hq]
    simp

/-- The descended derivative representatives have pointwise zero transverse
divergence. -/
theorem torusFirstDerivative_transverseDivergence
    (C : EuclideanCellSourceCertificate P n) (q : TransverseTorus) :
    C.torusFirstDerivative 0 q 0 + C.torusFirstDerivative 1 q 1 = 0 := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · simp only [torusFirstDerivative, torusPeriodizedExtension, dite_eq_left hq]
    exact C.transverseDivergence _
  · simp [torusFirstDerivative, torusPeriodizedExtension, hq]

/-- The descended source retains the certified pointwise value bound. -/
theorem norm_torusSource_le
    (C : EuclideanCellSourceCertificate P n) (q : TransverseTorus) :
    ‖C.torusSource q‖ ≤ C.valueBound * P.scaleFamily.ell n := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [torusSource, torusPeriodizedExtension, dite_eq_left hq]
    exact C.norm_source_le _
  · rw [torusSource, torusPeriodizedExtension, dite_eq_right hq, norm_zero]
    exact mul_nonneg C.valueBound_nonneg (P.scaleFamily.ell_pos n).le

/-- The descended first derivatives retain their uniform pointwise bound. -/
theorem norm_torusFirstDerivative_le
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2)
    (q : TransverseTorus) :
    ‖C.torusFirstDerivative j q‖ ≤ C.firstDerivativeBound := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk n
  · rw [torusFirstDerivative, torusPeriodizedExtension, dite_eq_left hq]
    exact C.norm_firstDerivative_le j _
  · rw [torusFirstDerivative, torusPeriodizedExtension, dite_eq_right hq, norm_zero]
    exact C.firstDerivativeBound_nonneg

/-- The periodic source agrees with the original Euclidean source throughout
the placed buffer. -/
theorem periodicSource_eq_source_of_mem_bufferDisk
    (C : EuclideanCellSourceCertificate P n) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    C.periodicSource x = C.source x :=
  P.periodizedExtension_eq_source n C.source hx

/-- The periodic derivative representative agrees with the stored Euclidean
derivative throughout the placed buffer. -/
theorem periodicFirstDerivative_eq_firstDerivative_of_mem_bufferDisk
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) {x : ℝ × ℝ}
    (hx : x ∈ P.scaleFamily.bufferDisk n) :
    C.periodicFirstDerivative j x = C.firstDerivative j x :=
  P.periodizedExtension_eq_source n (C.firstDerivative j) hx

/-- On the entire canonical `(0,1]²` fundamental rectangle, the torus source
pulled back along the quotient is exactly the original Euclidean source.
Outside the buffer both sides vanish. -/
theorem torusSource_transverseTorusPoint_eq_source_of_mem_Ioc
    (C : EuclideanCellSourceCertificate P n) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    C.torusSource (transverseTorusPoint x) = C.source x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk n ↔
      x ∈ P.scaleFamily.bufferDisk n := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative n,
      hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk n
  · exact C.periodicSource_eq_source_of_mem_bufferDisk hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk n :=
      hbuffer_iff.not.mpr hx
    rw [torusSource,
      P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n
        C.source hq,
      C.source_eq_zero_of_not_mem_localCoreDisk]
    exact fun hcore ↦ hx (P.localCoreDisk_subset_bufferDisk n hcore)

/-- The same fundamental-rectangle identity holds for each displayed first
derivative representative. -/
theorem torusFirstDerivative_transverseTorusPoint_eq_firstDerivative_of_mem_Ioc
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) {x : ℝ × ℝ}
    (hxzero : x.1 ∈ Set.Ioc (0 : ℝ) (0 + 1))
    (hxone : x.2 ∈ Set.Ioc (0 : ℝ) (0 + 1)) :
    C.torusFirstDerivative j (transverseTorusPoint x) =
      C.firstDerivative j x := by
  have hrep : transverseIocRepresentative (transverseTorusPoint x) = x :=
    transverseIocRepresentative_transverseTorusPoint_of_mem_Ioc hxzero hxone
  have hbuffer_iff : transverseTorusPoint x ∈ P.torusBufferDisk n ↔
      x ∈ P.scaleFamily.bufferDisk n := by
    rw [P.mem_torusBufferDisk_iff_transverseIocRepresentative n,
      hrep]
  by_cases hx : x ∈ P.scaleFamily.bufferDisk n
  · exact C.periodicFirstDerivative_eq_firstDerivative_of_mem_bufferDisk j hx
  · have hq : transverseTorusPoint x ∉ P.torusBufferDisk n :=
      hbuffer_iff.not.mpr hx
    rw [torusFirstDerivative,
      P.torusPeriodizedExtension_eq_zero_of_not_mem_torusBufferDisk n
        (C.firstDerivative j) hq,
      C.firstDerivative_eq_zero_of_not_mem_localCoreDisk]
    exact fun hcore ↦ hx (P.localCoreDisk_subset_bufferDisk n hcore)

/-! ### Real `L∞` representatives -/

/-- Pointwise real part of the descended source. -/
def realTorusSource (C : EuclideanCellSourceCertificate P n) :
    TransverseTorus → R3 :=
  fun q ↦ vecRe (C.torusSource q)

/-- Pointwise real part of one descended derivative. -/
def realTorusFirstDerivative (C : EuclideanCellSourceCertificate P n)
    (j : Fin 2) : TransverseTorus → R3 :=
  fun q ↦ vecRe (C.torusFirstDerivative j q)

/-- Pointwise reality makes complexification of the real source exactly the
original complex source, with no almost-everywhere qualification. -/
theorem complexifyR3_realTorusSource
    (C : EuclideanCellSourceCertificate P n) (q : TransverseTorus) :
    complexifyR3 (C.realTorusSource q) = C.torusSource q := by
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simp [realTorusSource, vecRe, complexifyR3_apply]
  · simp [realTorusSource, vecRe, complexifyR3_apply,
      C.torusSource_pointwiseReal q i]

/-- Complexification of each real derivative is exactly its complex
representative. -/
theorem complexifyR3_realTorusFirstDerivative
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2)
    (q : TransverseTorus) :
    complexifyR3 (C.realTorusFirstDerivative j q) =
      C.torusFirstDerivative j q := by
  apply PiLp.ext
  intro i
  apply Complex.ext
  · simp [realTorusFirstDerivative, vecRe, complexifyR3_apply]
  · simp [realTorusFirstDerivative, vecRe, complexifyR3_apply,
      C.torusFirstDerivative_pointwiseReal j q i]

/-- The real source representative is measurable. -/
theorem measurable_realTorusSource
    (C : EuclideanCellSourceCertificate P n) :
    Measurable C.realTorusSource :=
  vecReCLM.measurable.comp C.measurable_torusSource

/-- The real derivative representatives are measurable. -/
theorem measurable_realTorusFirstDerivative
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    Measurable (C.realTorusFirstDerivative j) :=
  vecReCLM.measurable.comp (C.measurable_torusFirstDerivative j)

/-- The real source obeys the same cell-scale bound. -/
theorem norm_realTorusSource_le
    (C : EuclideanCellSourceCertificate P n) (q : TransverseTorus) :
    ‖C.realTorusSource q‖ ≤ C.valueBound * P.scaleFamily.ell n :=
  (norm_vecRe_le (C.torusSource q)).trans (C.norm_torusSource_le q)

/-- The real derivative representatives obey the same uniform bound. -/
theorem norm_realTorusFirstDerivative_le
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2)
    (q : TransverseTorus) :
    ‖C.realTorusFirstDerivative j q‖ ≤ C.firstDerivativeBound :=
  (norm_vecRe_le (C.torusFirstDerivative j q)).trans
    (C.norm_torusFirstDerivative_le j q)

/-- The measurable bounded real source is a transverse `L∞` field. -/
theorem realTorusSource_memLp_top
    (C : EuclideanCellSourceCertificate P n) :
    MemLp C.realTorusSource ∞ transverseMeasure :=
  memLp_top_of_bound C.measurable_realTorusSource.aestronglyMeasurable
    (C.valueBound * P.scaleFamily.ell n)
    (Filter.Eventually.of_forall C.norm_realTorusSource_le)

/-- Each measurable bounded real derivative is a transverse `L∞`
field. -/
theorem realTorusFirstDerivative_memLp_top
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    MemLp (C.realTorusFirstDerivative j) ∞ transverseMeasure :=
  memLp_top_of_bound
    (C.measurable_realTorusFirstDerivative j).aestronglyMeasurable
    C.firstDerivativeBound
    (Filter.Eventually.of_forall (C.norm_realTorusFirstDerivative_le j))

/-- The bundled real transverse value field. -/
def transverseValueLInf (C : EuclideanCellSourceCertificate P n) :
    TransverseR3LInf :=
  C.realTorusSource_memLp_top.toLp C.realTorusSource

/-- One bundled real transverse derivative field. -/
def transverseFirstDerivativeLInf
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    TransverseR3LInf :=
  (C.realTorusFirstDerivative_memLp_top j).toLp
    (C.realTorusFirstDerivative j)

/-- The bundled value has the raw real torus source as an a.e.
representative. -/
theorem transverseValueLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) :
    (C.transverseValueLInf : TransverseTorus → R3)
      =ᵐ[transverseMeasure] C.realTorusSource :=
  MemLp.coeFn_toLp _

/-- Each bundled derivative has its raw real torus derivative as an a.e.
representative. -/
theorem transverseFirstDerivativeLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    (C.transverseFirstDerivativeLInf j : TransverseTorus → R3)
      =ᵐ[transverseMeasure] C.realTorusFirstDerivative j :=
  MemLp.coeFn_toLp _

/-- Complexification of the bundled real value agrees a.e. with the exact
extension-by-zero source expected by differentiable localization. -/
theorem complexifyR3LInf_transverseValueLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) :
    (complexifyR3LInf C.transverseValueLInf : TransverseTorus → C3)
      =ᵐ[transverseMeasure] C.torusSource := by
  change (((complexifyR3.compLpL ∞ transverseMeasure)
      C.transverseValueLInf : TransverseC3LInf) : TransverseTorus → C3)
    =ᵐ[transverseMeasure] C.torusSource
  filter_upwards [complexifyR3.coeFn_compLpL C.transverseValueLInf,
    C.transverseValueLInf_coe_ae] with q hcomplex hvalue
  rw [hcomplex, hvalue, C.complexifyR3_realTorusSource q]

/-- Complexification of each bundled real derivative agrees a.e. with the
corresponding exact derivative representative. -/
theorem complexifyR3LInf_transverseFirstDerivativeLInf_coe_ae
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    (complexifyR3LInf (C.transverseFirstDerivativeLInf j) :
        TransverseTorus → C3)
      =ᵐ[transverseMeasure] C.torusFirstDerivative j := by
  change (((complexifyR3.compLpL ∞ transverseMeasure)
      (C.transverseFirstDerivativeLInf j) : TransverseC3LInf) :
        TransverseTorus → C3)
    =ᵐ[transverseMeasure] C.torusFirstDerivative j
  filter_upwards [complexifyR3.coeFn_compLpL
      (C.transverseFirstDerivativeLInf j),
    C.transverseFirstDerivativeLInf_coe_ae j] with q hcomplex hderiv
  rw [hcomplex, hderiv, C.complexifyR3_realTorusFirstDerivative j q]

/-! ### Exact remaining Fourier condition -/

/-- The tuple of the two bundled derivative fields. -/
def transverseGradientLInf
    (C : EuclideanCellSourceCertificate P n) :
    TransverseR3GradientLInf :=
  toLp ∞ fun j ↦ C.transverseFirstDerivativeLInf j

/-- The bundled gradient of a cell certificate evaluates in direction `j` to the single bundled
derivative field `transverseFirstDerivativeLInf j`. -/
@[simp] theorem transverseGradientLInf_apply
    (C : EuclideanCellSourceCertificate P n) (j : Fin 2) :
    C.transverseGradientLInf j = C.transverseFirstDerivativeLInf j :=
  rfl

/-- The statement needed to upgrade the measurable chart transfer to the
repository's Fourier-graph `W^{1,∞}` space.  This is a property, not an
assumption attached to the Euclidean certificate; no theorem in this module
claims it for the periodized source (it is proved in
`Global/TorusChartFourierWeakTransfer.lean`). -/
def HasFourierWeakTransfer
    (C : EuclideanCellSourceCertificate P n) : Prop :=
  ∀ j : Fin 2,
    HasTransverseFourierDerivative j
      (complexifyR3LTwo C.transverseValueLInf)
      (complexifyR3LTwo (C.transverseFirstDerivativeLInf j))

/-- Once the explicit Fourier weak-transfer identity is proved, the already
constructed value and derivative `L∞` fields form a
`TransverseRealW1Inf` element.  The hypothesis exposes, rather than hides,
the one analytic input not proved in this module. -/
def toTransverseRealW1Inf
    (C : EuclideanCellSourceCertificate P n)
    (hweak : C.HasFourierWeakTransfer) : TransverseRealW1Inf := by
  refine ⟨(C.transverseValueLInf, C.transverseGradientLInf), ?_⟩
  rw [mem_transverseW1InfSubmodule_iff]
  intro j frequency i
  exact hweak j frequency i

/-- Under the explicit weak-transfer hypothesis, each stored complex
derivative coordinate has the constructed raw derivative as an a.e.
representative. -/
theorem transverseW1InfComplexDerivCoordLInf_toTransverseRealW1Inf_coe_ae
    (C : EuclideanCellSourceCertificate P n)
    (hweak : C.HasFourierWeakTransfer) (j : Fin 2) (i : Fin 3) :
    (transverseW1InfComplexDerivCoordLInf j i
        (C.toTransverseRealW1Inf hweak) : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] fun q ↦ C.torusFirstDerivative j q i := by
  change ((((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL ∞ transverseMeasure)
      (complexifyR3LInf (C.transverseFirstDerivativeLInf j)) :
        TransverseScalarLInf) : TransverseTorus → ℂ)
    =ᵐ[transverseMeasure] fun q ↦ C.torusFirstDerivative j q i
  filter_upwards [
    (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
      (complexifyR3LInf (C.transverseFirstDerivativeLInf j)),
    C.complexifyR3LInf_transverseFirstDerivativeLInf_coe_ae j]
      with q hcoord hderiv
  rw [hcoord, hderiv]
  rfl

/-- The conditionally assembled Fourier-graph field is divergence-free; this
uses only the a.e. pointwise cancellation, not an additional
analytic hypothesis. -/
theorem toTransverseRealW1Inf_isTransverseDivergenceFree
    (C : EuclideanCellSourceCertificate P n)
    (hweak : C.HasFourierWeakTransfer) :
    IsTransverseDivergenceFree (C.toTransverseRealW1Inf hweak) := by
  unfold IsTransverseDivergenceFree
  apply Lp.ext
  let d0 : TransverseScalarLInf :=
    transverseW1InfComplexDerivCoordLInf 0 0
      (C.toTransverseRealW1Inf hweak)
  let d1 : TransverseScalarLInf :=
    transverseW1InfComplexDerivCoordLInf 1 1
      (C.toTransverseRealW1Inf hweak)
  have hd0 :=
    C.transverseW1InfComplexDerivCoordLInf_toTransverseRealW1Inf_coe_ae
      hweak 0 0
  have hd1 :=
    C.transverseW1InfComplexDerivCoordLInf_toTransverseRealW1Inf_coe_ae
      hweak 1 1
  have hadd := Lp.coeFn_add d0 d1
  have hzero := Lp.coeFn_zero ℂ ∞ transverseMeasure
  filter_upwards [hd0, hd1, hadd, hzero] with q hd0q hd1q haddq hzeroq
  change ((d0 + d1 : TransverseScalarLInf) q) =
    ((0 : TransverseScalarLInf) q)
  rw [haddq, hzeroq]
  change d0 q + d1 q = 0
  have h0 : d0 q = C.torusFirstDerivative 0 q 0 := by
    simpa [d0] using hd0q
  have h1 : d1 q = C.torusFirstDerivative 1 q 1 := by
    simpa [d1] using hd1q
  rw [h0, h1, C.torusFirstDerivative_transverseDivergence q]

end EuclideanCellSourceCertificate

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
