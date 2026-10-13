/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.GradientIdentification

/-!
# MollifiedDecorrelation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: mollification against the stationary Helmholtz splitting, and the
decorrelation kill

Step 3 of the proof of `l.corrector.limit` consumes part (ii) of
`l.approximation.stationary.by.local`: the stationary solenoidal flux `𝐣 = 𝐟 +
∇w` must be approximated, inside each cube `cu_K`, by members of
`L²_{sol,0}(cu_K)`.  The manuscript's competitor is the row divergence of a
cutoff antisymmetric *stream* tensor `S` with `𝐣_i = Σ_m ∂_m S_{im}`, whose
per-realization layer is already available
(`Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`).

Part (ii) cannot hold for an arbitrary stationary solenoidal `𝐣`: by
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`
(`normSq_le_cubeAverage_normSq_const_sub`) a nonzero *constant* — hence
Koopman-invariant — field is a genuine counterexample to the displayed bound, so
a condition forcing the translation-invariant part of `𝐣` to vanish is necessary
rather than merely convenient.

*Motivation, not a claim proved here.*  The stream constructions that smooth
along the translation action — the resolvent stream
`S^λ_{im} = −G_λ(D_m 𝐣_i − D_i 𝐣_m)`, and the kernel stream
`S_{im} = A_{g_m} 𝐣_i − A_{g_i} 𝐣_m` built from a smooth compactly supported
vector field `g` on `ℝᵈ` — reproduce `𝐣` up to a residual of the shape `A_κ 𝐣`
with `κ` a probability density spread over a large scale.  Making such a residual
small is therefore the quantitative content of "the invariant part of `𝐣`
vanishes".

This file supplies that quantitative content, on the abstract stationary carrier
and with no ergodic theorem, no Liouville argument and no resolvent.  Writing
`A_κ` for the mollification by a probability density `κ` along the translation
action, the two results are:

* `norm_toLp_mollify_le_of_helmholtz` — if `𝐣 = 𝐟 + p` with `p ∈ L²_pot(Ω)` and
  `𝐣 ∈ L²_sol(Ω)` (the Helmholtz characterization of the whole-space corrector
  `∇w = p`, ABK26), then `‖A_κ 𝐣‖_{L²(Ω)} ≤ ‖A_κ 𝐟‖_{L²(Ω)}`: smoothing the flux
  is controlled by smoothing the forcing.  This rests on the fact that `A_κ`
  preserves both halves of the stationary Helmholtz splitting, which in turn is
  a one-line consequence of the pairing formula `integral_inner_mollify`
  together with the Koopman invariance of `L²_pot(Ω)`
  (`koopman_mem_stationaryPotentialSubspace`).

* `integral_normSq_mollify_le_of_covariance_support` — if the stationary
  covariance `w ↦ E[⟪X(w + ·), X⟫]` vanishes for `‖w‖ ≥ ρ` (which is what a
  finite range of dependence together with a vanishing mean gives), then
  `E[|A_κ X|²] ≤ ‖κ‖_∞ · |B_ρ| · E[|X|²]`.

Composing them (`integral_normSq_mollify_le_of_helmholtz_of_covariance_support`)
gives `E[|A_κ 𝐣|²] ≤ ‖κ‖_∞ |B_ρ| E[|𝐟|²]`, so `A_κ 𝐣 → 0` in `L²(Ω)` along any
family of probability densities whose sup norms tend to `0`, even though the
flux `𝐣` itself has no finite range of dependence.  Nothing here uses the mean
ergodic theorem: the whole input is the finite range of the *forcing's*
covariance.

**Disclosure.**  Nothing in this file realizes any source node.  It proves the
`Ω`-level decorrelation input of part (ii) of
`l.approximation.stationary.by.local`; it does not prove part (ii) (the stream
construction and the cube cutoff are not done here), and it claims no node
status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### The Koopman action as a group of unitaries -/

section KoopmanAlgebra

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Koopman translate of an `L²` class is represented by the translated
representative. -/
theorem coeFn_koopman (x : Vec d) (F : Lp E 2 μ) :
    koopman (μ := μ) x F =ᵐ[μ] fun ω => F (x +ᵥ ω) :=
  Lp.coeFn_compMeasurePreserving (E := E) (p := 2) F
    (measurePreserving_const_vadd (μ := μ) x)

/-- The Koopman operators compose: `U_x ∘ U_y = U_{y+x}`. -/
theorem koopman_koopman (x y : Vec d) (F : Lp E 2 μ) :
    koopman (μ := μ) x (koopman (μ := μ) y F) = koopman (μ := μ) (y + x) F := by
  refine Lp.ext ?_
  have hpull : ∀ᵐ ω ∂μ, (koopman (μ := μ) y F) (x +ᵥ ω) = F (y +ᵥ (x +ᵥ ω)) :=
    (measurePreserving_const_vadd (μ := μ) x).quasiMeasurePreserving.ae
      (coeFn_koopman (μ := μ) y F)
  filter_upwards [coeFn_koopman (μ := μ) x (koopman (μ := μ) y F), hpull,
    coeFn_koopman (μ := μ) (y + x) F] with ω h1 h2 h3
  rw [h1, h2, h3, vadd_vadd]

end KoopmanAlgebra

section KoopmanInner

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The Koopman adjoint identity**: the translation operators are unitary, so a
translation may be moved to the other side of the inner product with the
opposite sign. -/
theorem inner_koopman_left (x : Vec d) (F G : Lp E 2 μ) :
    inner ℝ (koopman (μ := μ) x F) G = inner ℝ F (koopman (μ := μ) (-x) G) := by
  have hG : koopman (μ := μ) x (koopman (μ := μ) (-x) G) = G := by
    rw [koopman_koopman, neg_add_cancel, koopman_zero]
  calc inner ℝ (koopman (μ := μ) x F) G
      = inner ℝ (koopman (μ := μ) x F)
          (koopman (μ := μ) x (koopman (μ := μ) (-x) G)) := by rw [hG]
    _ = inner ℝ F (koopman (μ := μ) (-x) G) :=
        (koopman (μ := μ) x).inner_map_map F (koopman (μ := μ) (-x) G)

end KoopmanInner

/-! ### The Koopman action preserves the stationary Helmholtz splitting -/

section KoopmanSplitting

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- Coordinate extraction commutes with the Koopman action. -/
theorem koopman_vectorL2Coord (z : Vec d) (i : Fin d) (F : VectorL2 d μ) :
    koopman (μ := μ) z (vectorL2Coord (μ := μ) i F)
      = vectorL2Coord (μ := μ) i (koopman (μ := μ) z F) := by
  refine Lp.ext ?_
  have hpull : ∀ᵐ ω ∂μ, (vectorL2Coord (μ := μ) i F) (z +ᵥ ω) = (F (z +ᵥ ω)) i :=
    (measurePreserving_const_vadd (μ := μ) z).quasiMeasurePreserving.ae
      ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).coeFn_compLpL F)
  filter_upwards [coeFn_koopman (μ := μ) z (vectorL2Coord (μ := μ) i F), hpull,
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).coeFn_compLpL
      (koopman (μ := μ) z F),
    coeFn_koopman (μ := μ) z F] with ω h1 h2 h3 h4
  rw [h1, h2]
  exact (h3.trans (by rw [h4]; rfl)).symm

/-- The Koopman action transports strong horizontal gradients. -/
theorem hasHorizontalGradient_koopman (z : Vec d) {φ : ScalarL2 μ} {F : VectorL2 d μ}
    (h : HasHorizontalGradient (μ := μ) φ F) :
    HasHorizontalGradient (μ := μ) (koopman (μ := μ) z φ) (koopman (μ := μ) z F) := by
  intro i
  have hcomm : (fun t : ℝ => koopman (μ := μ) (t • (Pi.single i 1 : Vec d))
        (koopman (μ := μ) z φ))
      = fun t : ℝ => koopman (μ := μ) z
          (koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ) := by
    funext t
    rw [koopman_koopman, koopman_koopman, add_comm]
  rw [hcomm, ← koopman_vectorL2Coord]
  exact (koopman (μ := μ) z).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (h i)

/-- **The stationary potential subspace is Koopman invariant.** -/
theorem koopman_mem_stationaryPotentialSubspace (z : Vec d) {F : VectorL2 d μ}
    (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    koopman (μ := μ) z F ∈ stationaryPotentialSubspace (μ := μ) (d := d) := by
  set T : Submodule ℝ (VectorL2 d μ) :=
    Submodule.comap (koopman (μ := μ) (E := HilbertVec d) z).toLinearMap
      (stationaryPotentialSubspace (μ := μ) (d := d)) with hT
  have hsub : horizontalGradientRange (μ := μ) (d := d) ≤ T := by
    rintro G ⟨ψ, hψ⟩
    exact Submodule.le_topologicalClosure (horizontalGradientRange (μ := μ) (d := d))
      ⟨koopman (μ := μ) z ψ, hasHorizontalGradient_koopman z hψ⟩
  have hcoe : (T : Set (VectorL2 d μ))
      = (koopman (μ := μ) (E := HilbertVec d) z) ⁻¹'
        ((stationaryPotentialSubspace (μ := μ) (d := d)) : Set (VectorL2 d μ)) := rfl
  have hclosed : IsClosed (T : Set (VectorL2 d μ)) := by
    rw [hcoe]
    exact IsClosed.preimage (koopman (μ := μ) (E := HilbertVec d) z).continuous
      (Submodule.isClosed_topologicalClosure (horizontalGradientRange (μ := μ) (d := d)))
  exact Submodule.topologicalClosure_minimal
    (horizontalGradientRange (μ := μ) (d := d)) hsub hclosed hF

/-- **The stationary solenoidal subspace is Koopman invariant.** -/
theorem koopman_mem_stationarySolenoidalSubspace (z : Vec d) {F : VectorL2 d μ}
    (hF : F ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    koopman (μ := μ) z F ∈ stationarySolenoidalSubspace (μ := μ) (d := d) := by
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hu' : koopman (μ := μ) (-z) u ∈ stationaryPotentialSubspace (μ := μ) (d := d) :=
    koopman_mem_stationaryPotentialSubspace (-z) hu
  have hzero : inner ℝ (koopman (μ := μ) (-z) u) F = 0 :=
    (Submodule.mem_orthogonal _ _).1 hF _ hu'
  rwa [inner_koopman_left, neg_neg] at hzero

end KoopmanSplitting

/-! ### Inner-product bridges between classes and representatives -/

section InnerBridges

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `L²` inner product of two classes is the integral of the pointwise inner
products of any representatives. -/
theorem inner_toLp_toLp {X G : Ω → E} (hX : MemLp X 2 μ) (hG : MemLp G 2 μ) :
    inner ℝ (hX.toLp X) (hG.toLp G) = ∫ ω, inner ℝ (X ω) (G ω) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hX.coeFn_toLp, hG.coeFn_toLp] with ω h1 h2
  rw [h1, h2]

end InnerBridges

section KoopmanRepresentative

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pairing of a Koopman translate against another class, in integral form. -/
theorem inner_koopman_toLp_toLp {X G : Ω → E} (hX : MemLp X 2 μ) (hG : MemLp G 2 μ)
    (x : Vec d) :
    inner ℝ (koopman (μ := μ) x (hX.toLp X)) (hG.toLp G)
      = ∫ ω, inner ℝ (X (x +ᵥ ω)) (G ω) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_koopman_toLp hX x, hG.coeFn_toLp] with ω h1 h2
  rw [h1, h2]

end KoopmanRepresentative

/-! ### The pairing formula for a mollification -/

section Pairing

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Joint integrability of the pairing integrand of a mollification. -/
theorem integrable_prod_weighted_inner_comp_vadd {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X G : Ω → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (hGm : StronglyMeasurable G) (hG : MemLp G 2 μ) :
    Integrable
      (fun q : Ω × Vec d => κ q.2 * inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1)) (μ.prod volume) := by
  have hmeas : Measurable fun q : Ω × Vec d => (-q.2) +ᵥ q.1 :=
    measurable_vadd_pair_swap.comp (measurable_fst.prodMk measurable_snd.neg)
  have hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hGsq : Integrable (fun ω => ‖G ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
  have hjm : StronglyMeasurable
      fun q : Ω × Vec d => κ q.2 * inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1) :=
    ((hκc.measurable.comp measurable_snd).stronglyMeasurable).mul
      ((hXm.comp_measurable hmeas).inner (hGm.comp_measurable measurable_fst))
  have h1 : Integrable
      (fun q : Ω × Vec d => |κ q.2| * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2) (μ.prod volume) :=
    integrable_prod_weighted_comp_vadd (μ := μ) hκc.abs hκi.abs (hXm.norm.pow 2) hXsq
  have h2 : Integrable
      (fun q : Ω × Vec d => ‖G q.1‖ ^ 2 * |κ q.2|) (μ.prod volume) :=
    hGsq.mul_prod hκi.abs
  refine Integrable.mono' ((h1.add h2).const_mul (2⁻¹ : ℝ)) hjm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun q => ?_
  have hcs : |inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1)|
      ≤ ‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖ := abs_real_inner_le_norm _ _
  have hκ0 : (0 : ℝ) ≤ |κ q.2| := abs_nonneg _
  have hstep : |κ q.2| * |inner ℝ (X ((-q.2) +ᵥ q.1)) (G q.1)|
      ≤ |κ q.2| * (‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖) :=
    mul_le_mul_of_nonneg_left hcs hκ0
  have hyoung : ‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖
      ≤ 2⁻¹ * (‖X ((-q.2) +ᵥ q.1)‖ ^ 2 + ‖G q.1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖X ((-q.2) +ᵥ q.1)‖ - ‖G q.1‖)]
  have hfin : |κ q.2| * (‖X ((-q.2) +ᵥ q.1)‖ * ‖G q.1‖)
      ≤ 2⁻¹ * (|κ q.2| * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2 + ‖G q.1‖ ^ 2 * |κ q.2|) := by
    have := mul_le_mul_of_nonneg_left hyoung hκ0
    nlinarith [this]
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul]
  linarith [hstep, hfin]

/-- **The pairing formula for a mollification.**  Testing a mollified field
against another stationary `L²` field distributes the kernel over the Koopman
translates. -/
theorem integral_inner_mollify {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X G : Ω → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (hGm : StronglyMeasurable G) (hG : MemLp G 2 μ) :
    ∫ ω, inner ℝ (mollify κ X ω) (G ω) ∂μ
      = ∫ y, κ y * ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (G ω) ∂μ := by
  have hprod := integrable_prod_weighted_inner_comp_vadd (μ := μ) hκc hκi hXm hX hGm hG
  have hpt : ∀ᵐ ω ∂μ, inner ℝ (mollify κ X ω) (G ω)
      = ∫ y, κ y * inner ℝ (X ((-y) +ᵥ ω)) (G ω) := by
    filter_upwards [ae_integrable_smul_comp_vadd (μ := μ) hκc hκi hXm hX] with ω hω
    have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ (G ω)) hω
    have hlhs : (innerSL ℝ (G ω)) (mollify κ X ω)
        = inner ℝ (mollify κ X ω) (G ω) := by
      rw [innerSL_apply_apply, real_inner_comm]
    have hrhs : ∀ y : Vec d, (innerSL ℝ (G ω)) (κ y • X ((-y) +ᵥ ω))
        = κ y * inner ℝ (X ((-y) +ᵥ ω)) (G ω) := by
      intro y
      rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
    have hmoll : mollify κ X ω = ∫ y, κ y • X ((-y) +ᵥ ω) := rfl
    rw [← hlhs, hmoll, ← h]
    exact integral_congr_ae (Filter.Eventually.of_forall hrhs)
  rw [integral_congr_ae hpt, integral_integral_swap hprod]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => integral_const_mul _ _)

/-- The pairing formula at the level of `L²` classes. -/
theorem inner_toLp_mollify {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X : Ω → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (G : Lp E 2 μ) :
    inner ℝ ((memLp_two_mollify hκc hκi hXm hX).toLp (mollify κ X)) G
      = ∫ y, κ y * inner ℝ (koopman (μ := μ) (-y) (hX.toLp X)) G := by
  classical
  set G₀ : Ω → E := (Lp.aestronglyMeasurable G).mk G with hG₀def
  have hG₀m : StronglyMeasurable G₀ := (Lp.aestronglyMeasurable G).stronglyMeasurable_mk
  have hG₀ae : ⇑G =ᵐ[μ] G₀ := (Lp.aestronglyMeasurable G).ae_eq_mk
  have hG₀L : MemLp G₀ 2 μ := (Lp.memLp G).ae_eq hG₀ae
  have hG₀toLp : hG₀L.toLp G₀ = G := by
    rw [MemLp.toLp_congr hG₀L (Lp.memLp G) hG₀ae.symm, Lp.toLp_coeFn]
  rw [← hG₀toLp, inner_toLp_toLp, integral_inner_mollify hκc hκi hXm hX hG₀m hG₀L]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [inner_koopman_toLp_toLp hX hG₀L (-y)])

end Pairing

/-! ### Mollification preserves the stationary Helmholtz splitting -/

section Splitting

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **Mollification preserves the stationary solenoidal subspace.** -/
theorem toLp_mollify_mem_stationarySolenoidalSubspace {κ : Vec d → ℝ}
    (hκc : Continuous κ) (hκi : Integrable κ volume) {X : Ω → HilbertVec d}
    (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    (memLp_two_mollify hκc hκi hXm hX).toLp (mollify κ X)
      ∈ stationarySolenoidalSubspace (μ := μ) (d := d) := by
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hzero : ∀ y : Vec d,
      κ y * inner ℝ (koopman (μ := μ) (-y) (hX.toLp X)) u = 0 := by
    intro y
    have hk : koopman (μ := μ) (-y) (hX.toLp X)
        ∈ stationarySolenoidalSubspace (μ := μ) (d := d) :=
      koopman_mem_stationarySolenoidalSubspace (-y) hmem
    have h := (Submodule.mem_orthogonal _ _).1 hk u hu
    rw [real_inner_comm] at h
    rw [h, mul_zero]
  have hpair := inner_toLp_mollify hκc hκi hXm hX u
  rw [integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero] at hpair
  rw [real_inner_comm]
  exact hpair

/-- **Mollification preserves the stationary potential subspace.** -/
theorem toLp_mollify_mem_stationaryPotentialSubspace {κ : Vec d → ℝ}
    (hκc : Continuous κ) (hκi : Integrable κ volume) {X : Ω → HilbertVec d}
    (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hmem : hX.toLp X ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    (memLp_two_mollify hκc hκi hXm hX).toLp (mollify κ X)
      ∈ stationaryPotentialSubspace (μ := μ) (d := d) := by
  have hpot : (stationarySolenoidalSubspace (μ := μ) (d := d))ᗮ
      = stationaryPotentialSubspace (μ := μ) (d := d) :=
    Submodule.orthogonal_orthogonal _
  rw [← hpot]
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hzero : ∀ y : Vec d,
      κ y * inner ℝ (koopman (μ := μ) (-y) (hX.toLp X)) u = 0 := by
    intro y
    have hk : koopman (μ := μ) (-y) (hX.toLp X)
        ∈ stationaryPotentialSubspace (μ := μ) (d := d) :=
      koopman_mem_stationaryPotentialSubspace (-y) hmem
    have h := (Submodule.mem_orthogonal _ _).1 hu _ hk
    rw [h, mul_zero]
  have hpair := inner_toLp_mollify hκc hκi hXm hX u
  rw [integral_congr_ae (Filter.Eventually.of_forall hzero), integral_zero] at hpair
  rw [real_inner_comm]
  exact hpair

/-- **The Helmholtz reduction.** -/
theorem norm_toLp_mollify_le_of_helmholtz {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {f p j : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ)
    (hjdef : ∀ ω, j ω = f ω + p ω)
    (hpmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hjmem : hj.toLp j ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    ‖(memLp_two_mollify hκc hκi hjm hj).toLp (mollify κ j)‖
      ≤ ‖(memLp_two_mollify hκc hκi hfm hf).toLp (mollify κ f)‖ := by
  set AJ := (memLp_two_mollify hκc hκi hjm hj).toLp (mollify κ j) with hAJ
  set Af := (memLp_two_mollify hκc hκi hfm hf).toLp (mollify κ f) with hAf
  set Ap := (memLp_two_mollify hκc hκi hpm hp).toLp (mollify κ p) with hAp
  have hsplit : AJ = Af + Ap := by
    refine Lp.ext ?_
    filter_upwards [(memLp_two_mollify hκc hκi hjm hj).coeFn_toLp,
      Lp.coeFn_add Af Ap,
      (memLp_two_mollify hκc hκi hfm hf).coeFn_toLp,
      (memLp_two_mollify hκc hκi hpm hp).coeFn_toLp,
      ae_integrable_smul_comp_vadd (μ := μ) hκc hκi hfm hf,
      ae_integrable_smul_comp_vadd (μ := μ) hκc hκi hpm hp] with ω h1 h2 h3 h4 h5 h6
    rw [h1, h2, Pi.add_apply, h3, h4]
    show (∫ y, κ y • j ((-y) +ᵥ ω))
      = (∫ y, κ y • f ((-y) +ᵥ ω)) + ∫ y, κ y • p ((-y) +ᵥ ω)
    rw [← integral_add h5 h6]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [hjdef, smul_add])
  have hAJmem : AJ ∈ stationarySolenoidalSubspace (μ := μ) (d := d) :=
    toLp_mollify_mem_stationarySolenoidalSubspace hκc hκi hjm hj hjmem
  have hApmem : Ap ∈ stationaryPotentialSubspace (μ := μ) (d := d) :=
    toLp_mollify_mem_stationaryPotentialSubspace hκc hκi hpm hp hpmem
  have hortho : inner ℝ AJ Ap = 0 := by
    have h := (Submodule.mem_orthogonal _ _).1 hAJmem Ap hApmem
    rwa [real_inner_comm] at h
  have hsq : ‖AJ‖ ^ 2 = inner ℝ AJ Af := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 2 [hsplit]
    rw [inner_add_right, hortho, add_zero]
  have hcs : inner ℝ AJ Af ≤ ‖AJ‖ * ‖Af‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg AJ) with h0 | h0
  · rw [← h0]
    exact norm_nonneg Af
  · have hmul : ‖AJ‖ * ‖AJ‖ ≤ ‖AJ‖ * ‖Af‖ := by nlinarith [hsq, hcs]
    exact le_of_mul_le_mul_left hmul h0


end Splitting

/-! ### The decorrelation bound -/

section Decorrelation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [MeasurableVAdd₂ (Vec d) Ω] [SFinite μ] [CompleteSpace E] in
theorem integrable_inner_comp_vadd {X : Ω → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (w : Vec d) :
    Integrable (fun ω => inner ℝ (X (w +ᵥ ω)) (X ω)) μ := by
  have hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hXwsq : Integrable (fun ω => ‖X (w +ᵥ ω)‖ ^ 2) μ :=
    integrable_comp_const_vadd hXsq w
  refine Integrable.mono' ((hXwsq.add hXsq).const_mul (2⁻¹ : ℝ))
    (((hXm.comp_measurable (measurable_const_vadd w)).inner hXm)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have hcs : |inner ℝ (X (w +ᵥ ω)) (X ω)| ≤ ‖X (w +ᵥ ω)‖ * ‖X ω‖ :=
    abs_real_inner_le_norm _ _
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  nlinarith [hcs, sq_nonneg (‖X (w +ᵥ ω)‖ - ‖X ω‖)]

omit [MeasurableVAdd₂ (Vec d) Ω] [SFinite μ] [CompleteSpace E] in
theorem abs_integral_inner_comp_vadd_le {X : Ω → E} (hXm : StronglyMeasurable X)
    (hX : MemLp X 2 μ) (w : Vec d) :
    |∫ ω, inner ℝ (X (w +ᵥ ω)) (X ω) ∂μ| ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  have hXsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hXwsq : Integrable (fun ω => ‖X (w +ᵥ ω)‖ ^ 2) μ :=
    integrable_comp_const_vadd hXsq w
  have hprod := integrable_inner_comp_vadd (μ := μ) hXm hX w
  have hval : ∫ ω, ‖X (w +ᵥ ω)‖ ^ 2 ∂μ = ∫ ω, ‖X ω‖ ^ 2 ∂μ :=
    integral_comp_const_vadd (fun ω => ‖X ω‖ ^ 2) w
  calc |∫ ω, inner ℝ (X (w +ᵥ ω)) (X ω) ∂μ|
      ≤ ∫ ω, |inner ℝ (X (w +ᵥ ω)) (X ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2⁻¹ * (‖X (w +ᵥ ω)‖ ^ 2 + ‖X ω‖ ^ 2) ∂μ := by
        refine integral_mono hprod.abs ((hXwsq.add hXsq).const_mul (2⁻¹ : ℝ)) fun ω => ?_
        have hcs : |inner ℝ (X (w +ᵥ ω)) (X ω)| ≤ ‖X (w +ᵥ ω)‖ * ‖X ω‖ :=
          abs_real_inner_le_norm _ _
        nlinarith [hcs, sq_nonneg (‖X (w +ᵥ ω)‖ - ‖X ω‖)]
    _ = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
        rw [integral_const_mul, integral_add hXwsq hXsq, hval]
        ring

/-- **The decorrelation bound.** -/
theorem integral_normSq_mollify_le_of_covariance_support
    {κ : Vec d → ℝ} (hκ0 : ∀ y, 0 ≤ κ y) (hκc : Continuous κ)
    (hκi : Integrable κ volume) (hκ1 : ∫ y, κ y = 1) {M : ℝ} (hκM : ∀ y, κ y ≤ M)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) {ρ : ℝ}
    (hcov : ∀ w : Vec d, ρ ≤ ‖w‖ → ∫ ω, inner ℝ (X (w +ᵥ ω)) (X ω) ∂μ = 0) :
    ∫ ω, ‖mollify κ X ω‖ ^ 2 ∂μ
      ≤ M * (volume (Metric.ball (0 : Vec d) ρ)).toReal * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  classical
  set C : ℝ := ∫ ω, ‖X ω‖ ^ 2 ∂μ with hCdef
  set V : ℝ := (volume (Metric.ball (0 : Vec d) ρ)).toReal with hVdef
  have hC0 : 0 ≤ C := integral_nonneg fun ω => by positivity
  have hM0 : 0 ≤ M := le_trans (hκ0 0) (hκM 0)
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hAm : StronglyMeasurable (mollify κ X) := stronglyMeasurable_mollify hκc hXm
  have hA : MemLp (mollify κ X) 2 μ := memLp_two_mollify hκc hκi hXm hX
  -- the pointwise bound on the pairing against a Koopman translate
  have hkey : ∀ y : Vec d,
      |∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ| ≤ M * C * V := by
    intro y
    have hGm : StronglyMeasurable (fun ω => X ((-y) +ᵥ ω)) :=
      hXm.comp_measurable (measurable_const_vadd _)
    have hG : MemLp (fun ω => X ((-y) +ᵥ ω)) 2 μ :=
      hX.comp_measurePreserving (measurePreserving_const_vadd (μ := μ) (-y))
    have hswap : ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ
        = ∫ ω, inner ℝ (mollify κ X ω) (X ((-y) +ᵥ ω)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => real_inner_comm _ _)
    have hshift : ∀ z : Vec d, ∫ ω, inner ℝ (X ((-z) +ᵥ ω)) (X ((-y) +ᵥ ω)) ∂μ
        = ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ := by
      intro z
      have h := integral_comp_const_vadd (μ := μ)
        (fun ω => inner ℝ (X ((-z) +ᵥ ω)) (X ((-y) +ᵥ ω))) y
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [vadd_vadd, neg_add_cancel, zero_vadd, neg_add_eq_sub]
    have hprod := integrable_prod_weighted_inner_comp_vadd (μ := μ) hκc hκi hXm hX hGm hG
    have hint0 : Integrable
        (fun z : Vec d =>
          ∫ ω, κ z * inner ℝ (X ((-z) +ᵥ ω)) (X ((-y) +ᵥ ω)) ∂μ) volume :=
      hprod.swap.integral_prod_left
    have hcong : ∀ z : Vec d,
        (∫ ω, κ z * inner ℝ (X ((-z) +ᵥ ω)) (X ((-y) +ᵥ ω)) ∂μ)
          = κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ := by
      intro z
      rw [integral_const_mul, hshift z]
    have hint : Integrable
        (fun z : Vec d => κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ) volume :=
      hint0.congr (Filter.Eventually.of_forall hcong)
    have hindic : Integrable
        (Set.indicator (Metric.ball y ρ) (fun _ : Vec d => M * C)) volume :=
      (integrable_indicator_iff measurableSet_ball).2
        (integrableOn_const (measure_ball_lt_top).ne)
    have hbd : ∀ z : Vec d,
        |κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ|
          ≤ Set.indicator (Metric.ball y ρ) (fun _ : Vec d => M * C) z := by
      intro z
      by_cases hz : z ∈ Metric.ball y ρ
      · rw [Set.indicator_of_mem hz, abs_mul, abs_of_nonneg (hκ0 z)]
        exact mul_le_mul (hκM z) (abs_integral_inner_comp_vadd_le hXm hX _)
          (abs_nonneg _) hM0
      · rw [Set.indicator_of_notMem hz]
        have hnorm : ρ ≤ ‖y - z‖ := by
          simp only [Metric.mem_ball, not_lt] at hz
          rw [dist_eq_norm] at hz
          rwa [norm_sub_rev]
        rw [hcov _ hnorm, mul_zero, abs_zero]
    have heq : (∫ z, κ z * ∫ ω, inner ℝ (X ((-z) +ᵥ ω)) (X ((-y) +ᵥ ω)) ∂μ)
        = ∫ z, κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [hshift z])
    rw [hswap, integral_inner_mollify hκc hκi hXm hX hGm hG, heq]
    calc |∫ z, κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ|
        ≤ ∫ z, |κ z * ∫ ω, inner ℝ (X ((y - z) +ᵥ ω)) (X ω) ∂μ| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z, Set.indicator (Metric.ball y ρ) (fun _ : Vec d => M * C) z :=
          integral_mono hint.abs hindic hbd
      _ = M * C * V := by
          rw [integral_indicator_const (M * C) measurableSet_ball, measureReal_def,
            Measure.addHaar_ball_center volume y ρ, ← hVdef, smul_eq_mul]
          ring
  -- assemble
  have hfinal : ∫ ω, ‖mollify κ X ω‖ ^ 2 ∂μ
      = ∫ y, κ y * ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ := by
    rw [← integral_inner_mollify hκc hκi hXm hX hAm hA]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      (real_inner_self_eq_norm_sq _).symm)
  have hprodA := integrable_prod_weighted_inner_comp_vadd (μ := μ) hκc hκi hXm hX hAm hA
  have hintA0 : Integrable
      (fun y : Vec d =>
        ∫ ω, κ y * inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ) volume :=
    hprodA.swap.integral_prod_left
  have hintA : Integrable
      (fun y : Vec d => κ y * ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ) volume :=
    hintA0.congr (Filter.Eventually.of_forall fun y => integral_const_mul _ _)
  rw [hfinal]
  calc ∫ y, κ y * ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ
      ≤ ∫ y, κ y * (M * C * V) := by
        refine integral_mono hintA (hκi.mul_const _) fun y => ?_
        have h1 := hkey y
        have h2 : ∫ ω, inner ℝ (X ((-y) +ᵥ ω)) (mollify κ X ω) ∂μ ≤ M * C * V :=
          le_trans (le_abs_self _) h1
        exact mul_le_mul_of_nonneg_left h2 (hκ0 y)
    _ = M * V * C := by
        rw [integral_mul_const, hκ1, one_mul]
        ring


end Decorrelation

/-! ### The fresh-shell decorrelation kill -/

section Kill

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The decorrelation kill for the stationary solenoidal flux.**

Let `𝐣 = 𝐟 + p` be the stationary Helmholtz splitting of ABK26: `p = ∇w` lies in
`L²_pot(Ω)` and the flux `𝐣` lies in `L²_sol(Ω)`.  Suppose the *forcing* `𝐟` has
a covariance supported in the ball of radius `ρ` — which is exactly what a
finite range of dependence together with a vanishing mean supplies.  Then for
every probability density `κ` bounded by `M`,

`E[|A_κ 𝐣|²] ≤ M · |B_ρ| · E[|𝐟|²]`.

Along any family of densities whose sup norms tend to `0` the right-hand side
tends to `0`, so the translation-invariant part of the flux is annihilated even
though the flux itself has no finite range of dependence.  No ergodic theorem,
no Liouville argument and no resolvent is used.

**Disclosure.**  This is the `Ω`-level decorrelation input of part (ii) of
`l.approximation.stationary.by.local`, not part (ii) itself, and it claims no
node status. -/
theorem integral_normSq_mollify_le_of_helmholtz_of_covariance_support
    {κ : Vec d → ℝ} (hκ0 : ∀ y, 0 ≤ κ y) (hκc : Continuous κ)
    (hκi : Integrable κ volume) (hκ1 : ∫ y, κ y = 1) {M : ℝ} (hκM : ∀ y, κ y ≤ M)
    {f p j : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ)
    (hjdef : ∀ ω, j ω = f ω + p ω)
    (hpmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hjmem : hj.toLp j ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) {ρ : ℝ}
    (hcov : ∀ w : Vec d, ρ ≤ ‖w‖ → ∫ ω, inner ℝ (f (w +ᵥ ω)) (f ω) ∂μ = 0) :
    ∫ ω, ‖mollify κ j ω‖ ^ 2 ∂μ
      ≤ M * (volume (Metric.ball (0 : Vec d) ρ)).toReal * ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have h1 : ∫ ω, ‖mollify κ j ω‖ ^ 2 ∂μ
      = ‖(memLp_two_mollify hκc hκi hjm hj).toLp (mollify κ j)‖ ^ 2 :=
    integral_normSq_eq_norm_sq_toLp (memLp_two_mollify hκc hκi hjm hj)
  have h2 : ∫ ω, ‖mollify κ f ω‖ ^ 2 ∂μ
      = ‖(memLp_two_mollify hκc hκi hfm hf).toLp (mollify κ f)‖ ^ 2 :=
    integral_normSq_eq_norm_sq_toLp (memLp_two_mollify hκc hκi hfm hf)
  have h3 := norm_toLp_mollify_le_of_helmholtz hκc hκi hfm hf hpm hp hjm hj hjdef
    hpmem hjmem
  have h4 := integral_normSq_mollify_le_of_covariance_support hκ0 hκc hκi hκ1 hκM
    hfm hf hcov
  have h5 : ∫ ω, ‖mollify κ j ω‖ ^ 2 ∂μ ≤ ∫ ω, ‖mollify κ f ω‖ ^ 2 ∂μ := by
    rw [h1, h2]
    nlinarith [h3, norm_nonneg ((memLp_two_mollify hκc hκi hjm hj).toLp (mollify κ j)),
      norm_nonneg ((memLp_two_mollify hκc hκi hfm hf).toLp (mollify κ f))]
  linarith [h4, h5]

end Kill

end

end Algsuperdiff.Section3.Provider.Corrector
