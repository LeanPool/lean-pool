/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.CorrectorLimitFreshShell
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.OmegaStreamAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalApproximationEps
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# CorrectorLimitNode

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the corrector-limit lemma at the fresh shell

ABK26, Lemma `l.corrector.limit`, specialized to the fresh shell.

`Algsuperdiff/Section3/Provider/Corrector/CorrectorLimitFreshShell.lean` proves
Step 4 modulo an *exact* Ω-level antisymmetric stream for the flux, and modulo
the sample-integrability of the two cube energies.  This file removes both.

## Removing the stream, the tolerance and the scale

The stream the repository can build — `exists_freshShellStream` of
`Algsuperdiff/Section3/Provider/Corrector/OmegaStreamAssembly.lean` — represents
the flux only up to an `L²(Ω)` tolerance.  Two parameters are eliminated:

* the tolerance `ε`, by
  `Algsuperdiff/Section3/Provider/Corrector/SolenoidalApproximationEps.lean`,
  where the gap `E[|D − j|²]` is shown to be independent of the cube and is
  chosen after the Young parameter; and
* the localization scale `L`, which is chosen after the stream and before the
  cube, exactly as in the exact-stream proof.

## Removing the integrability hypotheses

`integrable_cubeAverage_dirichlet_energy` and
`integrable_cubeAverage_neumann_energy` below show that the cube energy of
*any* family satisfying the weak formulation of `e.corrector.limit.pde` is
automatically integrable in the sample — **no** measurability of the family in
the sample is assumed. The mechanism is the variational characterization of the
two cube problems. Writing `U = cu_K`, `F = f(· + ω)` and `⟪·,·⟫` for the
`L²(U)` pairing, the Dirichlet gradient `D` satisfies

`∫_U |D|² = sup { -2⟪F, v⟫ - ⟪v, v⟫ : v ∈ L²_{pot,0}(U) }`,

the supremum being attained at `v = D` because `⟪D + F, D⟫ = 0`; the Neumann
gradient satisfies the same identity with `L²_{pot}(U)` in place of
`L²_{pot,0}(U)`.  Since `L²(U; ℝᵈ)` is second countable, the admissible class
has a *countable* dense subset and the supremum may be restricted to it.  Each
member of the resulting countable family contributes a genuinely measurable
function of the sample — the competitor is a fixed field, so the sample
dependence enters only through the realization `F`, which is jointly measurable
by
`Algsuperdiff.Section3.Provider.Corrector.stronglyMeasurable_uncurry_realize`.
The energy is therefore a countable supremum of measurable functions, hence
measurable, and the a priori bound `∫_U |D|² ≤ ∫_U |F|²` (the Hoelder display in
Step 2; it is NOT `e.lower.bound.corrector.limit`, which is the separate
lower-bound display) dominates it by an integrable function.

## What the fresh-shell theorem takes

Only the manuscript's own hypothesis "let `w_D^{(K)}`, `w_N^{(K)} ` be the
solutions" of `e.corrector.limit.pde`: the two gradient families enter as
`Dfam`, `Nfam` carrying the weak formulations of that display, and nothing else.
Existence of the two cube solutions at every sample is unconditional — the
fresh-shell forcing has continuous realizations, and
`Algsuperdiff/Section3/Provider/Diffusivity/Corrector/FreshShellExistence.lean`
solves both cube problems for every continuous forcing — and their gradients are
unique.

## The concrete-witness discipline

CoarseGraining's `IsSolenoidalZeroNormalTraceOn U g` is orthogonality to
`∇H¹(U)` and carries no square integrability.  The Neumann half below is
therefore routed through the *concrete* competitor family `localStreamApprox`
and its companion per-sample membership, never through an existential witness
of that predicate; see the module docstring of
`SolenoidalApproximationEps.lean`.
-/

open MeasureTheory
open HCPolySupport
open scoped ENNReal

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

/-! ### The deterministic comparison lemmas, in tested form

`Algsuperdiff/Section3/Provider/Corrector/CubeComparison.lean` proves these for
the Dirichlet weak formulation.  Here the weak formulation enters only through
the single scalar identity `∫_U (D + F) · v = 0`, so one set of lemmas serves
both the Dirichlet and the Neumann cube problem. -/

section Deterministic

variable {d : ℕ}

/-- Splitting the tested flux into its two square-integrable halves. -/
private theorem setIntegral_vecDot_add_left_split {U : Set (Vec d)} {D F v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F) (hv : MemVectorL2 U v) :
    ∫ x in U, vecDot (D x + F x) (v x)
      = (∫ x in U, vecDot (D x) (v x)) + ∫ x in U, vecDot (F x) (v x) := by
  rw [← integral_add (integrableOn_vecDot_of_memVectorL2 hD hv)
    (integrableOn_vecDot_of_memVectorL2 hF hv)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => vecDot_add_left _ _ _)

/-- **Step 2 of `l.corrector.limit`, tested form.**  If the flux `D + F` is
orthogonal to the competitor `v`, then `-2 ∫ F · v - ∫ |v|² ≤ ∫ |D|²`.  This is
`Algsuperdiff.Section3.Provider.Corrector.setIntegral_vecDot_self_ge_of_isSolenoidalOn`
with the weak formulation replaced by the single identity it supplies. -/
private theorem setIntegral_vecDot_self_ge_of_test {U : Set (Vec d)} {D F v : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F) (hv : MemVectorL2 U v)
    (h0 : ∫ x in U, vecDot (D x + F x) (v x) = 0) :
    -2 * (∫ x in U, vecDot (F x) (v x)) - (∫ x in U, vecDot (v x) (v x))
      ≤ ∫ x in U, vecDot (D x) (D x) := by
  have hDv : IntegrableOn (fun x => vecDot (D x) (v x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hv
  have hDD : IntegrableOn (fun x => vecDot (D x) (D x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hD
  have hvv : IntegrableOn (fun x => vecDot (v x) (v x)) U :=
    integrableOn_vecDot_of_memVectorL2 hv hv
  have hsplit := setIntegral_vecDot_add_left_split hD hF hv
  rw [h0] at hsplit
  have hnn : 0 ≤ ∫ x in U, vecDot (D x - v x) (D x - v x) :=
    integral_nonneg fun x => vecDot_self_nonneg _
  have hexp : ∫ x in U, vecDot (D x - v x) (D x - v x)
      = (∫ x in U, vecDot (D x) (D x)) - 2 * (∫ x in U, vecDot (D x) (v x))
        + ∫ x in U, vecDot (v x) (v x) := by
    have hpt : ∀ x, vecDot (D x - v x) (D x - v x)
        = vecDot (D x) (D x) - 2 * vecDot (D x) (v x) + vecDot (v x) (v x) := fun x =>
      vecDot_sub_self _ _
    have h1 : ∫ x in U, (vecDot (D x) (D x) - 2 * vecDot (D x) (v x)
          + vecDot (v x) (v x))
        = (∫ x in U, (vecDot (D x) (D x) - 2 * vecDot (D x) (v x)))
          + ∫ x in U, vecDot (v x) (v x) :=
      integral_add (hDD.sub (hDv.const_mul 2)) hvv
    have h2 : ∫ x in U, (vecDot (D x) (D x) - 2 * vecDot (D x) (v x))
        = (∫ x in U, vecDot (D x) (D x)) - ∫ x in U, 2 * vecDot (D x) (v x) :=
      integral_sub hDD (hDv.const_mul 2)
    have h3 : ∫ x in U, 2 * vecDot (D x) (v x)
        = 2 * ∫ x in U, vecDot (D x) (v x) := integral_const_mul 2 _
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), h1, h2, h3]
  rw [hexp] at hnn
  linarith

/-- The supremum in the variational characterization is *attained* at the
solution itself: testing the flux against `D` turns the Step-2 lower bound into
an equality. -/
private theorem setIntegral_vecDot_self_eq_of_test {U : Set (Vec d)} {D F : Vec d → Vec d}
    (hD : MemVectorL2 U D) (hF : MemVectorL2 U F)
    (h0 : ∫ x in U, vecDot (D x + F x) (D x) = 0) :
    -2 * (∫ x in U, vecDot (F x) (D x)) - (∫ x in U, vecDot (D x) (D x))
      = ∫ x in U, vecDot (D x) (D x) := by
  have hsplit := setIntegral_vecDot_add_left_split hD hF hD
  rw [h0] at hsplit
  linarith

/-- **The a priori bound `‖∇w‖ ≤ ‖f‖`, tested form**.  This is
`Algsuperdiff.Section3.Provider.Corrector.setIntegral_vecDot_self_le_forcing`
with the weak formulation replaced by the single identity it supplies, so that
it applies verbatim to the Neumann cube problem as well. -/
private theorem setIntegral_vecDot_self_le_forcing_of_test {U : Set (Vec d)}
    {D F : Vec d → Vec d} (hD : MemVectorL2 U D) (hF : MemVectorL2 U F)
    (h0 : ∫ x in U, vecDot (D x + F x) (D x) = 0) :
    (∫ x in U, vecDot (D x) (D x)) ≤ ∫ x in U, vecDot (F x) (F x) := by
  have heq := setIntegral_vecDot_self_eq_of_test hD hF h0
  have hflux := setIntegral_vecDot_flux_eq hF hD
  have hnn : 0 ≤ ∫ x in U, vecDot (D x + F x) (D x + F x) :=
    integral_nonneg fun x => vecDot_self_nonneg _
  linarith

end Deterministic

/-! ### The admissible competitors as a subset of `L²(U; ℝᵈ)` -/

/-- The `L²(U; ℝᵈ)` image of the admissible class `P`.  For the Dirichlet cube
problem `P` is `Homogenization.IsPotentialZeroTraceOn U`, for the Neumann cube
problem `Homogenization.IsPotentialOn U`.  Only its separability is used, so no
submodule structure is needed. -/
def admissibleL2Set {d : ℕ} (U : Set (Vec d)) (P : (Vec d → Vec d) → Prop) :
    Set (HilbertVectorL2 U) :=
  {H | ∃ g, ∃ hg : MemVectorL2 U g, toHilbertVectorL2OfVecField hg = H ∧ P g}

private theorem mem_admissibleL2Set {d : ℕ} {U : Set (Vec d)}
    {P : (Vec d → Vec d) → Prop} {H : HilbertVectorL2 U} :
    H ∈ admissibleL2Set U P ↔
      ∃ g, ∃ hg : MemVectorL2 U g, toHilbertVectorL2OfVecField hg = H ∧ P g :=
  Iff.rfl

/-! ### The variational representation and its consequences -/

section Core

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- **The energy of a cube corrector is automatically sample integrable.**

`Dfam` is an arbitrary family of vector fields on a set `U` of finite volume —
no measurability in the sample is assumed — subject only to

* `hDP`: at almost every sample `Dfam ω` is an admissible competitor, and
* `htest`: at almost every sample the flux `Dfam ω + f(· + ω)` is orthogonal in
  `L²(U)` to *every* admissible competitor.

Those are exactly the two halves of the weak formulation of the cube problem
`e.corrector.limit.pde`, the class `P` being the zero-trace potential fields in
the Dirichlet case and all potential fields in the Neumann case.  Under them the
energy `ω ↦ ∫_U |Dfam ω|²` is integrable. -/
private theorem integrable_setIntegral_energy_of_test
    {U : Set (Vec d)} (hUfin : volume U ≠ ⊤) {f : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    {Dfam : Ω → (Vec d → Vec d)} {P : (Vec d → Vec d) → Prop}
    (hP0 : P 0) (hPmem : ∀ v, P v → MemVectorL2 U v)
    (hDP : ∀ᵐ ω ∂μ, P (Dfam ω))
    (htest : ∀ᵐ ω ∂μ, ∀ v, P v →
      ∫ x in U, vecDot (Dfam ω x + (realize f ω x).toVec) (v x) = 0) :
    Integrable (fun ω => ∫ x in U, vecDot (Dfam ω x) (Dfam ω x)) μ := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  -- Almost every realization is square integrable on `U`.
  have hFae : ∀ᵐ ω ∂μ, MemVectorL2 U fun x => (realize f ω x).toVec := by
    filter_upwards [ae_memLp_two_realize (μ := μ) hUfin hfm hf] with ω hω
    exact memVectorL2_toVec_of_memHilbertVectorL2 hω
  -- Step 2: a countable family of admissible competitors, dense in `L²(U;ℝᵈ)`.
  have : Nonempty (admissibleL2Set U P) :=
    ⟨⟨toHilbertVectorL2OfVecField (hPmem 0 hP0),
      mem_admissibleL2Set.2 ⟨0, hPmem 0 hP0, rfl, hP0⟩⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (admissibleL2Set U P)
  choose w hwmem hwL hwP using fun n : ℕ => mem_admissibleL2Set.1 (u n).2
  -- Step 4 preparation: strongly measurable representatives of the competitors.
  have hwrep : ∀ n : ℕ, ∃ v : Vec d → Vec d,
      StronglyMeasurable v ∧ w n =ᵐ[volume.restrict U] v := fun n =>
    ⟨(hwmem n).aestronglyMeasurable.mk (w n),
      (hwmem n).aestronglyMeasurable.stronglyMeasurable_mk,
      (hwmem n).aestronglyMeasurable.ae_eq_mk⟩
  choose w' hw'sm hw'ae using hwrep
  -- Step 3: the countable family of lower bounds.
  obtain ⟨phi, hphi⟩ : ∃ phi : ℕ → Ω → ℝ, phi = fun n ω =>
      -2 * (∫ x in U, vecDot ((realize f ω x).toVec) (w n x))
        - ∫ x in U, vecDot (w n x) (w n x) := ⟨_, rfl⟩
  have hphival : ∀ (n : ℕ) (ω : Ω), phi n ω
      = -2 * (∫ x in U, vecDot ((realize f ω x).toVec) (w n x))
        - ∫ x in U, vecDot (w n x) (w n x) := by
    intro n ω
    simp only [hphi]
  -- Step 4: each lower bound is a measurable function of the sample.
  have hphimeas : ∀ n, Measurable (phi n) := by
    intro n
    have hI : (fun ω => ∫ x in U, vecDot ((realize f ω x).toVec) (w n x))
        = fun ω => ∫ x in U, vecDot ((realize f ω x).toVec) (w' n x) := by
      funext ω
      refine integral_congr_ae ?_
      filter_upwards [hw'ae n] with x hx
      rw [hx]
    have hjoint : StronglyMeasurable fun q : Ω × Vec d =>
        vecDot ((realize f q.1 q.2).toVec) (w' n q.2) := by
      have h1 : StronglyMeasurable fun q : Ω × Vec d => realize f q.1 q.2 :=
        stronglyMeasurable_uncurry_realize hfm
      have h2 : StronglyMeasurable fun q : Ω × Vec d =>
          HilbertVec.ofVec (w' n q.2) :=
        (HilbertVec.continuousLinearEquivVec d).symm.continuous.comp_stronglyMeasurable
          ((hw'sm n).comp_measurable measurable_snd)
      have h3 : (fun q : Ω × Vec d => vecDot ((realize f q.1 q.2).toVec) (w' n q.2))
          = fun q : Ω × Vec d =>
            (inner ℝ (realize f q.1 q.2) (HilbertVec.ofVec (w' n q.2)) : ℝ) := by
        funext q
        rw [HilbertVec.inner_def, HilbertVec.toVec_ofVec]
      rw [h3]
      exact h1.inner h2
    have hint : StronglyMeasurable fun ω =>
        ∫ x in U, vecDot ((realize f ω x).toVec) (w' n x) :=
      hjoint.integral_prod_right'
    have hImeas : Measurable fun ω => ∫ x in U, vecDot ((realize f ω x).toVec) (w n x) := by
      rw [hI]
      exact hint.measurable
    simp only [hphi]
    exact (hImeas.const_mul (-2 : ℝ)).sub measurable_const
  -- Step 3: the energy is the supremum of the countable family.
  have hae : (fun ω => ∫ x in U, vecDot (Dfam ω x) (Dfam ω x))
      =ᵐ[μ] fun ω => ⨆ n, phi n ω := by
    filter_upwards [hDP, htest, hFae] with ω hD hT hFU
    have hDU : MemVectorL2 U (Dfam ω) := hPmem _ hD
    have hle : ∀ n, phi n ω ≤ ∫ x in U, vecDot (Dfam ω x) (Dfam ω x) := by
      intro n
      rw [hphival n ω]
      exact setIntegral_vecDot_self_ge_of_test hDU hFU (hwmem n) (hT (w n) (hwP n))
    have hbdd : BddAbove (Set.range fun n => phi n ω) := by
      refine ⟨∫ x in U, vecDot (Dfam ω x) (Dfam ω x), ?_⟩
      rintro y ⟨n, rfl⟩
      exact hle n
    have hkey : ∀ ε : ℝ, 0 < ε →
        (∫ x in U, vecDot (Dfam ω x) (Dfam ω x)) - ε ≤ ⨆ n, phi n ω := by
      intro ε hε
      obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : HilbertVectorL2 U → ℝ, Ψ = fun H =>
          -2 * (inner ℝ (toHilbertVectorL2OfVecField hFU) H : ℝ) - ‖H‖ ^ 2 := ⟨_, rfl⟩
      have hΨval : ∀ {g : Vec d → Vec d} (hg : MemVectorL2 U g),
          Ψ (toHilbertVectorL2OfVecField hg)
            = -2 * (∫ x in U, vecDot ((realize f ω x).toVec) (g x))
              - ∫ x in U, vecDot (g x) (g x) := by
        intro g hg
        simp only [hΨ]
        rw [inner_toHilbertVectorL2OfVecField_eq_integral hFU hg,
          ← real_inner_self_eq_norm_sq,
          inner_toHilbertVectorL2OfVecField_eq_integral hg hg]
      have hΨcont : Continuous Ψ := by
        simp only [hΨ]
        exact (continuous_const.mul (continuous_const.inner continuous_id)).sub
          (continuous_norm.pow 2)
      obtain ⟨δ, hδ, hδΨ⟩ := Metric.continuousAt_iff.1 hΨcont.continuousAt ε hε
      have hHdA : toHilbertVectorL2OfVecField hDU ∈ admissibleL2Set U P :=
        mem_admissibleL2Set.2 ⟨Dfam ω, hDU, rfl, hD⟩
      obtain ⟨n, hn⟩ :=
        Metric.mem_closure_range_iff.1 (hu ⟨toHilbertVectorL2OfVecField hDU, hHdA⟩) δ hδ
      have hn' : dist (toHilbertVectorL2OfVecField hDU) ((u n : HilbertVectorL2 U)) < δ := hn
      have hdist : dist ((u n : HilbertVectorL2 U)) (toHilbertVectorL2OfVecField hDU) < δ := by
        rwa [dist_comm] at hn'
      have hΨun : Ψ ((u n : HilbertVectorL2 U)) = phi n ω := by
        rw [← hwL n, hΨval (hwmem n), hphival n ω]
      have hΨHd : Ψ (toHilbertVectorL2OfVecField hDU)
          = ∫ x in U, vecDot (Dfam ω x) (Dfam ω x) := by
        rw [hΨval hDU]
        exact setIntegral_vecDot_self_eq_of_test hDU hFU (hT (Dfam ω) hD)
      have hfin := hδΨ hdist
      rw [hΨun, hΨHd, Real.dist_eq, abs_lt] at hfin
      exact (by linarith [hfin.1] : (∫ x in U, vecDot (Dfam ω x) (Dfam ω x)) - ε ≤ phi n ω).trans
        (le_ciSup hbdd n)
    refine le_antisymm ?_ (ciSup_le hle)
    by_contra hcon
    push Not at hcon
    have hεpos : 0 < ((∫ x in U, vecDot (Dfam ω x) (Dfam ω x)) - ⨆ n, phi n ω) / 2 := by
      linarith
    have hlast := hkey _ hεpos
    linarith
  -- Step 5: domination by the forcing energy.
  have hbound : ∀ᵐ ω ∂μ,
      ‖∫ x in U, vecDot (Dfam ω x) (Dfam ω x)‖ ≤ ∫ x in U, ‖realize f ω x‖ ^ 2 := by
    filter_upwards [hDP, htest, hFae] with ω hD hT hFU
    have hDU : MemVectorL2 U (Dfam ω) := hPmem _ hD
    have hnn : (0 : ℝ) ≤ ∫ x in U, vecDot (Dfam ω x) (Dfam ω x) :=
      integral_nonneg fun x => vecDot_self_nonneg _
    have hforce := setIntegral_vecDot_self_le_forcing_of_test hDU hFU (hT (Dfam ω) hD)
    have hFsq : (∫ x in U, vecDot ((realize f ω x).toVec) ((realize f ω x).toVec))
        = ∫ x in U, ‖realize f ω x‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x =>
        (HilbertVec.inner_def _ _).symm.trans (real_inner_self_eq_norm_sq _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, ← hFsq]
    exact hforce
  have hdom : Integrable (fun ω => ∫ x in U, ‖realize f ω x‖ ^ 2) μ :=
    integrable_setIntegral_normSq_realize (μ := μ) hUfin hfm hf
  exact hdom.mono' ((Measurable.iSup hphimeas).aestronglyMeasurable.congr hae.symm) hbound

end Core

/-! ### The two cube energies -/

section Geometry

variable {d : ℕ}

/-- The open cube has finite Lebesgue measure. -/
private theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ⊤ :=
  measure_ne_top_of_subset (openCubeSet_subset_cubeSet Q) (volume_cubeSet_lt_top Q).ne

/-- The cube average of an energy density, rewritten as a set integral over the
*open* cube, which is where the two weak formulations live. -/
private theorem cubeAverage_eq_openCubeSet (Q : TriadicCube d) (g : Vec d → ℝ) :
    cubeAverage Q g = (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, g x := by
  simp only [cubeAverage]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

end Geometry

section Main

/-- **The Dirichlet cube energy is automatically sample integrable.**

`Dfam` is any family of vector fields satisfying, at almost every sample, the
weak formulation of the Dirichlet cube problem `-Δ w = ∇·f` in `cu_K`,
`w ∈ H¹₀(cu_K)` of ABK26: `Dfam ω` is a
zero-trace potential field and `Dfam ω + f(· + ω)` is solenoidal.  Nothing is
assumed about the dependence of `Dfam` on the sample.  Then the cube average of
`|Dfam ω|²` is integrable, so that the expectation
`E[‖∇w_D^{(K)}‖²_{L²(cu_K)}]` of the lemma is well defined. -/
theorem integrable_cubeAverage_dirichlet_energy
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.SFinite μ]
    [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
    [MeasureTheory.VAddInvariantMeasure (Vec d) Ω μ]
    (Q : TriadicCube d) {f : Ω → HilbertVec d}
    (hfm : MeasureTheory.StronglyMeasurable f) (hf : MeasureTheory.MemLp f 2 μ)
    {Dfam : Ω → (Vec d → Vec d)}
    (hDpot : ∀ᵐ ω ∂μ, IsPotentialZeroTraceOn (openCubeSet Q) (Dfam ω))
    (hDsol : ∀ᵐ ω ∂μ, IsSolenoidalOn (openCubeSet Q)
      fun x => Dfam ω x + (realize f ω x).toVec) :
    MeasureTheory.Integrable
      (fun ω => cubeAverage Q fun x => vecDot (Dfam ω x) (Dfam ω x)) μ := by
  have htest : ∀ᵐ ω ∂μ, ∀ v, IsPotentialZeroTraceOn (openCubeSet Q) v →
      ∫ x in openCubeSet Q, vecDot (Dfam ω x + (realize f ω x).toVec) (v x) = 0 := by
    filter_upwards [hDsol] with ω hω v hv
    exact setIntegral_vecDot_eq_zero_of_isSolenoidalOn hω hv
  have hcore := integrable_setIntegral_energy_of_test (μ := μ)
    (volume_openCubeSet_ne_top Q) hfm hf
    (P := fun v => IsPotentialZeroTraceOn (openCubeSet Q) v) isPotentialZeroTraceOn_zero
    (fun _ hv => memVectorL2_of_isPotentialZeroTraceOn hv) hDpot htest
  refine (hcore.const_mul (cubeVolume Q)⁻¹).congr ?_
  filter_upwards with ω
  exact (cubeAverage_eq_openCubeSet Q _).symm

/-- **The Neumann cube energy is automatically sample integrable.**

`Nfam` is any family of vector fields satisfying, at almost every sample, the
weak formulation of the Neumann cube problem `-Δ w = ∇·f` in `cu_K`, `n · (∇w +
f) = 0` on `∂cu_K` of ABK26: `Nfam ω` is a potential field and `Nfam ω + f(· +
ω)` is solenoidal with vanishing normal trace.  Nothing is assumed about the
dependence of `Nfam` on the sample.  Then the cube average of `|Nfam ω|²` is
integrable, so that the expectation `E[‖∇w_N^{(K)}‖²_{L²(cu_K)}]` of the lemma
is well defined. -/
theorem integrable_cubeAverage_neumann_energy
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.SFinite μ]
    [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
    [MeasureTheory.VAddInvariantMeasure (Vec d) Ω μ]
    (Q : TriadicCube d) {f : Ω → HilbertVec d}
    (hfm : MeasureTheory.StronglyMeasurable f) (hf : MeasureTheory.MemLp f 2 μ)
    {Nfam : Ω → (Vec d → Vec d)}
    (hNpot : ∀ᵐ ω ∂μ, IsPotentialOn (openCubeSet Q) (Nfam ω))
    (hNsol : ∀ᵐ ω ∂μ, IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      fun x => Nfam ω x + (realize f ω x).toVec) :
    MeasureTheory.Integrable
      (fun ω => cubeAverage Q fun x => vecDot (Nfam ω x) (Nfam ω x)) μ := by
  have htest : ∀ᵐ ω ∂μ, ∀ v, IsPotentialOn (openCubeSet Q) v →
      ∫ x in openCubeSet Q, vecDot (Nfam ω x + (realize f ω x).toVec) (v x) = 0 := by
    filter_upwards [hNsol] with ω hω v hv
    exact setIntegral_vecDot_eq_zero_of_isSolenoidalZeroNormalTraceOn hω hv
  have hcore := integrable_setIntegral_energy_of_test (μ := μ)
    (volume_openCubeSet_ne_top Q) hfm hf
    (P := fun v => IsPotentialOn (openCubeSet Q) v) isPotentialOn_zero
    (fun _ hv => memVectorL2_of_isPotentialOn hv) hNpot htest
  refine (hcore.const_mul (cubeVolume Q)⁻¹).congr ?_
  filter_upwards with ω
  exact (cubeAverage_eq_openCubeSet Q _).symm

end Main

/-! ### The corrector limit for a flux with approximate streams -/

section General

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **`e.corrector.limit`** for a stationary flux possessing approximate
antisymmetric streams at every tolerance.

Let `f` be a stationary square-integrable forcing, let `∇w = p` be the
whole-space stationary corrector gradient — the element of `L²(Ω;ℝᵈ)`
characterized by `∇w ∈ L²_pot(Ω)` (`hpmem`) and `f + ∇w ∈ L²_sol(Ω)`
(`hflux`) — and let `j = f + ∇w` be the stationary flux (`hjdef`).  Let
`∇w_D^{(K)} = Dfam K` and `∇w_N^{(K)} = Nfam K` be the gradients of the two
solutions of `e.corrector.limit.pde`.  Then

`lim_K E[‖∇w_D^{(K)}‖²_{L²(cu_K)}] = lim_K E[‖∇w_N^{(K)}‖²_{L²(cu_K)}]
   = E[|∇w|²]`,

both limits existing.

`hstream` is the *approximate* representation hypothesis, in the exact shape
produced by `exists_freshShellStream`: for every tolerance `η > 0` there is a
stationary square-integrable antisymmetric stream with smooth realizations whose
row divergence is the realization of a stationary square-integrable `D` with
`E[|D − j|²] ≤ η`.  No exact stream is required, no integrability of a cube
energy is assumed, and neither the conclusion nor either one-sided bound is a
hypothesis. -/
theorem tendsto_integral_cubeAverage_dirichlet_neumann_of_approximateStream
    {f p j : Ω → HilbertVec d}
    (hfm : StronglyMeasurable f) (hf : MemLp f 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hpmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (hflux : hf.toLp f + hp.toLp p ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    (hjm : StronglyMeasurable j) (hj : MemLp j 2 μ)
    (hjdef : ∀ ω : Ω, j ω = p ω + f ω)
    (hstream : ∀ η : ℝ, 0 < η →
      ∃ S : Ω → (Fin d → HilbertVec d), ∃ D : Ω → HilbertVec d,
        StronglyMeasurable S ∧ MemLp S 2 μ ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i m)) ∧
        (∀ᵐ ω ∂μ, ∀ i m : Fin d,
          streamRealization S ω m i = -streamRealization S ω i m) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vec d,
          streamDivergence (streamRealization S ω) x = (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 μ ∧
        ∫ ω, ‖D ω - j ω‖ ^ 2 ∂μ ≤ η)
    {Dfam Nfam : ℕ → Ω → (Vec d → Vec d)}
    (hDpot : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsPotentialZeroTraceOn (openCubeSet (originCube d (K : ℤ))) (Dfam K ω))
    (hDsol : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsSolenoidalOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Dfam K ω x + (realize f ω x).toVec)
    (hNpot : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsPotentialOn (openCubeSet (originCube d (K : ℤ))) (Nfam K ω))
    (hNsol : ∀ K : ℕ, ∀ᵐ ω ∂μ,
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Nfam K ω x + (realize f ω x).toVec) :
    Filter.Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot (Dfam K ω x) (Dfam K ω x)) ∂μ) Filter.atTop
        (nhds (∫ ω, ‖p ω‖ ^ 2 ∂μ))
      ∧ Filter.Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot (Nfam K ω x) (Nfam K ω x)) ∂μ) Filter.atTop
          (nhds (∫ ω, ‖p ω‖ ^ 2 ∂μ)) := by
  have hDint : ∀ K : ℕ, Integrable (fun ω => cubeAverage (originCube d (K : ℤ))
      fun x => vecDot (Dfam K ω x) (Dfam K ω x)) μ := fun K =>
    integrable_cubeAverage_dirichlet_energy (μ := μ) (originCube d (K : ℤ))
      hfm hf (hDpot K) (hDsol K)
  have hNint : ∀ K : ℕ, Integrable (fun ω => cubeAverage (originCube d (K : ℤ))
      fun x => vecDot (Nfam K ω x) (Nfam K ω x)) μ := fun K =>
    integrable_cubeAverage_neumann_energy (μ := μ) (originCube d (K : ℤ))
      hfm hf (hNpot K) (hNsol K)
  refine tendsto_of_eventually_sandwich (fun K => ?_) (fun ε hε => ?_) (fun ε hε => ?_)
  · exact integral_cubeAverage_dirichlet_le_neumann (μ := μ) (originCube d (K : ℤ))
      hfm hf (hDpot K) (hDsol K) (hNpot K) (hNsol K) (hNint K)
  · exact eventually_integral_normSq_sub_le_integral_cubeAverage_dirichlet
      hfm hf hpm hp hpmem hflux hDpot hDsol hDint hε
  · exact eventually_integral_cubeAverage_neumann_le_integral_normSq_of_approximateStream
      hfm hf hpm hp hjm hj hjdef hstream hNpot hNsol hNint hε

end General

section FreshShell

variable {d : ℕ}

end FreshShell

end

end Algsuperdiff.Section3.Provider.Corrector
