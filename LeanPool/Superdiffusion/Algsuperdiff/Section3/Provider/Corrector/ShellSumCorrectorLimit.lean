/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.FreshShellCorrectorEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.ShellSumCarrierLaw

/-!
# ShellSumCorrectorLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The corrector limit at the shell-sum carrier

ABK26, `e.def.w`, `l.corrector.limit` and `e.perturb.assumption`.

`Algsuperdiff/Section3/Provider/Corrector/ShellSumCarrierLaw.lean` puts the
finite shell increment `k_m - k_n = Σ_{k ∈ (n,m]} j_k` on the compact-open
carrier `C(Vec d, Mat d)` as the law `shellSumValuePathLaw M.P n m`, and
supplies the stationarity instance, the `L²` layer of the forcing and the
unconditional decorrelation bound

`E[|A_κ 𝐣|²] ≤ ‖κ‖_∞ · |B_{√d·3^m+1}| · E[|𝐟|²]`

at that law.  Its header records that the Helmholtz splitting and the
approximate-stream assembly at the shell-sum carrier remain open.  This module
closes both and runs the corrector limit there.

Nothing in the argument is new mathematics: every step is the fresh-shell step
of `ValuePathTransport.lean` / `OmegaStreamAssembly.lean` /
`CorrectorLimitNode.lean` with the single fresh shell replaced by the block
`(n, m]`, i.e. with the decorrelation radius `√d + 1` replaced by the
increment's own range `√d · 3^m + 1`.  The *value* of the limit is **not**
evaluated here; that is the shell decomposition and the per-shell dilation, and
neither is claimed below.

## What is supplied

* `shellSumPotentialCorrector`, `shellSumFlux` — the canonical source-sign
  Helmholtz splitting `𝐣 = 𝐟 + ∇w` of the shell-sum forcing under
  `shellSumValuePathLaw M.P n m`, with the two subspace memberships
  (`toLp_shellSumCorrectorRepr_mem`, `toLp_shellSumFlux_mem`).
* `exists_shellSumStream` — the `ε`-approximate antisymmetric stream for that
  flux, at every tolerance.
* `tendsto_integral_cubeAverage_dirichlet_neumann_shellSum` — the corrector
  limit `e.corrector.limit` at the shell-sum carrier: both cube energies
  converge to `E[|∇w|²]`.

Unlike the fresh-shell chain, **no normalization of `e` is assumed anywhere**:
the `L²` layer `memLp_two_valuePathForcing_shellSum` of the shell-sum forcing
holds at every direction, so no unit binder is needed and none is introduced.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3 (ABKModel)

noncomputable section

variable {d : ℕ}

/-! ### The canonical Helmholtz splitting at the shell-sum law -/

/-- The shell-sum forcing as an element of the stationary `L²` layer of the
continuous-path carrier under the shell-sum law. -/
def shellSumForcingL2 (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    VectorL2 d (shellSumValuePathLaw M.P n m).toMeasure :=
  (memLp_two_valuePathForcing_shellSum M e n m).toLp (valuePathForcing e)

/-- The canonical source-sign potential corrector at the shell-sum law: the
negative of the orthogonal projection of the shell-sum forcing onto the
stationary potential subspace. -/
def shellSumPotentialCorrector (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    VectorL2 d (shellSumValuePathLaw M.P n m).toMeasure :=
  -stationaryPotentialProjection (μ := (shellSumValuePathLaw M.P n m).toMeasure)
    (shellSumForcingL2 M e n m)

/-- A strongly measurable representative of the canonical shell-sum corrector. -/
def shellSumCorrectorRepr (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    C(Vec d, Mat d) → HilbertVec d :=
  (Lp.aestronglyMeasurable (shellSumPotentialCorrector M e n m)).mk _

theorem stronglyMeasurable_shellSumCorrectorRepr (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    StronglyMeasurable (shellSumCorrectorRepr M e n m) :=
  (Lp.aestronglyMeasurable (shellSumPotentialCorrector M e n m)).stronglyMeasurable_mk

theorem memLp_two_shellSumCorrectorRepr (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    MemLp (shellSumCorrectorRepr M e n m) 2 (shellSumValuePathLaw M.P n m).toMeasure :=
  (Lp.memLp (shellSumPotentialCorrector M e n m)).ae_eq
    (Lp.aestronglyMeasurable (shellSumPotentialCorrector M e n m)).ae_eq_mk

theorem toLp_shellSumCorrectorRepr (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    (memLp_two_shellSumCorrectorRepr M e n m).toLp (shellSumCorrectorRepr M e n m)
      = shellSumPotentialCorrector M e n m := by
  rw [MemLp.toLp_congr (memLp_two_shellSumCorrectorRepr M e n m)
      (Lp.memLp (shellSumPotentialCorrector M e n m))
      (Lp.aestronglyMeasurable (shellSumPotentialCorrector M e n m)).ae_eq_mk.symm,
    Lp.toLp_coeFn]

/-- The canonical stationary flux `𝐣 = 𝐟 + ∇w` at the shell-sum law, as a
strongly measurable field. -/
def shellSumFlux (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    C(Vec d, Mat d) → HilbertVec d :=
  valuePathForcing e + shellSumCorrectorRepr M e n m

theorem shellSumFlux_apply (M : ABKModel d) (e : Vec d) (n m : ℤ)
    (f : C(Vec d, Mat d)) :
    shellSumFlux M e n m f = valuePathForcing e f + shellSumCorrectorRepr M e n m f :=
  rfl

theorem stronglyMeasurable_shellSumFlux (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    StronglyMeasurable (shellSumFlux M e n m) :=
  (stronglyMeasurable_valuePathForcing e).add
    (stronglyMeasurable_shellSumCorrectorRepr M e n m)

theorem memLp_two_shellSumFlux (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    MemLp (shellSumFlux M e n m) 2 (shellSumValuePathLaw M.P n m).toMeasure :=
  (memLp_two_valuePathForcing_shellSum M e n m).add
    (memLp_two_shellSumCorrectorRepr M e n m)

/-- The canonical shell-sum corrector is stationary potential. -/
theorem toLp_shellSumCorrectorRepr_mem (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    (memLp_two_shellSumCorrectorRepr M e n m).toLp (shellSumCorrectorRepr M e n m)
      ∈ stationaryPotentialSubspace
        (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d) := by
  rw [toLp_shellSumCorrectorRepr]
  exact (stationaryPotentialSubspace
    (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d)).neg_mem
    (stationaryPotentialProjection_mem _)

/-- The canonical shell-sum flux is stationary solenoidal. -/
theorem toLp_shellSumFlux_mem (M : ABKModel d) (e : Vec d) (n m : ℤ) :
    (memLp_two_shellSumFlux M e n m).toLp (shellSumFlux M e n m)
      ∈ stationarySolenoidalSubspace
        (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d) := by
  have hsplit : (memLp_two_shellSumFlux M e n m).toLp (shellSumFlux M e n m)
      = shellSumForcingL2 M e n m
        + (memLp_two_shellSumCorrectorRepr M e n m).toLp
            (shellSumCorrectorRepr M e n m) :=
    MemLp.toLp_add (memLp_two_valuePathForcing_shellSum M e n m)
      (memLp_two_shellSumCorrectorRepr M e n m)
  rw [hsplit, toLp_shellSumCorrectorRepr]
  have h := sub_stationaryPotentialProjection_mem_orthogonal
    (μ := (shellSumValuePathLaw M.P n m).toMeasure) (shellSumForcingL2 M e n m)
  simpa only [shellSumPotentialCorrector, sub_eq_add_neg] using h

/-! ### The approximate stream at the shell-sum carrier -/

/-- **The decorrelation leg at the product density, at the shell-sum carrier.**

The shell-sum bound `E[|A_κ 𝐣|²] ≤ ‖κ‖_∞ |B_{√d·3^m+1}| E[|𝐟|²]` of
`ShellSumCarrierLaw.lean`, applied to the product density of scale `s` whose sup
norm is `s^{-d}`, is below any tolerance at a large enough scale.  This is the
fresh-shell `exists_scale_integral_normSq_mollify_productDensity_valuePathFlux_le`
with the radius `√d + 1` replaced by the increment's own range. -/
theorem exists_scale_integral_normSq_mollify_productDensity_shellSumFlux_le
    (M : ABKModel d) (e : Vec d) (n m : ℤ) {t : ℝ} (ht : 0 < t) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      ∫ f, ‖mollify (productDensity d hs) (shellSumFlux M e n m) f‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure ≤ t := by
  set V : ℝ := (volume (Metric.ball (0 : Vec d)
    (Real.sqrt (d : ℝ) * (3 : ℝ) ^ m + 1))).toReal with hV
  set E : ℝ := ∫ f, ‖valuePathForcing e f‖ ^ 2
    ∂(shellSumValuePathLaw M.P n m).toMeasure with hE
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hE0 : 0 ≤ E := integral_nonneg fun f => by positivity
  have hC0 : 0 ≤ V * E := mul_nonneg hV0 hE0
  set s : ℝ := 1 + V * E / t with hs
  have hs1 : (1 : ℝ) ≤ s := by
    have : 0 ≤ V * E / t := div_nonneg hC0 ht.le
    simp only [hs]
    linarith
  have hspos : 0 < s := by linarith
  have hd1 : 1 ≤ d := by
    have h2 := M.shellPrefix.dimension
    omega
  refine ⟨s, hspos, ?_⟩
  have hbound := integral_normSq_mollify_le_of_helmholtz_shellSum M e n m
    (productDensity_nonneg d hspos) (continuous_productDensity d hspos)
    (integrable_productDensity d hspos) (integral_productDensity d hspos)
    (productDensity_le d hspos)
    (stronglyMeasurable_shellSumCorrectorRepr M e n m)
    (memLp_two_shellSumCorrectorRepr M e n m)
    (stronglyMeasurable_shellSumFlux M e n m) (memLp_two_shellSumFlux M e n m)
    (shellSumFlux_apply M e n m) (toLp_shellSumCorrectorRepr_mem M e n m)
    (toLp_shellSumFlux_mem M e n m)
  refine hbound.trans ?_
  have hpow : s ≤ s ^ d := by
    calc s = s ^ 1 := (pow_one s).symm
      _ ≤ s ^ d := pow_le_pow_right₀ hs1 hd1
  have hinv : 1 / s ^ d ≤ 1 / s := one_div_le_one_div_of_le hspos hpow
  have hstep : 1 / s ^ d * V * E ≤ 1 / s * (V * E) := by
    have hmul := mul_le_mul_of_nonneg_right hinv hC0
    calc 1 / s ^ d * V * E = 1 / s ^ d * (V * E) := by ring
      _ ≤ 1 / s * (V * E) := hmul
  refine hstep.trans ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hspos]
  have hexp : t * s = t + V * E := by
    rw [hs]
    field_simp
  rw [hexp]
  linarith

/-- **The `Ω`-level `ε`-approximate antisymmetric stream at the shell-sum
carrier.**

For every tolerance `ε > 0` there is a stationary square-integrable field `S`
whose realizations are smooth and antisymmetric and whose row divergence is, at
every point of space, the realization of a stationary square-integrable field
`D` with `E[|D − 𝐣|²] ≤ ε`, where `𝐣 = shellSumFlux M e n m`.

This is `exists_freshShellStream` with the fresh shell replaced by the block
`(n, m]`; the two error legs are the same, only the decorrelation radius
changes. -/
theorem exists_shellSumStream (M : ABKModel d) (e : Vec d) (n m : ℤ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ S : C(Vec d, Mat d) → (Fin d → HilbertVec d),
      ∃ D : C(Vec d, Mat d) → HilbertVec d,
      StronglyMeasurable S ∧ MemLp S 2 (shellSumValuePathLaw M.P n m).toMeasure ∧
        (∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure, ∀ i k : Fin d,
          ContDiff ℝ (⊤ : ℕ∞) (streamRealization S f i k)) ∧
        (∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure, ∀ i k : Fin d,
          streamRealization S f k i = -streamRealization S f i k) ∧
        (∀ᵐ f ∂(shellSumValuePathLaw M.P n m).toMeasure, ∀ x : Vec d,
          streamDivergence (streamRealization S f) x = (realize D f x).toVec) ∧
        StronglyMeasurable D ∧ MemLp D 2 (shellSumValuePathLaw M.P n m).toMeasure ∧
        ∫ f, ‖D f - shellSumFlux M e n m f‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure ≤ ε := by
  obtain ⟨r, hr, h₁⟩ := exists_radius_integral_normSq_mollify_productDensity_sub_le
    (μ := (shellSumValuePathLaw M.P n m).toMeasure)
    (stronglyMeasurable_shellSumFlux M e n m) (memLp_two_shellSumFlux M e n m)
    (by linarith : (0 : ℝ) < ε / 4)
  obtain ⟨s, hs, h₂⟩ :=
    exists_scale_integral_normSq_mollify_productDensity_shellSumFlux_le M e n m
      (by linarith : (0 : ℝ) < ε / 4)
  obtain ⟨S, D, hSm, hS, hsmooth, hanti, hdiv, hDm, hD, hle⟩ :=
    exists_twoScaleStream_integral_normSq_le
      (μ := (shellSumValuePathLaw M.P n m).toMeasure)
      hr hs (stronglyMeasurable_shellSumFlux M e n m)
      (memLp_two_shellSumFlux M e n m) (toLp_shellSumFlux_mem M e n m) h₁ h₂
  exact ⟨S, D, hSm, hS, hsmooth, hanti, hdiv, hDm, hD, by linarith⟩

/-! ### The corrector limit at the shell-sum carrier -/

/-- **`l.corrector.limit` at the shell-sum carrier** (ABK26, at the forcing of
`e.def.w`).

Let `∇w_{D,e}^{(K)} = Dfam K` and `∇w_{N,e}^{(K)} = Nfam K` be the gradients of
the two solutions of `e.corrector.limit.pde` at the shell-sum forcing
`𝐟 = valuePathForcing e` under the law of `k_m − k_n`.  Then both limits of
`e.corrector.limit` exist and equal `E[|∇w|²]`, the energy of the canonical
Helmholtz corrector at that law.

There is no stream hypothesis, no tolerance, no localization scale, no
integrability hypothesis and **no normalization of `e`**; the only binders are
the frozen model, the shell pair and the two weak formulations. -/
theorem tendsto_integral_cubeAverage_dirichlet_neumann_shellSum
    (M : ABKModel d) (e : Vec d) (n m : ℤ)
    {Dfam Nfam : ℕ → C(Vec d, Mat d) → (Vec d → Vec d)}
    (hDpot : ∀ K : ℕ, ∀ᵐ ω ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsPotentialZeroTraceOn (openCubeSet (originCube d (K : ℤ))) (Dfam K ω))
    (hDsol : ∀ K : ℕ, ∀ᵐ ω ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsSolenoidalOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Dfam K ω x + (realize (valuePathForcing e) ω x).toVec)
    (hNpot : ∀ K : ℕ, ∀ᵐ ω ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsPotentialOn (openCubeSet (originCube d (K : ℤ))) (Nfam K ω))
    (hNsol : ∀ K : ℕ, ∀ᵐ ω ∂(shellSumValuePathLaw M.P n m).toMeasure,
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (K : ℤ)))
        fun x => Nfam K ω x + (realize (valuePathForcing e) ω x).toVec) :
    Filter.Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
        (fun x => vecDot (Dfam K ω x) (Dfam K ω x))
        ∂(shellSumValuePathLaw M.P n m).toMeasure) Filter.atTop
        (nhds (∫ ω, ‖shellSumCorrectorRepr M e n m ω‖ ^ 2
          ∂(shellSumValuePathLaw M.P n m).toMeasure))
      ∧ Filter.Tendsto (fun K : ℕ => ∫ ω, cubeAverage (originCube d (K : ℤ))
          (fun x => vecDot (Nfam K ω x) (Nfam K ω x))
          ∂(shellSumValuePathLaw M.P n m).toMeasure) Filter.atTop
          (nhds (∫ ω, ‖shellSumCorrectorRepr M e n m ω‖ ^ 2
            ∂(shellSumValuePathLaw M.P n m).toMeasure)) := by
  have hflux : (memLp_two_valuePathForcing_shellSum M e n m).toLp (valuePathForcing e)
      + (memLp_two_shellSumCorrectorRepr M e n m).toLp (shellSumCorrectorRepr M e n m)
      ∈ stationarySolenoidalSubspace
        (μ := (shellSumValuePathLaw M.P n m).toMeasure) (d := d) := by
    have hsplit : (memLp_two_shellSumFlux M e n m).toLp (shellSumFlux M e n m)
        = (memLp_two_valuePathForcing_shellSum M e n m).toLp (valuePathForcing e)
          + (memLp_two_shellSumCorrectorRepr M e n m).toLp
              (shellSumCorrectorRepr M e n m) :=
      MemLp.toLp_add (memLp_two_valuePathForcing_shellSum M e n m)
        (memLp_two_shellSumCorrectorRepr M e n m)
    rw [← hsplit]
    exact toLp_shellSumFlux_mem M e n m
  exact tendsto_integral_cubeAverage_dirichlet_neumann_of_approximateStream
    (μ := (shellSumValuePathLaw M.P n m).toMeasure)
    (stronglyMeasurable_valuePathForcing e) (memLp_two_valuePathForcing_shellSum M e n m)
    (stronglyMeasurable_shellSumCorrectorRepr M e n m)
    (memLp_two_shellSumCorrectorRepr M e n m)
    (toLp_shellSumCorrectorRepr_mem M e n m) hflux
    (stronglyMeasurable_shellSumFlux M e n m) (memLp_two_shellSumFlux M e n m)
    (fun ω => (shellSumFlux_apply M e n m ω).trans (add_comm _ _))
    (fun η hη => exists_shellSumStream M e n m hη)
    hDpot hDsol hNpot hNsol

end

end Algsuperdiff.Section3.Provider.Corrector
