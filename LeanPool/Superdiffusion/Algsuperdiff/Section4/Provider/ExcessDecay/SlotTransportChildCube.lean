/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.GoodEventCaps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StabilityExponentComparison

/-!
# SlotTransportChildCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transporting the good-event caps from the parent cube to sub-cubes

The printed consumers read them at **sub-cubes** of the parent and at the
larger indices `s/6` and `s/4`:

* `e.good.set.giveth.v2` at `x+□_{n+1}`, indices `s/4` (`q = 1`) and `s/6` (`q
  = 2`);
* `e.bound.Lambdas.by.Es.v2` at `x+□_{n+1}`, index `s/4`, `q = 2` — the input
  of the coarse-grained Caccioppoli step `e.energy.bound.interior`, whose
  Caccioppoli pair is `(x+□_n) ⊂ (x+□_{n+1})`, so the *outer* cube of that pair
  is where the ellipticity ratios are needed.

This module performs that transport for **triadic sub-cubes** of the parent, at
the field and comparator of the parent (which is exactly how the manuscript
writes it: `𝓔_{t,∞,q}(y+□_{n+1}; ã_{L,n+2}, σ_{n+2})`, the *parent's*
flux-corrected field on the smaller cube).

## What is transported, and what is NOT

**Transported (proved below, unconditionally):**

1. the index change `s/8 → u` for every `u ≥ s/8`, at **no cost** — `𝓔` is
   antitone in its index (`StabilityIndexCube.lean`);
2. the scale-exponent change `q = 2 → q = 1`, at **no cost**, via the
   manuscript's own `e.compareEqs` (`StabilityExponentComparison.lean`): it
   converts `𝓔_{s/4,∞,1}` into `𝓔_{s/8,∞,2}`, i.e. straight onto the annular
   anchor's own index;
3. the cube change parent → **triadic descendant** at depth `h`, at cost
   `3^{(s/8)·h}` (`≤ 3^{1/8} < 1.15` for a one-scale descent and `s ≤ 1`).

In CoarseGraining's carrier the shells of an off-grid cube are maxima over the
*translated* grid, which is disjoint from the parent's grid, so no inclusion or
monotonicity argument reaches them; the printed route is `l.lambdas.stability`,
whose proof is a greedy Whitney-type decomposition of the off-grid cube by
parent-grid subcubes at all deeper scales, plus subadditivity of `σ_*^{-1}` and
a packing count.

Consequently the geometry lemma proved here — the child inclusion that the
manuscript itself silently uses — is recorded as a *verified input* to that
missing lemma, not as a substitute for it.

## Main definitions

* `fluxCorrectedErrorOn` — `𝓔_{s,∞,2}(Q; ã_{L,m}, σ_m)` for an arbitrary
  triadic cube `Q`, at the flux-corrected field and comparator of `□_m`.  The
  manuscript's shorthand; at `Q = □_m` it is `Support.fluxCorrectedError`.
* `fluxCorrectedErrorOnOne` — its `q = 1` sibling, the quantity the
  coarse-graining display `e.homogenization.L2.interior` carries.

## Main results

* `image_add_openCubeSet_succ_subset` — the geometry the manuscript uses
  without comment: the anchor's binder `(x+□_n) ⊆ (z+□_{n+1}) ∩ □_m`
  **implies** `(x+□_{n+1}) ⊆ (z+□_{n+2})`, the inclusion the proof restates.
* `ae_errorOn_descendant_le_harmonicSlot` — the `q = 2` cap at every triadic
  sub-cube and every index `u ≥ s/8`.
* `ae_errorOnOne_descendant_le_harmonicSlot` — the `q = 1` cap at every triadic
  sub-cube and every index `u ≥ s/4`: the first inequality of
  `e.good.set.giveth.v2`, in the grid rendering.
* `ae_boundLambdasByEs_descendant_harmonicSlot` — `e.bound.Lambdas.by.Es.v2`
  at every triadic sub-cube and every index `u ≥ s/8`, in the grid rendering.

## Deviations from print, recorded

1. **Grid, not continuum.**  All three cap statements quantify over
   `descendantsAtScale (originCube d (n+2)) k`, never over translates.  Nothing
   below is presented as `e.mathcalE.stability.applied` or as
   `l.lambdas.stability`.
2. **The printed intermediate rung is skipped.**  The printed chain goes
   `𝓔_{s/4,∞,1} ≤ C 𝓔_{s/6,∞,2} ≤ 𝓔_{s/8,∞,2} ≤ C`.  The route here is
   `𝓔_{s/4,∞,1} ≤ 𝓔_{s/8,∞,2}(same cube) ≤ 3^{(s/8)h} 𝓔_{s/8,∞,2}(parent) ≤ C/2`:
   the same endpoint, one rung fewer, and with explicit constants.  The printed
   first inequality itself (at the index `s/6`) is not proved; see
   `StabilityExponentComparison.lean`.

## References

* ABK26, `e.good.set.giveth.v2`, `e.bound.Lambdas.by.Es.v2`.
* ABK26, `e.mathcalE.stability.applied`.
* ABK26, `e.energy.bound.interior`.
* ABK26, `l.lambdas.stability`; `e.compareEqs`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The geometry the manuscript uses without comment -/

/-! ## 2. The parent's functionals read at a sub-cube -/

/-- `𝓔_{s,∞,2}(Q; a_L − (κ_L−κ_m)_{□_m}, σ_m)`: the *parent's* flux-corrected
field and comparator, evaluated on an arbitrary triadic cube `Q`.

This is the manuscript's own shorthand — the display carries
`𝓔_{s/6,∞,2}(y+□_{n+1}; ã_{L,n+2}, σ_{n+2})`, i.e. the field and comparator of
the parent cube `z+□_{n+2}` on the smaller cube.  Translated centres are
realized, as everywhere in Section 4, by translating the *sample* (resolution
A4). -/
def fluxCorrectedErrorOn (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d)
    (s : ℝ) (omega : Cutoff.CutoffSample d) : ℝ :=
  Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (isotropicComparatorMatrix (Annealed.sigmaBar M m))

/-- `max{σ_m⁻¹Λ_{s,2}(Q), σ_mλ_{s,2}⁻¹(Q)}` at the parent's field and comparator. -/
def fluxCorrectedEllipticityRatioMaxOn (M : ABKModel d) (L m : ℤ) (Q : TriadicCube d)
    (s : ℝ) (omega : Cutoff.CutoffSample d) : ℝ :=
  max ((Annealed.sigmaBar M m : ℝ)⁻¹ *
      Ch02.LambdaSq Q s (.finite 2)
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega))
    ((Annealed.sigmaBar M m : ℝ) *
      (Ch02.lambdaSq Q s (.finite 2)
        (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega))⁻¹)

/-- At the cube that carries the flux correction, the sub-cube functional is the
proved literal error of `ErrorAtoms`. -/
theorem fluxCorrectedErrorOn_originCube (M : ABKModel d) (L m : ℤ) (s : ℝ)
    (omega : Cutoff.CutoffSample d) :
    fluxCorrectedErrorOn M L m (originCube d m) s omega =
      Support.fluxCorrectedError M L m s omega  :=
  (Support.fluxCorrectedError_characterization M L m s omega).symm

theorem fluxCorrectedEllipticityRatioMaxOn_originCube (M : ABKModel d) (L m : ℤ)
    (s : ℝ) (omega : Cutoff.CutoffSample d) :
    fluxCorrectedEllipticityRatioMaxOn M L m (originCube d m) s omega =
      fluxCorrectedEllipticityRatioMax M L m s omega :=
  rfl

/-! ## 3. The `q = 2` cap at every triadic sub-cube -/

/-- **The caps step transported to triadic sub-cubes and to every larger
index.**

On the harmonic statement's good event `𝒢(n+2, z; s/8, 1/2)`, for every
`L ≥ n+2`, every triadic descendant `Q` of `□_{n+2}` at scale `k`, and every
index `u ≥ s/8`,

```
𝓔_{u,∞,2}(Q; ã_{L,n+2}, σ_{n+2})  ≤  3^{(s/8)·(n+2−k)} · C/2 .
```

The index change is free and the cube change costs the explicit factor; the
right-hand side is a constant, which is what the downstream Caccioppoli and
coarse-graining steps consume.  At `k = n+1` and `u = s/6` this is the middle
inequality of `e.good.set.giveth.v2` in its grid rendering (deviation 1). -/
theorem ae_errorOn_descendant_le_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ (k : ℤ) (Q : TriadicCube d),
                Q ∈ descendantsAtScale (originCube d (n + 2)) k →
                  ∀ u : ℝ, s / 8 ≤ u →
                    fluxCorrectedErrorOn M L (n + 2) Q u
                        (Cutoff.translateCutoffSample z omega) ≤
                      Real.rpow (3 : ℝ) (s / 8 * (Int.toNat (n + 2 - k) : ℝ)) *
                        (C * (1 / 2)) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorRepresentative_le_harmonicSlot d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  have hs8 : 0 < s / 8 := by linarith only [hs]
  have htr := (GoodEvents.measurePreserving_translateCutoffSample M
    z).quasiMeasurePreserving.ae
    (Support.ae_forall_fluxCorrectedError_eq_representative M (n + 2) ⟨s / 8, hs8⟩)
  filter_upwards [hC M s hsrange hregime hsmall hs n z, htr] with omega hcap heq
  intro hmem L hL k Q hQ u hu
  have hfactor : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (s / 8 * (Int.toNat (n + 2 - k) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hparent : fluxCorrectedErrorOn M L (n + 2) (originCube d (n + 2)) (s / 8)
      (Cutoff.translateCutoffSample z omega) ≤ C * (1 / 2) := by
    have h1 : Support.fluxCorrectedError M L (n + 2) (s / 8)
        (Cutoff.translateCutoffSample z omega) =
        Support.fluxCorrectedErrorRepresentative M L (n + 2) ⟨s / 8, hs8⟩
          (Cutoff.translateCutoffSample z omega) := heq ⟨L, hL⟩
    rw [fluxCorrectedErrorOn_originCube, h1]
    exact hcap hmem L hL
  have hdesc := homogenizationErrorOnCube_infinity_two_descendant_index_le
    (Q := originCube d (n + 2)) (R := Q) (k := k)
    (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega))
    (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) hs8 hu hQ
  exact le_trans hdesc (mul_le_mul_of_nonneg_left hparent hfactor)

/-! ## 4. The `q = 1` cap: the first inequality of `e.good.set.giveth.v2` -/

/-! ## 5. `e.bound.Lambdas.by.Es.v2` at every triadic sub-cube -/

/-- **`e.bound.Lambdas.by.Es.v2` transported to triadic sub-cubes.**

On the harmonic statement's good event, for every `L ≥ n+2`, every triadic
descendant `Q` of `□_{n+2}` at scale `k` and every index `u ≥ s/8`,

```
max{ σ_{n+2}⁻¹Λ_{u,2}(Q; ã_{L,n+2}) , σ_{n+2}λ_{u,2}⁻¹(Q; ã_{L,n+2}) }
      ≤  2d ( (3^{(s/8)(n+2−k)} · C/2)² + 1 ) .
```

This is the input the coarse-grained Caccioppoli step `e.energy.bound.interior`
consumes, at the *outer* cube of its Caccioppoli pair — provided that outer
cube is a triadic descendant of the parent. -/
theorem ae_boundLambdasByEs_descendant_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ (k : ℤ) (Q : TriadicCube d),
                Q ∈ descendantsAtScale (originCube d (n + 2)) k →
                  ∀ u : ℝ, s / 8 ≤ u →
                    fluxCorrectedEllipticityRatioMaxOn M L (n + 2) Q u
                        (Cutoff.translateCutoffSample z omega) ≤
                      2 * (d : ℝ) *
                        ((Real.rpow (3 : ℝ) (s / 8 * (Int.toNat (n + 2 - k) : ℝ)) *
                            (C * (1 / 2))) ^ 2 + 1) := by
  obtain ⟨C, hCpos, hC⟩ := ae_errorOn_descendant_le_harmonicSlot d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  have hs8 : 0 < s / 8 := by linarith only [hs]
  filter_upwards [hC M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL k Q hQ u hu
  have hu0 : 0 < u := by linarith only [hs8, hu]
  have hratio := max_ellipticityRatio_le_homogenizationError (d := d) Q
    (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
      (Cutoff.translateCutoffSample z omega)) hu0 (Annealed.sigmaBar M (n + 2)).2
  have hnonneg : 0 ≤ fluxCorrectedErrorOn M L (n + 2) Q u
      (Cutoff.translateCutoffSample z omega) :=
    homogenizationErrorOnCube_infinity_two_nonneg Q
      (Support.fluxCorrectedCoeffFamily M L (n + 2) (originCube d (n + 2))
        (Cutoff.translateCutoffSample z omega))
      (isotropicComparatorMatrix (Annealed.sigmaBar M (n + 2))) hu0
  exact le_trans hratio
    (two_mul_dim_mul_sq_add_one_le_of_le hnonneg (hcap hmem L hL k Q hQ u hu))

/-- The parent cube is its own triadic descendant at depth `0`. -/
private theorem parent_mem_descendantsAtScale (d : ℕ) (m : ℤ) :
    originCube d m ∈ descendantsAtScale (originCube d m) m := by
  have h : originCube d m ∈
      descendantsAtScale (originCube d m) (originCube d m).scale := by
    rw [descendantsAtScale_self]
    exact Finset.mem_singleton_self _
  exact h

/-- At depth `0` the transport factor is `1`. -/
private theorem transport_factor_parent (s : ℝ) (n : ℤ) :
    Real.rpow (3 : ℝ) (s / 8 * (Int.toNat (n + 2 - (n + 2)) : ℝ)) = 1 := by
  have hzero : (Int.toNat (n + 2 - (n + 2)) : ℝ) = 0 := by norm_num
  rw [hzero, mul_zero]
  exact Real.rpow_zero 3

/-- **`e.bound.Lambdas.by.Es.v2` at the parent cube, for every index
`u ≥ s/8`.**

```
max{ σ_{n+2}⁻¹Λ_{u,2}(z+□_{n+2}; ã) , σ_{n+2}λ_{u,2}⁻¹(z+□_{n+2}; ã) } · 1_𝒢
      ≤  2d((C/2)² + 1) .
``` -/
theorem ae_boundLambdasByEs_parent_index_le_harmonicSlot (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (s : ℝ), s ∈ Set.Icc (64 * M.gamma) 1 →
        M.gamma ≤ C⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
        M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
            Real.rpow (s / 8) (3 / 2 : ℝ) * Disorder.cstar M ^ (2 : ℕ) * (1 / 2) →
        ∀ hs : 0 < s, ∀ (n : ℤ) (z : Vec d),
          ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            omega ∈ Algsuperdiff.Frozen.Section4.goodEventAt M
                (Support.cgEllipLowerConstant d) (n + 2) z
                ⟨s / 8, by linarith only [hs]⟩ (1 / 2) →
              ∀ L : ℤ, n + 2 ≤ L → ∀ u : ℝ, s / 8 ≤ u →
                fluxCorrectedEllipticityRatioMax M L (n + 2) u
                    (Cutoff.translateCutoffSample z omega) ≤
                  2 * (d : ℝ) * ((C * (1 / 2)) ^ 2 + 1) := by
  obtain ⟨C, hCpos, hC⟩ := ae_boundLambdasByEs_descendant_harmonicSlot d
  refine ⟨C, hCpos, ?_⟩
  intro M s hsrange hregime hsmall hs n z
  filter_upwards [hC M s hsrange hregime hsmall hs n z] with omega hcap
  intro hmem L hL u hu
  have h := hcap hmem L hL (n + 2) (originCube d (n + 2))
    (parent_mem_descendantsAtScale d (n + 2)) u hu
  rw [fluxCorrectedEllipticityRatioMaxOn_originCube,
    transport_factor_parent s n, one_mul] at h
  exact h

end

end Algsuperdiff.Section4.Provider.ExcessDecay
