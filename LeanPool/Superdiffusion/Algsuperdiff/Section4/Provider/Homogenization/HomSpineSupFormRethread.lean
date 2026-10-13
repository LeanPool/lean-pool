/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineRecutClose
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineSupFormClause

/-!
# HomSpineSupFormRethread

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Step-3c re-thread at the sup-form clause

## The measurement this file records

Which consumers of the clause actually need the `ℓ^p`-over-depths
aggregate, and which only need the print's sup?

**Answer: NONE of them needs the `ℓ^p` aggregate.**  The Step-3c chain

```text
  the descendant bound
    → the translate-uniform box gauge
      → { the continuous representative, the `L^∞` endpoint }
        → clause (C3)
```

touches its `ℓ^p`-over-depths gauge hypothesis on `□_m` at
exactly ONE place — the outer-index collapse, which throws
the sum away and keeps a single depth term.  Everything after that point is a
statement about the per-depth quantities: the descendant bound `‖(G)_R‖ ≤
A·3^{(s+d/p)m}·3^{-(s+d/p)·scale R}`, the box gauge, the translate-uniform
carrier, and the `L^∞` lift, whose own depth summation is the INDEPENDENT
geometric factor `liftGeomFactor (s + d/p)` at the FIXED gap `1 - (s + d/p) ≥
1/2`.

So the whole leg re-threads verbatim at the sup-form clause of
`HomSpineSupFormClause`, **with identical constants**: the theorems below are
the same, with the `ℓ^p`-over-depths gauge bound replaced by
`NegBesovSupGaugeBound … A`, and the endpoint constant `96 d² · liftGeomFactor
(s + d/p)` is unchanged.  In particular the `ℓ^p` aggregation on the clause's
left-hand side was pure overshoot: it was forced by the PRODUCER
(`CoarseGraining`'s negative Besov seminorm is an `ℓ^p` depth `tsum`), never by
a consumer.

## The per-cell sharpening

At the print's own per-cell carrier (forced by the far-band
result for depth-global tests) the re-thread is not merely constant-preserving,
it is strictly better: the datum IS the per-cell descendant bound, so the order
shift `s ↦ s + d/p` — the price of reading one cell out of an `ℓ^p` mean over
`3^{jd}` cells — disappears, the guard becomes `s ≤ 1/2`, the endpoint constant
becomes `96 d² · liftGeomFactor s` (`≤ 3` on that range), and `p` leaves the
lifting leg entirely.

## What this file does not prove

The sup-form clause itself.  `HomSpineSupFormClause` states the exact
interface (`NegativeBesovGridSmoothDualConverseAtDepth` — the single-depth
grid/smooth-dual comparison, plus
`ofReal_negBesovSupPartialNorm_le_of_depthConverse`); the single-depth dual
test family is supplied by that interface and is consumed here as a named
input only.  The energy
slot is unchanged, so the `ℓ^p` energy factor `coarseGrainingGeomFactor p
(s/4)` (the D3 site) survives this re-cut; see `HomSpineSupFormClause` §5.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The descendant bound, from one depth at a time -/

/-- **The printed descendant bound from the SUP-form gauge.**

The finite-`p` descendant bound with the `ℓ^p` hypothesis
replaced by the sup-form one.  The proof never used more: it applied
the outer-index collapse and discarded the sum. -/
theorem descendantBound_of_supGauge {m : ℤ} {s p A : ℝ} (hp : 0 < p) {F : Vec d → Vec d}
    (hgauge : NegBesovSupGaugeBound (originCube d m) s p A F)
    (j : ℕ) (R : TriadicCube d) (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    ‖cubeAverageVec R F‖ ≤
      A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)) *
        (3 : ℝ) ^ (-((s + (d : ℝ) / p) * ((R.scale : ℤ) : ℝ))) := by
  have hcell := sqrt_vecNormSq_cubeAverageVec_le_of_depthBound hp (hgauge j) hR
  have hnorm : ‖cubeAverageVec R F‖ ≤ Real.sqrt (vecNormSq (cubeAverageVec R F)) :=
    norm_le_sqrt_vecNormSq _
  refine (hnorm.trans hcell).trans (le_of_eq ?_)
  have hscale : R.scale = m - (j : ℤ) := by
    have h := scale_eq_sub_of_mem_descendantsAtDepth hR
    simpa using! h
  have hexp : (s + (d : ℝ) / p) * (j : ℝ) =
      (s + (d : ℝ) / p) * (m : ℝ) + -((s + (d : ℝ) / p) * (((m - (j : ℤ)) : ℤ) : ℝ)) := by
    push_cast
    ring
  rw [hscale, hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← mul_assoc]

variable [NeZero d]

/-- **the translate-uniform carrier from the SUP-form gauge**, at the
constant. -/
theorem uniformBoxGaugeBound_of_supGauge (m : ℤ) {s p A : ℝ} (hp : 0 < p)
    (hguard : s + (d : ℝ) / p ≤ 1 / 2) {F : Vec d → Vec d}
    (hFI : ∀ i, Integrable (fun y => F y i) volume)
    (hFzero : ∀ y, y ∉ cubeSet (originCube d m) → F y = 0)
    (hgauge : NegBesovSupGaugeBound (originCube d m) s p A F) :
    UniformBoxGaugeBound m (s + (d : ℝ) / p)
      (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p) *
        (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)))) F := by
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hA' : (0 : ℝ) ≤ A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)) :=
    mul_nonneg hgauge.nonneg (three_rpow_nonneg _)
  refine uniformBoxGaugeBound_of_gridGauge m hs1 hA' hFI ?_
  refine gridGauge_of_descendantBound m hA' hFzero ?_
  intro j R hR
  exact descendantBound_of_supGauge hp hgauge j R hR

/-- The residue, from the sup-form gauge. -/
theorem hasContinuousRepresentative_of_supGauge (m : ℤ) {s p A : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hgauge : NegBesovSupGaugeBound (originCube d m) s p A G) :
    HasContinuousRepresentative w := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs' : 0 < s + (d : ℝ) / p := by linarith only [hs0, hdp]
  exact hasContinuousRepresentative_of_uniformBoxGauge hw hwI hwc hGI
    (uniformBoxGaugeBound_of_supGauge m hp hguard hGI hGzero hgauge) hs' hguard

/-! ## 2. The `L^∞` endpoint at the sup-form gauge -/

/-- **THE CONVERSION THEOREM AT THE PRINT'S OWN AGGREGATION.**

The finite-`p` `L^∞` conversion with the `ℓ^p`-over-depths
hypothesis replaced by the sup over depths, at the SAME constant
`96 d² · liftGeomFactor (s + d/p)`. -/
theorem ae_linfty_of_supGauge (m : ℤ) {s p A : ℝ}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2)
    {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : HasWeakGradientOn Set.univ w G) (hwI : Integrable w volume)
    (hwc : HasCompactSupport w) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0)
    (hgauge : NegBesovSupGaugeBound (originCube d m) s p A G)
    {g : Vec d → ℝ} (hgc : Continuous g) (hgw : w =ᵐ[volume] g)
    (hzero : ∀ y ∈ cubeFaceSet (originCube d m), g y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      (3 : ℝ) ^ (-(m : ℝ)) * |g x| ≤
        96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * A := by
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs' : 0 < s + (d : ℝ) / p := by linarith only [hs0, hdp]
  have hbox := uniformBoxGaugeBound_of_supGauge m hp hguard hGI hGzero hgauge
  have hres := ae_linfty_of_uniformBoxGauge_originCube (d := d) m hw hwI hwc hGI hbox hs'
    hguard hgc hgw hzero
  refine hres.mono fun x hx => ?_
  refine hx.trans (le_of_eq ?_)
  have hcanc := linfty_constant_cancels m (16 * (d : ℝ) * (6 * (d : ℝ) *
    liftGeomFactor (s + (d : ℝ) / p))) A (s + (d : ℝ) / p)
  calc 16 * (d : ℝ) *
        (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p) *
          (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ)))) *
        (3 : ℝ) ^ (-(m : ℝ) * (s + (d : ℝ) / p))
      = 16 * (d : ℝ) * (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p)) *
          (A * (3 : ℝ) ^ ((s + (d : ℝ) / p) * (m : ℝ))) *
          (3 : ℝ) ^ (-(m : ℝ) * (s + (d : ℝ) / p)) := by ring
    _ = 16 * (d : ℝ) * (6 * (d : ℝ) * liftGeomFactor (s + (d : ℝ) / p)) * A := hcanc
    _ = 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * A := by ring

/-! ## 3. Clause (C3) from the sup-form clause -/

/-- **CLAUSE (C3), FROM THE SUP-FORM MULTISCALE CLAUSE.**

The printed Step-3c clause re-threaded at
`CoarseGrainingSupMultiscale`: the printed Step-3c leg, with the print's own
`p = ∞` depth aggregation on the left-hand side of the clause, and with the
identical output constant `96 d² · liftGeomFactor (s + d/p) · C_w`.

The energy slot, the level condition `hlevel`, and the frame hypotheses are
carried over verbatim — none of them mentions the depth aggregation. -/
theorem spineClauseC3_of_supMultiscale {m : ℤ} {jn : ℕ}
    {Ccg s s1 s2 p sigmaBarM E1 E2 Dg S Cw EB Kg Kh KhInf : ℝ}
    {Gen : TriadicCube d → ℝ} {Fflux : Vec d → Vec d}
    {u v : H1Function (openCubeSet (originCube d m))}
    {W : Vec d → ℝ} {G : Vec d → Vec d}
    (hp : 0 < p) (hs0 : 0 < s) (hguard : s + (d : ℝ) / p ≤ 1 / 2) (hsig : 0 < sigmaBarM)
    (hCG : CoarseGrainingSupMultiscale (originCube d m) jn Ccg s s1 s2 p sigmaBarM
      E1 E2 Dg Gen G Fflux)
    (hS : ∀ N : ℕ,
      coarseGrainingEnergyPartial (originCube d m) p (s - s1) jn N Gen ≤ S)
    (hlevel : coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ)) ≤
      sigmaBarM *
        (Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh))
    (hWval : ∀ x ∈ openCubeSet (originCube d m), W x = u.toFun x - v.toFun x)
    (hWout : ∀ x, x ∉ openCubeSet (originCube d m) → W x = 0)
    (hw : HasWeakGradientOn Set.univ W G) (hwI : Integrable W volume)
    (hwc : HasCompactSupport W) (hGI : ∀ i, Integrable (fun y => G y i) volume)
    (hGzero : ∀ y, y ∉ cubeSet (originCube d m) → G y = 0) :
    ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
        (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) * EB *
          dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  have hgauge : NegBesovSupGaugeBound (originCube d m) s p
      (sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
        ((originCube d m).scale - (jn : ℤ))) G := hCG.gradGauge hS hsig
  obtain ⟨gc, hgc, hgw⟩ :=
    hasContinuousRepresentative_of_supGauge m hp hs0 hguard hw hwI hwc hGI hGzero hgauge
  have hzero : ∀ y ∈ cubeFaceSet (originCube d m), gc y = 0 :=
    faceZero_of_continuousRepresentative hWout hgc hgw
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := div_nonneg (Nat.cast_nonneg d) hp.le
  have hs1 : s + (d : ℝ) / p < 1 := by linarith only [hguard]
  have hlift : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) := liftGeomFactor_nonneg hs1
  have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (d : ℝ) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  have hK : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) :=
    mul_nonneg hd2 hlift
  have hres := ae_linfty_of_supGauge (d := d) m hp hs0 hguard hw hwI hwc hGI hGzero
    hgauge hgc hgw hzero
  have hA : sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
      ((originCube d m).scale - (jn : ℤ)) ≤
      Cw * EB * dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    have hstep := mul_le_mul_of_nonneg_left hlevel (inv_nonneg.mpr hsig.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsig), one_mul] at hstep
  have hfinal : 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) *
        (sigmaBarM⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigmaBarM E1 E2 Dg S
          ((originCube d m).scale - (jn : ℤ))) ≤
      (96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) * Cw) * EB *
        dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    refine (mul_le_mul_of_nonneg_left hA hK).trans (le_of_eq ?_)
    ring
  have hgwR : W =ᵐ[volume.restrict (openCubeSet (originCube d m))] gc :=
    hgw.filter_mono (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
  have hmem : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      x ∈ openCubeSet (originCube d m) :=
    MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet _)
  refine ((hres.and hgwR).and hmem).mono fun x hx => ?_
  have hval : u.toFun x - v.toFun x = gc x := by
    rw [← hWval x hx.2]
    exact hx.1.2
  rw [hval]
  exact hx.1.1.trans hfinal

end

end Algsuperdiff.Section4.Provider.Homogenization
