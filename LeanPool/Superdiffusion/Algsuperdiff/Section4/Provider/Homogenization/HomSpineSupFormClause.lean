/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCzGridGauge

/-!
# HomSpineSupFormClause

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The D1 re-cut, fork (iii): the SUP-over-depths clause carrier

## Why a sup-over-depths carrier

The manuscript aggregates depths by SUP, not by `ℓ^p`.  Its Step-3 display reads

```text
  3^{-ms} σ_m ‖∇u - ∇v‖_{W_hat^{-s,∞}(□_m)}
    ≤ C s^{-1} σ_m^{1/2} 𝓔_{s₁,∞,1} ·
        sup_{k ≤ n} 3^{-(s-s₁)(n-k)} max_{z ∈ 3^k ℤ^d ∩ □_m}
          ν^{1/2} ‖∇u‖_{L²(z+□_k)}  +  (forcing term),
```

i.e. `p = ∞` on BOTH sides.  This repository's earlier clause carrier put
the `ℓ^p`-over-depths aggregate on the left.  That
was a transcription choice, not the print's shape, and the refutation record
(`HomSpineCzGridGaugeRefuted`) together with its `|log γ|^{1/p}` necessity are
properties OF THAT CHOICE: the flat field's sup is `O(1)` while its `ℓ^p`
aggregate is not.

This file gives the sup-over-depths sibling and the one fact that makes the
re-cut worth doing:

* `negBesovSupPartialNorm` — `sup_{j ≤ N}` of the SAME per-depth gauge terms
  (`negBesovLpDepthSeminorm`) the `ℓ^p` carrier sums.  No new geometry:
  the depth weight is the print's own `3^{-s j}`.
* `NegBesovSupGaugeBound` — the unbounded-`N` form, `∀ j`, which is exactly
  what every downstream consumer of the `ℓ^p` gauge actually uses (see
  `HomSpineSupFormRethread`).
* `CoarseGrainingSupMultiscale` — the clause sibling at the sup left-hand side,
  with the energy slot LEFT AT ITS `ℓ^p` SPELLING (that slot is where the
  finite-`p` `CoarseGraining` theorem enters; see the D3 section below).
One caveat.  The depth-`j` GLOBAL comparison named below is not
realizable at a `γ`-uniform constant: there is a far-band
Gagliardo cost `Σ_{i<j} 3^{-i s p'} ≍ min(j, (s p')⁻¹)` for the depth-`j`
checkerboard test, saturating at `≈|log γ|^{1/p'}` over the Step-3 depth range
`⌈10|log γ|⌉`.  The print's carrier is per CELL, not per depth: the per-cell
re-cut of §§1--4 reads the gauge at
`sup_j max_{R ∈ D_j}` and needs only a single-CELL test.  Everything here
remains correct and is the intermediate reading (sup over depths of the `ℓ^p`
cell mean); §5 (D3) is independent of the cut.

* `NegativeBesovGridSmoothDualConverseAtDepth` +
  `ofReal_negBesovSupPartialNorm_le_of_depthConverse` — THE CONSUMPTION
  INTERFACE.  The sup-form clause needs the grid/smooth-dual comparison only ONE
  DEPTH AT A TIME; the depth-uniform constant `CA` is the only input, and no sum
  over depths is ever formed.  This is the slot the single-depth
  single-depth dual test family fills; it is a NAMED INPUT here, never proved.
  So the supply's clause conjunct is producible at a `γ`-uniform constant
  exactly when `CA` is `γ`-uniform; the refuted depth-summed `(★)` is never
  used.

## The D3 factor

`coarseGrainingGeomFactor p w = (1 - 3^{-wp})^{-1/p}` is the price the finite-`p`
energy slot pays over the print's sup-form energy datum (the mesoscale energy
bound).  It is `≤ 3/2` with NO `γ`-dependence as soon as `1 ≤ w·p`, and it is at
least `(w·p·log 3)^{-1/p}` always, so on the complementary range `w·p ≤ 1` it is
genuinely of size `(w p)^{-1/p}`.

At the §4.5 pin `w = s/4` this says: the factor is `O(1)` iff `s·p ≳ 4`, i.e.
iff `p` is allowed to grow like `|log γ|`.  So D3 is not a second, independent
obstruction — it is the SAME question as item (a) (a `p`-uniform
Calderón--Zygmund constant on a range reaching `p ≈ 4/s`), quantified.
-/

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped BigOperators ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The sup-over-depths gauge carrier -/

/-- **The sup-over-depths partial gauge**, `sup_{j ≤ N} 3^{-sj} [·]_{depth j}`.

The `p = ∞` sibling of the `ℓ^p`-over-depths gauge: the SAME per-depth terms, with
the outer `ℓ^p` sum replaced by the maximum.  This is the aggregation shape the
manuscript's `W_hat^{-s,∞}` display uses. -/
def negBesovSupPartialNorm (Q : TriadicCube d) (s p : ℝ) (N : ℕ) (F : Vec d → Vec d) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
    negBesovLpDepthSeminorm Q s p F j

theorem negBesovSupPartialNorm_def (Q : TriadicCube d) (s p : ℝ) (N : ℕ) (F : Vec d → Vec d) :
    negBesovSupPartialNorm Q s p N F =
      (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun j =>
        negBesovLpDepthSeminorm Q s p F j := rfl

/-- Every depth term the sup reaches is below it. -/
theorem negBesovLpDepthSeminorm_le_negBesovSupPartialNorm (Q : TriadicCube d) (s p : ℝ)
    (F : Vec d → Vec d) {j N : ℕ} (hjN : j ≤ N) :
    negBesovLpDepthSeminorm Q s p F j ≤ negBesovSupPartialNorm Q s p N F :=
  Finset.le_sup' (f := fun i => negBesovLpDepthSeminorm Q s p F i)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hjN))

/-- The sup is below any bound on the depth terms it reaches. -/
theorem negBesovSupPartialNorm_le {Q : TriadicCube d} {s p B : ℝ} {N : ℕ}
    {F : Vec d → Vec d} (h : ∀ j ≤ N, negBesovLpDepthSeminorm Q s p F j ≤ B) :
    negBesovSupPartialNorm Q s p N F ≤ B :=
  Finset.sup'_le _ _ fun j hj => h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

theorem negBesovSupPartialNorm_nonneg (Q : TriadicCube d) (s p : ℝ) (N : ℕ)
    (F : Vec d → Vec d) : 0 ≤ negBesovSupPartialNorm Q s p N F :=
  le_trans (negBesovLpDepthSeminorm_nonneg Q s p F 0)
    (negBesovLpDepthSeminorm_le_negBesovSupPartialNorm Q s p F (Nat.zero_le N))

/-! ## 2. The unbounded-depth form, and its two equivalent readings -/

/-- **The sup-form gauge bound at level `A`**: every depth term of the printed
grid gauge is below `A`.  This is `3^{-ms}[F]_{B^{-s}_{p,∞}(□_m)} ≤ A`, the
`p = ∞` depth aggregation the manuscript's display carries. -/
def NegBesovSupGaugeBound (Q : TriadicCube d) (s p A : ℝ) (F : Vec d → Vec d) : Prop :=
  ∀ j : ℕ, negBesovLpDepthSeminorm Q s p F j ≤ A

/-- The two readings agree: a level for every truncation is a level for every
depth. -/
theorem negBesovSupGaugeBound_iff_forall_partial {Q : TriadicCube d} {s p A : ℝ}
    {F : Vec d → Vec d} :
    NegBesovSupGaugeBound Q s p A F ↔ ∀ N : ℕ, negBesovSupPartialNorm Q s p N F ≤ A := by
  constructor
  · intro h N
    exact negBesovSupPartialNorm_le fun j _ => h j
  · intro h j
    exact le_trans (negBesovLpDepthSeminorm_le_negBesovSupPartialNorm Q s p F (le_refl j)) (h j)

theorem NegBesovSupGaugeBound.nonneg {Q : TriadicCube d} {s p A : ℝ} {F : Vec d → Vec d}
    (h : NegBesovSupGaugeBound Q s p A F) : 0 ≤ A :=
  le_trans (negBesovLpDepthSeminorm_nonneg Q s p F 0) (h 0)

/-! ## 3. The clause sibling at the sup left-hand side -/

/-- **THE SUP-FORM MULTISCALE CLAUSE** — the print's own aggregation.

The transcribed multiscale clause with the left-hand
`ℓ^p`-over-depths aggregate replaced by the sup, i.e. the manuscript's Step-3
display shape.  The energy slot is deliberately LEFT at its
`ℓ^p` spelling: that slot is the one the finite-`p` `CoarseGraining` theorem
(`exists_localCoarseGrainingLp`) supplies, and moving it to the sup is the D3
question, not a transcription choice (section 5).

THIS IS A HYPOTHESIS.  It is never proved in this repository. -/
def CoarseGrainingSupMultiscale (Q : TriadicCube d) (jn : ℕ)
    (Ccg s s1 s2 p sigma E1 E2 Dg : ℝ)
    (Gen : TriadicCube d → ℝ) (Fgrad Fflux : Vec d → Vec d) : Prop :=
  ∀ S : ℝ, (∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S) →
    ∀ N : ℕ,
      sigma * negBesovSupPartialNorm Q s p N Fgrad +
          negBesovSupPartialNorm Q s p N Fflux ≤
        coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ))

/-- **The Step-3c leg of the sup-form clause.**

The flux leg is discarded (the source's own route (ii) in the paper) and the
printed `σ_m` weight stripped; the output is the sup-form gauge bound at the
level the Step-3c consumers take. -/
theorem CoarseGrainingSupMultiscale.gradGauge {Q : TriadicCube d} {jn : ℕ}
    {Ccg s s1 s2 p sigma E1 E2 Dg : ℝ} {Gen : TriadicCube d → ℝ}
    {Fgrad Fflux : Vec d → Vec d}
    (h : CoarseGrainingSupMultiscale Q jn Ccg s s1 s2 p sigma E1 E2 Dg Gen Fgrad Fflux)
    {S : ℝ} (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p (s - s1) jn N Gen ≤ S)
    (hsigma : 0 < sigma) :
    NegBesovSupGaugeBound Q s p
      (sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)))
      Fgrad := by
  refine negBesovSupGaugeBound_iff_forall_partial.mpr fun N => ?_
  have hmain := h S hS N
  have hflux : (0 : ℝ) ≤ negBesovSupPartialNorm Q s p N Fflux :=
    negBesovSupPartialNorm_nonneg Q s p N Fflux
  have hstep : sigma * negBesovSupPartialNorm Q s p N Fgrad ≤
      coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) := by
    linarith only [hmain, hflux]
  have hne : sigma ≠ 0 := ne_of_gt hsigma
  calc negBesovSupPartialNorm Q s p N Fgrad
      = sigma⁻¹ * (sigma * negBesovSupPartialNorm Q s p N Fgrad) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ ≤ sigma⁻¹ * coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S (Q.scale - (jn : ℤ)) :=
        mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hsigma.le)

/-! ## 4. THE CONSUMPTION INTERFACE: one depth at a time -/

/-- **The single-depth grid/smooth-dual comparison.**

The depth-summed grid/smooth-dual converse asks for the FULL
`ℓ^p`-over-depths Besov seminorm against the smooth dual — that is the shape
refuted above, because the depth sum contributes `(1-3^{-sp})^{-1/p}`.  The
sup-form clause never forms that sum: it needs the comparison at ONE depth `j`
at a time, with the constant `CA` uniform in `j`,

```text
  ( 3^{sp(m-j)} avsum_{R ∈ D_j} ‖(F)_R‖^p )^{1/p}
      ≤ CA · ‖F‖_{W_hat^{-s,p}(□_m), smooth dual}.
```

THIS IS A HYPOTHESIS, and it is the ONLY external input of
`supGauge_of_depthConverse`.  It is the slot the single-depth dual-test family
(a dual test family at one depth) fills: one test function per depth, not
one test function per depth-tower. -/
def NegativeBesovGridSmoothDualConverseAtDepth (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (j : ℕ) (CA : ℝ≥0∞) : Prop :=
  ∀ F : CubeEuclideanLpField Q FiniteLpExponent.two,
    cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (1 / p.exponent.toReal) ≤
      CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F

/-- **One depth term of this development gauge against the smooth dual.**

The depth-`j` bridge `ofReal_negBesovLpDepthSeminorm_rpow_le`, rooted, composed
with the single-depth comparison.  No sum over depths occurs. -/
theorem ofReal_negBesovLpDepthSeminorm_le_of_depthConverse (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {CA : ℝ≥0∞} {j : ℕ}
    (hconv : NegativeBesovGridSmoothDualConverseAtDepth Q s p j CA)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) := by
  have ht : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  have hbase := ofReal_negBesovLpDepthSeminorm_rpow_le Q s p F j
  have hpow : (ENNReal.ofReal
      (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j)) ^ p.exponent.toReal ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j := by
    rw [ENNReal.ofReal_rpow_of_nonneg
      (negBesovLpDepthSeminorm_nonneg Q s.1 p.exponent.toReal F.toField j) ht.le]
    exact hbase
  have hroot := ENNReal.rpow_le_rpow hpow
    (by positivity : (0 : ℝ) ≤ 1 / p.exponent.toReal)
  have hleft : ((ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j)) ^ p.exponent.toReal) ^
        (1 / p.exponent.toReal) =
      ENNReal.ofReal (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt ht), ENNReal.rpow_one]
  have hright : (ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) ^ p.exponent.toReal *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^ (1 / p.exponent.toReal) =
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        cubeEuclideanNegativeBesovDepthEnergy Q s p F j ^ (1 / p.exponent.toReal) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p.exponent.toReal),
      ← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt ht), ENNReal.rpow_one]
  rw [hleft, hright] at hroot
  exact hroot.trans (mul_le_mul' le_rfl (hconv F))

/-- **THE SUP-FORM GAUGE, FROM THE SINGLE-DEPTH COMPARISON ALONE.**

Given the single-depth comparison at every depth with one constant `CA`, the
whole sup-over-depths partial gauge is below `√d · 3^{-sm} · CA` times the
smooth dual norm — with NO geometric factor and NO depth sum, because the sup
is realized depth-wise.

This is the exact shape in which the sup-form clause consumes the family. -/
theorem ofReal_negBesovSupPartialNorm_le_of_depthConverse (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {CA : ℝ≥0∞} (N : ℕ)
    (hconv : ∀ j : ℕ, NegativeBesovGridSmoothDualConverseAtDepth Q s p j CA)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    ENNReal.ofReal (negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField) ≤
      ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
        (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) := by
  classical
  set B : ℝ≥0∞ := ENNReal.ofReal (gridScaleGauge d s.1 Q.scale) *
    (CA * cubeEuclideanNegativeWspSmoothDualENorm Q s p F) with hB
  by_cases hBtop : B = ⊤
  · rw [hBtop]; exact le_top
  have hreal : ∀ j : ℕ, negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j ≤
      B.toReal := by
    intro j
    have hj := ofReal_negBesovLpDepthSeminorm_le_of_depthConverse Q s p (hconv j) F
    have hle : ENNReal.ofReal
        (negBesovLpDepthSeminorm Q s.1 p.exponent.toReal F.toField j) ≤ B := hj
    have := ENNReal.toReal_mono hBtop hle
    rwa [ENNReal.toReal_ofReal
      (negBesovLpDepthSeminorm_nonneg Q s.1 p.exponent.toReal F.toField j)] at this
  have hsup : negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField ≤ B.toReal :=
    negBesovSupPartialNorm_le fun j _ => hreal j
  calc ENNReal.ofReal (negBesovSupPartialNorm Q s.1 p.exponent.toReal N F.toField)
      ≤ ENNReal.ofReal B.toReal := ENNReal.ofReal_le_ofReal hsup
    _ = B := ENNReal.ofReal_toReal hBtop

end

end Algsuperdiff.Section4.Provider.Homogenization
