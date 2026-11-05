/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffMultiscaleEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ErrorRepresentative22
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ShellNorms

/-!
# Events

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Section 4 good events `𝒢₀`, `𝒢₁`, `𝒢₂` and their intersection

This module renders `d.good.event.for.lambda` (ABK26) as `Set
(Cutoff.CutoffSample d)` valued definitions over the proved Section 3 carriers,
on top of the *public* (measurable) observables of `ShellNorms`,
`ErrorRepresentative22` and `Observable/CutoffMultiscaleEllipticity`.

## Carrier conventions realized here

* **Well-definedness.** Every countable interior — the `k`-supremum of `𝒢₀`,
  the `k`- and `n`-sums of `𝒢₁` and `𝒢₂`, and every lattice maximum — is taken
  in `ℝ≥0∞`, so the events are well defined with no convergence side
  condition, and the thresholds are compared through `ENNReal.ofReal`.
* **Lattice maxima.** The manuscript's `max_{z ∈ 3^j ℤ^d ∩ S}` is the `ℝ≥0∞`
  supremum over the explicit integer enumeration `latticeCubeSet` /
  `latticeAnnulusSet` of the lattice points lying in `S`.  The index type is a
  subtype of `Fin d → ℤ`, hence countable, which is what the measurability
  lemmas consume; the supremum over the empty index is `0`, matching the sign
  convention of the printed maxima (all their entries are nonnegative).
* **Translation.** `λ_{γ,2}^{-1}(z+□_{k−2}; a_{k−2})` and
  `𝓔_{s,2,2}(z+□_n; a_{n−2}, σ_{n−2})` are rendered by translating the
  *sample*, never the cube: `… ∘ Cutoff.translateCutoffSample z`.
* **The coarse-graining constant.** `C_{(e.cg.ellip.lower)}` is the explicit
  real parameter `Ccg`.
* **Positive parts.** `(x)_+` inside `𝒢₀` is realized by `ENNReal.ofReal`, which *is* `max
  x 0` transported to `[0,∞]`; no separate truncation enters.

The cubes `□_j` are the *open* triadic cubes `openCubeSet (originCube d j)`.
The open/half-open choice is immaterial for every lattice enumeration below:
the boundary of `□_j` sits at `|x_i| = 3^j/2`, and `3^j/2` is never an integer
multiple of the lattice spacing `3^i` occurring in the displays, so no lattice
point of `3^i ℤ^d` lies on `∂□_j`.

## Main definitions

* `eventG0`, `eventG1`, `eventG2` —.
* `goodEventBase` — `e.lambda.good.events`.

## Parameter-binder convention (recorded)

`eventG0 M (Ccg : ℝ) (m : ℤ)` and `eventG1 M (m : ℤ) (s T : ℝ)` take plain
real parameters.  `eventG2` and `goodEventBase` take `s : {s : ℝ // 0 < s}`
because the public `𝒢₂` observable `annularErrorObservable` does: the
`(2,2)` measurable representative is selected on the source window `0 < s`.

## References

* ABK26, `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Support

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-! ## The explicit triadic lattice enumerations -/

/-- The point `3^j v` of the lattice `3^j ℤ^d`. -/
def triadicLatticePoint {d : ℕ} (j : ℤ) (v : Fin d → ℤ) : Vec d :=
  fun i => (3 : ℝ) ^ j * (v i : ℝ)

/-- The integer index set of `3^j ℤ^d ∩ □_outer`. -/
def latticeCubeSet (d : ℕ) (j outer : ℤ) : Set (Fin d → ℤ) :=
  {v | triadicLatticePoint j v ∈ openCubeSet (originCube d outer)}

/-- The integer index set of `3^j ℤ^d ∩ (□_outer ∖ □_inner)`. -/
def latticeAnnulusSet (d : ℕ) (j outer inner : ℤ) : Set (Fin d → ℤ) :=
  {v | triadicLatticePoint j v ∈
    openCubeSet (originCube d outer) \ openCubeSet (originCube d inner)}

variable {d : ℕ}

/-! ## The `𝒢₀` ingredients -/

/-- The coarse-ellipticity exponent `q = 2` read by `𝒢₀`'s
`λ_{γ,2}^{-1}`. -/
def coarseEllipticityExponentTwo : CoarseEllipticityExponent :=
  CoarseEllipticityExponent.finite ⟨2, by norm_num⟩

/-- The `𝒢₀` atom `λ_{γ,2}^{-1}(z+□_{k−2}; a_{k−2})`, rendered by translating
the sample (resolution A4).  The `λ`-literal is *genuinely* measurable
(Section 3's literal-measurability engine), so no representative is selected
here. -/
noncomputable def lambdaAnnulusAtom (M : ABKModel d) (k : ℤ) (z : Vec d) :
    Cutoff.CutoffSample d → ℝ :=
  fun omega =>
    Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2) M.gamma
      coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega)

theorem measurable_lambdaAnnulusAtom (M : ABKModel d) (k : ℤ) (z : Vec d) :
    Measurable (lambdaAnnulusAtom M k z) :=
  (Observable.measurable_cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2)
    M.shellPrefix.gamma_pos coarseEllipticityExponentTwo).comp
    (Cutoff.measurable_translateCutoffSample z)

private theorem measurable_shellAt (k : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d => omega.1 k :=
  (measurable_pi_apply k).comp measurable_subtype_coe

/-- The event `𝒢₀(m)` of `d.good.event.for.lambda`:

```
{ sup_{k ≤ m−1} 3^{−γ(m−k)/4}
    max_{z ∈ 3^{k−2}ℤ^d ∩ (□_m ∖ □_k)}
      ( σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; a_{k−2}) − C_{(e.cg.ellip.lower)} )_+
  ≤ 1 }
```
-/
noncomputable def eventG0 (M : ABKModel d) (Ccg : ℝ) (m : ℤ) :
    Set (Cutoff.CutoffSample d) :=
  {omega |
    (⨆ k : {k : ℤ // k ≤ m - 1},
      ENNReal.ofReal
          (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
        ⨆ v : ↥(latticeAnnulusSet d (k.1 - 2) m k.1),
          ENNReal.ofReal
            ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                lambdaAnnulusAtom M k.1 (triadicLatticePoint (k.1 - 2) v.1) omega -
              Ccg)) ≤ 1}

theorem measurableSet_eventG0 (M : ABKModel d) (Ccg : ℝ) (m : ℤ) :
    MeasurableSet (eventG0 M Ccg m) := by
  have h : Measurable fun omega : Cutoff.CutoffSample d =>
      ⨆ k : {k : ℤ // k ≤ m - 1},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * M.gamma * ((m - k.1 : ℤ) : ℝ))) *
          ⨆ v : ↥(latticeAnnulusSet d (k.1 - 2) m k.1),
            ENNReal.ofReal
              ((Annealed.sigmaBar M (k.1 - 3) : ℝ) *
                  lambdaAnnulusAtom M k.1 (triadicLatticePoint (k.1 - 2) v.1) omega -
                Ccg) := by
    refine Measurable.iSup fun k => Measurable.const_mul ?_ _
    refine Measurable.iSup fun v => ?_
    exact ((measurable_lambdaAnnulusAtom M k.1
      (triadicLatticePoint (k.1 - 2) v.1)).const_mul _).sub_const _ |>.ennreal_ofReal
  exact h measurableSet_Iic

/-- `𝒢₀` is monotone in the displayed constant: raising
`C_{(e.cg.ellip.lower)}` lowers every positive part. -/
theorem eventG0_subset_of_le (M : ABKModel d) (m : ℤ) {Ccg Ccg' : ℝ}
    (h : Ccg ≤ Ccg') : eventG0 M Ccg m ⊆ eventG0 M Ccg' m := by
  intro omega homega
  refine le_trans (iSup_mono fun k => mul_le_mul_right (iSup_mono fun v =>
    ENNReal.ofReal_le_ofReal ?_) _) homega
  linarith only [h]

/-- The event `𝒢₁(m; s, T)` of `d.good.event.for.lambda`: the intersection of

```
{ ∑_{k=m}^∞ 3^{(2−γ)m} ‖∇j_k‖_{W^{1,∞}(□_m)} ≤ T }
```

and

```
{ ∑_{n=−∞}^{m} 3^{−s(m−n)/4}
    ∑_{k=n−1}^{m} ( 3^{(2−γ)k} max_{z ∈ 3^kℤ^d ∩ □_m} ‖j_k‖_{W^{2,∞}(z+□_k)} )^2
  ≤ T^2 }
```
-/
noncomputable def eventG1 (M : ABKModel d) (m : ℤ) (s T : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  {omega |
      (∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          shellW1InfGradNorm m (omega.1 k.1))) ≤ ENNReal.ofReal T} ∩
    {omega |
      (∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(latticeCubeSet d k m),
                  ENNReal.ofReal
                    (shellW2InfNormAt (triadicLatticePoint k v.1) k (omega.1 k))) ^ 2) ≤
        ENNReal.ofReal (T ^ 2)}

theorem mem_eventG1_iff (M : ABKModel d) (m : ℤ) (s T : ℝ)
    (omega : Cutoff.CutoffSample d) :
    omega ∈ eventG1 M m s T ↔
      ((∑' k : {k : ℤ // m ≤ k},
          ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
            shellW1InfGradNorm m (omega.1 k.1))) ≤ ENNReal.ofReal T ∧
        (∑' n : {n : ℤ // n ≤ m},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
            ∑ k ∈ Finset.Icc (n.1 - 1) m,
              (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                  ⨆ v : ↥(latticeCubeSet d k m),
                    ENNReal.ofReal
                      (shellW2InfNormAt (triadicLatticePoint k v.1) k (omega.1 k))) ^ 2) ≤
          ENNReal.ofReal (T ^ 2)) :=
  Iff.rfl

theorem measurableSet_eventG1 (M : ABKModel d) (m : ℤ) (s T : ℝ) :
    MeasurableSet (eventG1 M m s T) := by
  have h1 : Measurable fun omega : Cutoff.CutoffSample d =>
      ∑' k : {k : ℤ // m ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (m : ℝ)) *
          shellW1InfGradNorm m (omega.1 k.1)) := by
    refine Measurable.tsum (L := SummationFilter.unconditional {k : ℤ // m ≤ k}) fun k => ?_
    exact ((measurable_shellW1InfGradNorm m).comp (measurable_shellAt k.1)).const_mul
      _ |>.ennreal_ofReal
  have h2 : Measurable fun omega : Cutoff.CutoffSample d =>
      ∑' n : {n : ℤ // n ≤ m},
        ENNReal.ofReal
            (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * s * ((m - n.1 : ℤ) : ℝ))) *
          ∑ k ∈ Finset.Icc (n.1 - 1) m,
            (ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (k : ℝ))) *
                ⨆ v : ↥(latticeCubeSet d k m),
                  ENNReal.ofReal
                    (shellW2InfNormAt (triadicLatticePoint k v.1) k (omega.1 k))) ^ 2 := by
    refine Measurable.tsum (L := SummationFilter.unconditional {n : ℤ // n ≤ m})
      fun n => Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ fun k _ => Measurable.pow_const ?_ 2
    refine Measurable.const_mul (Measurable.iSup fun v => ?_) _
    exact ((measurable_shellW2InfNormAt (triadicLatticePoint k v.1) k).comp
      (measurable_shellAt k)).ennreal_ofReal
  exact (h1 measurableSet_Iic).inter (h2 measurableSet_Iic)

/-- `𝒢₁` is monotone in its threshold. -/
theorem eventG1_subset_of_le (M : ABKModel d) (m : ℤ) (s : ℝ) {T T' : ℝ}
    (hT : 0 ≤ T) (h : T ≤ T') : eventG1 M m s T ⊆ eventG1 M m s T' := by
  rintro omega ⟨h1, h2⟩
  exact ⟨h1.trans (ENNReal.ofReal_le_ofReal h),
    h2.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hT h 2))⟩

/-- The event `𝒢₂(m; s, ε)` of `d.good.event.for.lambda`:

```
{ s ∑_{j=−∞}^{m} ∑_{n=−∞}^{j−1} 3^{−s(m−n)/4}
    max_{z ∈ 3^nℤ^d ∩ (□_j ∖ □_{j−1})} 𝓔_{s,2,2}(z+□_n; a_{n−2}, σ_{n−2})^2
  ≤ ε^2 }
```

The square sits inside the lattice maximum, exactly as printed. -/
noncomputable def eventG2 (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (ep : ℝ) : Set (Cutoff.CutoffSample d) :=
  {omega |
    ENNReal.ofReal (s : ℝ) *
        (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
            ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
              ENNReal.ofReal
                (annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1) omega) ^ 2)) ≤
      ENNReal.ofReal (ep ^ 2)}

theorem mem_eventG2_iff (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (ep : ℝ) (omega : Cutoff.CutoffSample d) :
    omega ∈ eventG2 M m s ep ↔
      ENNReal.ofReal (s : ℝ) *
          (∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
            ENNReal.ofReal
                (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
              ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
                ENNReal.ofReal
                  (annularErrorObservable M n.1 s
                    (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1)
                      omega) ^ 2)) ≤
        ENNReal.ofReal (ep ^ 2) :=
  Iff.rfl

theorem measurableSet_eventG2 (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    (ep : ℝ) : MeasurableSet (eventG2 M m s ep) := by
  have h : Measurable fun omega : Cutoff.CutoffSample d =>
      ENNReal.ofReal (s : ℝ) *
        ∑' j : {j : ℤ // j ≤ m}, ∑' n : {n : ℤ // n ≤ j.1 - 1},
          ENNReal.ofReal
              (Real.rpow (3 : ℝ) (-(1 / 4 : ℝ) * (s : ℝ) * ((m - n.1 : ℤ) : ℝ))) *
            ⨆ v : ↥(latticeAnnulusSet d n.1 j.1 (j.1 - 1)),
              ENNReal.ofReal
                (annularErrorObservable M n.1 s
                  (Cutoff.translateCutoffSample (triadicLatticePoint n.1 v.1)
                    omega) ^ 2) := by
    refine Measurable.const_mul ?_ _
    refine Measurable.tsum (L := SummationFilter.unconditional {j : ℤ // j ≤ m}) fun j =>
      Measurable.tsum (L := SummationFilter.unconditional {n : ℤ // n ≤ j.1 - 1}) fun n => ?_
    refine Measurable.const_mul (Measurable.iSup fun v => ?_) _
    exact (((measurable_annularErrorObservable M n.1 s).comp
      (Cutoff.measurable_translateCutoffSample
        (triadicLatticePoint n.1 v.1))).pow_const 2).ennreal_ofReal
  exact h measurableSet_Iic

/-- `𝒢₂` is monotone in its threshold. -/
theorem eventG2_subset_of_le (M : ABKModel d) (m : ℤ) (s : {s : ℝ // 0 < s})
    {ep ep' : ℝ} (hep : 0 ≤ ep) (h : ep ≤ ep') :
    eventG2 M m s ep ⊆ eventG2 M m s ep' := fun _ homega =>
  homega.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hep h 2))

/-! ## The composed good event -/

/-- The composed good event `𝒢(m; s, ε)` of `e.lambda.good.events`:

```
𝒢(m; s, ε) = 𝒢₀(m) ∩ 𝒢₁(m; s, s ε c⋆^{1/2} γ^{−1/2}) ∩ 𝒢₂(m; s, ε).
```

The translate `𝒢(m, y; s, ε)` is
`Cutoff.translateCutoffSample y ⁻¹' goodEventBase M Ccg m s ep` (resolution
A4); it is not introduced here. -/
noncomputable def goodEventBase (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) : Set (Cutoff.CutoffSample d) :=
  eventG0 M Ccg m ∩
    eventG1 M m (s : ℝ)
      ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) ∩
    eventG2 M m s ep

theorem measurableSet_goodEventBase (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    MeasurableSet (goodEventBase M Ccg m s ep) :=
  ((measurableSet_eventG0 M Ccg m).inter
      (measurableSet_eventG1 M m (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))).inter
    (measurableSet_eventG2 M m s ep)

theorem goodEventBase_subset_eventG0 (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    goodEventBase M Ccg m s ep ⊆ eventG0 M Ccg m := fun _ h => h.1.1

theorem goodEventBase_subset_eventG1 (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    goodEventBase M Ccg m s ep ⊆
      eventG1 M m (s : ℝ)
        ((s : ℝ) * ep * Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹) :=
  fun _ h => h.1.2

theorem goodEventBase_subset_eventG2 (M : ABKModel d) (Ccg : ℝ) (m : ℤ)
    (s : {s : ℝ // 0 < s}) (ep : ℝ) :
    goodEventBase M Ccg m s ep ⊆ eventG2 M m s ep := fun _ h => h.2

end

end Algsuperdiff.Section4.Support
