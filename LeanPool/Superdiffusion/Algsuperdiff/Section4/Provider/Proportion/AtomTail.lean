/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.Nonlocal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.CgEllipLowerConstant

/-!
# AtomTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The per-atom `Γ_{1/3}` tail of the `𝒢₀` bracket

ABK26, §4.1, `l.good.scales.ratio.lambda`, the per-annulus atom tail, display:

```
( σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; 𝐚_{k−2}) − C_{(e.cg.ellip.lower)} )_+
  ≤ 𝒪_{Γ_{1/3}} ( exp( − C^{−1} c⋆² γ^{−1} ) ) ,      k ∈ ℤ.
```

The left side is `Localize.cgExcess M Ccg (k−2) z` at the definite
constant `Support.cgEllipLowerConstant d` (the *same* choice the frozen `𝒢₀`
uses, so no cross-anchor witness mismatch is possible).  The right side is
produced here from the Section 3 anchor
`Frozen.Section3.coarse_ellipticity_bounds` alone.

## What the anchor gives, and how it is instantiated

The anchor's lower leg is a `Probability.IsLowerIntegerFamilyOrlicz`: ONE
measurable witness `Y` with

* `∀ ω, ∀ L ≥ m−1,  λ_{s,q}^{-1}(□_m; 𝐚_L)(ω) · σ_{m−1} ≤ b + Y ω`, and
* `Y ≤ 𝒪_{Γ_{(1−σ)/2}}(exp(−(C_cg^{−1} E^{−2} γ^{−1})))`,

for `b = lowerEllipticityProfile C_cg γ s q`.  The instantiation used here is

| anchor slot | value | why |
|---|---|---|
| `m` | `k − 2` | the `𝒢₀` bracket's cube index; then `m − 1 = k − 3` is its `σ` index |
| `L` | `k − 2` | the `𝒢₀` bracket's truncation index; `k − 2 ≥ k − 3` |
| `σ` | `1/3` | `Γ_{(1−σ)/2} = Γ_{1/3}` is the tex's index (graph) |
| `q` | `Support.coarseEllipticityExponentTwo` | `𝒢₀` reads `λ_{γ,2}^{-1}` |
| `s` | `M.gamma` | `𝒢₀` reads `λ_{γ,2}^{-1}` |

At `s = γ` and `q = 2` the deterministic shift collapses to the bare constant,
`lowerEllipticityProfile C_cg γ γ 2 = C_cg γ (2γ−γ)^{−1} = C_cg`
(`lowerEllipticityProfile_two_diag`), which is *why* the manuscript's
`C_{(e.cg.ellip.lower)}` is a pure constant and why the bracket subtracted
inside `𝒢₀` is exactly the anchor's own shift.

## The lattice `z`: stationarity, not a new estimate

The `𝒢₀` bracket at the lattice centre `z` is the origin bracket read at the
translated sample.  The tail therefore transfers by the law-level
stationarity `GoodEvents.measurePreserving_translateCutoffSample` (valid for
real `z`), through the generic device `isBigOWith_comp_measurePreserving`
proved below.  No per-`z` instance of the anchor is used, and no lattice
restriction is needed.

## References

* ABK26, `l.good.scales.ratio.lambda`, statement, proof; the atom-tail step.
* `p.cg.ellipticity.bounds` = `Frozen.Section3.coarse_ellipticity_bounds`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

/-! ## 1. Two generic weak-Orlicz devices -/

section Generic

variable {Omega : Type*} [MeasurableSpace Omega]

/-- **A weak-Orlicz upper tail transports along a measure-preserving map.** The
tail event of `X ∘ T` is the `T`-preimage of the tail event of `X`, and a
measure-preserving map does not change its mass.  This is the device that turns
the origin-centred estimate into the estimate at an arbitrary lattice centre. -/
theorem isBigOWith_comp_measurePreserving {mu : Measure Omega} {Psi : ℝ → ℝ}
    {X : Omega → ℝ} {A : ℝ} {T : Omega → Omega}
    (hT : MeasurePreserving T mu mu) (hX : Measurable X)
    (h : IsBigOWith mu Psi X A) :
    IsBigOWith mu Psi (fun omega => X (T omega)) A := by
  intro t ht
  have hmeas : MeasurableSet (upperTailEvent X (A * t)) :=
    measurableSet_lt measurable_const hX
  have hset : upperTailEvent (fun omega => X (T omega)) (A * t)
      = T ⁻¹' upperTailEvent X (A * t) := rfl
  rw [hset, hT.measureReal_preimage hmeas.nullMeasurableSet]
  exact h ht

/-- **Clamping at zero does not change a weak-Orlicz upper tail at a positive
scale.**  For `A > 0` and `t ≥ 1` the level `A t` is positive, so the tail events
of `X` and of `max X 0` coincide.  This is what turns the anchor's witness `Y`
into a bound for the positive part `(·)_+`. -/
theorem isBigOWith_max_zero {mu : Measure Omega} {Psi : ℝ → ℝ} {X : Omega → ℝ}
    {A : ℝ} (hA : 0 < A) (h : IsBigOWith mu Psi X A) :
    IsBigOWith mu Psi (fun omega => max (X omega) 0) A := by
  intro t ht
  have hAt : 0 < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hset : upperTailEvent (fun omega => max (X omega) 0) (A * t)
      = upperTailEvent X (A * t) := by
    ext omega
    simp only [upperTailEvent, Set.mem_ofPred_eq, lt_max_iff]
    constructor
    · rintro (h1 | h2)
      · exact h1
      · exact absurd h2 (not_lt.2 hAt.le)
    · exact fun h1 => Or.inl h1
  rw [hset]
  exact h ht

end Generic

/-! ## 2. The deterministic shift at the diagonal window `s = γ`, `q = 2` -/

/-- **`lowerEllipticityProfile C γ γ 2 = C`.**  The anchor's deterministic shift at
the `𝒢₀` parameters is the bare constant: the pole `s (2s − γ)^{−1}` equals `1`
on the diagonal `s = γ`.  This is the identification that lets the `𝒢₀` bracket
subtract the anchor's own shift and call it `C_{(e.cg.ellip.lower)}`. -/
theorem lowerEllipticityProfile_two_diag (C gamma : ℝ) (hgamma : gamma ≠ 0) :
    lowerEllipticityProfile C gamma gamma Support.coarseEllipticityExponentTwo = C := by
  change (if (2 : ℝ) < 2 then C * Real.rpow (gamma / (2 * gamma - gamma)) (2 / 2)
      else C * gamma * (2 * gamma - gamma)⁻¹) = C
  rw [ite_eq_right (by norm_num : ¬((2 : ℝ) < 2))]
  rw [show (2 : ℝ) * gamma - gamma = gamma by ring, mul_assoc,
    mul_inv_cancel₀ hgamma, mul_one]

/-! ## 3. The Orlicz amplitude -/

variable {d : ℕ}

/-- **The amplitude of the coarse-ellipticity display**, `exp(−(C_cg^{−1} E^{−2}
γ^{−1}))`.  At the budget `E = C c⋆^{−1}` supplied this is `exp(−(C_cg C²)^{−1}
c⋆² γ^{−1})`, the manuscript's `exp(−C^{−1} c⋆² γ^{−1})`. -/
def cgTailScale (M : ABKModel d) (E : ℝ) : ℝ :=
  Real.exp (-((Support.cgEllipLowerConstant d)⁻¹ * (E⁻¹) ^ 2 * M.gamma⁻¹))

theorem cgTailScale_pos (M : ABKModel d) (E : ℝ) : 0 < cgTailScale M E :=
  Real.exp_pos _

/-! ## 4. The per-atom tail -/

/-- **The `𝒢₀` atom tail, at the anchor's own premises.**

```
( σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; 𝐚_{k−2}) − C_{(e.cg.ellip.lower)} )_+
  ≤ 𝒪_{Γ_{1/3}} ( exp(−(C_cg^{−1} E^{−2} γ^{−1})) )
```

for `k ∈ ℤ` real centre `z` (in particular every triadic lattice point).  The
constant subtracted is `Support.cgEllipLowerConstant d`, the same definite
choice the frozen `𝒢₀` uses.

The hypotheses are exactly the anchor's, at `σ = 1/3`, `s = γ`, `q = 2`:
`hstate` is `𝒮(k−3, E)`, `hE` and `hEup` are its `E`-window, and `hwin` is its
`s`-window read at `s = γ`. -/
theorem isBigOWith_cgExcess_of_state (M : ABKModel d) {E : {E : ℝ // 1 ≤ E}}
    (k : ℤ) (z : Vec d)
    (hstate : Algsuperdiff.Frozen.Section3.inductionState M (k - 3) E)
    (hE : max (Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
        (Disorder.cstar M)⁻¹ ≤ (E : ℝ))
    (hEup : (E : ℝ) ≤ M.gamma ^ (-(1 / 5 : ℝ)))
    (hwin : cgTailScale M (E : ℝ) ≤ M.gamma / 2) :
    IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega =>
        Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
      (cgTailScale M (E : ℝ)) := by
  classical
  have hgamma0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgamma4 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  -- the anchor at the definite constant
  have hspec := (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d).choose_spec
  have hsigma : (1 / 3 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hsWindow : M.gamma ∈
      Set.Icc (M.gamma / 2 +
        Real.exp (-((Support.cgEllipLowerConstant d)⁻¹ * (((E : ℝ))⁻¹) ^ 2 * M.gamma⁻¹)))
        (1 : ℝ) := by
    refine ⟨?_, by linarith only [hgamma4]⟩
    have h := hwin
    rw [cgTailScale] at h
    linarith only [h]
  obtain ⟨hlower, -⟩ :=
    hspec.2 M (k - 2) E (by
        have : k - 2 - 1 = k - 3 := by ring
        rw [this]; exact hstate)
      (1 / 3 : ℝ) hsigma hE hEup Support.coarseEllipticityExponentTwo M.gamma hsWindow
  -- the single witness of the lower leg
  obtain ⟨Y, hY⟩ := hlower
  -- the Orlicz index of the anchor at `σ = 1/3`
  have hindex : ((1 : ℝ) - 1 / 3) / 2 = 1 / 3 := by norm_num
  rw [hindex] at hY
  -- the deterministic shift collapses to the bare constant
  have hshift :
      lowerEllipticityProfile
          (Algsuperdiff.Frozen.Section3.coarse_ellipticity_bounds d).choose M.gamma
          M.gamma Support.coarseEllipticityExponentTwo = Support.cgEllipLowerConstant d :=
    lowerEllipticityProfile_two_diag _ _ (ne_of_gt hgamma0)
  rw [hshift] at hY
  -- the tail of the clamped, translated witness
  have htail : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma (1 / 3 : ℝ))
      (fun omega => max (Y (Cutoff.translateCutoffSample z omega)) 0)
      (cgTailScale M (E : ℝ)) := by
    refine isBigOWith_comp_measurePreserving
      (GoodEvents.measurePreserving_translateCutoffSample M z)
      (hY.measurable_witness.max measurable_const) ?_
    exact isBigOWith_max_zero (cgTailScale_pos M (E : ℝ)) hY.tail
  refine htail.of_le ?_
  intro omega
  -- the pointwise domination, at the single index `L = k − 2 ≥ k − 3`
  have hdom := hY.dominates (Cutoff.translateCutoffSample z omega) (k - 2) (by omega)
  have hlit :
      Observable.cutoffLowerEllipticityInv M (k - 2) (k - 2) M.gamma
          (by
            exact lt_of_lt_of_le
              (add_pos (div_pos hgamma0 (by norm_num)) (Real.exp_pos _)) hsWindow.1)
          Support.coarseEllipticityExponentTwo
          (Cutoff.translateCutoffSample z omega) =
        Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2) M.gamma
          Support.coarseEllipticityExponentTwo
          (Cutoff.translateCutoffSample z omega) :=
    congrFun (Observable.cutoffLowerEllipticityInv_eq_literal M (k - 2) (k - 2)
      M.gamma _ Support.coarseEllipticityExponentTwo) _
  rw [hlit] at hdom
  have hidx : k - 2 - 1 = k - 3 := by ring
  rw [hidx] at hdom
  simp only [Localize.cgExcess]
  refine max_le_max ?_ le_rfl
  have hcomm : (Annealed.sigmaBar M (k - 2 - 1) : ℝ) *
      Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2) M.gamma
        Support.coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega)
      = Observable.cutoffLowerEllipticityInvLiteral M (k - 2) (k - 2) M.gamma
          Support.coarseEllipticityExponentTwo (Cutoff.translateCutoffSample z omega) *
        (Annealed.sigmaBar M (k - 3) : ℝ) := by
    rw [hidx]; ring
  rw [hcomm]
  linarith only [hdom]

/-! ## 5. The packaged form, through's all-scales budget -/

/-- **The `𝒢₀` atom tail in the printed shape.**

There is a dimensional constant `C(d)` such that every model in the printed
regime `γ ≤ C^{−10} c⋆^{10}` — and satisfying the anchor's own `s`-window at `s
= γ` — has, for every `k ∈ ℤ` and every real centre `z`,

```
( σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; 𝐚_{k−2}) − C_{(e.cg.ellip.lower)} )_+
  ≤ 𝒪_{Γ_{1/3}} ( exp(−(C_cg C²)^{−1} c⋆² γ^{−1}) ) ,
```

the amplitude being the manuscript's `exp(−C^{−1} c⋆² γ^{−1})` after the
`E = C c⋆^{−1}` substitution `E^{−2} = C^{−2} c⋆²`.

The induction state and both `E`-window premises of `p.cg.ellipticity.bounds`
are discharged here, by `exists_allScalesInductionState_ge` at the floor
`(3/2)·exp(3 C_cg)` and the proved `c⋆ ≤ 3/2`.  The `s`-window premise `hwin` is passed
through: it is the anchor's own window and is a caller obligation. -/
theorem exists_cgExcess_atomTail (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            (cgTailScale M (E : ℝ) ≤ M.gamma / 2 →
              ∀ (k : ℤ) (z : Vec d),
                IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                  (gammaSigma (1 / 3 : ℝ))
                  (fun omega =>
                    Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
                  (cgTailScale M (E : ℝ))) := by
  classical
  obtain ⟨C, hC6, hCfloor, hall⟩ :=
    GoodEvents.exists_allScalesInductionState_ge d
      (3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
  refine ⟨C, hC6, ?_⟩
  intro M hreg
  obtain ⟨E, hEval, hEreg, hstate⟩ := hall M hreg
  refine ⟨E, hEval, ?_⟩
  intro hwin k z
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hcs0]
    calc Disorder.cstar M ≤ 3 / 2 := hcs
      _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
  have hexp0 : (0 : ℝ) < Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) :=
    Real.exp_pos _
  -- `exp(3 C_cg) ≤ E`, from the floor `C ≥ (3/2) exp(3 C_cg)` and `c⋆⁻¹ ≥ 2/3`
  have hexpE : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) ≤ (E : ℝ) := by
    have hstep : 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
        (Disorder.cstar M)⁻¹ ≤ (E : ℝ) :=
      GoodEvents.mul_cstarInv_le_of_budget M hEval hCfloor
    have hlow : Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
        ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
          (Disorder.cstar M)⁻¹ := by
      have h := mul_le_mul_of_nonneg_left hcsinv
        (by positivity : (0 : ℝ) ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)))
      calc Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ))
          = 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) * (2 / 3) := by
            ring
        _ ≤ 3 / 2 * Real.exp (Support.cgEllipLowerConstant d / (1 / 3 : ℝ)) *
              (Disorder.cstar M)⁻¹ := h
    exact le_trans hlow hstep
  have hEwindow := GoodEvents.coarseEllipticityBudget M hEval
    (le_trans (by norm_num) hC6) hEreg hstate hexpE (k - 2)
  refine isBigOWith_cgExcess_of_state M k z ?_ hEwindow.2.1 hEwindow.2.2 hwin
  have hidx : k - 2 - 1 = k - 3 := by ring
  rw [hidx] at hEwindow
  exact hEwindow.1

end

end Algsuperdiff.Section4.Provider.Proportion
