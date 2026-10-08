/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.QuadraticResponseRecombination
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.WeakEstimateFenchelBound
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# High-contrast homogenization: Entry.Response.Direct.TerminalEnergyDeficitBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Terminal-Optimizer Replacement Engine

At a response maximizer the pathwise response is half the unweighted variation energy, so
replacing the terminal-cell optimizer's energy by the pathwise response leaves exactly the `(φ -
1)`-weighted optimizer energy, the cost of the terminal-optimizer replacement in the centred
cutoff decomposition of AK.HC (3.45)-(3.54). The competitor-splitting identity `∇v · b ∇v
− ∇w · b ∇w = (∇v − ∇w) · symmPart(b) (∇v + ∇w)` together with Cauchy-Schwarz
for the positive semidefinite averaged form `symmPart(a)` bounds the energy defect between two
competitors by the square roots of their averaged difference and sum energies. Restricting the
terminal optimizer to a subcell gives an admissible competitor there, and combining these facts
bounds the discrepancy between the terminal optimizer's half energy and a subcell's response by
that subcell's deficit, `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J(V)| ≤ D + 2√(J(V) · D)`.

Paper: the terminal-optimizer replacement of `p.response.transfer`.
-/

section
/-!
## The congruence toolbox of the almost-everywhere elliptic representative

A point of the coefficient carrier is elliptic only almost everywhere, while the variational
identities of the response are stated for a pointwise elliptic coefficient.  The elliptic
representative supplies, for each sample, a pointwise elliptic field agreeing almost everywhere
with the carrier coefficient on the parent domain, and `Response.aHarmonicOfAEEq` carries a
harmonic function along that replacement.  This module records the invariances the first error row
of `p.response.transfer` still needs: restriction of ellipticity to a measurable subset,
invariance of `ResponseJ` on a subset, the averaged response and the `ψ`-weighted variation energy
of a carried-along harmonic function, and the transport of their `IntegrableOn` facts.
-/

open HCPolySupport.HighContrast.CG

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Ellipticity restricts to a measurable subset. -/
theorem isEllipticFieldOn_subset {d : ℕ} {lam Lam : ℝ} {U V : Set (Vec d)} {f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U f) (hVU : V ⊆ U) (hV : MeasurableSet V) :
    IsEllipticFieldOn lam Lam V f :=
  IsEllipticFieldOn.mono hEll hV hVU

/-- The response `ResponseJ` on a subset is unchanged by an almost-everywhere replacement of the
coefficient on the parent. -/
theorem responseJ_congr_of_ae_eq_subset {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {a b : CoeffField d} (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) :
    ResponseJ V p r a = ResponseJ V p r b := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  exact responseJ_congr_of_ae_eq habV p r

/-- The averaged response integrand of a carried-along harmonic function, on a subset. -/
theorem volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) (u : AHarmonicFunction a U) :
    volumeAverage V (scalarResponseIntegrand U b p r (Response.aHarmonicOfAEEq h u))
      = volumeAverage V (scalarResponseIntegrand U a p r u) := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [habV] with x hx
  simp only [scalarResponseIntegrand, Response.aHarmonicOfAEEq_grad, ← hx]

/-- The averaged `ψ`-weighted variation energy of a carried-along harmonic function, on a subset:
weighting by an arbitrary scalar function changes nothing in the transport. -/
theorem volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
    {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (ψ : Vec d → ℝ) (u : AHarmonicFunction a U) :
    volumeAverage V (fun x => ψ x *
        scalarVariationEnergyIntegrand b (Response.aHarmonicOfAEEq h u) x)
      = volumeAverage V (fun x => ψ x * scalarVariationEnergyIntegrand a u x) := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  unfold volumeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [habV] with x hx
  simp only [scalarVariationEnergyIntegrand, Response.aHarmonicOfAEEq_grad, ← hx]

/-- An `IntegrableOn` fact transports across the carried-along harmonic function, for the
response integrand of the parent, restricted to a subset. -/
theorem integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff {d : ℕ}
    {U V : Set (Vec d)} (hVU : V ⊆ U) {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p r : Vec d) (u : AHarmonicFunction a U)
    (hint : MeasureTheory.IntegrableOn (scalarResponseIntegrand U a p r u) V) :
    MeasureTheory.IntegrableOn
      (scalarResponseIntegrand U b p r (Response.aHarmonicOfAEEq h u)) V := by
  have habV : a =ᵐ[volumeMeasureOn V] b :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) h
  have hcongr :
      (scalarResponseIntegrand U a p r u)
        =ᵐ[volumeMeasureOn V]
      (scalarResponseIntegrand U b p r (Response.aHarmonicOfAEEq h u)) := by
    filter_upwards [habV] with x hx
    simp only [scalarResponseIntegrand, Response.aHarmonicOfAEEq_grad, ← hx]
  exact hint.congr hcongr

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff energy defect as a `(φ − 1)`-weighted energy

At a response maximizer the pathwise response `J(U; p, r; b)` of AK.HC (2.9) is half the
unweighted variation energy.  Consequently, in the centred cutoff decomposition of
AK.HC (3.45)-(3.54), replacing the terminal optimizer energy by the pathwise response leaves
exactly the `(φ − 1)`-weighted optimizer energy: the cost of the terminal-optimizer replacement
is the fluctuation of the optimizer energy against the cutoff, and `φ − 1` has mean zero on the
cell where `φ` has mean one.

* `cutoffHalfEnergy_sub_respJ_eq` — the first error row `e1`: the terminal-optimizer replacement
  costs exactly the `(φ − 1)`-weighted energy.
* `volumeAverage_sub_one_eq_zero` — a cutoff of mean one has mean-zero fluctuation.

Paper: AK.HC (3.45)-(3.54).
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The doubled optimizer energy `⟨Z₁, Z₂⟩ = ∇v · b ∇v` agrees pointwise with the variation
energy `∇v · (symmPart b) ∇v`: the antisymmetric part of `b` contributes nothing to the
quadratic form. -/
private theorem vecDot_optimizerField_eq {d : ℕ} (b : CoeffField d) {U : Set (Vec d)}
    (v : AHarmonicFunction b U) :
    (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
  funext x
  simp only [optimizerField, scalarVariationEnergyIntegrand]
  exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm

/-- **The cutoff energy defect `e1`.**  For a response maximizer `v` of the loads `(p, r)` in the
adapted cell `⋄_t^q`, the cutoff-weighted half optimizer energy differs from the pathwise
response `J(U; p, r; b)` by half the `(φ − 1)`-weighted optimizer energy.  This is the exact
algebraic form of the first error row of the centred cutoff decomposition AK.HC (3.45)-(3.54):
the terminal-optimizer replacement costs the `(φ − 1)`-weighted energy, and `φ − 1` has mean
zero on the cell.  The side conditions are the integrability hypotheses of the CoarseGraining
energy–response identity together with the integrability of the weighted energy. -/
theorem cutoffHalfEnergy_sub_respJ_eq {d : ℕ} {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (φ : Vec d → ℝ) (p r : Vec d) (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hv : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b v)
    (hu_int : weakFluxIntegrable (HighContrast.adaptedCell q t) b v)
    (hresp_u : IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) b p r v)
      (HighContrast.adaptedCell q t))
    (hlin_self : IntegrableOn
      (scalarFirstVariationIntegrand (HighContrast.adaptedCell q t) b p r v v)
      (HighContrast.adaptedCell q t))
    (henergy : IntegrableOn (scalarVariationEnergyIntegrand b v) (HighContrast.adaptedCell q t))
    (hφD : IntegrableOn
      (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      (HighContrast.adaptedCell q t)) :
    (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
        (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      - respJ q t p r b
    = (1 / 2 : ℝ) * volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2) := by
  have _ := hq
  have _ := hEll
  have hD_eq := vecDot_optimizerField_eq b v
  have hD_int : IntegrableOn
      (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      (HighContrast.adaptedCell q t) := by
    rw [hD_eq]
    exact henergy
  have hsub : volumeAverage (HighContrast.adaptedCell q t)
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = volumeAverage (HighContrast.adaptedCell q t)
          (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - volumeAverage (HighContrast.adaptedCell q t) (scalarVariationEnergyIntegrand b v) := by
    have hfun :
        (fun x => (φ x - 1) * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
          = (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2) := by
      funext x
      simp only [Pi.sub_apply]
      ring
    rw [hfun, volumeAverage_sub hφD hD_int, hD_eq]
  unfold respJ
  rw [responseJ_energy_of_isResponseMaximizer (HighContrast.adaptedCell q t) b p r v hv
    hu_int hresp_u hlin_self henergy]
  rw [hsub]
  ring

/-- **Mean-zero fluctuation of a mean-one cutoff.**  If `φ` averages to `1` over a cell of finite
nonzero volume, then `φ − 1` averages to `0`. -/
theorem volumeAverage_sub_one_eq_zero {d : ℕ} (U : Set (Vec d)) {φ : Vec d → ℝ}
    (hφ1 : volumeAverage U φ = 1) (hvol : (volume U).toReal ≠ 0)
    (hφ : IntegrableOn φ U) :
    volumeAverage U (fun x => φ x - 1) = 0 := by
  have hfin : volume U ≠ ⊤ := ((ENNReal.toReal_ne_zero).mp hvol).2
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) U := integrableOn_const hfin
  have h : (fun x => φ x - 1) = φ - (fun _ : Vec d => (1 : ℝ)) := by
    funext x
    rfl
  rw [h, volumeAverage_sub hφ h1, hφ1, volumeAverage_const hvol]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The competitor split of the weighted optimizer energy

The first error row of the cutoff estimate of `p.response.transfer` replaces the terminal
optimizer energy of a cell by the scale-`s` cell optimizers.  The pathwise algebra behind that
replacement is the identity

`∇v · b ∇v − ∇w · b ∇w = (∇v − ∇w) · symmPart b (∇v + ∇w)`,

which holds because the quadratic form only sees the symmetric part of `b`.  Combined with the
Cauchy–Schwarz inequality for the positive semidefinite symmetric part, it bounds the
`(φ − 1)`-weighted energy defect of two competitors by the square roots of the averaged
difference and sum energies.

* `abs_vecDot_matVecMul_le_sqrt_mul_sqrt` — Cauchy–Schwarz for a symmetric positive
  semidefinite matrix.
* the pathwise competitor identity for the optimizer field.
* the weighted energy defect bound.

Paper: the first error row of `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Cauchy–Schwarz for a symmetric positive semidefinite matrix.**  For a real matrix `S` with
`matTranspose S = S` whose quadratic form is nonnegative, the pairing `u · S w` is bounded by the
square roots of the two diagonal energies `u · S u` and `w · S w`, i.e.
`|u · S w| ≤ √(u · S u) · √(w · S w)`. -/
theorem abs_vecDot_matVecMul_le_sqrt_mul_sqrt {d : ℕ} {S : Mat d}
    (hsymm : matTranspose S = S) (hpsd : ∀ z : Vec d, 0 ≤ vecDot z (matVecMul S z))
    (u w : Vec d) :
    |vecDot u (matVecMul S w)|
      ≤ Real.sqrt (vecDot u (matVecMul S u)) * Real.sqrt (vecDot w (matVecMul S w)) := by
  have hsymm' : S.IsSymm := by
    change matTranspose S = S
    exact hsymm
  have hsq : vecDot u (matVecMul S w) ^ 2
      ≤ vecDot u (matVecMul S u) * vecDot w (matVecMul S w) :=
    sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hsymm' hpsd u w
  calc |vecDot u (matVecMul S w)|
      = Real.sqrt (vecDot u (matVecMul S w) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecDot u (matVecMul S u) * vecDot w (matVecMul S w)) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (vecDot u (matVecMul S u)) * Real.sqrt (vecDot w (matVecMul S w)) :=
        Real.sqrt_mul (hpsd u) _

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Averaged Cauchy--Schwarz in the coefficient metric

The terminal-optimizer comparison of `p.response.transfer` pairs one gradient field against
another in the metric `symmPart a`, and controls the pairing by the two diagonal energies through
Cauchy--Schwarz for the averaged bilinear form.  This module records that averaged inequality on a
set carrying a pointwise elliptic coefficient, in the normalized-average form the estimate uses.

* `abs_volumeAverage_vecDot_symmPart_le` — averaged Cauchy--Schwarz for `symmPart a`.

Paper: `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integral Cauchy–Schwarz for two nonnegative integrable functions:
`∫ √f·√g ≤ √(∫f)·√(∫g)`. -/
private theorem integral_sqrt_mul_sqrt_le_aux
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ x, Real.sqrt (f x) * Real.sqrt (g x) ∂μ ≤
      Real.sqrt (∫ x, f x ∂μ) * Real.sqrt (∫ x, g x ∂μ) := by
  have hsf_meas : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have hsg_meas : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hsqf : (fun x => Real.sqrt (f x) ^ 2) =ᵐ[μ] f := by
    filter_upwards [hf0] with x hx
    rw [Real.sq_sqrt hx]
  have hsqg : (fun x => Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hg0] with x hx
    rw [Real.sq_sqrt hx]
  have hmemf : MemLp (fun x => Real.sqrt (f x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsf_meas).2 (hf.congr hsqf.symm)
  have hmemg : MemLp (fun x => Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq hsg_meas).2 (hg.congr hsqg.symm)
  have hsf0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (f x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have hsg0 : 0 ≤ᵐ[μ] fun x => Real.sqrt (g x) :=
    Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    hsf0 hsg0 (by simpa using hmemf) (by simpa using hmemg)
  have hrf : ∫ x, Real.sqrt (f x) ^ (2 : ℝ) ∂μ = ∫ x, f x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf0] with x hx
      rw [Real.rpow_two, Real.sq_sqrt hx])
  have hrg : ∫ x, Real.sqrt (g x) ^ (2 : ℝ) ∂μ = ∫ x, g x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hg0] with x hx
      rw [Real.rpow_two, Real.sq_sqrt hx])
  rw [hrf, hrg] at key
  rw [Real.sqrt_eq_rpow (∫ x, f x ∂μ), Real.sqrt_eq_rpow (∫ x, g x ∂μ)]
  convert key using 2

/-- **Averaged Cauchy–Schwarz in the coefficient metric.**  On a set `U` carrying a coefficient
`a` elliptic pointwise, the volume average of the `symmPart a`-pairing of two vector fields is
bounded by the geometric mean of the averages of their two diagonal energies:
`|⨍_U f · symmPart a g| ≤ √(⨍_U f · symmPart a f) · √(⨍_U g · symmPart a g)`.  No hypothesis on
the measure of `U` is needed: the normalizing constant `(volume U).toReal⁻¹` is nonnegative and
factors through both sides, so the degenerate cases are covered as well. -/
theorem abs_volumeAverage_vecDot_symmPart_le {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam U a) (f g : Vec d → Vec d)
    (hff : MeasureTheory.IntegrableOn
      (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))) U)
    (hgg : MeasureTheory.IntegrableOn
      (fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x))) U)
    (hfg : MeasureTheory.IntegrableOn
      (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x))) U) :
    |volumeAverage U (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x)))|
      ≤ Real.sqrt (volumeAverage U (fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))))
        * Real.sqrt (volumeAverage U (fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x))))
          := by
  let A : Vec d → ℝ := fun x => vecDot (f x) (matVecMul (symmPart (a x)) (f x))
  let B : Vec d → ℝ := fun x => vecDot (g x) (matVecMul (symmPart (a x)) (g x))
  let H : Vec d → ℝ := fun x => vecDot (f x) (matVecMul (symmPart (a x)) (g x))
  have hA_int : IntegrableOn A U := hff
  have hB_int : IntegrableOn B U := hgg
  have hH_int : IntegrableOn H U := hfg
  have hSsymm : ∀ x, matTranspose (symmPart (a x)) = symmPart (a x) :=
    fun x => matTranspose_symmPart (a x)
  have hSpsd : ∀ x ∈ U, ∀ z : Vec d, 0 ≤ vecDot z (matVecMul (symmPart (a x)) z) := by
    intro x hx z
    have hEllx : IsEllipticMatrix lam Lam (a x) := hEll.2 x hx
    have hlow := lowerBound_symmPart_of_isEllipticMatrix hEllx z
    have hlam : 0 ≤ lam := le_of_lt hEllx.1
    have hnn : 0 ≤ vecNormSq z := vecNormSq_nonneg z
    exact le_trans (mul_nonneg hlam hnn) hlow
  have hpoint : ∀ x ∈ U, |H x| ≤ Real.sqrt (A x) * Real.sqrt (B x) := by
    intro x hx
    exact abs_vecDot_matVecMul_le_sqrt_mul_sqrt (hSsymm x) (hSpsd x hx) (f x) (g x)
  have hprod_meas : AEStronglyMeasurable
      (fun x => Real.sqrt (A x) * Real.sqrt (B x)) (volume.restrict U) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA_int.aestronglyMeasurable).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hB_int.aestronglyMeasurable)
  have hbound : ∀ᵐ x ∂(volume.restrict U),
      ‖Real.sqrt (A x) * Real.sqrt (B x)‖ ≤ A x + B x := by
    refine (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    have hAx : 0 ≤ A x := hSpsd x hx (f x)
    have hBx : 0 ≤ B x := hSpsd x hx (g x)
    have hAB : Real.sqrt (A x) * Real.sqrt (B x) ≤ A x + B x := by
      nlinarith only [sq_nonneg (Real.sqrt (A x) - Real.sqrt (B x)),
        Real.sq_sqrt hAx, Real.sq_sqrt hBx]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith only [hAB]
  have hprod_int : Integrable (fun x => Real.sqrt (A x) * Real.sqrt (B x))
      (volume.restrict U) :=
    Integrable.mono' (hA_int.add hB_int) hprod_meas hbound
  have hstep_abs : |volumeAverage U H| ≤ volumeAverage U (fun x => |H x|) := by
    have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have habs : |∫ x in U, H x| ≤ ∫ x in U, |H x| := abs_integral_le_integral_abs
    calc |volumeAverage U H|
        = (volume U).toReal⁻¹ * |∫ x in U, H x| := by
            unfold volumeAverage
            rw [abs_mul, abs_of_nonneg hc]
      _ ≤ (volume U).toReal⁻¹ * ∫ x in U, |H x| :=
            mul_le_mul_of_nonneg_left habs hc
      _ = volumeAverage U (fun x => |H x|) := by
            unfold volumeAverage
            rfl
  have hstep_mono : volumeAverage U (fun x => |H x|)
      ≤ volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x)) := by
    have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have habsH : Integrable (fun x => |H x|) (volume.restrict U) := by
      simpa [Real.norm_eq_abs] using hH_int.abs
    unfold volumeAverage
    apply mul_le_mul_of_nonneg_left _ hc
    exact integral_mono_ae habsH hprod_int
      ((ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hpoint x hx)))
  have hA_nonneg : 0 ≤ᵐ[volume.restrict U] A :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hSpsd x hx (f x)))
  have hB_nonneg : 0 ≤ᵐ[volume.restrict U] B :=
    (ae_restrict_iff' hU).2 (Filter.Eventually.of_forall (fun x hx => hSpsd x hx (g x)))
  have hc : 0 ≤ (volume U).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hcs : (∫ x in U, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in U, A x) * Real.sqrt (∫ x in U, B x) :=
    integral_sqrt_mul_sqrt_le_aux hA_int hB_int hA_nonneg hB_nonneg
  have hsqrtc : Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt ((volume U).toReal⁻¹)
      = (volume U).toReal⁻¹ := Real.mul_self_sqrt hc
  have hsqrtA : Real.sqrt (volumeAverage U A)
      = Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt (∫ x in U, A x) := by
    rw [show volumeAverage U A = (volume U).toReal⁻¹ * ∫ x in U, A x from rfl,
      Real.sqrt_mul hc (∫ x in U, A x)]
  have hsqrtB : Real.sqrt (volumeAverage U B)
      = Real.sqrt ((volume U).toReal⁻¹) * Real.sqrt (∫ x in U, B x) := by
    rw [show volumeAverage U B = (volume U).toReal⁻¹ * ∫ x in U, B x from rfl,
      Real.sqrt_mul hc (∫ x in U, B x)]
  have hstep_cs : volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := by
    calc volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x))
        = (volume U).toReal⁻¹ * ∫ x in U, Real.sqrt (A x) * Real.sqrt (B x) := rfl
      _ ≤ (volume U).toReal⁻¹
            * (Real.sqrt (∫ x in U, A x) * Real.sqrt (∫ x in U, B x)) :=
            mul_le_mul_of_nonneg_left hcs hc
      _ = Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := by
            rw [hsqrtA, hsqrtB]
            conv_lhs => rw [← hsqrtc]
            ring
  calc |volumeAverage U H|
      ≤ volumeAverage U (fun x => |H x|) := hstep_abs
    _ ≤ volumeAverage U (fun x => Real.sqrt (A x) * Real.sqrt (B x)) := hstep_mono
    _ ≤ Real.sqrt (volumeAverage U A) * Real.sqrt (volumeAverage U B) := hstep_cs

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The restricted terminal optimizer and its subcell responses

The terminal-optimizer replacement of `p.response.transfer` restricts the optimizer of the terminal
cell to each aligned subcell of the coarse scale and compares the restricted response value there
with the subcell's own response.  The response integrand and the variation-energy integrand are
pointwise expressions in the coefficient and the gradient of the harmonic function, so restricting
the function to a subdomain leaves both integrands unchanged as functions.  Exact partition
averaging then expresses the terminal response value as the flat average of the restricted response
values over the aligned subcells; the entire scale defect therefore sits in the gap between each
subcell's own response and the restricted one.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Restricting a harmonic function to a subdomain leaves the scalar response integrand unchanged.
Both integrands are pointwise expressions in the coefficient and the gradient, and the restricted
harmonic function has the same gradient as the parent, so the two functions agree.  This is the
integrand identity used in the terminal-optimizer replacement of `p.response.transfer`. -/
theorem scalarResponseIntegrand_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (p r : Vec d) (u : AHarmonicFunction a U) :
    scalarResponseIntegrand V a p r (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
      = scalarResponseIntegrand U a p r u := by
  funext x
  have hgrad :
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [scalarResponseIntegrand, hgrad]

/-- Restricting a harmonic function to a subdomain leaves the scalar variation-energy integrand
unchanged.  The integrand is a pointwise expression in the coefficient and the gradient, and the
restricted harmonic function has the same gradient as the parent.  This is the energy identity used
in the terminal-optimizer replacement of `p.response.transfer`. -/
theorem scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    (u : AHarmonicFunction a U) :
    scalarVariationEnergyIntegrand a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll)
      = scalarVariationEnergyIntegrand a u := by
  funext x
  have hgrad :
      (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simp only [scalarVariationEnergyIntegrand, hgrad]

/-- Exact partition averaging at a response maximizer: the flat average over the depth-`n` aligned
subcells of the parent response integrand is the parent response value, and at a maximizer that
value is the terminal response `J`.  Thus no response is lost in the subdivision; the entire scale
defect sits in the gap between each subcell's own response and the restricted one.  This is the
bookkeeping identity of the terminal-optimizer replacement of `p.response.transfer`. -/
theorem avsum_volumeAverage_scalarResponseIntegrand_eq_responseJ {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (n : ℕ) {a : CoeffField d} (p r : Vec d)
    (u : AHarmonicFunction a (HighContrast.adaptedCell q t))
    (hmax : IsResponseMaximizer (HighContrast.adaptedCell q t) p r a u)
    (hint : MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u) (HighContrast.adaptedCell
        q t)) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
            (scalarResponseIntegrand (HighContrast.adaptedCell q t) a p r u)
      = ResponseJ (HighContrast.adaptedCell q t) p r a := by
  rw [avsum_volumeAverage_eq q hq t n hint,
    ← responseJ_eq_of_isResponseMaximizer (HighContrast.adaptedCell q t) p r a hmax]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The subcell response deficit controls the terminal optimizer's energy

The terminal-optimizer replacement of `p.response.transfer` compares the energy of the terminal
optimizer with the subcell responses.  Let `V ⊆ U`, let `u` optimize the response problem on the
large cell `U`, and let `v` optimize the same load on the small cell `V`.  Restricted to `V`, `u`
is an admissible competitor there, so its response value on `V` falls short of `J(V)` by the
nonnegative deficit

  `D = J(V) - ⨍_V g_V(u)`.

The quadratic-response identity makes the `symmPart(a)`-energy of `∇u - ∇v` on `V` exactly `2 D`.
Splitting the two energies and bounding the cross term by Cauchy--Schwarz against
`⨍_V ⟨∇v, symmPart(a) ∇v⟩ = 2 J(V)` bounds the terminal optimizer's energy against the subcell
response:

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J(V)| ≤ D + 2 √(J(V) · D)`.

This is the pathwise engine of the terminal-optimizer replacement of `p.response.transfer`.

Paper: `p.response.transfer`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit controls the terminal optimizer's energy.**  Let `V ⊆ U` be open sets,
`a` a coefficient elliptic on `V`, `v` a response maximizer on `V` for the load `(p, r)`, and `u`
any `a`-harmonic function on `U`.  Writing `J = J(V; p, r; a)` for the subcell response and
`D = J - ⨍_V g_V(u)` for the deficit of the restricted parent `u` against it, the terminal
optimizer's energy on `V` is controlled by the subcell response through

  `|½ ⨍_V ⟨∇u, symmPart(a) ∇u⟩ - J| ≤ D + 2 √(J · D)`.

The difference energy of `∇u - ∇v` is `2 D` by the quadratic-response identity, and the cross
term `⨍_V ⟨∇v, symmPart(a)(∇u - ∇v)⟩` is bounded by averaged Cauchy--Schwarz against the two
diagonal energies `2 J` and `2 D`.  The side conditions are the integrability hypotheses of the
difference-energy identity, the energy--response identity at `v`, the cross integrability, and the
parent's energy integrability. -/
theorem abs_half_energy_sub_responseJ_le_deficit {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam V a)
    {p r : Vec d} (u : AHarmonicFunction a U) (v : AHarmonicFunction a V)
    (hmax : IsResponseMaximizer V p r a v)
    (huV_int : weakFluxIntegrable V a (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
    (hv_int : weakFluxIntegrable V a v)
    (hresp_v : MeasureTheory.IntegrableOn (scalarResponseIntegrand V a p r v) V)
    (hlin_vv : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v v) V)
    (henergy_v : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a v) V)
    (hlin_diff : MeasureTheory.IntegrableOn (scalarFirstVariationIntegrand V a p r v
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy_diff : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a
      (AHarmonicFunction.addSMulOfIntegrable
        (u.restrictOfIsEllipticFieldOn hU hV hVU hEll) v huV_int hv_int (-1))) V)
    (henergy_u : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a u) V)
    (hcross : MeasureTheory.IntegrableOn (fun x => vecDot (v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) V) :
    |(1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u) - ResponseJ V p r a|
      ≤ (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
        + 2 * Real.sqrt (ResponseJ V p r a
            * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
  set uV : AHarmonicFunction a V := u.restrictOfIsEllipticFieldOn hU hV hVU hEll with huVdef
  -- The restricted optimizer has the same gradient as its parent.
  have hgrad : (u.restrictOfIsEllipticFieldOn hU hV hVU hEll).toH1.grad = u.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  have hgradV : uV.toH1.grad = u.toH1.grad := by
    rw [huVdef]
    exact hgrad
  -- The deficit energy: `⨍_V ⟨∇u - ∇v, symmPart(a)(∇u - ∇v)⟩ = 2 D`.
  have hdelta : volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
      = 2 * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u)) := by
    have h6 := difference_energy_eq_response_deficit hVU hU hV hEll hmax huV_int hv_int
      hresp_v hlin_diff henergy_diff
    rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u] at h6
    rw [hgrad] at h6
    exact h6
  -- The difference integrand is the variation energy of the perturbation `uV - v`.
  have hwgrad : (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)).toH1.grad
      = fun x => u.toH1.grad x - v.toH1.grad x := by
    rw [AHarmonicFunction.grad_addSMulOfIntegrable]
    funext x i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [congrFun hgradV x]
    ring
  have hSdxs_eq : (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
      = scalarVariationEnergyIntegrand a
          (AHarmonicFunction.addSMulOfIntegrable uV v huV_int hv_int (-1)) := by
    funext x
    simp only [scalarVariationEnergyIntegrand]
    rw [congrFun hwgrad x]
  have hSdxs_int : IntegrableOn (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) V := by
    rw [hSdxs_eq]
    exact henergy_diff
  -- The energy--response identity at the subcell maximizer.
  have hJ : ResponseJ V p r a
      = (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a v) :=
    responseJ_energy_of_isResponseMaximizer V a p r v hmax hv_int hresp_v hlin_vv henergy_v
  -- Pointwise splitting of the two energies.
  have hpoint : ∀ x, scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x
      = vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))
        + 2 * vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)) := by
    intro x
    have hcomm := vecDot_matVecMul_symmPart_comm (a x) (u.toH1.grad x) (v.toH1.grad x)
    simp only [scalarVariationEnergyIntegrand, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm]
    ring
  -- Averaging the pointwise splitting.
  have h2cross_int : IntegrableOn ((2 : ℝ) • (fun x => vecDot (v.toH1.grad x)
      (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))) V := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hcross.const_mul (2 : ℝ)
  have hfun : (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
        + (2 : ℝ) • (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    funext x
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hpoint x
  have hsub : volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = volumeAverage V (scalarVariationEnergyIntegrand a u)
        - volumeAverage V (scalarVariationEnergyIntegrand a v) :=
    volumeAverage_sub henergy_u henergy_v
  have havg : volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
        - scalarVariationEnergyIntegrand a v x)
      = volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
        + 2 * volumeAverage V (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    rw [hfun, volumeAverage_add hSdxs_int h2cross_int,
      volumeAverage_smul V (2 : ℝ) (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))]
  -- The terminal energy differs from `J` by the deficit plus the cross average.
  have hmain : (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
        - ResponseJ V p r a
      = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
        + volumeAverage V (fun x => vecDot (v.toH1.grad x)
          (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
    calc
      (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
          - ResponseJ V p r a
          = (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
            - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a v) := by rw [hJ]
      _ = (1 / 2 : ℝ) * (volumeAverage V (scalarVariationEnergyIntegrand a u)
            - volumeAverage V (scalarVariationEnergyIntegrand a v)) := by ring
      _ = (1 / 2 : ℝ) * volumeAverage V (fun x => scalarVariationEnergyIntegrand a u x
            - scalarVariationEnergyIntegrand a v x) := by rw [hsub]
      _ = (1 / 2 : ℝ) * (volumeAverage V (fun x => vecDot (u.toH1.grad x - v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))
            + 2 * volumeAverage V (fun x => vecDot (v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))) := by rw [havg]
      _ = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
            + volumeAverage V (fun x => vecDot (v.toH1.grad x)
            (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x))) := by
            rw [hdelta]
            ring
  -- Nonnegativity of the two quantities under the square roots.
  have hJnonneg : 0 ≤ ResponseJ V p r a := by
    have hA := volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V a hEll v
    rw [hJ]
    exact mul_nonneg (by norm_num) hA
  have hDnonneg : 0 ≤ ResponseJ V p r a
      - volumeAverage V (scalarResponseIntegrand U a p r u) := by
    have hle := hmax uV
    have hJuV' : volumeAverage V (scalarResponseIntegrand V a p r
          (u.restrictOfIsEllipticFieldOn hU hV hVU hEll))
        = volumeAverage V (scalarResponseIntegrand U a p r u) := by
      rw [scalarResponseIntegrand_restrictOfIsEllipticFieldOn hU hV hVU hEll p r u]
    have hJuV : volumeAverage V (scalarResponseIntegrand V a p r uV)
        = volumeAverage V (scalarResponseIntegrand U a p r u) := by
      rw [huVdef]
      exact hJuV'
    have hJv := responseJ_eq_of_isResponseMaximizer V p r a hmax
    linarith only [hle, hJuV, hJv]
  -- Cauchy--Schwarz for the cross term.
  have hcs0 := abs_volumeAverage_vecDot_symmPart_le (U := V) (a := a) hV.measurableSet hEll
    v.toH1.grad (fun x => u.toH1.grad x - v.toH1.grad x)
    (by simpa only [scalarVariationEnergyIntegrand] using! henergy_v)
    hSdxs_int hcross
  have hEv : volumeAverage V (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (v.toH1.grad x))) = 2 * ResponseJ V p r a := by
    have h' : volumeAverage V (scalarVariationEnergyIntegrand a v)
        = 2 * ResponseJ V p r a := by linarith only [hJ]
    simpa only [scalarVariationEnergyIntegrand] using! h'
  have hcs : |volumeAverage V (fun x => vecDot (v.toH1.grad x)
        (matVecMul (symmPart (a x)) (u.toH1.grad x - v.toH1.grad x)))|
      ≤ 2 * Real.sqrt (ResponseJ V p r a
          * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
    have h := hcs0
    rw [hEv, hdelta] at h
    have hsqrt : Real.sqrt (2 * ResponseJ V p r a)
          * Real.sqrt (2 * (ResponseJ V p r a
            - volumeAverage V (scalarResponseIntegrand U a p r u)))
        = 2 * Real.sqrt (ResponseJ V p r a
            * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
      calc
        Real.sqrt (2 * ResponseJ V p r a) * Real.sqrt (2 * (ResponseJ V p r a
              - volumeAverage V (scalarResponseIntegrand U a p r u)))
            = (Real.sqrt 2 * Real.sqrt (ResponseJ V p r a))
              * (Real.sqrt 2 * Real.sqrt (ResponseJ V p r a
                - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = (Real.sqrt 2 * Real.sqrt 2)
              * (Real.sqrt (ResponseJ V p r a)
                * Real.sqrt (ResponseJ V p r a
                  - volumeAverage V (scalarResponseIntegrand U a p r u))) := by ring
        _ = 2 * (Real.sqrt (ResponseJ V p r a)
              * Real.sqrt (ResponseJ V p r a
                - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        _ = 2 * Real.sqrt (ResponseJ V p r a
              * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
              rw [Real.sqrt_mul hJnonneg]
    rw [hsqrt] at h
    exact h
  calc
    |(1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand a u)
        - ResponseJ V p r a|
        = |(ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
            + volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := by rw [hmain]
    _ ≤ |ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u)|
          + |volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := abs_add_le _ _
    _ = (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
          + |volumeAverage V (fun x => vecDot (v.toH1.grad x)
              (matVecMul (symmPart (a x))
                (u.toH1.grad x - v.toH1.grad x)))| := by rw [abs_of_nonneg hDnonneg]
    _ ≤ (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))
          + 2 * Real.sqrt (ResponseJ V p r a
              * (ResponseJ V p r a - volumeAverage V (scalarResponseIntegrand U a p r u))) := by
          linarith only [hcs]

end

end HCPolySupport.HighContrast.Multiscale
end
