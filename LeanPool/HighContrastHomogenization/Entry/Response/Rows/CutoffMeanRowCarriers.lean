/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ResponseImbalanceComparison
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CellHalfFinalBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.CutoffMeanDefectIntegrability
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.OptimizerMeanRowCarriers

/-!
# High-contrast homogenization: Entry.Response.Rows.CutoffMeanRowCarriers

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-mean row on the response's own data

The cutoff-mean row of `p.response.transfer` is the sum of a cell half, bounded from the
response's own cell data by `(L_s^∓ 2 τ^∓)^{1/2}`, and an oscillation half, read at the dual
variable `Y^∓` and bounded by its depth-`H` and descendant contributions against
`c₂ 3^{-H}(E[J_t^∓] L_s^∓)^{1/2}`; this file combines the two into the row's final concrete form
for both signs. The oscillation bound is stated through a single constant, here shown to be
nonnegative and to satisfy the elementary arithmetic identity the combination needs, and a short
identity for the cutoff's own fluctuation average closes the remaining bookkeeping. Together these
give the cutoff-mean row exactly in the form the cutoff estimate consumes, with no further
hypothesis on the coefficient sample.
-/

section
/-!
## The cutoff-mean row at the carriers

The cutoff-mean row of `p.response.transfer` is the sum of a cell half and an oscillation half.
`CellHalfFinalBound` bounds the cell half by `(L_s^∓ 2 tau^∓)^{1/2}` from the carriers' own
annealed data.  The oscillation half of `CutoffOscillationHalfClosure`, read at the dual variable
`Y^∓`,
bounds the scalar annealed functional `⨍_{U_t}(φ-1)(⟨Y₂, ∇u⟩ + ⟨Y₁, a∇u⟩)` against its depth-`H`
cell part; `CellHalfFinalBound` identifies the crossed pairing of the vector oscillation part
with exactly that difference, once the within-cell fluctuation is split by
`volumeAverage_fluct_eq_osc_add_cell`.  Together with the coordinate integrabilities of
`CutoffMeanDefectIntegrability`, the row assembly of `OptimizerMeanRowCarriers` then gives the
named obligation
`CutoffMeanRow∓` with no sample-side premise left.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The constant of the oscillation half of the cutoff-mean row: the cutoff Lipschitz constant
`32 d² Θ`, the square root of the geometric series `∑ 3^{-n/2}` of the descendant weights, the
generation shift of the source-load layers and the `√8` of the doubled cell energy. -/
@[expose]
def respCutoffOscConst (d : ℕ) : ℝ :=
  32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
      (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))) *
        Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2))) *
    Real.sqrt 8

/-- The oscillation-half constant is nonnegative. -/
theorem zero_le_respCutoffOscConst (d : ℕ) : 0 ≤ respCutoffOscConst d := by
  have h1 : (1 : ℝ) ≤ responseCutoffProfileConst := one_le_responseCutoffProfileConst
  have h2 : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst := by positivity
  exact mul_nonneg (mul_nonneg h2
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)

/-- The cell average of the cutoff fluctuation is the cell average of the cutoff, shifted. -/
private theorem volumeAverage_sub_one_eq_sub_one {d : ℕ} {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) {φ : Vec d → ℝ}
    (hφ : IntegrableOn φ V) :
    volumeAverage V (fun x => φ x - 1) = volumeAverage V φ - 1 := by
  have h := volumeAverage_sub (U := V) (f := φ) (g := fun _ : Vec d => (1 : ℝ)) hφ
    (integrableOn_const hfin)
  rw [show (fun x : Vec d => φ x - 1) = φ - fun _ : Vec d => (1 : ℝ) by
    funext x; simp only [Pi.sub_apply], h, volumeAverage_const hvol]

/-- The arithmetic of the oscillation-half constant: the bound the descendant sum delivers is the
bound the row asks for. -/
private theorem oscConst_arith (d : ℕ) (L EJ HH : ℝ) (hEJ : 0 ≤ EJ) :
    (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * HH) *
        (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2))) *
          Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * L)) * Real.sqrt (2 * (4 * EJ))
      = respCutoffOscConst d * (HH * Real.sqrt (EJ * L)) := by
  have h1 : Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * L)
      = Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2)) * Real.sqrt L :=
    Real.sqrt_mul (Real.rpow_nonneg (by norm_num) _) L
  have h2 : Real.sqrt (2 * (4 * EJ)) = Real.sqrt 8 * Real.sqrt EJ := by
    rw [show (2 : ℝ) * (4 * EJ) = 8 * EJ by ring]
    exact Real.sqrt_mul (by norm_num) EJ
  have h3 : Real.sqrt (EJ * L) = Real.sqrt EJ * Real.sqrt L := Real.sqrt_mul hEJ L
  rw [h1, h2, h3, respCutoffOscConst]
  ring

/-- Split the cutoff fluctuation against an integrable carrier into its cell oscillation and
its cell-average contribution. The bounded cutoff keeps each weighted carrier integrable. -/
private theorem cutoffFluctuation_split {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (H : ℕ) (φ g : Vec d → ℝ) (hφ : IsResponseCutoff q t φ)
    (hg : IntegrableOn g (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) φ) * g x)
      = volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * g x)
        - ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) g := by
  have hsplit := volumeAverage_fluct_eq_osc_add_cell q hq t H φ g
    ((hg.bdd_mul (c := 1) (hφ.2.2.2.2.2.1.continuous.sub
      continuous_const).measurable.aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith only [hφ.1 x], by linarith only [hφ.2.1 x]⟩))
    (fun w hw => by
      have hsub : adaptedCellAtCenter q (t - (H : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
        adaptedCellAtCenter_subset_adaptedCell q t H hw
      have hA := (hg.mono_set hsub).bdd_mul (c := 2)
        (hφ.2.2.2.2.2.1.continuous.measurable.aestronglyMeasurable.restrict)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_le]
          exact ⟨by linarith only [hφ.1 x], hφ.2.1 x⟩)
      have hB := (hg.mono_set hsub).const_mul
        (volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) φ)
      refine (hA.sub hB).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      ring)
    (fun w hw => by
      have hsub : adaptedCellAtCenter q (t - (H : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
        adaptedCellAtCenter_subset_adaptedCell q t H hw
      exact (hg.mono_set hsub).const_mul _)
  exact eq_sub_of_add_eq hsplit.symm

/-- Integrating the cell and oscillation decomposition preserves the split. -/
private theorem integral_cutoffFluctuation_split {d : ℕ} [NeZero d] {α : Type*}
    [MeasurableSpace α] (P : Measure α) (q : Mat d) (hq : IsUnit q) (H : ℕ)
    (s t : ℤ) (hst : t - (H : ℤ) = s) (φ : Vec d → ℝ)
    (hφ : IsResponseCutoff q t φ) (g : α → Vec d → ℝ)
    (hg : ∀ a, IntegrableOn (g a) (HighContrast.adaptedCell q t))
    (hcell : Integrable (fun a => volumeAverage (HighContrast.adaptedCell q t)
      (fun x => (φ x - 1) * g a x)) P)
    (hpart : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        (volumeAverage (adaptedCellAtCenter q s w) φ - 1) *
          volumeAverage (adaptedCellAtCenter q s w) (g a)) P) :
    (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
      volumeAverage (adaptedCellAtCenter q s w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter q s w) φ) * g a x) ∂P)
      = (∫ a, volumeAverage (HighContrast.adaptedCell q t)
          (fun x => (φ x - 1) * g a x) ∂P)
        - ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter q s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q s w) (g a) ∂P := by
  have hpoint : ∀ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter q s w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter q s w) φ) * g a x)
      = volumeAverage (HighContrast.adaptedCell q t) (fun x => (φ x - 1) * g a x)
        - ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            (volumeAverage (adaptedCellAtCenter q s w) φ - 1) *
              volumeAverage (adaptedCellAtCenter q s w) (g a) := by
    intro a
    simpa only [hst] using cutoffFluctuation_split q hq t H φ (g a) hφ (hg a)
  rw [← integral_sub hcell hpart]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- Move the cell part's cutoff average from the lower cell index to the terminal index. -/
private theorem integral_cutoffCellPart_shift {d : ℕ} [NeZero d] {α : Type*}
    [MeasurableSpace α] (P : Measure α) (q : Mat d) (H : ℕ) (s t : ℤ)
    (hst : t - (H : ℤ) = s) (φ : Vec d → ℝ) (g : α → Vec d → ℝ)
    (hwt : ∀ w, volumeAverage (adaptedCellAtCenter q s w)
      (fun x => φ x - 1) = volumeAverage (adaptedCellAtCenter q s w) φ - 1) :
    (∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
      (volumeAverage (adaptedCellAtCenter q s w) φ - 1) *
        volumeAverage (adaptedCellAtCenter q s w) (g a) ∂P)
      = ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
          volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w)
            (fun x => φ x - 1) *
            volumeAverage (adaptedCellAtCenter q (t - (H : ℤ)) w) (g a) ∂P := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  rw [hst]
  simp only [hwt]

/-- **The cutoff-mean row at the carriers, minus sign.**  Under the annealed data of the response
window — stationarity, coarse ellipticity, the invertible rounded grid, the maximizer family, the
two terminal responses and the convergence of the source-load series at every dual vector — the
named obligation `CutoffMeanRowMinus` holds with constant `max 1 (respCutoffOscConst d)`. -/
theorem cutoffMeanRowMinus_of_carriers {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hF : (toFullBlockMat F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblkw : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (hblkt : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hsumm : ∀ Y : BlockVec d,
      Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y))
    (hτ : 0 ≤ respTauMinus P jStar F s t e) :
    CutoffMeanRowMinus (max 1 (respCutoffOscConst d)) P jStar F H s t e φ uM := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hst : t - (H : ℤ) = s := by omega
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  have hL : 0 ≤ respLsMinus P jStar F s t e :=
    zero_le_respLsMinus P jStar F s t e
  have hEJ : 0 ≤ respEJMinus P jStar F t e := zero_le_respEJMinus P jStar F t e hq
  have hEint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have hY := respYMinus_eq_integral_cellAverage_optimizerField P jStar F t e hjStar hm hF
    hblkt uM hmax
  have hUm : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hVm : ∀ w : Fin d → ℤ, MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : ∀ w ∈ triadicIndexBox d H,
      adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    intro w hw
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hst] at h
  have hwt : ∀ w : Fin d → ℤ,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1 := fun w =>
    volumeAverage_sub_one_eq_sub_one
      (Geometry.volume_adaptedCellAtCenter_ne_top (respGrid jStar F) s w)
      (ne_of_gt (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w))
      (integrableOn_isResponseCutoff hq hφ s w)
  have hpath : ∀ (V : Set (Vec d)), MeasurableSet V → V ⊆ respCell jStar F t →
      ∀ (eta : Vec d → ℝ), Continuous eta → ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) V
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) V :=
    fun V hV hVsub eta hc a i =>
      integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm t uM hV
        hVsub hc a i
  have hG : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i)
          (respCell jStar F t)
        ∧ IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i)
          (respCell jStar F t) := by
    intro a i
    have h := hpath (respCell jStar F t) hUm (fun x hx => hx) (fun _ => (1 : ℝ))
      continuous_const a i
    simpa only [one_mul] using h
  obtain ⟨hIntC1, hIntC2, hIntCell1, hIntCell2, hIntM1, hIntM2, hIntOsc1, hIntOsc2⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffMinus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uM hmax hEint hJt hsumm
  have hcrossH : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => vecDot (respYMinus P jStar F t e).2
              (optimizerField (respCoeffMinus F a) (uM a) x).1
            + vecDot (respYMinus P jStar F t e).1
              (optimizerField (respCoeffMinus F a) (uM a) x).2)) P := by
    intro w hw
    have h := integrable_volumeAverage_cross_optimizerField_respCoeffMinus P jStar hjStar F hm
      t e uM hmax hJt hblkw (respYMinus P jStar F t e) H w hw
    rwa [hst] at h
  refine cutoffMeanRowMinus_of_cellSplit P jStar F H s t ht e φ uM hY hq
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) φ hφc a i).1)
    (fun a i => (hG a i).1)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) (fun x => φ x - 1)
      (hφc.sub continuous_const) a i).1)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
      (hφc.sub continuous_const) a i).1)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
      continuous_const a i).1)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) φ hφc a i).2)
    (fun a i => (hG a i).2)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) (fun x => φ x - 1)
      (hφc.sub continuous_const) a i).2)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
      (hφc.sub continuous_const) a i).2)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
      continuous_const a i).2)
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
    (respCutoffOscConst d) (zero_le_respCutoffOscConst d) ?_ ?_ hτ hL
  · -- the cell half
    refine abs_vecDot_cellPart_respYMinus_le_clean P hstat jStar hjStar F hm H s t ht hjs e φ hφ
      uM hmax (hsumm (respYMinus P jStar F t e)) (fun w => hblkw s w) hJt hJs _ ?_
    simp only [hwt]
  · -- the oscillation half
    have hbridge : vecDot (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
          (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1
          (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)
        = ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (vecDot (respYMinus P jStar F t e).2
                    (optimizerField (respCoeffMinus F a) (uM a) x).1
                  + vecDot (respYMinus P jStar F t e).1
                    (optimizerField (respCoeffMinus F a) (uM a) x).2)) ∂P :=
      vecDot_avsum_volumeAverage_osc_eq P (triadicIndexBox d H)
      (fun w => adaptedCellAtCenter (respGrid jStar F) s w) φ
      (fun a x => optimizerField (respCoeffMinus F a) (uM a) x) (respYMinus P jStar F t e)
      hIntOsc1 hIntOsc2
      (fun a w hw i => (hpath (adaptedCellAtCenter (respGrid jStar F) s w) (hVm w) (hVU w hw)
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ)
        (hφc.sub continuous_const) a i).1)
      (fun a w hw i => (hpath (adaptedCellAtCenter (respGrid jStar F) s w) (hVm w) (hVU w hw)
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ)
        (hφc.sub continuous_const) a i).2)
    have hhalf := integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffMinus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ (respYMinus P jStar F t e) uM
      hmax hEint hJt (hsumm (respYMinus P jStar F t e))
    have hTint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => vecDot (respYMinus P jStar F t e).2
                    (optimizerField (respCoeffMinus F a) (uM a) x).1
                  + vecDot (respYMinus P jStar F t e).1
                    (optimizerField (respCoeffMinus F a) (uM a) x).2)) P :=
      integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
        (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
        (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => vecDot (respYMinus P jStar F t e).2
                (optimizerField (respCoeffMinus F a) (uM a) x).1
              + vecDot (respYMinus P jStar F t e).1
                (optimizerField (respCoeffMinus F a) (uM a) x).2))
        (fun _ W hW => hcrossH W hW) 0
    have hcrossOn : ∀ a : CoeffSpace d, IntegrableOn
        (fun x => vecDot (respYMinus P jStar F t e).2
              (optimizerField (respCoeffMinus F a) (uM a) x).1
            + vecDot (respYMinus P jStar F t e).1
              (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t) := by
      intro a
      have h := integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar
        hjStar F hm
        t 0 a (uM a) (respYMinus P jStar F t e) (zero_mem_triadicIndexBox 0)
      have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0
          = respCell jStar F t := by
        rw [Nat.cast_zero, sub_zero]
        exact adaptedCellAtCenter_zero (respGrid jStar F) t
      rw [hUcell] at h
      exact h.1
    have hEq1 := integral_cutoffFluctuation_split P (respGrid jStar F) hq H s t hst φ hφ
      (fun a x => vecDot (respYMinus P jStar F t e).2
            (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot (respYMinus P jStar F t e).1
            (optimizerField (respCoeffMinus F a) (uM a) x).2)
      (fun a => by simpa only [respCell] using hcrossOn a) hhalf.1 hTint
    have hEq2 := integral_cutoffCellPart_shift P (respGrid jStar F) H s t hst φ
      (fun a x => vecDot (respYMinus P jStar F t e).2
            (optimizerField (respCoeffMinus F a) (uM a) x).1
          + vecDot (respYMinus P jStar F t e).1
            (optimizerField (respCoeffMinus F a) (uM a) x).2) hwt
    have hbound : |vecDot (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P)
          (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1
          (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P)|
        ≤ respCutoffOscConst d * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) := by
      rw [hbridge, hEq1, hEq2]
      exact le_trans hhalf.2 (le_of_eq (oscConst_arith d (respLsMinus P jStar F s t e)
        (respEJMinus P jStar F t e) ((3 : ℝ) ^ (-(H : ℝ))) hEJ))
    exact hbound

/-- **The cutoff-mean row at the carriers, minus sign.**  Under the annealed data of the response
window — stationarity, coarse ellipticity, the invertible rounded grid, the maximizer family, the
two terminal responses and the convergence of the source-load series at every dual vector — the
named obligation `CutoffMeanRowPlus` holds with constant `max 1 (respCutoffOscConst d)`. -/
theorem cutoffMeanRowPlus_of_carriers {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (hF : (toFullBlockMat F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s)
    (e : Vec d) (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblkw : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (hblkt : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hsumm : ∀ Y : BlockVec d,
      Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y))
    (hτ : 0 ≤ respTauPlus P jStar F s t e) :
    CutoffMeanRowPlus (max 1 (respCutoffOscConst d)) P jStar F H s t e φ uP := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hst : t - (H : ℤ) = s := by omega
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  have hL : 0 ≤ respLsPlus P jStar F s t e :=
    zero_le_respLsPlus P jStar F s t e
  have hEJ : 0 ≤ respEJPlus P jStar F t e := zero_le_respEJPlus P jStar F t e hq
  have hEint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have hY := respYPlus_eq_integral_cellAverage_optimizerField P jStar F t e hjStar hm hF
    hblkt uP hmax
  have hUm : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hVm : ∀ w : Fin d → ℤ, MeasurableSet (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w => (isOpen_adaptedCellAtCenter_of_isUnit hq s w).measurableSet
  have hVU : ∀ w ∈ triadicIndexBox d H,
      adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F t := by
    intro w hw
    have h := adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    rwa [hst] at h
  have hwt : ∀ w : Fin d → ℤ,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1 := fun w =>
    volumeAverage_sub_one_eq_sub_one
      (Geometry.volume_adaptedCellAtCenter_ne_top (respGrid jStar F) s w)
      (ne_of_gt (volume_adaptedCellAtCenter_toReal_pos (respGrid jStar F) hq s w))
      (integrableOn_isResponseCutoff hq hφ s w)
  have hpath : ∀ (V : Set (Vec d)), MeasurableSet V → V ⊆ respCell jStar F t →
      ∀ (eta : Vec d → ℝ), Continuous eta → ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) V
        ∧ IntegrableOn (fun x => eta x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) V :=
    fun V hV hVsub eta hc a i =>
      integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm t uP hV
        hVsub hc a i
  have hG : ∀ (a : CoeffSpace d) (i : Fin d),
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i)
          (respCell jStar F t)
        ∧ IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i)
          (respCell jStar F t) := by
    intro a i
    have h := hpath (respCell jStar F t) hUm (fun x hx => hx) (fun _ => (1 : ℝ))
      continuous_const a i
    simpa only [one_mul] using h
  obtain ⟨hIntC1, hIntC2, hIntCell1, hIntCell2, hIntM1, hIntM2, hIntOsc1, hIntOsc2⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffPlus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uP hmax hEint hJt hsumm
  have hcrossH : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (fun x => vecDot (respYPlus P jStar F t e).2
              (optimizerField (respCoeffPlus F a) (uP a) x).1
            + vecDot (respYPlus P jStar F t e).1
              (optimizerField (respCoeffPlus F a) (uP a) x).2)) P := by
    intro w hw
    have h := integrable_volumeAverage_cross_optimizerField_respCoeffPlus P jStar hjStar F hm
      t e uP hmax hJt hblkw (respYPlus P jStar F t e) H w hw
    rwa [hst] at h
  refine cutoffMeanRowPlus_of_cellSplit P jStar F H s t ht e φ uP hY hq
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) φ hφc a i).1)
    (fun a i => (hG a i).1)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) (fun x => φ x - 1)
      (hφc.sub continuous_const) a i).1)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
      (hφc.sub continuous_const) a i).1)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
      continuous_const a i).1)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) φ hφc a i).2)
    (fun a i => (hG a i).2)
    (fun a i => (hpath (respCell jStar F t) hUm (fun x hx => hx) (fun x => φ x - 1)
      (hφc.sub continuous_const) a i).2)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ)
      (hφc.sub continuous_const) a i).2)
    (fun a i w hw => (hpath (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
      (by rw [hst]; exact hVm w) (by rw [hst]; exact hVU w hw)
      (fun _ => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) φ - 1)
      continuous_const a i).2)
    hIntM1 hIntC1 hIntOsc1 hIntCell1 hIntM2 hIntC2 hIntOsc2 hIntCell2
    (respCutoffOscConst d) (zero_le_respCutoffOscConst d) ?_ ?_ hτ hL
  · -- the cell half
    refine abs_vecDot_cellPart_respYPlus_le_clean P hstat jStar hjStar F hm H s t ht hjs e φ hφ
      uP hmax (hsumm (respYPlus P jStar F t e)) (fun w => hblkw s w) hJt hJs _ ?_
    simp only [hwt]
  · -- the oscillation half
    have hbridge : vecDot (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
          (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1
          (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)
        = ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (vecDot (respYPlus P jStar F t e).2
                    (optimizerField (respCoeffPlus F a) (uP a) x).1
                  + vecDot (respYPlus P jStar F t e).1
                    (optimizerField (respCoeffPlus F a) (uP a) x).2)) ∂P :=
      vecDot_avsum_volumeAverage_osc_eq P (triadicIndexBox d H)
      (fun w => adaptedCellAtCenter (respGrid jStar F) s w) φ
      (fun a x => optimizerField (respCoeffPlus F a) (uP a) x) (respYPlus P jStar F t e)
      hIntOsc1 hIntOsc2
      (fun a w hw i => (hpath (adaptedCellAtCenter (respGrid jStar F) s w) (hVm w) (hVU w hw)
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ)
        (hφc.sub continuous_const) a i).1)
      (fun a w hw i => (hpath (adaptedCellAtCenter (respGrid jStar F) s w) (hVm w) (hVU w hw)
        (fun x => φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ)
        (hφc.sub continuous_const) a i).2)
    have hhalf := integrable_and_abs_integral_cross_sub_cellPart_le_respCoeffPlus_car hd P hstat
      γ E Ψ Kg Src hdag jStar hjStar F hm hq H s t ht hjs e φ hφ (respYPlus P jStar F t e) uP
      hmax hEint hJt (hsumm (respYPlus P jStar F t e))
    have hTint : Integrable (fun a => ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1) *
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => vecDot (respYPlus P jStar F t e).2
                    (optimizerField (respCoeffPlus F a) (uP a) x).1
                  + vecDot (respYPlus P jStar F t e).1
                    (optimizerField (respCoeffPlus F a) (uP a) x).2)) P :=
      integrable_avsum_weighted_pairing (fun _ => triadicIndexBox d H)
        (fun _ w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ - 1)
        (fun _ w a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (fun x => vecDot (respYPlus P jStar F t e).2
                (optimizerField (respCoeffPlus F a) (uP a) x).1
              + vecDot (respYPlus P jStar F t e).1
                (optimizerField (respCoeffPlus F a) (uP a) x).2))
        (fun _ W hW => hcrossH W hW) 0
    have hcrossOn : ∀ a : CoeffSpace d, IntegrableOn
        (fun x => vecDot (respYPlus P jStar F t e).2
              (optimizerField (respCoeffPlus F a) (uP a) x).1
            + vecDot (respYPlus P jStar F t e).1
              (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t) := by
      intro a
      have h := integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar
        F hm
        t 0 a (uP a) (respYPlus P jStar F t e) (zero_mem_triadicIndexBox 0)
      have hUcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0
          = respCell jStar F t := by
        rw [Nat.cast_zero, sub_zero]
        exact adaptedCellAtCenter_zero (respGrid jStar F) t
      rw [hUcell] at h
      exact h.1
    have hEq1 := integral_cutoffFluctuation_split P (respGrid jStar F) hq H s t hst φ hφ
      (fun a x => vecDot (respYPlus P jStar F t e).2
            (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot (respYPlus P jStar F t e).1
            (optimizerField (respCoeffPlus F a) (uP a) x).2)
      (fun a => by simpa only [respCell] using hcrossOn a) hhalf.1 hTint
    have hEq2 := integral_cutoffCellPart_shift P (respGrid jStar F) H s t hst φ
      (fun a x => vecDot (respYPlus P jStar F t e).2
            (optimizerField (respCoeffPlus F a) (uP a) x).1
          + vecDot (respYPlus P jStar F t e).1
            (optimizerField (respCoeffPlus F a) (uP a) x).2) hwt
    have hbound : |vecDot (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P)
          (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1
          (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d H, volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (fun x => (φ x - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) φ) *
                (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P)|
        ≤ respCutoffOscConst d * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) := by
      rw [hbridge, hEq1, hEq2]
      exact le_trans hhalf.2 (le_of_eq (oscConst_arith d (respLsPlus P jStar F s t e)
        (respEJPlus P jStar F t e) ((3 : ℝ) ^ (-(H : ℝ))) hEJ))
    exact hbound

end

end HCPolySupport.HighContrast.Multiscale
end
