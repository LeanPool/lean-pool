/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Direct.TerminalEnergyDeficitBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.EllipticRepresentativeInputs
public import LeanPool.HighContrastHomogenization.Entry.Response.Pairing.CoarseBlockFenchelPairing
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# High-contrast homogenization: Entry.Response.Direct.DescendantEnergyAndFenchelSlots

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability and Closed Forms for the Descendant Sum

This module serves `p.response.transfer`.  At the response carriers, this file shows every linear
readout of each slot of the terminal
optimizer's doubled state, and their cross term, is `L^1(P)`-integrable on every descendant cell:
the recentred coefficients are elliptic only almost everywhere, so the argument runs at a single
pointwise elliptic representative on the terminal cell, serving every descendant cell at every
depth. Exact partition averaging identifies the flat average of the descendant cell energies, at
every depth, with the terminal cell energy, twice the terminal response at a maximizer; rescaling
by the constant converting it to the doubled energy the two crossed slots carry gives the row's
closed annealed form. The two cutoff-mean rows carry the crossed pairings `⟨N₁, Y₂⟩` and
`⟨Y₁, N₂⟩`, each bounded by the direct Fenchel pairing's own annealed coarse-block norm
times the square root of the cell energy.
-/

section
/-!
## The integrability of the terminal optimizer state on descendant cells

The descendant sum of `p.response.transfer` pairs the dual variable `Y` against the cell average,
over a descendant cell `V` of the terminal cell `U`, of the doubled state `X_u = (∇u, a_∓ ∇u)` of
the terminal optimizer `u`.  Each such pairing is a genuine integral, so every linear readout of
each state slot must be integrable on `V`.  The recentred coefficients `a_∓ = respCoeff∓ F a` are
elliptic only almost everywhere, so the integrability is read off a pointwise elliptic
representative on the terminal cell — one representative serves every descendant cell at every
depth, because every descendant cell is contained in the terminal cell — and transported back
across the almost-everywhere replacement, which changes the gradient slot not at all and the flux
slot only on a null set.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedCellCenter)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The state slots of the terminal optimizer are integrable on every descendant cell, minus
sign.**  For the recentred coefficient `a_- = a - g` of `p.response.transfer`, every linear readout
of the gradient slot and of the flux slot of the doubled state of the terminal optimizer is
integrable on each depth-`m` aligned descendant cell of the terminal cell. -/
theorem integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    (∀ r : Vec d, IntegrableOn
        (fun x => vecDot r (optimizerField (respCoeffMinus F a) u x).1)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
      ∧ (∀ p : Vec d, IntegrableOn
        (fun x => vecDot p (optimizerField (respCoeffMinus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (respCell jStar F t) := by
    change IsOpen (HighContrast.adaptedCell (respGrid jStar F) t)
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ respCell jStar F t := by
    change V ⊆ HighContrast.adaptedCell (respGrid jStar F) t
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr (by
      rw [hVdef]
      simpa only [adaptedCellAtCenter] using
        Transport.volume_adaptedCellTranslate_ne_top (respGrid jStar F) (t - (m : ℤ))
          (adaptedCellCenter (respGrid jStar F) (t - (m : ℤ)) W))
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u' : AHarmonicFunction f V :=
    (Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hVopen hVU hEllV with hu'
  have hgrad : u'.toH1.grad = u.toH1.grad := by
    rw [hu']
    simp only [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn, H1Function.restrict]
    exact Response.aHarmonicOfAEEq_grad hae u
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  constructor
  · intro r
    simpa only [optimizerField, hgrad] using hdata.grad r u'
  · intro p
    have hcongr : (fun x => vecDot p (matVecMul (f x) (u'.toH1.grad x)))
        =ᵐ[volumeMeasureOn V]
          (fun x => vecDot p (matVecMul ((respCoeffMinus F a) x) (u.toH1.grad x))) := by
      filter_upwards [haeV.symm] with x hx
      rw [hx, hgrad]
    simpa only [optimizerField] using (hdata.flux p u').congr_fun_ae hcongr

/-- **The state slots of the terminal optimizer are integrable on every descendant cell, plus
sign.**  The adjoint twin, for the recentred coefficient `a_+ = aᵀ + g`. -/
theorem integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    (∀ r : Vec d, IntegrableOn
        (fun x => vecDot r (optimizerField (respCoeffPlus F a) u x).1)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W))
      ∧ (∀ p : Vec d, IntegrableOn
        (fun x => vecDot p (optimizerField (respCoeffPlus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (respCell jStar F t) := by
    change IsOpen (HighContrast.adaptedCell (respGrid jStar F) t)
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ respCell jStar F t := by
    change V ⊆ HighContrast.adaptedCell (respGrid jStar F) t
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have : IsFiniteMeasure (volumeMeasureOn V) :=
    isFiniteMeasure_restrict.mpr (by
      rw [hVdef]
      simpa only [adaptedCellAtCenter] using
        Transport.volume_adaptedCellTranslate_ne_top (respGrid jStar F) (t - (m : ℤ))
          (adaptedCellCenter (respGrid jStar F) (t - (m : ℤ)) W))
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u' : AHarmonicFunction f V :=
    (Response.aHarmonicOfAEEq hae u).restrictOfIsEllipticFieldOn hU hVopen hVU hEllV with hu'
  have hgrad : u'.toH1.grad = u.toH1.grad := by
    rw [hu']
    simp only [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn, H1Function.restrict]
    exact Response.aHarmonicOfAEEq_grad hae u
  have hdata := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllV
  constructor
  · intro r
    simpa only [optimizerField, hgrad] using hdata.grad r u'
  · intro p
    have hcongr : (fun x => vecDot p (matVecMul (f x) (u'.toH1.grad x)))
        =ᵐ[volumeMeasureOn V]
          (fun x => vecDot p (matVecMul ((respCoeffPlus F a) x) (u.toH1.grad x))) := by
      filter_upwards [haeV.symm] with x hx
      rw [hx, hgrad]
    simpa only [optimizerField] using (hdata.flux p u').congr_fun_ae hcongr

/-- **The crossed pairing of the terminal optimizer state is integrable on every descendant cell,
minus sign.**  The scalar crossed pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a_-∇u⟩` of the descendant sum of
`p.response.transfer`, and its modulus, are integrable on each depth-`m` aligned descendant cell. -/
theorem integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    IntegrableOn (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      ∧ IntegrableOn (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffMinus F a) u x).2|)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := by
  obtain ⟨hgrad, hflux⟩ :=
    integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m
      a u hW
  constructor
  · simpa [MeasureTheory.IntegrableOn] using! (hgrad Y.2).integrable.add (hflux Y.1).integrable
  · simpa [MeasureTheory.IntegrableOn, Pi.add_apply] using
      ((hgrad Y.2).integrable.add (hflux Y.1).integrable).abs

/-- **The crossed pairing of the terminal optimizer state is integrable on every descendant cell,
plus sign.**  The adjoint twin, for the recentred coefficient `a_+ = aᵀ + g` and the dual variable
`Y^+`. -/
theorem integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter {d : ℕ}
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) (Y : BlockVec d)
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    IntegrableOn (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      ∧ IntegrableOn (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a) u x).1
          + vecDot Y.1 (optimizerField (respCoeffPlus F a) u x).2|)
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) := by
  obtain ⟨hgrad, hflux⟩ :=
    integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      u hW
  constructor
  · simpa [MeasureTheory.IntegrableOn] using! (hgrad Y.2).integrable.add (hflux Y.1).integrable
  · simpa [MeasureTheory.IntegrableOn, Pi.add_apply] using
      ((hgrad Y.2).integrable.add (hflux Y.1).integrable).abs

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The annealed flat average of the descendant cell energies

The descendant sum of `p.response.transfer` pairs each descendant cell average of the terminal
optimizer state with the annealed mean, and the Fenchel probe leaves behind the cell energy
`⨍_V ⟨∇u_t, S ∇u_t⟩`.  Its flat average over the depth-`m` triadic subdivision of the terminal
cell is the terminal cell energy (exact partition averaging), and for the maximizer the terminal
cell energy is twice the response:

```
⨍_{U_t} ⟨∇u_t, S ∇u_t⟩ = 2 J(U_t, p, q^∓; a_∓).
```

Taking expectations, the annealed flat average of twice the half cell energies is exactly
`2 E[J_t^∓]`, the scalar deficit the descendant row consumes.  Paper: `p.response.transfer`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Response integrability data for an almost-everywhere elliptic coefficient.**  If `b` is
a.e. equal on `V` to a coefficient `f` that is pointwise elliptic on `V`, then the four pairings
of the response identity are integrable for `b`.  Each `L²`/`L¹` statement for `f` is transported
across the a.e. equality. -/
private theorem responseLinearIntegrabilityData_of_aeEq
    {d : ℕ} {V : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn V)]
    {b f : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam V f) (hbf : b =ᵐ[volumeMeasureOn V] f) :
    ResponseLinearIntegrabilityData V b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u φ
    have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (b x) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hfluxb : MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp hfluxf
    exact integrableOn_vecDot_of_memVectorL2 hfluxb φ.toH1Function.grad_memVectorL2
  · intro p u
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p
      u.toH1.grad_memVectorL2
  · intro p u
    have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (b x) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hfluxb : MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp hfluxf
    exact CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hfluxb
  · intro u w
    have huf : MemVectorL2 V (fun x => matVecMul (symmPart (f x)) (u.toH1.grad x)) :=
      memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
    have hae : (fun x => matVecMul (symmPart (f x)) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
        (fun x => matVecMul (symmPart (b x)) (u.toH1.grad x)) := by
      filter_upwards [hbf] with x hx
      rw [hx]
    have hub : MemVectorL2 V (fun x => matVecMul (symmPart (b x)) (u.toH1.grad x)) :=
      (MeasureTheory.memLp_congr_ae hae).mp huf
    exact integrableOn_vecDot_of_memVectorL2 w.toH1.grad_memVectorL2 hub

/-- **Integrability data of the recentred sample `a_- = a - g` on the terminal cell.**  The
sample is an a.e. class; its ellipticity is supplied on the cell by an a.e.-equal elliptic
representative, and the four response pairings are transported to it. -/
private theorem responseLinearIntegrabilityData_respCell_respCoeffMinus
    {d : ℕ} (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hq : IsUnit (respGrid jStar F)) (a : CoeffSpace d) :
    ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffMinus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted (respGrid jStar F) hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_sub_skew hEll (respg F) (respg_isSkew F)
  have hae' : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)]
      (fun x => f x - respg F) := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  exact responseLinearIntegrabilityData_of_aeEq hEll' hae'

/-- **Integrability data of the adjoint recentred sample `a_+ = a^t + g` on the terminal cell.**
The transposed twin of `responseLinearIntegrabilityData_respCell_respCoeffMinus`. -/
private theorem responseLinearIntegrabilityData_respCell_respCoeffPlus
    {d : ℕ} (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hq : IsUnit (respGrid jStar F)) (a : CoeffSpace d) :
    ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffPlus F a) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted (respGrid jStar F) hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' := isEllipticFieldOn_transpose_add_skew hEll (respg F) (respg_isSkew F)
  have hae' : respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)]
      (fun x => matTranspose (f x) + respg F) := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) := by
    have hconv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
      adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  exact responseLinearIntegrabilityData_of_aeEq hEll' hae'

/-- **The annealed flat average of the descendant cell energies is twice the annealed terminal
response, minus sign.**  Exact partition averaging collapses the flat average of the depth-`m`
cell energies to the terminal cell energy, and the quadratic-response identity identifies the
latter with twice `J_t^-`. -/
theorem integral_avsum_two_mul_halfEnergy_eq_respEJMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) ∂P)
      = 2 * respEJMinus P jStar F t e := by
  have hpoint : ∀ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a) := by
    intro a
    have hInt : ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffMinus F a) :=
      responseLinearIntegrabilityData_respCell_respCoeffMinus jStar F t hq a
    have henergy := responseJ_energy_of_isResponseMaximizer (respCell jStar F t)
      (respCoeffMinus F a) (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (uM a) (hmax a) (hInt.weakFlux (uM a))
      (hInt.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (hInt.firstVariation (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (uM a) (uM a)) (hEint a)
    have hsum : (∑ W ∈ triadicIndexBox d m,
          2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))))
        = ∑ W ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) := by
      refine Finset.sum_congr rfl ?_
      intro W _
      ring
    rw [hsum, avsum_volumeAverage_eq (respGrid jStar F) hq t m (hEint a)]
    simp only [respJ, respCell] at henergy ⊢
    rw [henergy]
    ring
  have hconst : (∫ a, 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P)
      = 2 * ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a) ∂P := by
    simpa only [smul_eq_mul] using (hJ.integral_smul (2 : ℝ))
  rw [respEJMinus, ← hconst]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)

/-- **The annealed flat average of the descendant cell energies is twice the annealed terminal
response, plus sign.**  The adjoint twin of
`integral_avsum_two_mul_halfEnergy_eq_respEJMinus`. -/
theorem integral_avsum_two_mul_halfEnergy_eq_respEJPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) ∂P)
      = 2 * respEJPlus P jStar F t e := by
  have hpoint : ∀ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
      = 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a) := by
    intro a
    have hInt : ResponseLinearIntegrabilityData (respCell jStar F t) (respCoeffPlus F a) :=
      responseLinearIntegrabilityData_respCell_respCoeffPlus jStar F t hq a
    have henergy := responseJ_energy_of_isResponseMaximizer (respCell jStar F t)
      (respCoeffPlus F a) (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (uP a) (hmax a) (hInt.weakFlux (uP a))
      (hInt.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (hInt.firstVariation (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (uP a) (uP a)) (hEint a)
    have hsum : (∑ W ∈ triadicIndexBox d m,
          2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))))
        = ∑ W ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) := by
      refine Finset.sum_congr rfl ?_
      intro W _
      ring
    rw [hsum, avsum_volumeAverage_eq (respGrid jStar F) hq t m (hEint a)]
    simp only [respJ, respCell] at henergy ⊢
    rw [henergy]
    ring
  have hconst : (∫ a, 2 * respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P)
      = 2 * ∫ a, respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a) ∂P := by
    simpa only [smul_eq_mul] using (hJ.integral_smul (2 : ℝ))
  rw [respEJPlus, ← hconst]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The doubled descendant cell energy of the terminal optimizer at the carriers

The descendant sum of `p.response.transfer` pairs each cell head with the square root of twice the
cell energy of the terminal optimizer, and the sum of the two crossed slots carries the doubled
energy rather than the half energy.  Rescaling the annealed flat average of twice the half energy
by the constant `4` gives the doubled form, with the dual energy `E[J_t^∓]` replaced by
`4 E[J_t^∓]`.  Each cell energy is nonnegative because the symmetric part of an elliptic
coefficient is positive semidefinite; the recentred coefficients are elliptic only almost
everywhere, so this is read at a pointwise elliptic representative and transported back.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant cell energy of the terminal optimizer is nonnegative, minus sign.**  On every
aligned descendant cell of the terminal cell, the cell average of the variation energy integrand of
the recentred coefficient `a_- = a - g` is nonnegative. -/
theorem zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffMinus_adaptedCellAtCenter
    {d : ℕ} (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    Response.aHarmonicOfAEEq hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact Response.aHarmonicOfAEEq_grad hae u
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hnn : 0 ≤ volumeAverage V (scalarVariationEnergyIntegrand f
      (u₀.restrictOfIsEllipticFieldOn hU hVopen hVU hEllV)) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V f hEllV _
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hVopen hVU hEllV u₀] at hnn
  rwa [hE] at hnn

/-- **The descendant cell energy of the terminal optimizer is nonnegative, plus sign.**  The
adjoint twin, for the recentred coefficient `a_+ = aᵀ + g`. -/
theorem zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffPlus_adaptedCellAtCenter
    {d : ℕ} (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (m : ℕ) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    {W : Fin d → ℤ} (hW : W ∈ triadicIndexBox d m) :
    0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  set V : Set (Vec d) := adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W with hVdef
  have hU : IsOpen (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have h0 : HighContrast.adaptedCellTranslate (respGrid jStar F) t 0
        = HighContrast.adaptedCell (respGrid jStar F) t := by
      ext x; simp [HighContrast.adaptedCellTranslate]
    rw [← h0]
    exact Geometry.isOpen_adaptedCellTranslate hq t 0
  have hVopen : IsOpen V := by
    rw [hVdef]
    simp only [adaptedCellAtCenter]
    exact Geometry.isOpen_adaptedCellTranslate hq (t - (m : ℤ)) _
  have hVU : V ⊆ HighContrast.adaptedCell (respGrid jStar F) t := by
    rw [hVdef]
    exact adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hConv : IsOpenBoundedConvexDomain V := by
    rw [hVdef]
    exact isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq (t - (m : ℤ)) W
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  have hEllV : IsEllipticFieldOn lam Lam V f :=
    isEllipticFieldOn_subset hEll hVU hVopen.measurableSet
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  set u₀ : AHarmonicFunction f (HighContrast.adaptedCell (respGrid jStar F) t) :=
    Response.aHarmonicOfAEEq hae u with hu₀
  have hgrad : u₀.toH1.grad = u.toH1.grad := by
    rw [hu₀]
    exact Response.aHarmonicOfAEEq_grad hae u
  have hE : volumeAverage V (scalarVariationEnergyIntegrand f u₀)
      = volumeAverage V (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    simp only [volumeAverage]
    refine congrArg (fun z : ℝ => (volume V).toReal⁻¹ * z) (integral_congr_ae ?_)
    filter_upwards [haeV] with x hx
    simp only [scalarVariationEnergyIntegrand, hgrad, hx]
  have hnn : 0 ≤ volumeAverage V (scalarVariationEnergyIntegrand f
      (u₀.restrictOfIsEllipticFieldOn hU hVopen hVU hEllV)) :=
    volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn V f hEllV _
  rw [scalarVariationEnergyIntegrand_restrictOfIsEllipticFieldOn hU hVopen hVU hEllV u₀] at hnn
  rwa [hE] at hnn

/-- **The annealed flat average of the doubled descendant cell energies, minus sign.**  The
expectation of the flat average over the depth-`m` aligned cells of twice the doubled cell energy
of the terminal optimizer is `2 * (4 E[J_t^-])`, the value the descendant sum of
`p.response.transfer` consumes. -/
theorem integral_avsum_two_mul_doubledEnergy_eq_respEJMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) ∂P)
      = 2 * (4 * respEJMinus P jStar F t e) := by
  have hbase := integral_avsum_two_mul_halfEnergy_eq_respEJMinus P jStar F t m e hq uM hmax
    hEint hJ
  have hpt : ∀ a : CoeffSpace d,
      (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
        = 4 * ((((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
            2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m :
              ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) := by
    intro a
    have h1 : ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))
        = ∑ W ∈ triadicIndexBox d m,
          4 * (2 * ((1 / 2 : ℝ) * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)))) :=
      Finset.sum_congr rfl (fun W _ => by ring)
    rw [h1, ← Finset.mul_sum]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hbase]
  ring

/-- **The annealed flat average of the doubled descendant cell energies, plus sign.**  The adjoint
twin, with `4 E[J_t^+]`. -/
theorem integral_avsum_two_mul_doubledEnergy_eq_respEJPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (m : ℕ) (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hEint : ∀ a, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
        2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) ∂P)
      = 2 * (4 * respEJPlus P jStar F t e) := by
  have hbase := integral_avsum_two_mul_halfEnergy_eq_respEJPlus P jStar F t m e hq uP hmax
    hEint hJ
  have hpt : ∀ a : CoeffSpace d,
      (((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
        = 4 * ((((triadicIndexBox d m).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d m,
            2 * ((1 / 2 : ℝ) * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m :
              ℤ)) W)
              (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) := by
    intro a
    have h1 : ∑ W ∈ triadicIndexBox d m,
          2 * (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))
        = ∑ W ∈ triadicIndexBox d m,
          4 * (2 * ((1 / 2 : ℝ) * volumeAverage
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)))) :=
      Finset.sum_congr rfl (fun W _ => by ring)
    rw [h1, ← Finset.mul_sum]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hbase]
  ring

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The two slots of the full-dual pairing against the source-load head

The two cutoff-mean rows of `p.response.transfer` carry the two crossed pairings `⟨N₁, Y₂⟩` and
`⟨Y₁, N₂⟩` under separate absolute values, so each slot is bounded on its own.  The direct
full-dual Fenchel pairing bounds each slot by its own annealed coarse-block norm times the square
root of the cell energy.  Adding the other, nonnegative, annealed norm on the right puts both in
the single shape the descendant row consumes, with the source-load head
`G_V = |b_V^{1/2} Y₁| + |S_{*,V}^{-1/2} Y₂|` and the scalar deficit
`D_V = ½ ⨍_V ⟨∇v, S ∇v⟩`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The gradient slot of the full-dual pairing against the source-load head.**  The pairing of
the annealed flux `Y₂` with the gradient cell average of the optimizer state is at most the
source-load head of the cell times the square root of twice the half cell energy. -/
theorem abs_vecDot_cellAverage_grad_le_head {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (2 * ((1 / 2 : ℝ) *
            volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
  have hgrad := abs_vecDot_cellAverage_grad_le hConv hEll hvol v Y.2 hA2
  have hA1_nonneg : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1) := hA1
  have hle : Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
      ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :=
    le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hE : 0 ≤ Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
    Real.sqrt_nonneg _
  calc
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
        ≤ Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := hgrad
    _ ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        mul_le_mul_of_nonneg_right hle hE
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (2 * ((1 / 2 : ℝ) *
              volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
        rw [show 2 * ((1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v))
            = volumeAverage V (scalarVariationEnergyIntegrand b v) by ring]

/-- **The flux slot of the full-dual pairing against the source-load head.**  The pairing of the
annealed gradient `Y₁` with the flux cell average of the optimizer state is at most the
source-load head of the cell times the square root of twice the half cell energy. -/
theorem abs_vecDot_cellAverage_flux_le_head {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.1 (cellAverage V (optimizerField b v)).2|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (2 * ((1 / 2 : ℝ) *
            volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
  have hflux := abs_vecDot_cellAverage_flux_le hConv hEll hvol v Y.1 hA1
  have hA2_nonneg : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2) := hA2
  have hle : Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
      ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hE : 0 ≤ Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
    Real.sqrt_nonneg _
  calc
    |vecDot Y.1 (cellAverage V (optimizerField b v)).2|
        ≤ Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := hflux
    _ ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        mul_le_mul_of_nonneg_right hle hE
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
          * Real.sqrt (2 * ((1 / 2 : ℝ) *
              volumeAverage V (scalarVariationEnergyIntegrand b v))) := by
        rw [show 2 * ((1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v))
            = volumeAverage V (scalarVariationEnergyIntegrand b v) by ring]

end

end HCPolySupport.HighContrast.Multiscale
end
