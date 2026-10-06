/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.RoundedGrid
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.Translation

/-!
# High-contrast homogenization: Provider.Recurrence.StationarityTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Translation covariance of the coarse block and the stationarity transport

This is the translation covariance of the variational coarse block, among the
properties taken from HC in `s.introduction`: the pair

`𝐀(U + z; a) = 𝐀(U; T_z a)`,   `𝐀_*(U + z; a) = 𝐀_*(U; T_z a)`,   `z ∈ ℤ^d`,

and the consequence drawn from it, that under stationarity of the coefficient
law the translated blocks have the same law and hence the same expectation
whenever that expectation exists.

The pathwise identity is a change of variables in the variational definition of
the coarse block (`s.introduction`): translating a competitor is a bijection
between the admissible classes over `U + z` and over `U` that preserves the
energy average, so the two infima agree.  The coefficient field of the
coefficient space is an almost everywhere class, and the translation action `T_z`
of the coefficient-law setup in `s.introduction` is the class of `a(· + z)`; the
coarse response sees only the class, so the identity holds at every sample, with
no null set left
over.  The sharp half of the display is the image of the first half under the
primal-adjoint involution `H ↦ R H⁻¹ R` of `s.scale.selection`, which is how
`𝐀_*` is written here.

The annealed half is the change of variables `E[g ∘ T_z] = E[g]` under the law,
whose only input beyond stationarity of the coefficient law is that the entries
of the coarse response are measurable for the law, another of the properties
taken from HC.  The printed hedge "whenever they are finite" is the integrability
guard: it transports too, so an aligned cell inherits the finiteness of the mean
of the cell at the origin.

At the aligned adapted cells of a rounded geometry (`s.scale.selection`) the
translation vectors are integral, so the transport applies to them directly.  The resulting identity
`E[A_j^q(z)] = E_j^q` at every aligned center is what the averaging step of
`p.fixed.geometry.parent.child.recurrence` consumes when it replaces the annealed block of
each child by the mean at the parent scale, together with its averaged form
`E[G] = E_j^q`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Translates of a set -/

/-- The translate of a set is its image under the translation. -/
theorem translateSet_eq_image_add (y : Vec d) (U : Set (Vec d)) :
    translateSet y U = (fun x => y + x) '' U := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Set.mem_image]
  constructor
  · intro hx
    exact ⟨x - y, hx, by abel⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

/-! ## The translated sample -/

/-- The field of a translated sample is the translate of its field.  The
translation action `T_z` on the coefficient space acts on the almost everywhere
class; this is the identity of representatives it is built from. -/
theorem coe_translateCoeff_ae_eq (z : Fin d → ℤ) (a : CoeffSpace d) :
    (⇑(translateCoeff z a).1 : Vec d → Mat d) =ᵐ[volume]
      translateCoeffField (Source.AKL.intTranslation z) (⇑a.1) := by
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hx
  exact hx

/-! ## The pathwise covariance -/

/-- **`𝐀(U + z; a) = 𝐀(U; T_z a)`.**  The first half of the translation
covariance of the coarse block, at every sample of the coefficient space. -/
theorem coarseBlock_translateSet (z : Fin d → ℤ) (U : Set (Vec d)) (a : CoeffSpace d) :
    coarseBlock (translateSet (Source.AKL.intTranslation z) U) a =
      coarseBlock U (translateCoeff z a) := by
  rw [coarseBlock_eq_of_ae_eq (U := U) (translateCoeff z a) (coe_translateCoeff_ae_eq z a),
    coarseBlock, coarseBlockMatrix_translateSet_eq_translateCoeffField]

/-! ## The annealed transport -/

/-- **The integer translations preserve the law.**  This is stationarity of the
coefficient law under integer translations, restated as the measure-preserving
property of the translation action, the form
in which a change of variables applies to an arbitrary statistic of the
coefficient field. -/
theorem measurePreserving_translateCoeff {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) (z : Fin d → ℤ) :
    MeasurePreserving (translateCoeff z) P P :=
  ⟨measurable_translateCoeff z, hP z⟩

/-- **The translated blocks have the same law.**  This is the first conclusion
drawn from the pathwise covariance, read at each entry of the doubled block. -/
theorem map_blockMatEntry_coarseBlock_translateSet {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {U : Set (Vec d)}
    (hmeas : HasMeasurableCoarseBlock P U) (z : Fin d → ℤ) (α β : BlockCoord d) :
    Measure.map
        (fun a =>
          blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z) U) a) α β) P =
      Measure.map (fun a => blockMatEntry (coarseBlock U a) α β) P := by
  have hg : AEMeasurable (fun b => blockMatEntry (coarseBlock U b) α β)
      (Measure.map (translateCoeff z) P) := by
    rw [hP z]
    exact (hmeas α β).aemeasurable
  calc Measure.map
        (fun a =>
          blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z) U) a) α β) P
      = Measure.map ((fun b => blockMatEntry (coarseBlock U b) α β) ∘ translateCoeff z) P := by
        simp only [Function.comp_def, coarseBlock_translateSet]
    _ = Measure.map (fun b => blockMatEntry (coarseBlock U b) α β)
          (Measure.map (translateCoeff z) P) :=
        (AEMeasurable.map_map_of_aemeasurable hg
          (measurable_translateCoeff z).aemeasurable).symm
    _ = Measure.map (fun b => blockMatEntry (coarseBlock U b) α β) P := by rw [hP z]

/-- The expectation of an entry of the coarse response is unchanged by an integer
translation of the cell.  This is the change of variables `E[g ∘ T_z] = E[g]`
under stationarity of the coefficient law. -/
theorem integral_blockMatEntry_coarseBlock_translateSet {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {U : Set (Vec d)}
    (hmeas : HasMeasurableCoarseBlock P U) (z : Fin d → ℤ) (α β : BlockCoord d) :
    ∫ a, blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z) U) a) α β ∂P =
      ∫ a, blockMatEntry (coarseBlock U a) α β ∂P := by
  have hmap : AEStronglyMeasurable
      (fun b => blockMatEntry (coarseBlock U b) α β) (Measure.map (translateCoeff z) P) := by
    rw [hP z]
    exact hmeas α β
  calc ∫ a, blockMatEntry (coarseBlock (translateSet (Source.AKL.intTranslation z) U) a) α β ∂P
      = ∫ a, blockMatEntry (coarseBlock U (translateCoeff z a)) α β ∂P := by
        simp only [coarseBlock_translateSet]
    _ = ∫ b, blockMatEntry (coarseBlock U b) α β ∂(Measure.map (translateCoeff z) P) :=
        (integral_map (measurable_translateCoeff z).aemeasurable hmap).symm
    _ = ∫ b, blockMatEntry (coarseBlock U b) α β ∂P := by rw [hP z]

/-- **`𝐀̄(U + z) = 𝐀̄(U)`.**  The consequence drawn from the pathwise
covariance: under stationarity of the coefficient law the annealed blocks of a
cell and of its integer translate agree. -/
theorem annealedBlock_translateSet {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {U : Set (Vec d)}
    (hmeas : HasMeasurableCoarseBlock P U) (z : Fin d → ℤ) :
    annealedBlock P (translateSet (Source.AKL.intTranslation z) U) = annealedBlock P U := by
  have hentry : ∀ α β : BlockCoord d,
      blockMatEntry (annealedBlock P (translateSet (Source.AKL.intTranslation z) U)) α β =
        blockMatEntry (annealedBlock P U) α β := by
    intro α β
    rw [blockMatEntry_annealedBlock, blockMatEntry_annealedBlock]
    exact integral_blockMatEntry_coarseBlock_translateSet hP hmeas z α β
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> funext i j
  · exact hentry (Sum.inl i) (Sum.inl j)
  · exact hentry (Sum.inl i) (Sum.inr j)
  · exact hentry (Sum.inr i) (Sum.inl j)
  · exact hentry (Sum.inr i) (Sum.inr j)

/-- The finiteness hedge of the translation clause transports: if the coarse
response over a cell is integrable for the law, so is the coarse response over
every integer translate of it. -/
theorem hasIntegrableCoarseBlock_translateSet {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {U : Set (Vec d)}
    (hint : HasIntegrableCoarseBlock P U) (z : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (translateSet (Source.AKL.intTranslation z) U) := by
  intro α β
  have hmap : Integrable (fun b => blockMatEntry (coarseBlock U b) α β)
      (Measure.map (translateCoeff z) P) := by
    rw [hP z]
    exact hint α β
  have hcomp := hmap.comp_aemeasurable (measurable_translateCoeff z).aemeasurable
  simpa only [coarseBlock_translateSet, Function.comp_def] using hcomp

/-! ## The aligned adapted cells -/

/-- An aligned adapted cell of a rounded geometry (`s.scale.selection`) is the
translate of the cell at the origin by its own center. -/
theorem adaptedCellAt_eq_translateSet (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt q r w = translateSet (adaptedCellCenter q r w) (adaptedCell q r) := by
  rw [translateSet_eq_image_add]
  rfl

/-- An aligned adapted cell with integral center is an integer translate of the
cell at the origin. -/
theorem adaptedCellAt_eq_translateSet_intVec {q : Mat d} {r : ℤ} {w v : Fin d → ℤ}
    (hv : adaptedCellCenter q r w = fun i => (v i : ℝ)) :
    adaptedCellAt q r w = translateSet (Source.AKL.intTranslation v) (adaptedCell q r) := by
  rw [adaptedCellAt_eq_translateSet, hv]
  rfl

/-- **`A_r^q(z; a) = A_r^q(0; T_z a)`.**  The translation covariance of the
coarse block at an aligned adapted cell: the adapted response at an aligned
center is the response at the origin of the translated sample. -/
theorem adaptedResponse_eq_coarseBlock_translateCoeff {q : Mat d} {r : ℤ} {w v : Fin d → ℤ}
    (hv : adaptedCellCenter q r w = fun i => (v i : ℝ)) (a : CoeffSpace d) :
    adaptedResponse q r w a = coarseBlock (adaptedCell q r) (translateCoeff v a) := by
  rw [adaptedResponse, adaptedCellAt_eq_translateSet_intVec hv, coarseBlock_translateSet]

/-- The same identity with the integral translation vector supplied by the
lattice alignment of the rounded grid in `s.scale.selection`. -/
theorem exists_adaptedResponse_eq_coarseBlock_translateCoeff {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {j : ℤ} (hj : l ≤ j) (w : Fin d → ℤ) :
    ∃ v : Fin d → ℤ, adaptedCellCenter q j w = (fun i => (v i : ℝ)) ∧
      ∀ a : CoeffSpace d,
        adaptedResponse q j w a = coarseBlock (adaptedCell q j) (translateCoeff v a) := by
  obtain ⟨v, hv⟩ := exists_intVec_adaptedCellCenter hq hj w
  exact ⟨v, hv, fun a => adaptedResponse_eq_coarseBlock_translateCoeff hv a⟩

/-- **`E[A_j^q(z)] = E_j^q`.**  The adapted means at aligned translated cells
coincide: this is the identity the averaging step of
`p.fixed.geometry.parent.child.recurrence` consumes when it replaces the annealed block of
each child by the mean at the parent scale. -/
theorem annealedBlock_adaptedCellAt_eq_adaptedMean {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hj : l ≤ j) (hmeas : HasMeasurableCoarseBlock P (adaptedCell q j))
    (w : Fin d → ℤ) :
    annealedBlock P (adaptedCellAt q j w) = adaptedMean P q j := by
  obtain ⟨v, hv⟩ := exists_intVec_adaptedCellCenter hq hj w
  rw [adaptedCellAt_eq_translateSet_intVec hv, adaptedMean]
  exact annealedBlock_translateSet hP hmeas v

/-- The finiteness of the adapted mean transports to every aligned cell at the
same scale, so the guard `HasFiniteAdaptedMean` at the origin is the only one the
averaging step needs. -/
theorem hasIntegrableCoarseBlock_adaptedCellAt {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {j : ℤ} (hj : l ≤ j) (hint : HasFiniteAdaptedMean P q j) (w : Fin d → ℤ) :
    HasIntegrableCoarseBlock P (adaptedCellAt q j w) := by
  obtain ⟨v, hv⟩ := exists_intVec_adaptedCellCenter hq hj w
  rw [adaptedCellAt_eq_translateSet_intVec hv]
  exact hasIntegrableCoarseBlock_translateSet hP hint v

end

end Recurrence
end HighContrast
end HCPolySupport
