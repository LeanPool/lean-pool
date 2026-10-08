/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSkewLaw
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSkewUnitRange

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Unit range survives the recentering

The recentering of the reference block is a transformation of the coefficient
field — subtraction of a constant skew — and the small-contrast argument runs at
the recentered law.  Stationarity, the ellipticity datum and both contrasts are
already known to travel with it; the remaining frozen premise is unit range.

It travels for the same reason the triadic rebasing's does, and more simply: the
recentering moves no point of space, so each local sigma-field is carried into
*itself*.  A generating statistic of the shifted sample is the statistic of the
sample translated by a constant, and the constant depends only on the skew and
the test function, so the pullback of a generator is a generator with the same
test support.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem indep_map_measurableEquiv'
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {m₁ m₂ : MeasurableSpace β}
    (h : @ProbabilityTheory.Indep α
      (MeasurableSpace.comap (fun x : α => e x) m₁)
      (MeasurableSpace.comap (fun x : α => e x) m₂) mα μ) :
    @ProbabilityTheory.Indep β m₁ m₂ mβ
      (@Measure.map α β mα mβ (fun x : α => e x) μ) := by
  refine (ProbabilityTheory.Indep_iff
    (m₁ := m₁) (m₂ := m₂) (_mΩ := mβ)
    (μ := @Measure.map α β mα mβ (fun x : α => e x) μ)).2 ?_
  intro s t hs ht
  have hemb : @MeasurableEmbedding α β mα mβ (fun x : α => e x) :=
    @MeasurableEquiv.measurableEmbedding α β mα mβ e
  have hindep := (ProbabilityTheory.Indep_iff
    (m₁ := MeasurableSpace.comap (fun x : α => e x) m₁)
    (m₂ := MeasurableSpace.comap (fun x : α => e x) m₂)
    (_mΩ := mα) (μ := μ)).1 h
  have hsPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m₁)
      ((fun x : α => e x) ⁻¹' s) := ⟨s, hs, rfl⟩
  have htPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m₂)
      ((fun x : α => e x) ⁻¹' t) := ⟨t, ht, rfl⟩
  have hst := hindep ((fun x : α => e x) ⁻¹' s)
    ((fun x : α => e x) ⁻¹' t) hsPre htPre
  have hmapInter :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ (s ∩ t)
  have hmapS :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) s =
        μ ((fun x : α => e x) ⁻¹' s) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ s
  have hmapT :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) t =
        μ ((fun x : α => e x) ⁻¹' t) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ t
  calc
    (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := hmapInter
    _ = μ (((fun x : α => e x) ⁻¹' s) ∩
          ((fun x : α => e x) ⁻¹' t)) := rfl
    _ = μ ((fun x : α => e x) ⁻¹' s) *
          μ ((fun x : α => e x) ⁻¹' t) := hst
    _ = (@Measure.map α β mα mβ (fun x : α => e x) μ) s *
          (@Measure.map α β mα mβ (fun x : α => e x) μ) t := by
      rw [hmapS, hmapT]

/-- **The recentering is local.**  Each local sigma-field is carried into
itself, because a generating statistic of the shifted sample is the statistic of
the sample translated by a constant with the same test support. -/
theorem coeffSigma_comap_subSkew_le (U : Set (Vec d)) (g : Mat d)
    (hg : IsSkewMat g) :
    MeasurableSpace.comap (fun a : CoeffSpace d => a.subSkew g hg)
        (coeffSigma d U) ≤ coeffSigma d U := by
  change MeasurableSpace.comap (fun a : CoeffSpace d => a.subSkew g hg)
      (MeasurableSpace.generateFrom
        {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ), IsLocalTest U φ ∧
          ∃ t : Set ℝ, MeasurableSet t ∧ s = coeffPairing e e' φ ⁻¹' t}) ≤
    MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ), IsLocalTest U φ ∧
        ∃ t : Set ℝ, MeasurableSet t ∧ s = coeffPairing e e' φ ⁻¹' t}
  rw [MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨u, ⟨e, e', φ, hφ, t, ht, rfl⟩, rfl⟩
  have hset : (fun a : CoeffSpace d => a.subSkew g hg) ⁻¹'
      (coeffPairing e e' φ ⁻¹' t) =
      coeffPairing e e' φ ⁻¹'
        ((fun y : ℝ => y - vecDot e' (matVecMul g e) * ∫ x, φ x ∂volume) ⁻¹'
          t) := by
    ext a
    change coeffPairing e e' φ (a.subSkew g hg) ∈ t ↔ _
    rw [Selection.coeffPairing_subSkew e e' hφ g hg a]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', φ, hφ, _, (measurable_sub_const _) ht, rfl⟩

/-- **Unit range is invariant under the recentering.** -/
theorem isUnitRangeLaw_recenteredLaw {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {g : Mat d} (hg : IsSkewMat g) :
    HCPoly.Frozen.IsUnitRangeLaw (Quenched.recenteredLaw P hg) := by
  intro U V hU hV hUV
  have hIndep : ProbabilityTheory.Indep (coeffSigma d U) (coeffSigma d V) P :=
    hP U V hU hV hUV
  have hUle : MeasurableSpace.comap
      (fun a : CoeffSpace d => a.subSkew g hg) (coeffSigma d U) ≤
        coeffSigma d U := coeffSigma_comap_subSkew_le U g hg
  have hVle : MeasurableSpace.comap
      (fun a : CoeffSpace d => a.subSkew g hg) (coeffSigma d V) ≤
        coeffSigma d V := coeffSigma_comap_subSkew_le V g hg
  have hComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun a : CoeffSpace d => a.subSkew g hg) (coeffSigma d U))
      (MeasurableSpace.comap
        (fun a : CoeffSpace d => a.subSkew g hg) (coeffSigma d V)) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hIndep hUle) hVle
  have hMap := indep_map_measurableEquiv'
    (μ := P) (Quenched.subSkewEquiv hg) hComap
  simpa [Quenched.recenteredLaw] using hMap

end

end HighContrast
end HCPolySupport
