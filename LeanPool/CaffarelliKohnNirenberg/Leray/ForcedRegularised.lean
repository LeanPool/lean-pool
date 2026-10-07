/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedConstruction

/-!
# The forced regularized solutions

`lem:regularised-forced`: for every divergence-free datum in `J`, every
locally square-integrable force and every `ε > 0`, the forced regularized
problem has a velocity, a weak gradient and a pressure with the slice
continuity, initial datum and divergence freedom of the velocity, the weak
gradient on almost every positive time slice, square integrability of the
gradient and of the quadratic pressure on bounded slabs, the Riesz
representation and Laplacian identity of the quadratic pressure on every
positive time slice, and the energy inequality `eq:reg-energy-forced`. The
pressure is the quadratic Riesz pressure plus the force pressure of
`lem:force-pressure`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The velocity of the forced regularized problem, set to zero when
`ε ≤ 0`. -/
@[expose]
def forcedRegVelocity (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) (ε : ℝ) :
    ParabolicPoint → Vec3 :=
  if hε : 0 < ε then forcedRegRep ρ ε hε ha hf else 0

/-- The weak gradient field of the forced regularized velocity. -/
@[expose]
def forcedRegGradient (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) (ε : ℝ) :
    ParabolicPoint → Fin 3 → Vec3 :=
  forcedMollifiedGrad (forcedRegVelocity ρ a ha f hf ε)

/-- The pressure of the forced regularized problem: the quadratic Riesz
pressure plus the force pressure, set to zero when `ε ≤ 0`. -/
@[expose]
def forcedRegPressure (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) (ε : ℝ) :
    ParabolicPoint → ℝ :=
  if hε : 0 < ε then
    fun z => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z
  else 0

theorem forcedRegVelocity_eq (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : IsInJ a)
    {f : ParabolicPoint → Vec3} (hf : IsLocallySquareIntegrableForce f) {ε : ℝ} (hε : 0 < ε) :
    forcedRegVelocity ρ a ha f hf ε = forcedRegRep ρ ε hε ha hf := by
  unfold forcedRegVelocity
  simp only [hε, ↓reduceDIte]
  rfl

theorem forcedRegPressure_sub (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : IsInJ a)
    {f : ParabolicPoint → Vec3} (hf : IsLocallySquareIntegrableForce f) {ε : ℝ} (hε : 0 < ε)
    (z : ParabolicPoint) :
    forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z =
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z := by
  unfold forcedRegPressure
  simp only [hε, ↓reduceDIte]
  exact add_sub_cancel_right _ _

theorem forcedRegPressure_sub_apply (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : IsInJ a)
    {f : ParabolicPoint → Vec3} (hf : IsLocallySquareIntegrableForce f) {ε : ℝ} (hε : 0 < ε)
    (x : Vec3) (t : ℝ) :
    forcedRegPressure ρ a ha f hf ε (x, t) - forcePressure f hf (x, t) =
      forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t) :=
  forcedRegPressure_sub ρ ha hf hε (x, t)

section Clauses

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- On every time slice the quadratic pressure is the Riesz pressure of the
regularized tensor and satisfies its Laplacian identity. -/
theorem forcedRegRep_pressureSlice (t : ℝ) :
    ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
          forcedRegRep ρ ε hε ha hf (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
      (fun x : Vec3 => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
          (fun i j => (hF i j).toLp (fun x : Vec3 =>
            regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
              forcedRegRep ρ ε hε ha hf (x, t) j)) ∧
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x : Vec3, forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t) *
            spatialLaplacian ψ x) =
          -∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
            regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
              forcedRegRep ρ ε hε ha hf (x, t) j * mixedSecond ψ i j x := by
  have hrep := forcedRegRep_slice ρ ε hε ha hf t
  have hF : ∀ i j : Fin 3, MemLp
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
        forcedRegRep ρ ε hε ha hf (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume := fun i j =>
    (memLp_forcedTensorComp (regularizedMildTensor ρ ε hε (forcedRegCurve ρ ε hε ha hf t))
      i j).ae_eq (regPressureTensorSlice_ae_eq ρ ε hε hrep i j).symm
  have hEq : (fun i j => (hF i j).toLp (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
        forcedRegRep ρ ε hε ha hf (x, t) j)) =
      forcedPressureTensorLp (regularizedMildTensor ρ ε hε (forcedRegCurve ρ ε hε ha hf t)) := by
    funext i j
    exact MemLp.toLp_congr _ _ (regPressureTensorSlice_ae_eq ρ ε hε hrep i j)
  have hslice : (fun x : Vec3 => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (x, t))
      =ᵐ[volume] rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
        (fun i j => (hF i j).toLp (fun x : Vec3 =>
          regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
            forcedRegRep ρ ε hε ha hf (x, t) j)) := by
    rw [hEq]
    exact forcedQuadPressure_slice ρ ε hε _ t
  refine ⟨hF, hslice, fun ψ hψ hψc => ?_⟩
  refine (integral_congr_ae ?_).trans (regularisedPressureSlice_riesz_laplacian_pairing
    (fun i j x => regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) i *
      forcedRegRep ρ ε hε ha hf (x, t) j) hF ψ hψ hψc)
  filter_upwards [hslice] with x hx
  rw [hx]

/-- The work of the force on `(0, t)` for `t ≥ 0`. -/
theorem forcedRegRep_work {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Ioc 0 t, inner ℝ (forcedRegCurve ρ ε hε ha hf s)
        (forcedForceSlice (forcedForceMod f hf) s) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
        ∑ i : Fin 3, f z i * forcedRegRep ρ ε hε ha hf z i := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Ioc_self, Ioo_self, Measure.restrict_empty, integral_zero_measure]
    have hE : spaceTimeSet (Set.univ : Set Vec3) (∅ : Set ℝ) = ∅ := prod_empty
    rw [hE, Measure.restrict_empty, integral_zero_measure]
  · exact forcedForce_work_eq (continuous_forcedRegCurve ρ ε hε ha hf)
      (forcedRegRep_stronglyMeasurable ρ ε hε ha hf) (forcedRegRep_slice ρ ε hε ha hf) f hf hpos

/-- `eq:reg-energy-forced` in the form of `lem:regularised-forced`. -/
theorem forcedRegRep_energyClause {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (regUniformVelocitySlice (forcedRegRep ρ ε hε ha hf) t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (forcedRegRep ρ ε hε ha hf)
          (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) t < ⊤ ∧
      (eLpNorm (regUniformVelocitySlice (forcedRegRep ρ ε hε ha hf) t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (forcedRegRep ρ ε hε ha hf)
          (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) t).toReal ≤
        (eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)).toReal +
        2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          ∑ i : Fin 3, f z i * forcedRegRep ρ ε hε ha hf z i := by
  obtain ⟨D, hdis, hD0, hen⟩ := forcedRegRep_energy ρ ε hε ha hf ht
  have hv : eLpNorm (regUniformVelocitySlice (forcedRegRep ρ ε hε ha hf) t) 2 volume =
      ENNReal.ofReal ‖forcedRegCurve ρ ε hε ha hf t‖ := by
    rw [eLpNorm_congr_ae (regUniformVelocitySlice_ae_eq (forcedRegRep_slice ρ ε hε ha hf t)),
      Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have hb : eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume =
      ENNReal.ofReal ‖forcedRegDatum ρ ε hε ha‖ := by
    have h := realVectorL2OfCoordinateFunction_ae_eq_toLp _ (forcedRegInitial_memLp ρ ε hε ha)
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    unfold forcedRegDatum
    rw [eLpNorm_congr_ae h]
    rfl
  have hdiss : regUniformDissipation (forcedRegRep ρ ε hε ha hf)
      (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) t ≤ ENNReal.ofReal D :=
    (regUniformDissipation_eq_slab _ _ t).trans_le ((lintegral_slab_eq_prod _ _).trans_le hdis)
  have hle : eLpNorm (regUniformVelocitySlice (forcedRegRep ρ ε hε ha hf) t) 2 volume ^ (2 : ℕ) +
      2 * regUniformDissipation (forcedRegRep ρ ε hε ha hf)
        (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf)) t ≤
      ENNReal.ofReal (‖forcedRegCurve ρ ε hε ha hf t‖ ^ 2 + 2 * D) := by
    rw [hv, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    gcongr
  refine ⟨hle.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  rw [hb, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.toReal_ofReal (by positivity),
    ← forcedRegRep_work ρ ε hε ha hf ht]
  calc _ ≤ (ENNReal.ofReal (‖forcedRegCurve ρ ε hε ha hf t‖ ^ 2 + 2 * D)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = ‖forcedRegCurve ρ ε hε ha hf t‖ ^ 2 + 2 * D := ENNReal.toReal_ofReal (by positivity)
    _ ≤ _ := hen

end Clauses

/-- `lem:regularised-forced`: the forced regularized solutions, with the
force pressure of `lem:force-pressure`, have the slice, gradient, pressure and
energy properties used by the limiting argument of `thm:leray-forced`. -/
theorem forcedRegularised (ρ : RegMollifierProfile) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε),
      let u := forcedRegVelocity ρ a ha f hf ε
      let Du := forcedRegGradient ρ a ha f hf ε
      let p := forcedRegPressure ρ a ha f hf ε
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) ∧
      (∀ T : ℝ, 0 < T →
        MemLp Du 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp (fun z => p z - forcePressure f hf z) 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t) - forcePressure f hf (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, (p (x, t) - forcePressure f hf (x, t)) *
                spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
            2 * CKN.Leray.regUniformDissipation u Du t < ⊤ ∧
          (eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
            2 * CKN.Leray.regUniformDissipation u Du t).toReal ≤
            (eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)).toReal +
            2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
              ∑ i : Fin 3, f z i * u z i) := by
  intro a ha f hf ε hε
  dsimp only
  simp only [forcedRegPressure_sub ρ ha hf hε, forcedRegPressure_sub_apply ρ ha hf hε]
  rw [show forcedRegGradient ρ a ha f hf ε = forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) by
    unfold forcedRegGradient
    rw [forcedRegVelocity_eq ρ ha hf hε], forcedRegVelocity_eq ρ ha hf hε]
  refine ⟨⟨fun t _ => forcedRegRep_memLp ρ ε hε ha hf t, ?_, forcedRegRep_initial ρ ε hε ha hf,
    fun t ht => forcedRegRep_weakDivFree ρ ε hε ha hf ht⟩, forcedRegRep_weakGradient ρ ε hε ha hf,
    fun T hT => ⟨?_, ?_⟩, fun t _ => forcedRegRep_pressureSlice ρ ε hε ha hf t,
    fun t ht => forcedRegRep_energyClause ρ ε hε ha hf ht⟩
  · exact ((continuous_forcedRegCurve ρ ε hε ha hf).comp continuous_subtype_val).congr
      fun t => (forcedRegRep_class ρ ε hε ha hf t.1).symm
  · obtain ⟨D, hdis, -, -⟩ := forcedRegRep_energy ρ ε hε ha hf hT.le
    exact memLp_slab_of_prod (memLp_forcedMollifiedGrad_prod
      (forcedRegRep_stronglyMeasurable ρ ε hε ha hf)
      (forcedRegRep_locallyIntegrable ρ ε hε ha hf) (hdis.trans_lt ENNReal.ofReal_lt_top))
  · exact memLp_slab_of_prod (memLp_forcedQuadPressure_slab ρ ε hε
      (continuous_forcedRegCurve ρ ε hε ha hf) T)

end CKN.Leray

end
