/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingFourierCurve
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedDerivativeBridge

/-!
# Continuous scalar Sobolev trajectories of the regularized velocity

The global Bessel realization gives a continuous spatial `L²` path for
every ordered classical derivative on a finite interval.
-/

public section

open MeasureTheory Set
open scoped ENNReal


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- Every ordered spatial derivative of the physical regularized velocity
has a continuous scalar `L²` realization on a finite closed interval
(`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_wordDeriv_continuous_L2
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (T : ℝ) (hT : 0 ≤ T) (i : Fin 3) (α : List (Fin 3)) :
    ∃ F : ℝ → Lp ℝ 2 (volume : Measure Vec3),
      Continuous F ∧
      ∀ t ∈ Icc 0 T,
        (F t : Vec3 → ℝ) =ᵐ[volume]
          wordDeriv α (fun x : Vec3 =>
            CKN.Leray.regR12Velocity ρ ε hε a ha (x, t) i) := by
  let n : ℕ := α.length
  have hα : α.length ≤ 2 * (n + 1) := by dsimp [n]; omega
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) T hT
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  let G := lps_regR12HighLiftFreq n T hT v
  let F := lps_dampedScalarCurve n α hα i G
  refine ⟨F, lps_dampedScalarCurve_continuous n α hα i G
    (lps_regR12HighLiftFreq_continuous n T hT v), ?_⟩
  intro t ht
  have hrep := lps_dampedScalarCurve_ae_eq n α hα i G t
  have heq := lps_regR12Velocity_wordDeriv_eq_high_model
    ρ ε hε a ha n T hT v hv' t ht i α hα
  exact hrep.trans (Filter.Eventually.of_forall fun x => (congrFun heq x).symm)

/-- Every ordered spatial derivative of the regularized velocity belongs
to `L²` on a positive finite space-time slab (`prop:lps-smoothing`). -/
theorem lps_regR12Velocity_all_word_memLp_slab
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (δ T : ℝ) (hδ : 0 ≤ δ) (hδT : δ < T)
    (i : Fin 3) (α : List (Fin 3)) :
    MemLp (fun z : ParabolicPoint =>
      wordDeriv α (fun x : Vec3 =>
        CKN.Leray.regR12Velocity ρ ε hε a ha (x, z.2) i) z.1)
      2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T))) := by
  let n : ℕ := α.length
  have hα : α.length ≤ 2 * (n + 1) := by dsimp [n]; omega
  have hT : 0 ≤ T := le_of_lt (lt_of_le_of_lt hδ hδT)
  obtain ⟨v, hv⟩ :=
    CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha (n + 2) T hT
  have hv' : ∀ s : CKN.Leray.RegularizedMildTimeInterval T,
      CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * (n + 2) : ℕ) : ℝ) (by positivity) (v s) =
        CKN.Leray.complexifyVectorL2
          (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  exact lps_regR12Velocity_wordDeriv_memLp_slab
    ρ ε hε a ha n δ T hδ hδT v hv' i α hα

end ESS
