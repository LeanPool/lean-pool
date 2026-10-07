/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedScalarCurve
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedSmooth
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingPressureSmooth
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingRegularizedRHSL2
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalR1
public import LeanPool.CaffarelliKohnNirenberg.Leray.JSpaceFourierLimit

/-!
# The actual regularized momentum right-hand side in spatial `L²`

At positive times the regularized velocity and canonical pressure
are spatially smooth, with all their classical ordered derivatives in
`L²`. The complete regularized momentum right-hand side has the same
property.
-/

public section

open MeasureTheory Set
open scoped ENNReal


noncomputable section

namespace ESS

open CKN.Leray
open CKN CKN.Foundation.Parabolic

/-- The physical regularized velocity is in the solenoidal `L²`
space on every nonnegative-time slice. -/
theorem lps_regR12Velocity_slice_isInJ
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 ≤ t) :
    IsInJ (fun x : Vec3 => CKN.Leray.regR12Velocity ρ ε hε a ha (x, t)) := by
  have hpath : ∀ T : ℝ, 0 ≤ T →
      ∃ v : C(CKN.Leray.RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      ∀ s : CKN.Leray.RegularizedMildTimeInterval T,
        CKN.Leray.regularisedBesselSobolevToL2CLM
          ((2 * 2 : ℕ) : ℝ) (by positivity) (v s) =
          CKN.Leray.complexifyVectorL2
            (CKN.Leray.regR12Curve ρ ε hε a ha s.1) := by
    intro T hT
    obtain ⟨v, hv⟩ := CKN.Leray.regUniformMollifiedInitial_global_bessel_path
      ρ ε hε a ha 2 T hT
    refine ⟨v, ?_⟩
    intro s
    simpa only [CKN.Leray.regR12Curve] using hv s
  have hR1 := CKN.Leray.regR12Velocity_R1 ρ ε hε a ha hpath
  exact CKN.isInJ_iff_weakDivFree.mpr (hR1.2.2.2 t ht)

/-- Every ordered spatial derivative of the actual regularized
momentum right-hand side is in `L²` on a positive-time slice
(`prop:lps-smoothing`). -/
theorem lps_regR12TimeRHS_all_word_memLp_actual
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (t : ℝ) (ht : 0 < t) (i : Fin 3)
    (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x : Vec3 =>
      CKN.Leray.regR12TimeRHS ρ ε hε
        (CKN.Leray.regR12Velocity ρ ε hε a ha)
        (CKN.Leray.forcedQuadPressure ρ ε hε
          (CKN.Leray.regR12Curve ρ ε hε a ha)) (x, t) i)) 2 volume := by
  exact lps_regR12TimeRHS_all_word_memLp ρ ε hε
    (CKN.Leray.regR12Velocity ρ ε hε a ha)
    (CKN.Leray.forcedQuadPressure ρ ε hε
      (CKN.Leray.regR12Curve ρ ε hε a ha)) t
    (lps_regR12Velocity_slice_isInJ ρ ε hε a ha t ht.le)
    (fun i => lps_regR12Velocity_slice_contDiff ρ ε hε a ha t ht.le i)
    (lps_regR12Pressure_slice_contDiff ρ ε hε a ha t ht)
    (fun i α => lps_regR12Velocity_all_word_memLp_slice
      ρ ε hε a ha t ht.le i α)
    (lps_regR12Pressure_all_word_memLp_slice ρ ε hε a ha t ht)
    i α

end ESS
