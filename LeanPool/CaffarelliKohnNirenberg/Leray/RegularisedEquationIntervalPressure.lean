/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedPressure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedGlobalR1

/-!
# Canonical pressure on a regularized mild interval

The interval pressure is the Riesz pressure of the same clamped velocity
path that occurs in its mild identity.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The spatial `L²` path represented by a coordinate field on a closed
regularized mild interval. Values outside the interval use its endpoint. -/
@[expose]
def regularisedIntervalMildCurve
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 ≤ T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    ℝ → RealVectorL2 := fun s =>
      let τ := regularizedMildTimeClamp T hT s
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, τ.1)) (hSlice τ.1 τ.2)

/-- The canonical Riesz pressure on a finite interval, built from its own
clamped velocity path. -/
@[expose]
def regularisedIntervalCanonicalPressure
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 ≤ T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    ParabolicPoint → ℝ :=
  forcedQuadPressure ρ ε hε (regularisedIntervalMildCurve u T hT hSlice)

/-- On each interval time slice, the canonical interval pressure is the
Riesz representative of the tensor from that same velocity slice. -/
theorem regularisedIntervalCanonicalPressure_slice
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 ≤ T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    (fun x : Vec3 => regularisedIntervalCanonicalPressure
      ρ ε hε u T hT hSlice (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num)
        (forcedPressureTensorLp (regularizedMildTensor ρ ε hε
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t))
            (hSlice t ht)))) := by
  have hclamp : regularizedMildTimeClamp T hT t = ⟨t, ht⟩ :=
    regularizedMildTimeClamp_eq_of_mem T hT ht
  simpa [regularisedIntervalCanonicalPressure, regularisedIntervalMildCurve,
    hclamp] using
    (forcedQuadPressure_slice ρ ε hε
      (regularisedIntervalMildCurve u T hT hSlice) t)

end CKN.Leray

end
