/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEllipticity
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorEnergyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorWindowMove
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorClause

/-!
# InteriorComposedArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Arithmetic for the interior-clause composition

Square roots, `3`-powers and `s`-powers only.  Nothing here has analytic
content: every statement is an identity or an elementary inequality between
explicit real expressions, isolated from the composition so that the assembly
itself stays readable.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.Book MeasureTheory

noncomputable section

variable {d : ℕ}


/-- A frame comparison separates the normalized energy and forcing legs. -/
theorem scalar_frame_main_le
    (A cap E sig R P QS Qf Q1 S4 T factor X Y : ℝ)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hcap : E ≤ cap) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hQS : 0 ≤ QS) (hQf : 0 ≤ Qf) (hR : 0 ≤ R)
    (hS4 : 0 ≤ S4) (hinv : 0 ≤ sig⁻¹) (hcancel : sig⁻¹ * sig = 1)
    (hRP : R * P ≤ 1) (hforce : R * Qf ≤ factor * Q1) (hproduct : S4 * QS = T) :
    A * (sig⁻¹ * R * S4 * E * (sig * (P * X) + QS * (Qf * Y))) ≤
      A * (S4 * E * X) + (factor * cap * A) * (T * sig⁻¹ * Q1 * Y) := by
  have hfirst : (R * P) * X ≤ X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hRP hX
  have hforceScaled : (R * Qf) * (QS * Y) ≤ (factor * Q1) * (QS * Y) :=
    mul_le_mul_of_nonneg_right hforce (mul_nonneg hQS hY)
  have hsecond : E * (sig⁻¹ * ((R * Qf) * (QS * Y))) ≤
      cap * (sig⁻¹ * ((factor * Q1) * (QS * Y))) :=
    mul_le_mul hcap (mul_le_mul_of_nonneg_left hforceScaled hinv)
      (mul_nonneg hinv (mul_nonneg (mul_nonneg hR hQf) (mul_nonneg hQS hY)))
      (hE.trans hcap)
  calc
    A * (sig⁻¹ * R * S4 * E * (sig * (P * X) + QS * (Qf * Y))) =
        A * (S4 * (E * ((sig⁻¹ * sig) * ((R * P) * X)))) +
          A * (S4 * (E * (sig⁻¹ * ((R * Qf) * (QS * Y))))) := by ring
    _ = A * (S4 * (E * ((R * P) * X))) +
        A * (S4 * (E * (sig⁻¹ * ((R * Qf) * (QS * Y))))) := by rw [hcancel]; ring
    _ ≤ A * (S4 * (E * X)) +
        A * (S4 * (cap * (sig⁻¹ * ((factor * Q1) * (QS * Y))))) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfirst hE) hS4) hA)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsecond hS4) hA)
    _ = A * (S4 * E * X) + (factor * cap * A) * (T * sig⁻¹ * Q1 * Y) := by
      rw [← hproduct]
      ring

/-- A dominated decay factor controls a frame-normalized forcing term. -/
theorem scalar_frame_decay_le
    (A sig R Q Q1 decay T Y : ℝ) (hA : 0 ≤ A) (hinv : 0 ≤ sig⁻¹)
    (hQ1 : 0 ≤ Q1) (hY : 0 ≤ Y) (hdecay : decay ≤ T) (hframe : R * Q = Q1) :
    A * (sig⁻¹ * R * decay * Q * Y) ≤ A * (T * sig⁻¹ * Q1 * Y) := by
  calc
    A * (sig⁻¹ * R * decay * Q * Y) =
        A * (decay * (sig⁻¹ * ((R * Q) * Y))) := by ring
    _ = A * (decay * (sig⁻¹ * (Q1 * Y))) := by rw [hframe]
    _ ≤ A * (T * (sig⁻¹ * (Q1 * Y))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdecay (mul_nonneg hinv (mul_nonneg hQ1 hY))) hA
    _ = A * (T * sig⁻¹ * Q1 * Y) := by ring

/-- Product and domination identities assemble the three scalar comparison legs,
independently of the exponents used to obtain those identities. -/
theorem scalar_frame_three_term_bounds
    (A1 A2 A3 cap E sig R P QS Qf Qshift Q1 S4 T sixth half factor X Y : ℝ)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hE : 0 ≤ E) (hcap : E ≤ cap)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hQS : 0 ≤ QS) (hQf : 0 ≤ Qf) (hQ1 : 0 ≤ Q1)
    (hR : 0 ≤ R) (hS4 : 0 ≤ S4) (hT : 0 ≤ T) (hinv : 0 ≤ sig⁻¹)
    (hcancel : sig⁻¹ * sig = 1) (hRP : R * P ≤ 1)
    (hforce : R * Qf ≤ factor * Q1) (hframe : R * Qshift = Q1)
    (hproduct : S4 * QS = T) (hsixth : sixth ≤ T) (hhalf : half ≤ T)
    (hfactor : 0 ≤ factor) :
    A1 * (sig⁻¹ * R * S4 * E * (sig * (P * X) + QS * (Qf * Y))) ≤
        A1 * (S4 * E * X) + (factor * cap * A1) * (T * sig⁻¹ * Q1 * Y) ∧
      A2 * (sig⁻¹ * R * sixth * Qshift * Y) ≤ A2 * (T * sig⁻¹ * Q1 * Y) ∧
      A3 * (sig⁻¹ * R * half * Qshift * Y) ≤ A3 * (T * sig⁻¹ * Q1 * Y) ∧
      0 ≤ S4 * E * X ∧ 0 ≤ T * sig⁻¹ * Q1 * Y ∧ 0 ≤ factor * cap * A1 := by
  refine ⟨scalar_frame_main_le A1 cap E sig R P QS Qf Q1 S4 T factor X Y
      hA1 hE hcap hX hY hQS hQf hR hS4 hinv hcancel hRP hforce hproduct,
    scalar_frame_decay_le A2 sig R Qshift Q1 sixth T Y hA2 hinv hQ1 hY hsixth hframe,
    scalar_frame_decay_le A3 sig R Qshift Q1 half T Y hA3 hinv hQ1 hY hhalf hframe,
    mul_nonneg (mul_nonneg hS4 hE) hX,
    mul_nonneg (mul_nonneg (mul_nonneg hT hinv) hQ1) hY,
    mul_nonneg (mul_nonneg hfactor (hE.trans hcap)) hA1⟩

/-! ## 1. Square roots of powers -/

/-- `√(b^{2y}) = b^y` for a positive base. -/
theorem sqrt_rpow_two_mul {b : ℝ} (hb : 0 < b) (y : ℝ) :
    Real.sqrt (Real.rpow b (2 * y)) = Real.rpow b y := by
  change Real.sqrt (b ^ (2 * y)) = b ^ y
  have hsq : b ^ (2 * y) = (b ^ y) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (b ^ y) 2, ← Real.rpow_mul hb.le]
    congr 1
    push_cast
    ring
  rw [hsq, Real.sqrt_sq (Real.rpow_nonneg hb.le y)]

/-- Subadditivity of the square root. -/
theorem sqrt_add_le_sqrt_add_sqrt {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B := by
  have hsum : A + B ≤ (Real.sqrt A + Real.sqrt B) ^ (2 : ℕ) := by
    have hAB : Real.sqrt A * Real.sqrt B ≥ 0 :=
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)
    have hexp : (Real.sqrt A + Real.sqrt B) ^ (2 : ℕ) =
        Real.sqrt A ^ (2 : ℕ) + 2 * (Real.sqrt A * Real.sqrt B) +
          Real.sqrt B ^ (2 : ℕ) := by ring
    rw [hexp, Real.sq_sqrt hA, Real.sq_sqrt hB]
    linarith only [hAB]
  refine le_trans (Real.sqrt_le_sqrt hsum) (le_of_eq ?_)
  exact Real.sqrt_sq (by positivity)

/-- `√a · √(a⁻¹) = 1` for `a > 0`. -/
theorem sqrt_mul_sqrt_inv {a : ℝ} (ha : 0 < a) :
    Real.sqrt a * Real.sqrt a⁻¹ = 1 := by
  rw [← Real.sqrt_mul ha.le, mul_inv_cancel₀ ha.ne', Real.sqrt_one]

/-- **The two legs of the interior-Caccioppoli right-hand side.**

```text
  ( σ 3^{-2(n+2)} X² + s^{-11} σ^{-1} 3^{2s(n+2)} Y² )^{1/2}
      ≤ σ^{1/2} 3^{-(n+2)} X  +  s^{-11/2} σ^{-1/2} 3^{s(n+2)} Y .
``` -/
theorem sqrt_interiorAnchorEnergyRHSOn_le (M : ABKModel d) (n : ℤ) {s : ℝ}
    (hs : 0 < s) (W : Set (Vec d)) (f : Vec d → ℝ) (g : Vec d → Vec d) :
    Real.sqrt (interiorAnchorEnergyRHSOn M n s W f g) ≤
      Real.sqrt (Annealed.sigmaBar M (n + 2) : ℝ) *
          Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) *
          (eLpNorm (fun y => f y - volumeAverage W f) 2
            (Support.normalizedVolumeMeasureOn W)).toReal +
        Real.rpow s (-(11 / 2 : ℝ)) *
          Real.sqrt ((Annealed.sigmaBar M (n + 2) : ℝ))⁻¹ *
          Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) *
          (Support.normalizedGagliardoESeminormOn W s g).toReal := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M (n + 2) : ℝ) := (Annealed.sigmaBar M (n + 2)).2
  set X : ℝ := (eLpNorm (fun y => f y - volumeAverage W f) 2
    (Support.normalizedVolumeMeasureOn W)).toReal with hXdef
  set Y : ℝ := (Support.normalizedGagliardoESeminormOn W s g).toReal with hYdef
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hY : 0 ≤ Y := ENNReal.toReal_nonneg
  set P3 : ℝ := Real.rpow (3 : ℝ) (-2 * (((n + 2 : ℤ)) : ℝ)) with hP3def
  set Q3 : ℝ := Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) with hQ3def
  set PS : ℝ := Real.rpow s (-11 : ℝ) with hPSdef
  set QS : ℝ := Real.rpow s (-(11 / 2 : ℝ)) with hQSdef
  set P3s : ℝ := Real.rpow (3 : ℝ) (2 * s * (((n + 2 : ℤ)) : ℝ)) with hP3sdef
  set Q3s : ℝ := Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) with hQ3sdef
  set SIG : ℝ := (Annealed.sigmaBar M (n + 2) : ℝ) with hSIGdef
  have hP3nn : (0 : ℝ) ≤ P3 := Real.rpow_nonneg (by norm_num) _
  have hPSnn : (0 : ℝ) ≤ PS := Real.rpow_nonneg hs.le _
  have hP3snn : (0 : ℝ) ≤ P3s := Real.rpow_nonneg (by norm_num) _
  have hP3sqrt : Real.sqrt P3 = Q3 := by
    rw [hP3def, hQ3def, show (-2 : ℝ) * (((n + 2 : ℤ)) : ℝ) = 2 * (-(((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hPSsqrt : Real.sqrt PS = QS := by
    rw [hPSdef, hQSdef, show (-11 : ℝ) = 2 * (-(11 / 2 : ℝ)) by norm_num]
    exact sqrt_rpow_two_mul hs _
  have hP3ssqrt : Real.sqrt P3s = Q3s := by
    rw [hP3sdef, hQ3sdef,
      show (2 : ℝ) * s * (((n + 2 : ℤ)) : ℝ) = 2 * (s * (((n + 2 : ℤ)) : ℝ)) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hAnn : (0 : ℝ) ≤ SIG * P3 * X ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hsig.le hP3nn) (pow_nonneg hX 2)
  have hBnn : (0 : ℝ) ≤ PS * SIG⁻¹ * P3s * Y ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hPSnn (inv_nonneg.mpr hsig.le)) hP3snn)
      (pow_nonneg hY 2)
  have hA : Real.sqrt (SIG * P3 * X ^ (2 : ℕ)) = Real.sqrt SIG * Q3 * X := by
    rw [Real.sqrt_mul (mul_nonneg hsig.le hP3nn) (X ^ (2 : ℕ)), Real.sqrt_sq hX,
      Real.sqrt_mul hsig.le P3, hP3sqrt]
  have hB : Real.sqrt (PS * SIG⁻¹ * P3s * Y ^ (2 : ℕ)) =
      QS * Real.sqrt SIG⁻¹ * Q3s * Y := by
    have h1 : (0 : ℝ) ≤ PS * SIG⁻¹ := mul_nonneg hPSnn (inv_nonneg.mpr hsig.le)
    rw [Real.sqrt_mul (mul_nonneg h1 hP3snn) (Y ^ (2 : ℕ)), Real.sqrt_sq hY,
      Real.sqrt_mul h1 P3s, Real.sqrt_mul hPSnn SIG⁻¹, hPSsqrt, hP3ssqrt]
  rw [interiorAnchorEnergyRHSOn_def]
  exact le_trans (sqrt_add_le_sqrt_add_sqrt hAnn hBnn)
    (le_of_eq (by rw [hA, hB]))

/-- The comparator's half-norm, in the `Real.sqrt` spelling. -/
theorem constantCoeffMatrixNormHalf_scalarComparator_sqrt [NeZero d] {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsigma) =
      Real.sqrt sigma := by
  rw [constantCoeffMatrixNormHalf_scalarComparator hsigma, rpow_half_eq_sqrt]

/-! ## 3. The `3`-powers of the frame division -/

/-- Dividing by the left-hand weight `3^{-n}` is multiplying by `3^{n}`. -/
theorem rpow_three_neg_mul_self (n : ℤ) :
    Real.rpow (3 : ℝ) (-(n : ℝ)) * Real.rpow (3 : ℝ) ((n : ℝ)) = 1 := by
  change (3 : ℝ) ^ (-(n : ℝ)) * (3 : ℝ) ^ ((n : ℝ)) = 1
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  norm_num

/-- The `L²` leg's scale weights: `3^{n} · 3^{-(n+2)} ≤ 1`. -/
theorem rpow_three_frame_l2_le_one (n : ℤ) :
    Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (-(((n + 2 : ℤ)) : ℝ)) ≤ 1 := by
  change (3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ (-(((n + 2 : ℤ)) : ℝ)) ≤ 1
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hexp : (n : ℝ) + -(((n + 2 : ℤ)) : ℝ) = -2 := by push_cast; ring
  rw [hexp]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)

/-- The forcing leg's scale weights: `3^{n} · 3^{s(n+2)} ≤ 9 · 3^{(1+s)n}`. -/
theorem rpow_three_frame_force_le (n : ℤ) {s : ℝ} (hs1 : s ≤ 1) :
    Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) ≤
      9 * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
  have hsplit : Real.rpow (3 : ℝ) ((n : ℝ)) * Real.rpow (3 : ℝ) (s * (((n + 2 : ℤ)) : ℝ)) =
      Real.rpow (3 : ℝ) (2 * s) * Real.rpow (3 : ℝ) ((1 + s) * (n : ℝ)) := by
    change (3 : ℝ) ^ ((n : ℝ)) * (3 : ℝ) ^ (s * (((n + 2 : ℤ)) : ℝ)) =
      (3 : ℝ) ^ (2 * s) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hnine : Real.rpow (3 : ℝ) (2 * s) ≤ 9 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith only [hs1] : 2 * s ≤ (2 : ℝ))
    have h9 : (3 : ℝ) ^ (2 : ℝ) = 9 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [h9] at h
    exact h
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hnine (Real.rpow_nonneg (by norm_num) _)

/-! ## 4. The `s`-powers of the composition -/

/-- `(s⁻¹)^k = s^{-k}` for positive `s` and a natural exponent. -/
theorem inv_pow_eq_rpow_neg {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (s⁻¹) ^ k = Real.rpow s (-(k : ℝ)) := by
  change _ = s ^ (-(k : ℝ))
  rw [Real.rpow_neg hs.le, Real.rpow_natCast, inv_pow]

/-- The two `s`-powers of the composition add: `s^{-4} · s^{-11/2} = s^{-19/2}`. -/
theorem rpow_s_four_mul_eleven_halves {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) * Real.rpow s (-(11 / 2 : ℝ)) = Real.rpow s (-(19 / 2 : ℝ)) := by
  change s ^ (-(4 : ℝ)) * s ^ (-(11 / 2 : ℝ)) = s ^ (-(19 / 2 : ℝ))
  rw [← Real.rpow_add hs]
  congr 1
  ring

/-- On `(0,1]` every `s`-power above `−19/2` is dominated by `s^{-19/2}`. -/
theorem rpow_le_rpow_neg_nineteen_halves {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : -(19 / 2 : ℝ) ≤ a) : Real.rpow s a ≤ Real.rpow s (-(19 / 2 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 ha

end

end Algsuperdiff.Section4.Provider.ExcessDecay
