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


/-- Compare the forcing term through separate bracket and seminorm bounds.
The coefficient family and comparator are arbitrary. -/
theorem coarseGrainingForceTerm_le_of_seminorm_bounds (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) (r s : ℝ)
    (f : Vec d → Vec d) {b scale child parent : ℝ}
    (hb : 0 ≤ b) (hscale : 0 ≤ scale)
    (hbracket : coarseGrainingForceBracket Q a a0 r ≤ b)
    (hnonneg : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s f)
    (hbesov : Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s f ≤ scale * child)
    (hchild : child ≤ parent) :
    coarseGrainingForceTerm Q a a0 r s f ≤ b * (scale * parent) := by
  exact mul_le_mul hbracket
    (hbesov.trans (mul_le_mul_of_nonneg_left hchild hscale)) hnonneg hb

/-- The scale-one Besov weight on an origin cube. -/
theorem cubeBesovScaleWeight_one_originCube (n : ℤ) :
    cubeBesovScaleWeight (1 : ℝ) (originCube d n) = Real.rpow (3 : ℝ) (-(n : ℝ)) := by
  have h := cubeBesovScaleWeight_neg_originCube (d := d) n (-1)
  rw [neg_neg] at h
  rw [h]
  congr 1
  ring

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

/-- The two scalar energy legs, for any positive diffusivity and real forcing exponent. -/
theorem sqrt_scalar_anchor_energy_le (sig s t exponent X Y : ℝ)
    (hsig : 0 < sig) (hs : 0 < s) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (sig * Real.rpow (3 : ℝ) (-2 * t) * X ^ 2 +
      Real.rpow s exponent * sig⁻¹ * Real.rpow (3 : ℝ) (2 * s * t) * Y ^ 2) ≤
      Real.sqrt sig * Real.rpow (3 : ℝ) (-t) * X +
        Real.rpow s (exponent / 2) * Real.sqrt sig⁻¹ * Real.rpow (3 : ℝ) (s * t) * Y := by
  have hP0 : 0 ≤ Real.rpow (3 : ℝ) (-2 * t) := Real.rpow_nonneg (by norm_num) _
  have hS0 : 0 ≤ Real.rpow s exponent := Real.rpow_nonneg hs.le _
  have hQ0 : 0 ≤ Real.rpow (3 : ℝ) (2 * s * t) := Real.rpow_nonneg (by norm_num) _
  have hSInv0 : 0 ≤ Real.rpow s exponent * sig⁻¹ :=
    mul_nonneg hS0 (inv_nonneg.mpr hsig.le)
  have hP : Real.sqrt (Real.rpow (3 : ℝ) (-2 * t)) = Real.rpow (3 : ℝ) (-t) := by
    rw [show (-2 : ℝ) * t = 2 * (-t) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hS : Real.sqrt (Real.rpow s exponent) = Real.rpow s (exponent / 2) := by
    conv_lhs => rw [show exponent = 2 * (exponent / 2) by ring]
    exact sqrt_rpow_two_mul hs _
  have hQ : Real.sqrt (Real.rpow (3 : ℝ) (2 * s * t)) = Real.rpow (3 : ℝ) (s * t) := by
    rw [show (2 : ℝ) * s * t = 2 * (s * t) by ring]
    exact sqrt_rpow_two_mul (by norm_num) _
  have hA : Real.sqrt (sig * Real.rpow (3 : ℝ) (-2 * t) * X ^ 2) =
      Real.sqrt sig * Real.rpow (3 : ℝ) (-t) * X := by
    rw [Real.sqrt_mul (mul_nonneg hsig.le hP0) (X ^ 2), Real.sqrt_sq hX,
      Real.sqrt_mul hsig.le (Real.rpow (3 : ℝ) (-2 * t)), hP]
  have hB : Real.sqrt (Real.rpow s exponent * sig⁻¹ * Real.rpow (3 : ℝ) (2 * s * t) * Y ^ 2) =
      Real.rpow s (exponent / 2) * Real.sqrt sig⁻¹ * Real.rpow (3 : ℝ) (s * t) * Y := by
    rw [Real.sqrt_mul (mul_nonneg hSInv0 hQ0) (Y ^ 2), Real.sqrt_sq hY,
      Real.sqrt_mul hSInv0 (Real.rpow (3 : ℝ) (2 * s * t)),
      Real.sqrt_mul hS0 sig⁻¹, hS, hQ]
  exact (sqrt_add_le_sqrt_add_sqrt
    (mul_nonneg (mul_nonneg hsig.le hP0) (sq_nonneg X))
    (mul_nonneg (mul_nonneg hSInv0 hQ0) (sq_nonneg Y))).trans
      (le_of_eq (by rw [hA, hB]))

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
  simpa only [interiorAnchorEnergyRHSOn_def, show ((-11) : ℝ) / 2 = -(11 / 2 : ℝ) by norm_num] using
    sqrt_scalar_anchor_energy_le (Annealed.sigmaBar M (n + 2) : ℝ) s
      (((n + 2 : ℤ)) : ℝ) (-11)
      (eLpNorm (fun y => f y - volumeAverage W f) 2
        (Support.normalizedVolumeMeasureOn W)).toReal
      (Support.normalizedGagliardoESeminormOn W s g).toReal
      (Annealed.sigmaBar M (n + 2)).2 hs ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The comparator's half-norm, in the `Real.sqrt` spelling. -/
theorem constantCoeffMatrixNormHalf_scalarComparator_sqrt [NeZero d] {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Ch03.constantCoeffMatrixNormHalf (scalarComparator (d := d) hsigma) =
      Real.sqrt sigma := by
  rw [constantCoeffMatrixNormHalf_scalarComparator hsigma, rpow_half_eq_sqrt]


/-- Error and energy bounds control both coarse-graining comparison coefficients. -/
theorem coarseGraining_comparisonBounds [NeZero d]
    (Q : TriadicCube d) (a : Ch03.CoeffFamily d) {sig : ℝ} (hsig : 0 < sig)
    (r kappa Erep Eb e0 Cout P QS Qf X Y : ℝ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d)))
    (hkappa : 0 ≤ kappa) (hErep : 0 ≤ Erep) (hEb : 0 ≤ Eb) (hEbe0 : Eb ≤ e0)
    (herr : Ch03.coarseGrainingHomogenizationErrorAtDepth Q a
      (scalarComparator hsig) r 0 ≤ kappa * Erep)
    (hbracket : coarseGrainingForceBracket Q a (scalarComparator hsig) r ≤
      Real.sqrt (2 * (d : ℝ) * (Eb ^ 2 + 1)) * Eb + 2 * (2 * (d : ℝ) * (Eb ^ 2 + 1)))
    (hEnergy : Ch03.h1EnergyNormOnCube Q a u ≤
      Real.sqrt Cout * (Real.sqrt sig * P * X + QS * Real.sqrt sig⁻¹ * Qf * Y)) :
    let k0 := 2 * (d : ℝ) * (e0 ^ 2 + 1)
    coarseGrainingForceBracket Q a (scalarComparator hsig) r ≤
        Real.sqrt k0 * e0 + 2 * k0 ∧
      coarseGrainingEnergyTerm Q a (scalarComparator hsig) r u ≤
        kappa * Real.sqrt Cout * Erep * (sig * (P * X) + QS * (Qf * Y)) := by
  dsimp only
  have hKble : 2 * (d : ℝ) * (Eb ^ 2 + 1) ≤ 2 * (d : ℝ) * (e0 ^ 2 + 1) := by
    have hsq : Eb ^ 2 ≤ e0 ^ 2 := pow_le_pow_left₀ hEb hEbe0 2
    exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) (by positivity)
  refine ⟨hbracket.trans ?_, ?_⟩
  · exact add_le_add
      (mul_le_mul (Real.sqrt_le_sqrt hKble) hEbe0 hEb (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_left hKble (by norm_num))
  · rw [coarseGrainingEnergyTerm, constantCoeffMatrixNormHalf_scalarComparator_sqrt]
    have hstep := mul_le_mul
      (mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg sig)) hEnergy
      (h1EnergyNormOnCube_nonneg Q a u)
      (mul_nonneg (Real.sqrt_nonneg sig) (mul_nonneg hkappa hErep))
    refine hstep.trans (le_of_eq ?_)
    have hself : Real.sqrt sig * Real.sqrt sig = sig := Real.mul_self_sqrt hsig.le
    have hinv : Real.sqrt sig * Real.sqrt sig⁻¹ = 1 := sqrt_mul_sqrt_inv hsig
    calc
      Real.sqrt sig * (kappa * Erep) *
          (Real.sqrt Cout * (Real.sqrt sig * P * X + QS * Real.sqrt sig⁻¹ * Qf * Y)) =
        kappa * Real.sqrt Cout * Erep *
          ((Real.sqrt sig * Real.sqrt sig) * (P * X) +
            (Real.sqrt sig * Real.sqrt sig⁻¹) * (QS * (Qf * Y))) := by ring
      _ = kappa * Real.sqrt Cout * Erep * (sig * (P * X) + QS * (Qf * Y)) := by
        rw [hself, hinv, one_mul]

/-- The translated Besov estimate with its origin-cube scale weight evaluated. -/
theorem besovVectorSeminormTwo_originCube_translated_neg_le [NeZero d]
    {x : Vec d} (n : ℤ) {s : ℝ} {g : Vec d → Vec d} (hs : 0 < s) (hs1 : s ≤ 1)
    (hL2 : MemLp g 2
      (Support.normalizedVolumeMeasureOn ((fun y => x + y) '' openCubeSet (originCube d n))))
    (hW : MemLp (Gagliardo.gagliardoKernel s 2 g) 2
      (Support.normalizedGagliardoMeasureOn
        ((fun y => x + y) '' openCubeSet (originCube d n)))) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo (originCube d n) s
        (fun y => -g (y + x)) ≤
      besovGagliardoConstant d * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
        (Support.normalizedGagliardoESeminormOn
          ((fun y => x + y) '' openCubeSet (originCube d n)) s g).toReal := by
  have h := besovVectorSeminormTwo_translated_neg_le_gagliardo_window
    (originCube d n) hs hs1 hL2 hW
  rwa [cubeBesovScaleWeight_neg_originCube (d := d) n s] at h

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


/-- Nonnegativity of composed constants for supplied energy and window factors. -/
theorem comparison_constants_nonneg (d : ℕ) [NeZero d]
    (CE energyFactor windowFactor : ℝ)
    (hCE : 0 ≤ CE) (henergy : 0 ≤ energyFactor) (hwindow : 0 ≤ windowFactor) :
    let kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3
    let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ))
    let k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1)
    let b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0
    let cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d
    let A1 : ℝ := cg * 216 * (kappa * energyFactor)
    let A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * windowFactor))
    let A3 : ℝ := interiorCorrectionConst d * windowFactor
    0 ≤ kappa ∧ 0 ≤ b0 ∧ 0 ≤ cg ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 ∧
      0 ≤ 9 * (CE * (1 / 2 : ℝ)) * A1 ∧ 0 ≤ CE * (1 / 2 : ℝ) * A1 := by
  intro kappa e0 k0 b0 cg A1 A2 A3
  have hkappa : 0 ≤ kappa := by positivity
  have he0 : 0 ≤ e0 := mul_nonneg hkappa (by positivity)
  have hk0 : 0 ≤ k0 := by positivity
  have hb0 : 0 ≤ b0 := by positivity
  have hcg : 0 ≤ cg := by
    have h1 := negNormBaseConst_pos d
    have h2 := coarseGrainingP2Const_pos d
    positivity
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by
    have h1 := besovGagliardoConstant_nonneg d
    positivity
  have hA3 : 0 ≤ A3 := by
    have h1 := interiorCorrectionConst_pos d
    positivity
  have hCE2 : 0 ≤ 9 * (CE * (1 / 2 : ℝ)) * A1 := by positivity
  have hCE3 : 0 ≤ CE * (1 / 2 : ℝ) * A1 := by positivity
  exact ⟨hkappa, hb0, hcg, hA1, hA2, hA3, hCE2, hCE3⟩

/-- Positivity of the common constants in the two composed scale estimates. -/
theorem composed_constants_nonneg (d : ℕ) [NeZero d] (CE Cout : ℝ) (hCE : 0 ≤ CE) :
    let kappa : ℝ := Real.sqrt (192 * (d : ℝ)) * 3
    let e0 : ℝ := kappa * (CE * (1 / 2 : ℝ))
    let k0 : ℝ := 2 * (d : ℝ) * (e0 ^ 2 + 1)
    let b0 : ℝ := Real.sqrt k0 * e0 + 2 * k0
    let cg : ℝ := 3 * negNormBaseConst d * coarseGrainingP2Const d
    let A1 : ℝ := cg * 216 * (kappa * Real.sqrt Cout)
    let A2 : ℝ := cg * 1944 * (b0 * (besovGagliardoConstant d * gagliardoWindowConst d))
    let A3 : ℝ := interiorCorrectionConst d * gagliardoWindowConst d
    0 ≤ kappa ∧ 0 ≤ b0 ∧ 0 ≤ cg ∧ 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 := by
  obtain ⟨hkappa, hb0, hcg, hA1, hA2, hA3, -, -⟩ :=
    comparison_constants_nonneg d CE (Real.sqrt Cout) (gagliardoWindowConst d)
      hCE (Real.sqrt_nonneg _) (gagliardoWindowConst_pos d).le
  exact ⟨hkappa, hb0, hcg, hA1, hA2, hA3⟩

/-- Cancel a positive scalar and an inverse pair of frame weights. -/
theorem scalar_frame_cancel_le {sig P R lhs rhs : ℝ} (hsig : 0 < sig)
    (hR : 0 ≤ R) (hPR : P * R = 1) (h : sig * (P * lhs) ≤ rhs) :
    lhs ≤ (sig⁻¹ * R) * rhs := by
  have hcancel : (sig⁻¹ * R) * (sig * (P * lhs)) = lhs := by
    calc
      (sig⁻¹ * R) * (sig * (P * lhs)) = (sig⁻¹ * sig) * ((P * R) * lhs) := by ring
      _ = lhs := by rw [inv_mul_cancel₀ hsig.ne', hPR]; ring
  rw [← hcancel]
  exact mul_le_mul_of_nonneg_left h (mul_nonneg (inv_nonneg.mpr hsig.le) hR)

/-- Replace three comparison legs and collect their two nonnegative output quantities. -/
theorem three_leg_comparison_close
    {w cg a b c energy forcing child E F Y A1 B A2 A3 X Z lhs : ℝ}
    (hw : 0 ≤ w) (hcg : 0 ≤ cg) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (henergy : energy ≤ E) (hforcing : forcing ≤ F) (hchild : child ≤ Y)
    (hstep : lhs ≤ w * (cg * (a * energy + b * forcing) + c * child))
    (hfirst : w * (cg * (a * E)) ≤ A1 * X + B * Z)
    (hsecond : w * (cg * (b * F)) ≤ A2 * Z)
    (hthird : w * (c * Y) ≤ A3 * Z)
    (hA1 : 0 ≤ A1) (hB : 0 ≤ B) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hX : 0 ≤ X) (hZ : 0 ≤ Z) :
    lhs ≤ (A1 + B + A2 + A3 + 1) * (X + Z) := by
  have hmono := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left henergy ha)
        (mul_le_mul_of_nonneg_left hforcing hb)) hcg)
      (mul_le_mul_of_nonneg_left hchild hc)) hw
  have hC1 : A1 ≤ A1 + B + A2 + A3 + 1 := by linarith only [hB, hA2, hA3]
  have hC2 : B + A2 + A3 ≤ A1 + B + A2 + A3 + 1 := by linarith only [hA1]
  calc
    lhs ≤ w * (cg * (a * E + b * F) + c * Y) := hstep.trans hmono
    _ = w * (cg * (a * E)) + w * (cg * (b * F)) + w * (c * Y) := by ring
    _ ≤ (A1 * X + B * Z) + A2 * Z + A3 * Z :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = A1 * X + (B + A2 + A3) * Z := by ring
    _ ≤ (A1 + B + A2 + A3 + 1) * X + (A1 + B + A2 + A3 + 1) * Z :=
      add_le_add (mul_le_mul_of_nonneg_right hC1 hX) (mul_le_mul_of_nonneg_right hC2 hZ)
    _ = (A1 + B + A2 + A3 + 1) * (X + Z) := by ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
