/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.CurveTrace
public import LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Extension-field sums and trace scaling

Connects Carlitz’s extension sums (1969) to the trace formulation used in Harcos
(2015), §3.
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open scoped BigOperators
open KloostermanWeil.Carlitz

/-- The two-coefficient Kloosterman sum over units of the chosen finite extension. -/
noncomputable def extensionKloostermanAB
    (p n : ℕ) [Fact p.Prime]
    (A B : GaloisField p n) : ℂ := by
  classical
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ u : (GaloisField p n)ˣ,
    psiExt p n
      (A * (u : GaloisField p n) + B * (u : GaloisField p n)⁻¹)

theorem scalarTraceSum_eq_extensionKloostermanAB
    (p n : ℕ) [Fact p.Prime]
    (c : GaloisField p n) (m : ZMod p) :
    extensionKloostermanScalarSum p n c m =
      extensionKloostermanAB p n
        (algebraMap (ZMod p) (GaloisField p n) m)
        (algebraMap (ZMod p) (GaloisField p n) m * c) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  unfold extensionKloostermanScalarSum extensionKloostermanAB
  apply Finset.sum_congr rfl
  intro u hu
  apply congrArg ZMod.stdAddChar
  change m • (Algebra.trace (ZMod p) (GaloisField p n))
      ((u : GaloisField p n) + c / (u : GaloisField p n)) = _
  rw [← LinearMap.map_smul]
  congr 1
  simp only [Algebra.smul_def]
  field_simp

theorem Kext_eq_extensionKloostermanAB_one
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    Kext p n t =
      extensionKloostermanAB p n
        1 (algebraMap (ZMod p) (GaloisField p n) t) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  unfold Kext extensionKloostermanAB
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun x : GaloisField p n =>
      if x = 0 then (0 : ℂ)
      else psiExt p n
        (x + algebraMap (ZMod p) (GaloisField p n) t * x⁻¹)) 0]
  simp only [ite_eq_left, zero_add]
  have hsub :
      (∑ x : {x : GaloisField p n // x ≠ 0},
        if x.1 = 0 then (0 : ℂ)
        else psiExt p n
          (x.1 + algebraMap (ZMod p) (GaloisField p n) t * x.1⁻¹)) =
      ∑ x : {x : GaloisField p n // x ≠ 0},
        psiExt p n
          (x.1 + algebraMap (ZMod p) (GaloisField p n) t * x.1⁻¹) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_right x.property]
  rw [hsub]
  refine Fintype.sum_equiv unitsEquivNeZero.symm
    (fun x : {x : GaloisField p n // x ≠ 0} =>
      psiExt p n
        (x.1 + algebraMap (ZMod p) (GaloisField p n) t * x.1⁻¹))
    (fun u : (GaloisField p n)ˣ =>
      psiExt p n
        (1 * (u : GaloisField p n) +
          algebraMap (ZMod p) (GaloisField p n) t *
            (u : GaloisField p n)⁻¹)) ?_
  intro x
  simp


theorem scale_arg
    {F : Type*} [Field F] (M C U : F) (hM : M ≠ 0) :
    M * U + (M * C) * U⁻¹ =
      M * U + (M ^ 2 * C) * (M * U)⁻¹ := by
  rw [mul_inv_rev]
  have htail :
      (M ^ 2 * C) * (U⁻¹ * M⁻¹) =
        (M * C) * U⁻¹ := by
    calc
      (M ^ 2 * C) * (U⁻¹ * M⁻¹) =
          (M * M⁻¹) * ((M * C) * U⁻¹) := by
            ring
      _ = (M * C) * U⁻¹ := by
        rw [mul_inv_cancel₀ hM, one_mul]
  rw [htail]

/-- The extension Kloosterman sum written over the whole field with zero omitted. -/
noncomputable def extensionKloostermanAB0
    (p n : ℕ) [Fact p.Prime]
    (A B : GaloisField p n) : ℂ := by
  classical
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ x : GaloisField p n,
    if x = 0 then 0
    else psiExt p n (A * x + B * x⁻¹)

theorem extensionKloostermanAB_eq_AB0
    (p n : ℕ) [Fact p.Prime]
    (A B : GaloisField p n) :
    extensionKloostermanAB p n A B =
      extensionKloostermanAB0 p n A B := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  unfold extensionKloostermanAB extensionKloostermanAB0
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun x : GaloisField p n =>
      if x = 0 then (0 : ℂ) else psiExt p n (A * x + B * x⁻¹)) 0]
  simp only [ite_eq_left, zero_add]
  have hsub :
      (∑ x : {x : GaloisField p n // x ≠ 0},
        if x.1 = 0 then (0 : ℂ)
        else psiExt p n (A * x.1 + B * x.1⁻¹)) =
      ∑ x : {x : GaloisField p n // x ≠ 0},
        psiExt p n (A * x.1 + B * x.1⁻¹) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_right x.property]
  rw [hsub]
  exact Fintype.sum_equiv unitsEquivNeZero
    (fun u : (GaloisField p n)ˣ =>
      psiExt p n
        (A * (u : GaloisField p n) + B * (u : GaloisField p n)⁻¹))
    (fun x : {x : GaloisField p n // x ≠ 0} =>
      psiExt p n (A * x.1 + B * x.1⁻¹))
    (fun _ => rfl)

theorem Kext_eq_AB0_one
    (p n : ℕ) [Fact p.Prime] (t : ZMod p) :
    Kext p n t =
      extensionKloostermanAB0 p n
        1 (algebraMap (ZMod p) (GaloisField p n) t) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  unfold Kext extensionKloostermanAB0
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h0 : x = 0
  · simp [h0]
  · simp [h0]

theorem extensionKloostermanAB0_scaling
    (p n : ℕ) [Fact p.Prime]
    (c m : ZMod p) (hm : m ≠ 0) :
    extensionKloostermanAB0 p n
        (algebraMap (ZMod p) (GaloisField p n) m)
        (algebraMap (ZMod p) (GaloisField p n) m *
          algebraMap (ZMod p) (GaloisField p n) c) =
      extensionKloostermanAB0 p n
        1 (algebraMap (ZMod p) (GaloisField p n) (m ^ 2 * c)) := by
  classical
  let := Fintype.ofFinite (GaloisField p n)
  let M0 : GaloisField p n :=
    algebraMap (ZMod p) (GaloisField p n) m
  have hM0 : M0 ≠ 0 := by
    intro hzero
    apply hm
    apply FaithfulSMul.algebraMap_injective (ZMod p) (GaloisField p n)
    simpa [M0] using hzero
  let M : (GaloisField p n)ˣ := Units.mk0 M0 hM0
  unfold extensionKloostermanAB0
  refine Fintype.sum_equiv (Units.mulLeft M)
    (fun x : GaloisField p n =>
      if x = 0 then (0 : ℂ)
      else psiExt p n
        (algebraMap (ZMod p) (GaloisField p n) m * x +
          (algebraMap (ZMod p) (GaloisField p n) m *
            algebraMap (ZMod p) (GaloisField p n) c) * x⁻¹))
    (fun y : GaloisField p n =>
      if y = 0 then (0 : ℂ)
      else psiExt p n
        (1 * y +
          algebraMap (ZMod p) (GaloisField p n) (m ^ 2 * c) * y⁻¹)) ?_
  intro x
  by_cases hx : x = 0
  · subst x
    simp [M, M0]
  · have hMx : M0 * x ≠ 0 := mul_ne_zero hM0 hx
    simp only [ite_eq_right hx]
    have hcoe : ((Units.mulLeft M) x : GaloisField p n) = M0 * x := by
      rfl
    rw [ite_eq_right (by simpa [hcoe] using hMx)]
    apply congrArg (psiExt p n)
    change
      M0 * x +
          (M0 * algebraMap (ZMod p) (GaloisField p n) c) * x⁻¹ =
        1 * (M0 * x) +
          algebraMap (ZMod p) (GaloisField p n) (m ^ 2 * c) *
            (M0 * x)⁻¹
    rw [one_mul, map_mul, map_pow]
    exact scale_arg M0
      (algebraMap (ZMod p) (GaloisField p n) c) x hM0

theorem extensionKloostermanAB_scaling
    (p n : ℕ) [Fact p.Prime]
    (c m : ZMod p) (hm : m ≠ 0) :
    extensionKloostermanAB p n
        (algebraMap (ZMod p) (GaloisField p n) m)
        (algebraMap (ZMod p) (GaloisField p n) m *
          algebraMap (ZMod p) (GaloisField p n) c) =
      Kext p n (m ^ 2 * c) := by
  rw [extensionKloostermanAB_eq_AB0]
  rw [Kext_eq_AB0_one]
  exact extensionKloostermanAB0_scaling p n c m hm

theorem scalarTraceSum_eq_Kext_sq
    (p n : ℕ) [Fact p.Prime]
    (c m : ZMod p) (hm : m ≠ 0) :
    extensionKloostermanScalarSum p n
        (algebraMap (ZMod p) (GaloisField p n) c) m =
      Kext p n (m ^ 2 * c) := by
  rw [scalarTraceSum_eq_extensionKloostermanAB]
  exact extensionKloostermanAB_scaling p n c m hm


end KloostermanWeil.Stepanov
