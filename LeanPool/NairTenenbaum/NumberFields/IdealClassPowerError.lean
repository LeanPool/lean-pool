/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Geometry.NormConeLatticePowerError

/-! # Power-saving counts in an ideal class

The fundamental-cone lattice count counts principal ideals with a prescribed
ideal divisor, up to the finite torsion-unit multiplicity. Multiplication by
a representative of the inverse class converts this to each ideal class.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NairTenenbaum

open NumberField NumberField.mixedEmbedding fundamentalCone Module Ideal NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

/-- The power-saving exponent in the number-field ideal-counting estimate. -/
noncomputable def numberFieldCountingExponent : ℝ :=
  (Module.finrank ℚ K - 1 : ℕ) / (Module.finrank ℚ K : ℝ)

theorem numberFieldCountingExponent_nonneg : 0 ≤ numberFieldCountingExponent K := by
  unfold numberFieldCountingExponent
  positivity

theorem numberFieldCountingExponent_lt_one : numberFieldCountingExponent K < 1 := by
  unfold numberFieldCountingExponent
  apply (div_lt_one (Nat.cast_pos.mpr Module.finrank_pos)).mpr
  exact_mod_cast Nat.sub_one_lt Module.finrank_pos.ne'

/-- The count of principal divisor ideals below the norm cutoff. -/
noncomputable def principalDivisorIdealCount (J : (Ideal (𝓞 K))⁰) (x : ℝ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧
    absNorm (I : Ideal (𝓞 K)) ≤ x}

/-- The count of ideals in a fixed class below the norm cutoff. -/
noncomputable def idealClassNormCount (C : ClassGroup (𝓞 K)) (x : ℝ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ x ∧ ClassGroup.mk0 I = C}

theorem idealSet_normCount_eq_lattice (J : (Ideal (𝓞 K))⁰) (x : ℝ) :
    Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ x} =
      Nat.card {a : mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J) //
        (a : mixedSpace K) ∈ fundamentalCone K ∧ mixedEmbedding.norm (a : mixedSpace K) ≤ x} := by
  apply Nat.card_congr
  exact
    { toFun := fun a => ⟨⟨a.1.1, a.1.2.2⟩, a.1.2.1, a.2⟩
      invFun := fun a => ⟨⟨a.1.1, a.2.1, a.1.2⟩, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem exists_idealSet_normCount_power_error (J : (Ideal (𝓞 K))⁰) :
    ∃ V C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ x} : ℝ) - V * x| ≤
        C * x ^ numberFieldCountingExponent K := by
  classical
  let L := mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J)
  let : Module.Free ℤ L := ZLattice.module_free ℝ L
  obtain ⟨V, C, hC, HC⟩ := exists_normCone_lattice_power_error K (Module.Free.chooseBasis ℤ L)
  refine ⟨V, C, hC, fun x hx => ?_⟩
  rw [idealSet_normCount_eq_lattice]
  exact HC x hx

theorem exists_principalDivisorIdealCount_power_error (J : (Ideal (𝓞 K))⁰) :
    ∃ V C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(principalDivisorIdealCount K J x : ℝ) - V * x| ≤ C * x ^ numberFieldCountingExponent K := by
  obtain ⟨V, C, hC, HC⟩ := exists_idealSet_normCount_power_error K J
  have hw : (0 : ℝ) < torsionOrder K := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (torsionOrder_ne_zero
      K))
  refine ⟨V / torsionOrder K, C / torsionOrder K, div_nonneg hC hw.le, fun x hx => ?_⟩
  have H := HC x hx
  rw [← card_isPrincipal_dvd_norm_le, Nat.cast_mul] at H
  change |(principalDivisorIdealCount K J x : ℝ) * torsionOrder K - V * x| ≤ _ at H
  have HE : (principalDivisorIdealCount K J x : ℝ) - V / torsionOrder K * x =
      ((principalDivisorIdealCount K J x : ℝ) * torsionOrder K - V * x) / torsionOrder K := by
    field_simp
  rw [HE, abs_div, abs_of_pos hw]
  convert div_le_div_of_nonneg_right H hw.le using 1; ring

theorem idealClassNormCount_eq_principalDivisor {C : ClassGroup (𝓞 K)}
    {J : (Ideal (𝓞 K))⁰} (hJ : ClassGroup.mk0 J = C⁻¹) (x : ℝ) :
    idealClassNormCount K C x = principalDivisorIdealCount K J (x * absNorm (J : Ideal (𝓞 K))) := by
  unfold idealClassNormCount principalDivisorIdealCount
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  apply Nat.card_congr
  refine ((Equiv.dvd J).subtypeEquiv fun I => ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm x, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ => (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors
      J))).symm

theorem exists_idealClassNormCount_power_error (A : ClassGroup (𝓞 K)) :
    ∃ V C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(idealClassNormCount K A x : ℝ) - V * x| ≤ C * x ^ numberFieldCountingExponent K := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective A⁻¹
  obtain ⟨V, C, hC, HC⟩ := exists_principalDivisorIdealCount_power_error K J
  let q : ℝ := absNorm (J : Ideal (𝓞 K))
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (show 1 ≤ absNorm (J : Ideal (𝓞 K)) from absNorm_pos_of_nonZeroDivisors J)
  refine ⟨V * q, C * q ^ numberFieldCountingExponent K, by positivity, fun x hx => ?_⟩
  have hxq : 1 ≤ x * q := hx.trans (le_mul_of_one_le_right (by linarith) hq)
  have H := HC (x * q) hxq
  rw [← idealClassNormCount_eq_principalDivisor K hJ,
    Real.mul_rpow (by linarith : 0 ≤ x) (by linarith : 0 ≤ q)] at H
  rw [show V * (x * q) = V * q * x by ring] at H
  convert H using 1
  ring

end NairTenenbaum
