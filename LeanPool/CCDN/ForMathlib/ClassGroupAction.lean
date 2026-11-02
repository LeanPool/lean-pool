/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-! Compatibility of class-group automorphism actions with integral-ideal representatives. -/

public section

open scoped nonZeroDivisors

namespace CCDN

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]

/-- Fractional-ideal transport agrees with the map of integral ideals. -/
lemma fractionalIdeal_ringEquiv_coeIdeal (K L : Type*) [CommRing K] [CommRing L]
    [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
    (g : A ≃+* B) (I : Ideal A) :
    FractionalIdeal.ringEquivOfRingEquiv K L g (I : FractionalIdeal A⁰ K) =
      ((I.map g : Ideal B) : FractionalIdeal B⁰ L) := by
  let : RingHomInvPair (g : A →+* B) g.symm := RingHomInvPair.of_ringEquiv g
  let : RingHomInvPair (g.symm : B →+* A) g := RingHomInvPair.of_ringEquiv g.symm
  ext y
  change y ∈ Submodule.map (IsFractionRing.semilinearEquivOfRingEquiv K L g).toLinearMap
    (I : FractionalIdeal A⁰ K).val ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal A⁰).mp hx
    apply (FractionalIdeal.mem_coeIdeal B⁰).mpr
    refine ⟨g a, Ideal.mem_map_of_mem g ha, ?_⟩
    exact (IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L g a).symm
  · intro hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal B⁰).mp hy
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_of_equiv g a).mp ha
    refine ⟨algebraMap A K b, FractionalIdeal.mem_coeIdeal_of_mem A⁰ hb, ?_⟩
    exact IsFractionRing.semilinearEquivOfRingEquiv_algebraMap K L g b

/-- The class-group action carries an integral ideal to its mapped ideal class. -/
lemma classGroup_mulEquiv_mk0 {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDedekindDomain S]
    (g : R ≃+* S) (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv g (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map g,
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective g.injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  apply (ClassGroup.equiv (FractionRing S)).injective
  simp only [ClassGroup.mulEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ClassGroup.equiv_mk0]
  change (QuotientGroup.mk' (toPrincipalIdeal S (FractionRing S)).range)
      ((Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv
        (FractionRing R) (FractionRing S) g).toMulEquiv) (FractionalIdeal.mk0 (FractionRing R) I)) =
    (QuotientGroup.mk' (toPrincipalIdeal S (FractionRing S)).range) _
  apply congrArg (QuotientGroup.mk' (toPrincipalIdeal S (FractionRing S)).range)
  apply Units.ext
  exact fractionalIdeal_ringEquiv_coeIdeal (FractionRing R) (FractionRing S) g I

/-- An involutive ring automorphism acts involutively on the class group. -/
lemma classGroup_mulEquiv_involutive {R : Type*} [CommRing R] [IsDomain R]
    (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (ClassGroup.mulEquiv σ) := by
  have hσσ : σ.trans σ = RingEquiv.refl R := by ext x; exact hσ x
  let F := FractionalIdeal.ringEquivOfRingEquiv (FractionRing R) (FractionRing R) σ
  have hF : Function.Involutive F := by
    intro I
    dsimp only [F]
    rw [← FractionalIdeal.ringEquivOfRingEquiv_trans_apply, hσσ,
      FractionalIdeal.ringEquivOfRingEquiv_refl]
    rfl
  let G := (FractionalIdeal R⁰ (FractionRing R))ˣ
  let N := (toPrincipalIdeal R (FractionRing R)).range
  let φ : G ≃* G := Units.mapEquiv F.toMulEquiv
  have hN : N.map φ.toMonoidHom = N :=
    FractionalIdeal.map_ringEquivOfRingEquiv_toPrincipalIdeal σ
  let q := QuotientGroup.congr N N φ hN
  let e := ClassGroup.equiv (R := R) (FractionRing R)
  have hc (c : ClassGroup R) : e (ClassGroup.mulEquiv σ c) = q (e c) := by
    change e (e.symm (q (e c))) = _
    exact e.apply_symm_apply _
  intro c
  apply e.injective
  rw [hc, hc]
  refine QuotientGroup.induction_on (e c) ?_
  intro I
  change (QuotientGroup.mk' N) (φ (φ I)) = (QuotientGroup.mk' N) I
  apply congrArg (QuotientGroup.mk' N)
  apply Units.ext
  exact hF I

end CCDN
