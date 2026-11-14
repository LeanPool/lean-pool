/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TopologicalDiskExponentialLift

-- [TABLET NODE: P4590T1RotationalDiskCenter]

/-!
# P4590T1RotationalDiskCenter

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4590T1RotationalDiskCenter (S : Set (Real × Real)) (hS : TopologicalDisk S)
    (c : Real × Real)
    (hR : ∀ p ∈ S, (c.1 - (p.2 - c.2), c.2 + (p.1 - c.1)) ∈ S) :
    c ∈ S := by
-- BODY
  classical
  by_contra hc
  obtain ⟨F, hF, hExp⟩ := TopologicalDiskExponentialLift S hS c hc
  obtain ⟨e⟩ := hS
  let D : Set (Real × Real) := Metric.closedBall 0 1
  let : ContractibleSpace D := Metric.contractibleSpace_closedBall (by norm_num)
  let : ContractibleSpace S := e.symm.contractibleSpace
  let R : S → S := fun p => ⟨(c.1 - (p.1.2 - c.2), c.2 + (p.1.1 - c.1)),
    hR p p.2⟩
  have hRc : Continuous R := by dsimp [R]; fun_prop
  let a : ℂ := (Real.pi / 2 : Real) * Complex.I
  let H : S → ℂ := fun p => F (R p) - F p - a
  have hHc : Continuous H := (hF.comp hRc).sub hF |>.sub continuous_const
  have hexpa : Complex.exp a = Complex.I := by
    simp [a, Complex.exp_mul_I]
  have hDelta (p : S) : Complex.exp (F (R p) - F p) = Complex.exp a := by
    rw [Complex.exp_sub, hExp, hExp, hexpa]
    have hn : (⟨p.1.1 - c.1, p.1.2 - c.2⟩ : ℂ) ≠ 0 := by
      rw [← hExp p]
      exact Complex.exp_ne_zero _
    apply (div_eq_iff hn).mpr
    apply Complex.ext <;> dsimp [R] <;> simp
  have hmem (p : S) : H p ∈ AddSubgroup.zmultiples
      (2 * (Real.pi : ℂ) * Complex.I) := by
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hDelta p)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    simp only [H, hn, zsmul_eq_mul]
    ring
  let G : S → AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I) :=
    fun p => ⟨H p, hmem p⟩
  have hGc : Continuous G := hHc.subtype_mk _
  have heq (p q : S) : H p = H q :=
    congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous G hGc p q)
  let p : S := e ⟨0, by norm_num [Metric.mem_closedBall]⟩
  have hR4 : R (R (R (R p))) = p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp [R] <;> ring
  have h0 := heq (R p) p
  have h1 := heq (R (R p)) p
  have h2 := heq (R (R (R p))) p
  dsimp only [H] at h0 h1 h2
  rw [hR4] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hDelta p)
  have hz : (1 : Int) + 4 * n = 0 := by
    have h0i := congrArg Complex.im h0
    have h1i := congrArg Complex.im h1
    have h2i := congrArg Complex.im h2
    have hni := congrArg Complex.im hn
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.sub_im, Complex.mul_im,
        Complex.div_ofNat_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.div_ofNat_im,
        Complex.ofReal_im, zero_div, Complex.I_re, mul_zero, add_zero, sub_left_inj,
        Complex.add_im, Complex.intCast_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, sub_zero, zero_mul, Complex.intCast_im, sub_self, a]
        at h0i h1i h2i hni
    have hreal : (1 : Real) + 4 * (n : Real) = 0 := by
      nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  omega

end ApollonianSuperharmonic

end
