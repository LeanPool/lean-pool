/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Transport.DiscreteConvolution

/-!
# High-contrast homogenization: Provider.Response.ProfileRowAlignedSum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The finite geometric row above the alignment scale

This is the scalar sum exchange behind
`e.bridge.boundary.sum`.  The response exponent is fixed at
`3/2`, while the terminal increment row may use any nonnegative exponent
strictly below it.
-/

namespace HCPolySupport.HighContrast.Response

noncomputable section

private theorem sum_row_comm {f : ℤ → ℤ → ℝ} {A R : Finset ℤ} {s : ℤ}
    (hsub : ∀ k ∈ A, Finset.Icc (k + 1) s ⊆ R) :
    ∑ k ∈ A, ∑ r ∈ Finset.Icc (k + 1) s, f k r =
      ∑ r ∈ R, ∑ k ∈ A.filter fun k ↦ r ∈ Finset.Icc (k + 1) s,
        f k r := by
  classical
  have hleft : ∀ k ∈ A,
      ∑ r ∈ Finset.Icc (k + 1) s, f k r =
        ∑ r ∈ R, if r ∈ Finset.Icc (k + 1) s then f k r else 0 := by
    intro k hk
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub k hk)]
  rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm

/-- The exchanged tail of the response row is bounded by the terminal
`rhoDr`-weighted increment row. -/
theorem profileRow_weighted_tail_le {rhoDr : ℝ}
    (hrho : rhoDr < 3 / 2) {jStar s : ℤ}
    (x : ℤ → ℝ)
    (hx : ∀ r ∈ Finset.Icc (jStar + 1) s, 0 ≤ x r) :
    ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
        ∑ r ∈ Finset.Icc (k + 1) s, x r ≤
      (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) *
        ∑ r ∈ Finset.Icc (jStar + 1) s,
          (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) * x r := by
  classical
  let A : Finset ℤ := Finset.Icc jStar s
  let R : Finset ℤ := Finset.Icc (jStar + 1) s
  have hsub : ∀ k ∈ A, Finset.Icc (k + 1) s ⊆ R := by
    intro k hk r hr
    rw [show A = Finset.Icc jStar s by rfl, Finset.mem_Icc] at hk
    rw [Finset.mem_Icc] at hr
    change r ∈ Finset.Icc (jStar + 1) s
    rw [Finset.mem_Icc]
    exact ⟨by omega, hr.2⟩
  have hswap :
      ∑ k ∈ A, profileRowWeight k s *
          ∑ r ∈ Finset.Icc (k + 1) s, x r =
        ∑ r ∈ R,
          (∑ k ∈ A.filter fun k ↦ r ∈ Finset.Icc (k + 1) s,
            profileRowWeight k s) * x r := by
    calc
      ∑ k ∈ A, profileRowWeight k s *
          ∑ r ∈ Finset.Icc (k + 1) s, x r =
        ∑ k ∈ A, ∑ r ∈ Finset.Icc (k + 1) s,
          profileRowWeight k s * x r := by
        exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      _ = ∑ r ∈ R,
          ∑ k ∈ A.filter fun k ↦ r ∈ Finset.Icc (k + 1) s,
            profileRowWeight k s * x r :=
        sum_row_comm hsub
      _ = ∑ r ∈ R,
          (∑ k ∈ A.filter fun k ↦ r ∈ Finset.Icc (k + 1) s,
            profileRowWeight k s) * x r := by
        exact Finset.sum_congr rfl fun r _ => by rw [Finset.sum_mul]
  change (∑ k ∈ A, profileRowWeight k s *
      ∑ r ∈ Finset.Icc (k + 1) s, x r) ≤ _
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hrange : jStar + 1 ≤ r ∧ r ≤ s := by
    simpa only [R, Finset.mem_Icc] using hr
  have hxr : 0 ≤ x r := hx r (by simpa only [R] using hr)
  let Ar : Finset ℤ := A.filter fun k ↦ r ∈ Finset.Icc (k + 1) s
  have hbelow : ∀ k ∈ Ar, k ≤ r - 1 := by
    intro k hk
    have hkr := (Finset.mem_filter.mp hk).2
    rw [Finset.mem_Icc] at hkr
    omega
  have hfactor : ∀ k ∈ Ar,
      profileRowWeight k s =
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ))) *
          (3 : ℝ) ^ (-(3 / 2) * (((r - 1 : ℤ) : ℝ) - (k : ℝ))) := by
    intro k _
    rw [profileRowWeight, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hgeom := Transport.sum_geom_below_le (c := (3 / 2 : ℝ))
    (by norm_num) (r - 1) Ar hbelow
  have hAr :
      ∑ k ∈ Ar, profileRowWeight k s ≤
        (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) *
          (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) := by
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    have hfac0 : 0 ≤
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hfirst := mul_le_mul_of_nonneg_left hgeom hfac0
    have hgap : (0 : ℝ) ≤ (s : ℝ) - (r : ℝ) := by
      exact_mod_cast sub_nonneg.mpr hrange.2
    have hprod : 0 ≤ (3 / 2 - rhoDr) * ((s : ℝ) - (r : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hrho.le) hgap
    have hexp :
        -(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ)) ≤
          -rhoDr * ((s : ℝ) - (r : ℝ)) := by
      push_cast
      nlinarith only [hprod]
    have hdecay :
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ))) ≤
          (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hratio : (3 : ℝ) ^ (-(3 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hden0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) :=
      div_nonneg zero_le_one (sub_nonneg.mpr hratio.le)
    calc
      (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ))) *
          (∑ k ∈ Ar,
            (3 : ℝ) ^ (-(3 / 2) * (((r - 1 : ℤ) : ℝ) - (k : ℝ)))) ≤
          (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - ((r - 1 : ℤ) : ℝ))) *
            (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) := hfirst
      _ ≤ (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) *
            (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) := by
        exact mul_le_mul_of_nonneg_right hdecay hden0
      _ = _ := by ring
  simpa only [Ar, mul_assoc] using mul_le_mul_of_nonneg_right hAr hxr

/-- The complete finite row of terminal means has coefficient
`(1 + D)/(1 - 3⁻³˲²)`. -/
theorem profileRow_weighted_one_add_tail_le {rhoDr : ℝ}
    (hrho : rhoDr < 3 / 2) {jStar s : ℤ}
    (x : ℤ → ℝ)
    (hx : ∀ r ∈ Finset.Icc (jStar + 1) s, 0 ≤ x r) :
    ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
        (1 + ∑ r ∈ Finset.Icc (k + 1) s, x r) ≤
      (1 + ∑ r ∈ Finset.Icc (jStar + 1) s,
          (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) * x r) /
        (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hmass := Transport.sum_geom_below_le (c := (3 / 2 : ℝ)) (by norm_num)
    s (Finset.Icc jStar s) (fun k hk => (Finset.mem_Icc.mp hk).2)
  have hweight : ∀ k ∈ Finset.Icc jStar s,
      profileRowWeight k s =
        (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (k : ℝ))) := by
    intro k _
    rw [profileRowWeight]
    congr 1
    ring
  have hmass' :
      ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s ≤
        1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [Finset.sum_congr rfl hweight]
    exact hmass
  have htail := profileRow_weighted_tail_le hrho x hx
  have hsplit :
      ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
          (1 + ∑ r ∈ Finset.Icc (k + 1) s, x r) =
        (∑ k ∈ Finset.Icc jStar s, profileRowWeight k s) +
          ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
            ∑ r ∈ Finset.Icc (k + 1) s, x r := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  calc
    (∑ k ∈ Finset.Icc jStar s, profileRowWeight k s) +
        ∑ k ∈ Finset.Icc jStar s, profileRowWeight k s *
          ∑ r ∈ Finset.Icc (k + 1) s, x r ≤
      1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) +
        (1 / (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ)))) *
          ∑ r ∈ Finset.Icc (jStar + 1) s,
            (3 : ℝ) ^ (-rhoDr * ((s : ℝ) - (r : ℝ))) * x r :=
      add_le_add hmass' htail
    _ = _ := by ring

end

end HCPolySupport.HighContrast.Response
