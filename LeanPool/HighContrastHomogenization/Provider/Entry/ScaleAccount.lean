/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SelectionObjects

/-!
# High-contrast homogenization: Provider.Entry.ScaleAccount

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The burn and scale account of the entry argument

The proof of `t.polynomial.entry` closes by turning the
selector's additive estimate `m_ent ≤ j_† + (C_sel + C_gap) Λ_Π`
into the printed ceiling `m_ent ≤ ⌈C(d,g) log_3(2 + Π K_{Ψ_S})⌉` and its
exponential form `3^{m_ent} ≤ 3(2 + Π K_{Ψ_S})^{C(d,g)}`.  Three accounts feed
that step.

*The coupled burn.*  `e.global.selection.lower.scale` is the
larger of the source burn `j_S` of `e.source.lower.scale` and the ceiling
that makes the pair a coupled window; with `d/(4d+3) ≤ 1` and
`16(d+1)^2/(4d+3) ≤ 8(d+1)` the second is below `C_exec Λ_Π + 2 + 8(d+1) log_3 K_bar_S`.

*The source burn.*  Its three entries are the dimensional floor `k_0(d)`, the
ceiling of `2 log_3 K_bar_S`, and the ceiling of
`2 + 4(d+1) log_3 K_bar_S + log_3 𝔐_Q(K_bar_S)`.  The moment multiplier of the source
gauge satisfies `log_3 𝔐_Q(K_bar) ≤ C_mom(d,g)(1 + log_3 K_bar)`, because `1 + T ≤ 2T`
on `T ≥ 1` and `log(1 + log K_bar) ≤ log K_bar`; hence `j_S ≤ C_burn log_3 K_bar_S`.

*The gauge comparison.*  Since `K_{Ψ_S} > 1` one has `K_bar_S ≤ 2K_{Ψ_S}` and
`Λ_Π ≤ Λ_S := log_3(2 + Π K_{Ψ_S})`, while `Λ_S ≥ 1`; therefore
`log_3 K_bar_S ≤ log_3 2 + Λ_S ≤ (1 + log_3 2)Λ_S`, and every additive constant of
the account is itself below its own multiple of `Λ_S`.  The exponential form is
then immediate from `3^{Λ_S} = 2 + Π K_{Ψ_S}`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Entry

noncomputable section

/-! ## The moment multiplier and the source burn -/

/-- **The moment multiplier is logarithmically tame.**  Its base-three
logarithm grows at most affinely in `log_3 K_bar`, with a slope and an intercept
that depend only on the exponent. -/
private theorem logb_momentMultiplier_le {Q Kbar : ℝ} (hQ : 1 ≤ Q) (hK : 2 ≤ Kbar) :
    Real.logb 3 (momentMultiplier Q Kbar) ≤
      (Real.log 2 + Real.log (2 * Q)) / Real.log 3 +
        (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * Real.logb 3 Kbar := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hK1 : (1 : ℝ) < Kbar := by linarith only [hK]
  have hK0 : (0 : ℝ) < Kbar := by linarith only [hK]
  have hlogK : 0 < Real.log Kbar := Real.log_pos hK1
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hn0 : (0 : ℤ) ≤ ⌈Q * (Q + 1) / 2⌉ :=
    Int.ceil_nonneg (div_nonneg (mul_nonneg hQ0.le (by linarith only [hQ0])) (by norm_num))
  have hzp : (0 : ℝ) < Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) := zpow_pos hK0 _
  have hKn : (1 : ℝ) ≤ Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) :=
    one_le_zpow₀ hK1.le hn0
  have h2Q : (2 : ℝ) ≤ 2 * Q := by linarith only [hQ]
  have hlogpos : (0 : ℝ) < 1 + Real.log Kbar := by linarith only [hlogK]
  have hprod : (0 : ℝ) < 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) :=
    mul_pos (by linarith only [h2Q]) hzp
  have hprod1 : (1 : ℝ) ≤ 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) := by
    have h := mul_le_mul_of_nonneg_left hKn (by linarith only [h2Q] : (0 : ℝ) ≤ 2 * Q)
    linarith only [h, h2Q]
  have hT1 : (1 : ℝ) ≤ 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar) := by
    have h := mul_le_mul_of_nonneg_left (by linarith only [hlogK] : (1 : ℝ) ≤ 1 + Real.log Kbar)
      (by linarith only [hprod1] : (0 : ℝ) ≤ 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ))
    linarith only [h, hprod1]
  -- the logarithm of the base of the moment multiplier
  have hlogT : Real.log (2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)) =
      Real.log (2 * Q) + ((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) * Real.log Kbar +
        Real.log (1 + Real.log Kbar) := by
    rw [Real.log_mul (ne_of_gt hprod) (ne_of_gt hlogpos),
      Real.log_mul (ne_of_gt (by linarith only [h2Q] : (0 : ℝ) < 2 * Q)) (ne_of_gt hzp),
      Real.log_zpow]
  have hlog1 : Real.log (1 + Real.log Kbar) ≤ Real.log Kbar := by
    have h := Real.log_le_sub_one_of_pos hlogpos
    linarith only [h]
  have hlogS : Real.log (1 + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)) ≤
      Real.log 2 + Real.log (2 * Q) +
        (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * Real.log Kbar := by
    have hmono := Real.log_le_log (by linarith only [hT1] :
        (0 : ℝ) < 1 + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar))
      (by linarith only [hT1] :
        (1 : ℝ) + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar) ≤
          2 * (2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)))
    rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hT1] :
      (0 : ℝ) < 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar))), hlogT] at hmono
    linarith only [hmono, hlog1]
  -- the moment multiplier itself
  have hbase : (0 : ℝ) < 1 + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar) := by
    linarith only [hT1]
  have hmm : Real.log (momentMultiplier Q Kbar) =
      Q⁻¹ * Real.log (1 + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)) := by
    rw [momentMultiplier, Real.log_rpow hbase]
  have hQi : Q⁻¹ ≤ 1 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hQ
  have hlogS0 : (0 : ℝ) ≤
      Real.log (1 + 2 * Q * Kbar ^ (⌈Q * (Q + 1) / 2⌉ : ℤ) * (1 + Real.log Kbar)) :=
    Real.log_nonneg (by linarith only [hT1])
  have hstep : Real.log (momentMultiplier Q Kbar) ≤
      Real.log 2 + Real.log (2 * Q) +
        (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * Real.log Kbar := by
    rw [hmm]
    have h := mul_le_mul_of_nonneg_right hQi hlogS0
    linarith only [h, hlogS]
  calc Real.logb 3 (momentMultiplier Q Kbar)
      = Real.log (momentMultiplier Q Kbar) / Real.log 3 := by rw [Real.logb]
    _ ≤ (Real.log 2 + Real.log (2 * Q) +
          (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * Real.log Kbar) / Real.log 3 := by
        gcongr
    _ = (Real.log 2 + Real.log (2 * Q)) / Real.log 3 +
          (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * (Real.log Kbar / Real.log 3) := by ring
    _ = (Real.log 2 + Real.log (2 * Q)) / Real.log 3 +
          (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1) * Real.logb 3 Kbar := by rw [Real.logb]

/-- **The source burn is affine in `log_3 K_bar`.**  Each of the three entries of
`e.source.lower.scale` is, and the intercept and the slope depend only on
the dimension and the moment exponent. -/
private theorem exists_sourceBurn_bound (d : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ A Bc : ℝ, 0 ≤ A ∧ 0 ≤ Bc ∧ ∀ K : ℝ,
      ((sourceBurn d Q K : ℤ) : ℝ) ≤ A + Bc * Real.logb 3 (growthBar K) := by
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ (kZero d : ℝ) := Nat.cast_nonneg _
  have hA0 : (0 : ℝ) ≤ (Real.log 2 + Real.log (2 * Q)) / Real.log 3 :=
    div_nonneg (by
      have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h2 : (0 : ℝ) ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith only [hQ])
      linarith only [h1, h2]) h3.le
  have hn0 : (0 : ℝ) ≤ ((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) := by
    have h : (0 : ℤ) ≤ ⌈Q * (Q + 1) / 2⌉ :=
      Int.ceil_nonneg (div_nonneg (mul_nonneg hQ0.le (by linarith only [hQ0])) (by norm_num))
    exact_mod_cast h
  refine ⟨(kZero d : ℝ) + 4 + (Real.log 2 + Real.log (2 * Q)) / Real.log 3,
    2 + 4 * ((d : ℝ) + 1) + (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1),
    by linarith only [hk0, hA0], by linarith only [hd0, hn0], fun K => ?_⟩
  have hK2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hL0 : (0 : ℝ) ≤ Real.logb 3 (growthBar K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK2])
  have hslack : (0 : ℝ) ≤
      (4 * ((d : ℝ) + 1) + (((⌈Q * (Q + 1) / 2⌉ : ℤ) : ℝ) + 1)) * Real.logb 3 (growthBar K) :=
    mul_nonneg (by linarith only [hd0, hn0]) hL0
  have hmom := logb_momentMultiplier_le hQ hK2
  rw [sourceBurn, Int.cast_max, Int.cast_max]
  refine max_le ?_ (max_le ?_ ?_)
  · push_cast
    linarith only [hA0, hslack, hL0]
  · have hc := (Int.ceil_lt_add_one (2 * Real.logb 3 (growthBar K))).le
    linarith only [hc, hA0, hslack, hk0]
  · have hc := (Int.ceil_lt_add_one (2 + 4 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) +
      Real.logb 3 (momentMultiplier Q (growthBar K)))).le
    linarith only [hc, hmom, hk0, hL0]

/-! ## The coupled execution burn -/

/-- **The coupled execution burn is below the printed additive account.**  The
second entry of `e.global.selection.lower.scale` loses only
`d/(4d+3) ≤ 1` and `16(d+1)^2/(4d+3) ≤ 8(d+1)` against the ceiling it rounds. -/
private theorem coupledExecBurn_le (d : ℕ) {Q K Cexec Lam A Bc : ℝ}
    (hCexec : 0 ≤ Cexec) (hLam : 0 ≤ Lam) (hA0 : 0 ≤ A) (hBc0 : 0 ≤ Bc)
    (hburn : ((sourceBurn d Q K : ℤ) : ℝ) ≤ A + Bc * Real.logb 3 (growthBar K)) :
    ((coupledExecBurn d Q K Cexec Lam : ℤ) : ℝ) ≤
      A + Bc * Real.logb 3 (growthBar K) +
        (Cexec * Lam + 2 + 8 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K)) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hK2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hL0 : (0 : ℝ) ≤ Real.logb 3 (growthBar K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK2])
  have hceil0 : (0 : ℝ) ≤ ((⌈Cexec * Lam⌉ : ℤ) : ℝ) := by
    have h : (0 : ℤ) ≤ ⌈Cexec * Lam⌉ := Int.ceil_nonneg (mul_nonneg hCexec hLam)
    exact_mod_cast h
  have hceil1 : ((⌈Cexec * Lam⌉ : ℤ) : ℝ) ≤ Cexec * Lam + 1 := (Int.ceil_lt_add_one _).le
  have hden : (0 : ℝ) < 4 * (d : ℝ) + 3 := by linarith only [hd0]
  have hX : ((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) / (4 * (d : ℝ) + 3) ≤
      ((⌈Cexec * Lam⌉ : ℤ) : ℝ) + 8 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) := by
    rw [div_le_iff₀ hden]
    have e1 : (((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          8 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K)) * (4 * (d : ℝ) + 3) -
        ((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) =
        ((⌈Cexec * Lam⌉ : ℤ) : ℝ) * (3 * (d : ℝ) + 3) +
          Real.logb 3 (growthBar K) * (8 * ((d : ℝ) + 1) * (2 * (d : ℝ) + 1)) := by ring
    have e2 : (0 : ℝ) ≤ ((⌈Cexec * Lam⌉ : ℤ) : ℝ) * (3 * (d : ℝ) + 3) :=
      mul_nonneg hceil0 (by linarith only [hd0])
    have e3 : (0 : ℝ) ≤
        Real.logb 3 (growthBar K) * (8 * ((d : ℝ) + 1) * (2 * (d : ℝ) + 1)) :=
      mul_nonneg hL0 (by positivity)
    linarith only [e1, e2, e3]
  have hslack : (0 : ℝ) ≤ Cexec * Lam + 2 + 8 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) :=
    by
      have h1 : (0 : ℝ) ≤ Cexec * Lam := mul_nonneg hCexec hLam
      have h2 : (0 : ℝ) ≤ 8 * ((d : ℝ) + 1) * Real.logb 3 (growthBar K) :=
        mul_nonneg (by linarith only [hd0]) hL0
      linarith only [h1, h2]
  have hAB : (0 : ℝ) ≤ A + Bc * Real.logb 3 (growthBar K) :=
    add_nonneg hA0 (mul_nonneg hBc0 hL0)
  rw [coupledExecBurn, Int.cast_max]
  refine max_le (by linarith only [hburn, hslack]) ?_
  have hc := (Int.ceil_lt_add_one (((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
    16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) / (4 * (d : ℝ) + 3))).le
  linarith only [hc, hX, hceil1, hAB]

/-! ## The account in abstract form -/

/-- The additive account of the entry generation, with the three logarithmic
quantities abstracted: the whole chain is a single linear combination once the
comparison `Λ_Π ≤ Λ_S`, the growth comparison `log_3 K_bar ≤ θ Λ_S` and `Λ_S ≥ 1`
are available. -/
private theorem ment_le_mul_of_bounds {d : ℕ} {A Bc th Cexec Csel Cgap LK LP LS jd mt : ℝ}
    (hA0 : 0 ≤ A) (hBc0 : 0 ≤ Bc) (hLS1 : 1 ≤ LS) (hLPS : LP ≤ LS)
    (hLKth : LK ≤ th * LS) (hCexec : 0 ≤ Cexec) (hCsel : 0 ≤ Csel) (hCgap : 0 ≤ Cgap)
    (hjd : jd ≤ A + Bc * LK + (Cexec * LP + 2 + 8 * ((d : ℝ) + 1) * LK))
    (hmt : mt ≤ jd + (Csel + Cgap) * LP) :
    mt ≤ (A + (Bc + 8 * ((d : ℝ) + 1)) * th + Cexec + 2 + Csel + Cgap) * LS := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have s1 : A ≤ A * LS := by
    have h := mul_le_mul_of_nonneg_left hLS1 hA0
    linarith only [h]
  have s2 : (Bc + 8 * ((d : ℝ) + 1)) * LK ≤ (Bc + 8 * ((d : ℝ) + 1)) * (th * LS) :=
    mul_le_mul_of_nonneg_left hLKth (by linarith only [hBc0, hd0])
  have s3 : Cexec * LP ≤ Cexec * LS := mul_le_mul_of_nonneg_left hLPS hCexec
  have s4 : (2 : ℝ) ≤ 2 * LS := by linarith only [hLS1]
  have s5 : (Csel + Cgap) * LP ≤ (Csel + Cgap) * LS :=
    mul_le_mul_of_nonneg_left hLPS (by linarith only [hCsel, hCgap])
  linarith only [hjd, hmt, s1, s2, s3, s4, s5]

/-- The two printed readings of the entry generation, from the single additive
bound: the ceiling form and the polynomial form, the latter through
`3^{log_3 b} = b`. -/
theorem exists_ceil_and_pow {C b : ℝ} (hb : 0 < b) {ment : ℤ} (hment0 : 0 ≤ ment)
    (hfin : (ment : ℝ) ≤ C * Real.logb 3 b) :
    ∃ mEnt : ℕ, (mEnt : ℤ) = ment ∧
      (mEnt : ℤ) ≤ ⌈C * Real.logb 3 b⌉ ∧ (3 : ℝ) ^ (mEnt : ℕ) ≤ 3 * b ^ C := by
  refine ⟨ment.toNat, Int.toNat_of_nonneg hment0, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hment0]
    exact_mod_cast le_trans hfin (Int.le_ceil (C * Real.logb 3 b))
  · have hcast : ((ment.toNat : ℕ) : ℝ) = (ment : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hment0
    have h2 : (3 : ℝ) ^ ((ment : ℝ)) ≤ (3 : ℝ) ^ (C * Real.logb 3 b) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 3)).mpr hfin
    have h3 : (3 : ℝ) ^ (C * Real.logb 3 b) = b ^ C := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_logb (by norm_num) (by norm_num) hb]
    have h4 : (0 : ℝ) < b ^ C := Real.rpow_pos_of_pos hb _
    rw [← Real.rpow_natCast 3 ment.toNat, hcast]
    linarith only [h2, h3, h4]

/-! ## The scale account of the entry argument -/

end

end Entry
end HighContrast
end HCPolySupport
