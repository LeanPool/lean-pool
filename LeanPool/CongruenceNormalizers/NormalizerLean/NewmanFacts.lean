/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanVal

/-!
# Newman's theorem, step 2 continued: the integer divisibilities

For g = κ·S ∈ Norm(Γ₀(N)), S = [[α, β/h], [hγ, δ]], e = αδ − βγ, with h = h(N), n = n(N),
ε = gcd(N, 24):

* F1  e ∣ h·αγ        F2  e ∣ α²          F3  eN ∣ h²γ²         F4  eε ∣ 2h·αγ
* F5  e ∣ nh·βδ       F6  e ∣ n·β²        F7  e ∣ δ²            F8  eε ∣ 2nh·βδ
* F9  e ∣ N·βγ        F10 eh ∣ N·αβ       F11 eN ∣ Nh·γδ        F12 eε ∣ 2N·βγ
* and, for [[x, y], [N, t]] ∈ Γ₀(N) and s = t − x, the same four with s in place of N.
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

theorem InL.entries {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) :
    ∃ a b c d : ℤ, M 0 0 = a ∧ M 0 1 = b ∧ M 1 0 = c ∧ M 1 1 = d ∧ (N : ℤ) ∣ c ∧
      (epsPart N : ℤ) ∣ d - a := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  exact ⟨a, b, c, d, by simp, by simp, by simp, by simp, hc, hd⟩

theorem int_eq_of_real {e X a : ℤ} (he : e ≠ 0) (h : ((e : ℝ))⁻¹ * (X : ℝ) = a) : X = e * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have : (X : ℝ) = e * a := by rw [← h]; field_simp
  exact_mod_cast this

theorem phi_InL {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ) {Y : SL(2, ℝ)}
    (hY : Y ∈ Gamma0R N) : InL N (Phi (hPart N) α β γ δ (Y : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← coe_conj_eq_Phi hg (hPart_pos N).ne']
  exact InL.of_mem ((Subgroup.mem_normalizer_iff.1 hgN Y).1 hY)

theorem InL.nsmul' {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) (m : ℕ) :
    InL N ((m : ℝ) • M) := by
  have := h.zsmul m
  simpa using this

/-- The four basic facts in `InL` form. -/
theorem InL_basic {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    InL N (Phi (hPart N) α β γ δ !![0, 1; 0, 0]) ∧
      InL N ((N : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 1, 0]) ∧
      InL N ((N : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 0, 1]) := by
  have hh : hPart N ≠ 0 := (hPart_pos N).ne'
  have h1 : InL N (Phi (hPart N) α β γ δ 1) := by rw [Phi_one hh he]; exact InL.one N
  have hT := phi_InL hgN hg (matT_mem N)
  have hU := phi_InL hgN hg (matU_mem N)
  have hTU := phi_InL hgN hg (mul_mem (matT_mem N) (matU_mem N))
  have eE12 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = (matT : Matrix (Fin 2) (Fin 2) ℝ) - 1
    := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matT]
  have eE21 : (N : ℝ) • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      (matU N : Matrix (Fin 2) (Fin 2) ℝ) - 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matU]
  have eE22 : (N : ℝ) • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (N : ℝ) • 1 - (((matT * matU N : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) -
        (matT : Matrix (Fin 2) (Fin 2) ℝ) - (matU N : Matrix (Fin 2) (Fin 2) ℝ) + 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [matT, matU]
  refine ⟨?_, ?_, ?_⟩
  · rw [eE12, Phi_sub]; exact hT.sub h1
  · rw [← Phi_smul, eE21, Phi_sub]; exact hU.sub h1
  · rw [← Phi_smul, eE22, Phi_sub, Phi_smul, Phi_add, Phi_sub, Phi_sub]
    exact (h1.nsmul' N).sub (((hTU.sub hT).sub hU).add h1)

/-- The γ_p fact in `InL` form. -/
theorem InL_s {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} (hdet : x * t - y * N = 1) :
    InL N (((t - x : ℤ) : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 0, 1]) ∧
      (epsPart N : ℤ) ∣ t - x := by
  have hh : hPart N ≠ 0 := (hPart_pos N).ne'
  let γp : SL(2, ℝ) := ⟨!![(x : ℝ), y; N, t], by
    rw [det_fin_two_of]
    have : ((x * t - y * N : ℤ) : ℝ) = 1 := by exact_mod_cast hdet
    push_cast at this
    linear_combination this⟩
  have hγp : γp ∈ Gamma0R N := mem_Gamma0R_of_entries x y N t (by simp [γp]) (dvd_refl _)
  have hε : (epsPart N : ℤ) ∣ t - x := by
    obtain ⟨a, b, c, d, hm, -, hd⟩ := InL.of_mem hγp
    have h00 := congrFun (congrFun hm 0) 0
    have h11 := congrFun (congrFun hm 1) 1
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, Int.cast_inj,
      cons_val_one, γp] at h00 h11
    have : x = a := by exact_mod_cast h00
    have : t = d := by exact_mod_cast h11
    subst_vars
    exact hd
  refine ⟨?_, hε⟩
  have h1 : InL N (Phi (hPart N) α β γ δ 1) := by rw [Phi_one hh he]; exact InL.one N
  have hP := phi_InL hgN hg hγp
  obtain ⟨hE12, hE21, -⟩ := InL_basic hgN hg he
  have eE : ((t - x : ℤ) : ℝ) • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (γp : Matrix (Fin 2) (Fin 2) ℝ) - (x : ℝ) • 1 - (y : ℝ) • !![0, 1; 0, 0] -
        (N : ℝ) • !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [γp]
  rw [← Phi_smul, eE, Phi_sub, Phi_sub, Phi_sub, Phi_smul, Phi_smul, Phi_smul]
  exact ((hP.sub (h1.zsmul x)).sub (hE12.zsmul y)).sub hE21

/-- The integer divisibilities F1–F12. -/
theorem int_facts {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    (α * δ - β * γ) ∣ (hPart N : ℤ) * (α * γ) ∧ (α * δ - β * γ) ∣ 1 * α ^ 2 ∧ (α * δ - β * γ) * N
      ∣ (hPart N : ℤ) ^ 2 * γ ^ 2 ∧ (α * δ - β * γ) * (epsPart N : ℤ) ∣ (2 * (hPart N : ℤ)) * (α *
      γ) ∧
    (α * δ - β * γ) ∣ ((nPart N : ℤ) * (hPart N : ℤ)) * (β * δ) ∧ (α * δ - β * γ) ∣ (nPart N : ℤ)
      * β ^ 2 ∧ (α * δ - β * γ) ∣ 1 * δ ^ 2 ∧ (α * δ - β * γ) * (epsPart N : ℤ) ∣ (2 * (nPart N :
      ℤ) * (hPart N : ℤ)) * (β * δ) ∧
    (α * δ - β * γ) ∣ (N : ℤ) * (β * γ) ∧ (α * δ - β * γ) * (hPart N : ℤ) ∣ (N : ℤ) * (α * β) ∧ (α
      * δ - β * γ) * N ∣ ((N : ℤ) * (hPart N : ℤ)) * (γ * δ) ∧
    (α * δ - β * γ) * (epsPart N : ℤ) ∣ (2 * (N : ℤ)) * (β * γ) := by
  have hh : hPart N ≠ 0 := (hPart_pos N).ne'
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hNr : (N : ℝ) = nPart N * (hPart N : ℝ) ^ 2 := by
    exact_mod_cast (hPart_sq_mul_nPart N (NeZero.ne N)).symm
  have hNz : (N : ℤ) = (nPart N : ℤ) * (hPart N : ℤ) ^ 2 := by exact_mod_cast (hPart_sq_mul_nPart
    N (NeZero.ne N)).symm
  have hN0 : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨P12, P21, P22⟩ := InL_basic hgN hg he
  -- E₁₂
  obtain ⟨a1, b1, c1, d1, h00, h01, h10, h11, hc1, hd1⟩ := P12.entries
  rw [Phi_E12] at h00 h01 h10 h11
  have r00 := int_eq_of_real (X := -(α * (hPart N : ℤ) * γ)) he (by rw [← h00]; simp)
  have r01 := int_eq_of_real (X := α ^ 2) he (by rw [← h01]; simp)
  have r10 := int_eq_of_real (X := -((hPart N : ℤ) ^ 2 * γ ^ 2)) he (by rw [← h10]; simp)
  have r11 := int_eq_of_real (X := α * (hPart N : ℤ) * γ) he (by rw [← h11]; simp)
  -- E₂₁ (times N)
  obtain ⟨a2, b2, c2, d2, i00, i01, i10, i11, hc2, hd2⟩ := P21.entries
  rw [Phi_E21 hh] at i00 i01 i10 i11
  have s00 := int_eq_of_real (X := (nPart N : ℤ) * (hPart N : ℤ) * (β * δ)) he
    (by rw [← i00]; simp [hNr]; field_simp)
  have s01 := int_eq_of_real (X := -((nPart N : ℤ) * β ^ 2)) he
    (by rw [← i01]; simp [hNr]; field_simp)
  have s10 := int_eq_of_real (X := (N : ℤ) * δ ^ 2) he (by rw [← i10]; simp; ring)
  have s11 := int_eq_of_real (X := -((nPart N : ℤ) * (hPart N : ℤ) * (β * δ))) he
    (by rw [← i11]; simp [hNr]; field_simp)
  -- E₂₂ (times N)
  obtain ⟨a3, b3, c3, d3, j00, j01, j10, j11, hc3, hd3⟩ := P22.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((N : ℤ) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real (X := (nPart N : ℤ) * (hPart N : ℤ) * (α * β)) he
    (by rw [← j01]; simp [hNr]; field_simp)
  have t10 := int_eq_of_real (X := -((N : ℤ) * (hPart N : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (N : ℤ) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c1', rfl⟩ := hc1
  obtain ⟨c2', rfl⟩ := hc2
  obtain ⟨c3', rfl⟩ := hc3
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  obtain ⟨k3, hk3⟩ := hd3
  have hε : (epsPart N : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.2 (epsPart_dvd N)
  obtain ⟨m, hm⟩ := hε
  have ha1 : a1 = -d1 := mul_left_cancel₀ he (by linear_combination -r00 - r11)
  have ha2 : d2 = -a2 := mul_left_cancel₀ he (by linear_combination -s11 - s00)
  have hd3' : d3 - a3 = N - 2 * a3 := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨d1, by linear_combination r11⟩, ⟨b1, by linear_combination r01⟩,
    ⟨-c1', by linear_combination -r10⟩,
    ⟨k1, by linear_combination 2 * r11 + (α * δ - β * γ) * hk1 + (α * δ - β * γ) * ha1⟩,
    ⟨a2, by linear_combination s00⟩, ⟨-b2, by linear_combination -s01⟩,
    ⟨c2', mul_left_cancel₀ hN0 (by linear_combination s10)⟩,
    ⟨-k2, by linear_combination 2 * s00 - (α * δ - β * γ) * hk2 + (α * δ - β * γ) * ha2⟩,
    ⟨-a3, by linear_combination -t00⟩, ⟨b3, by rw [hNz]; linear_combination (hPart N : ℤ) * t01⟩,
    ⟨-c3', by linear_combination -t10⟩, ?_⟩
  -- F12: ε ∣ N − 2 a3 and ε ∣ N give ε ∣ 2 a3
  have h2a : (epsPart N : ℤ) ∣ 2 * a3 := by
    have : (epsPart N : ℤ) ∣ (N : ℤ) - (d3 - a3) := dvd_sub ⟨m, hm⟩ ⟨k3, hk3⟩
    rw [hd3'] at this
    simpa using this
  obtain ⟨k4, hk4⟩ := h2a
  exact ⟨-k4, by linear_combination -2 * t00 - (α * δ - β * γ) * hk4⟩

theorem int_eq_of_real_div {e X a : ℤ} {d : ℕ} (he : e ≠ 0) (hd : d ≠ 0)
    (h : ((e : ℝ))⁻¹ * ((X : ℝ) / d) = a) : X = e * d * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have : (X : ℝ) = e * d * a := by rw [← h]; field_simp
  exact_mod_cast this

/-- The four facts with s = t − x in place of N. -/
theorem int_facts_s {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} (hdet : x * t - y * N = 1) :
    (α * δ - β * γ) ∣ (t - x) * (β * γ) ∧
      (α * δ - β * γ) * (hPart N : ℤ) ∣ (t - x) * (α * β) ∧
      (α * δ - β * γ) * N ∣ ((t - x) * (hPart N : ℤ)) * (γ * δ) ∧
      (α * δ - β * γ) * (epsPart N : ℤ) ∣ (2 * (t - x)) * (β * γ) := by
  have hh : hPart N ≠ 0 := (hPart_pos N).ne'
  obtain ⟨P, hε⟩ := InL_s hgN hg he hdet
  obtain ⟨a4, b4, c4, d4, j00, j01, j10, j11, hc4, hd4⟩ := P.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((t - x) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real_div (X := (t - x) * (α * β)) he hh
    (by rw [← j01]; simp; ring)
  have t10 := int_eq_of_real (X := -((t - x) * (hPart N : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (t - x) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c4', rfl⟩ := hc4
  obtain ⟨k4, hk4⟩ := hd4
  have hd4' : d4 - a4 = (t - x) - 2 * a4 := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨-a4, by linear_combination -t00⟩, ⟨b4, by linear_combination t01⟩,
    ⟨-c4', by linear_combination -t10⟩, ?_⟩
  have h2a : (epsPart N : ℤ) ∣ 2 * a4 := by
    have : (epsPart N : ℤ) ∣ (t - x) - (d4 - a4) := dvd_sub hε ⟨k4, hk4⟩
    rw [hd4'] at this
    simpa using this
  obtain ⟨k5, hk5⟩ := h2a
  exact ⟨-k5, by linear_combination -2 * t00 - (α * δ - β * γ) * hk5⟩

end

end CongruenceNormalizers
