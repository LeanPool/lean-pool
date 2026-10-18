/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanVal
public import LeanPool.CongruenceNormalizers.NormalizerDelta.Defs

/-!
# Newman's argument for subgroups of Γ₀(N)

`NewmanData` records the lattice, unipotent and valuation hypotheses used in the argument.
The proof applies both to Γ₀(N), instantiated in `NormalizerLean/NewmanFacts`, and to ΓΔ(N).
Its integer divisibilities, local conclusion and final matrix form are proved once here.
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

theorem int_eq_of_real {e X a : ℤ} (he : e ≠ 0) (h : ((e : ℝ))⁻¹ * (X : ℝ) = a) : X = e * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have : (X : ℝ) = e * a := by rw [← h]; field_simp
  exact_mod_cast this

theorem int_eq_of_real_div {e X a : ℤ} {d : ℕ} (he : e ≠ 0) (hd : d ≠ 0)
    (h : ((e : ℝ))⁻¹ * ((X : ℝ) / d) = a) : X = e * d * a := by
  have her : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have : (X : ℝ) = e * d * a := by rw [← h]; field_simp
  exact_mod_cast this

theorem dvd_of_forall_vz_le {m x : ℤ} (hm : m ≠ 0) (hx : x ≠ 0)
    (h : ∀ p : ℕ, p.Prime → vz p m ≤ vz p x) : m ∣ x := by
  rw [← Int.natAbs_dvd_natAbs]
  rw [← Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hm) (Int.natAbs_ne_zero.2 hx)]
  intro p
  by_cases hp : p.Prime
  · exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem vz_int_natCast (p n : ℕ) : vz p (n : ℤ) = n.factorization p := vz_natCast p n

/-- n = N / η². -/
def nOf (N η : ℕ) : ℕ := N / η ^ 2

/-- The hypotheses of Newman's argument for Γ ≤ Γ₀(N), with lattice parameter ε and output η. -/
structure NewmanData (N : ℕ) (Γ : Subgroup SL(2, ℝ)) (ε η : ℕ) : Prop where
  le : Γ ≤ Gamma0R N
  T_mem : matT ∈ Γ
  U_mem : matU N ∈ Γ
  inL : ∀ Y ∈ Γ, InLe N ε (Y : Matrix (Fin 2) (Fin 2) ℝ)
  eps_dvd : ε ∣ N
  h_pos : 0 < η
  h_sq_dvd : η ^ 2 ∣ N
  h_fact : ∀ p, η.factorization p = min (ε.factorization p) (N.factorization p / 2)
  gamma : ∀ p : ℕ, p.Prime → p ∣ N → ε.factorization p < N.factorization p →
    ∃ x y t : ℤ, x * t - y * N = 1 ∧
      (∃ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℝ) = !![(x : ℝ), y; N, t]) ∧
      t - x ≠ 0 ∧ vz p (t - x) = ε.factorization p

variable {Γ : Subgroup SL(2, ℝ)} {ε η : ℕ}

theorem NewmanData.n_mul_sq {N : ℕ} (D : NewmanData N Γ ε η) : nOf N η * η ^ 2 = N :=
  Nat.div_mul_cancel D.h_sq_dvd

theorem NewmanData.factorization_n {N : ℕ} (D : NewmanData N Γ ε η) (hN : N ≠ 0) (p : ℕ) :
    (nOf N η).factorization p + 2 * η.factorization p = N.factorization p := by
  have h := D.n_mul_sq
  have hn : nOf N η ≠ 0 := by rintro h0; rw [h0, zero_mul] at h; exact hN h.symm
  have := congrArg (fun m => m.factorization p) h
  rw [Nat.factorization_mul hn (by have := D.h_pos; positivity), Nat.factorization_pow] at this
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
  omega

/-- The local matrix shape from primitivity and the necessary valuation bounds. -/
theorem local_form_gen (ν j k δ₀ a b c d : ℕ)
    (hk : k = min j (ν / 2))
    (prim : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0)
    (u1 : min (a + d) (b + c) ≤ δ₀)
    (C2 : δ₀ ≤ 2 * a) (C3 : δ₀ + ν ≤ 2 * k + 2 * c)
    (C6 : δ₀ + 2 * k ≤ ν + 2 * b) (C7 : δ₀ ≤ 2 * d)
    (C10 : δ₀ + k ≤ j + a + b) (C11 : δ₀ + ν ≤ j + k + c + d) :
    (δ₀ = 0 ∧ ν - 2 * k ≤ c) ∨
      (δ₀ = ν - 2 * k ∧ ν - 2 * k ≤ a ∧ ν - 2 * k ≤ c ∧ ν - 2 * k ≤ d) := by
  omega

/-- The products of entries that are integers. -/
theorem products_intG {N : ℕ} {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hg : g ∈ NormG Γ) {x y z w
  : ℝ}
    (hx : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = x) (hy : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = y)
    (hz : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = z) (hw : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = w) :
    IsIntR (x * x) ∧ IsIntR (x * z) ∧ IsIntR (z * z) ∧ IsIntR (N * (y * y)) ∧
      IsIntR (N * (w * w)) ∧ IsIntR (N * (y * w)) ∧ IsIntR (N * (x * w)) ∧
      IsIntR (N * (x * y)) ∧ IsIntR (N * (z * w)) ∧ IsIntR (N * (y * z))  := by
  exact integral_products_of_normalizer D.le D.T_mem D.U_mem hg hx hy hz hw

/-- **Step 1** ([Nw §2]): g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ without a common prime
factor. -/
theorem exists_prim_formG {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hg : g ∈
  NormG Γ) :
    ∃ (κ : ℝ) (α β γ δ : ℤ), κ ≠ 0 ∧
      (∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ)) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        κ • !![(α : ℝ), (β : ℝ) / η; (η : ℝ) * γ, (δ : ℝ)]  := by
  exact primitive_form_of_normalizer D.le D.T_mem D.U_mem η D.h_pos hg

theorem InLe.entries {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InLe N ε M) :
    ∃ a b c d : ℤ, M 0 0 = a ∧ M 0 1 = b ∧ M 1 0 = c ∧ M 1 1 = d ∧ (N : ℤ) ∣ c ∧
      (ε : ℤ) ∣ d - a := by
  obtain ⟨a, b, c, d, rfl, hc, hd⟩ := h
  exact ⟨a, b, c, d, by simp, by simp, by simp, by simp, hc, hd⟩


theorem phi_InLe {N : ℕ} {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈ NormG Γ) {κ
  : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ) {Y : SL(2, ℝ)}
    (hY : Y ∈ Γ) : InLe N ε (Phi (η) α β γ δ (Y : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← coe_conj_eq_Phi hg D.h_pos.ne']
  exact D.inL _ ((Subgroup.mem_normalizer_iff.1 hgN Y).1 hY)

theorem InLe.nsmul' {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InLe N ε M) (m : ℕ) :
    InLe N ε ((m : ℝ) • M) := by
  have := h.zsmul m
  simpa using this

/-- The four basic facts in `InLe` form. -/
theorem InLe_basic {N : ℕ} {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈ NormG Γ)
  {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    InLe N ε (Phi (η) α β γ δ !![0, 1; 0, 0]) ∧
      InLe N ε ((N : ℝ) • Phi (η) α β γ δ !![0, 0; 1, 0]) ∧
      InLe N ε ((N : ℝ) • Phi (η) α β γ δ !![0, 0; 0, 1]) := by
  have hh : η ≠ 0 := D.h_pos.ne'
  have h1 : InLe N ε (Phi (η) α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hT := phi_InLe D hgN hg D.T_mem
  have hU := phi_InLe D hgN hg D.U_mem
  have hTU := phi_InLe D hgN hg (mul_mem D.T_mem D.U_mem)
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

/-- The γ_p fact in `InLe` form, for γ_p = [[x, y], [N, t]] ∈ Γ. -/
theorem InLe_s {N : ℕ} {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈ NormG Γ)
    {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} {γp : SL(2, ℝ)} (hγp : γp ∈ Γ)
    (hγm : (γp : Matrix (Fin 2) (Fin 2) ℝ) = !![(x : ℝ), y; N, t]) :
    InLe N ε (((t - x : ℤ) : ℝ) • Phi (η) α β γ δ !![0, 0; 0, 1]) ∧
      (ε : ℤ) ∣ t - x := by
  have hh : η ≠ 0 := D.h_pos.ne'
  have hε : (ε : ℤ) ∣ t - x := by
    obtain ⟨a, b, c, d, hm, -, hd⟩ := D.inL _ hγp
    have h00 := congrFun (congrFun hm 0) 0
    have h11 := congrFun (congrFun hm 1) 1
    rw [hγm] at h00 h11
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, Int.cast_inj,
      cons_val_one] at h00 h11
    have : x = a := by exact_mod_cast h00
    have : t = d := by exact_mod_cast h11
    subst_vars
    exact hd
  refine ⟨?_, hε⟩
  have h1 : InLe N ε (Phi (η) α β γ δ 1) := by rw [Phi_one hh he]; exact InLe.one N
  have hP := phi_InLe D hgN hg hγp
  obtain ⟨hE12, hE21, -⟩ := InLe_basic D hgN hg he
  have eE : ((t - x : ℤ) : ℝ) • (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (γp : Matrix (Fin 2) (Fin 2) ℝ) - (x : ℝ) • 1 - (y : ℝ) • !![0, 1; 0, 0] -
        (N : ℝ) • !![0, 0; 1, 0] := by
    rw [hγm]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [← Phi_smul, eE, Phi_sub, Phi_sub, Phi_sub, Phi_smul, Phi_smul, Phi_smul]
  exact ((hP.sub (h1.zsmul x)).sub (hE12.zsmul y)).sub hE21

/-- The integer divisibilities F1–F12. -/
theorem int_factsG {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈ NormG Γ)
  {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    (α * δ - β * γ) ∣ (η : ℤ) * (α * γ) ∧ (α * δ - β * γ) ∣ 1 * α ^ 2 ∧ (α * δ - β * γ) * N ∣ (η :
      ℤ) ^ 2 * γ ^ 2 ∧ (α * δ - β * γ) * (ε : ℤ) ∣ (2 * (η : ℤ)) * (α * γ) ∧
    (α * δ - β * γ) ∣ ((nOf N η : ℤ) * (η : ℤ)) * (β * δ) ∧ (α * δ - β * γ) ∣ (nOf N η : ℤ) * β ^
      2 ∧ (α * δ - β * γ) ∣ 1 * δ ^ 2 ∧ (α * δ - β * γ) * (ε : ℤ) ∣ (2 * (nOf N η : ℤ) * (η : ℤ))
      * (β * δ) ∧
    (α * δ - β * γ) ∣ (N : ℤ) * (β * γ) ∧ (α * δ - β * γ) * (η : ℤ) ∣ (N : ℤ) * (α * β) ∧ (α * δ -
      β * γ) * N ∣ ((N : ℤ) * (η : ℤ)) * (γ * δ) ∧
    (α * δ - β * γ) * (ε : ℤ) ∣ (2 * (N : ℤ)) * (β * γ) := by
  have hh : η ≠ 0 := D.h_pos.ne'
  have hhr : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hNr : (N : ℝ) = nOf N η * (η : ℝ) ^ 2 := by
    exact_mod_cast D.n_mul_sq.symm
  have hNz : (N : ℤ) = (nOf N η : ℤ) * (η : ℤ) ^ 2 := by exact_mod_cast D.n_mul_sq.symm
  have hN0 : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  obtain ⟨P12, P21, P22⟩ := InLe_basic D hgN hg he
  -- E₁₂
  obtain ⟨a1, b1, c1, d1, h00, h01, h10, h11, hc1, hd1⟩ := P12.entries
  rw [Phi_E12] at h00 h01 h10 h11
  have r00 := int_eq_of_real (X := -(α * (η : ℤ) * γ)) he (by rw [← h00]; simp)
  have r01 := int_eq_of_real (X := α ^ 2) he (by rw [← h01]; simp)
  have r10 := int_eq_of_real (X := -((η : ℤ) ^ 2 * γ ^ 2)) he (by rw [← h10]; simp)
  have r11 := int_eq_of_real (X := α * (η : ℤ) * γ) he (by rw [← h11]; simp)
  -- E₂₁ (times N)
  obtain ⟨a2, b2, c2, d2, i00, i01, i10, i11, hc2, hd2⟩ := P21.entries
  rw [Phi_E21 hh] at i00 i01 i10 i11
  have s00 := int_eq_of_real (X := (nOf N η : ℤ) * (η : ℤ) * (β * δ)) he
    (by rw [← i00]; simp [hNr]; field_simp)
  have s01 := int_eq_of_real (X := -((nOf N η : ℤ) * β ^ 2)) he
    (by rw [← i01]; simp [hNr]; field_simp)
  have s10 := int_eq_of_real (X := (N : ℤ) * δ ^ 2) he (by rw [← i10]; simp; ring)
  have s11 := int_eq_of_real (X := -((nOf N η : ℤ) * (η : ℤ) * (β * δ))) he
    (by rw [← i11]; simp [hNr]; field_simp)
  -- E₂₂ (times N)
  obtain ⟨a3, b3, c3, d3, j00, j01, j10, j11, hc3, hd3⟩ := P22.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((N : ℤ) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real (X := (nOf N η : ℤ) * (η : ℤ) * (α * β)) he
    (by rw [← j01]; simp [hNr]; field_simp)
  have t10 := int_eq_of_real (X := -((N : ℤ) * (η : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (N : ℤ) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c1', rfl⟩ := hc1
  obtain ⟨c2', rfl⟩ := hc2
  obtain ⟨c3', rfl⟩ := hc3
  obtain ⟨k1, hk1⟩ := hd1
  obtain ⟨k2, hk2⟩ := hd2
  obtain ⟨k3, hk3⟩ := hd3
  have hε : (ε : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.2 D.eps_dvd
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
    ⟨-a3, by linear_combination -t00⟩, ⟨b3, by rw [hNz]; linear_combination (η : ℤ) * t01⟩,
    ⟨-c3', by linear_combination -t10⟩, ?_⟩
  -- F12: ε ∣ N − 2 a3 and ε ∣ N give ε ∣ 2 a3
  have h2a : (ε : ℤ) ∣ 2 * a3 := by
    have : (ε : ℤ) ∣ (N : ℤ) - (d3 - a3) := dvd_sub ⟨m, hm⟩ ⟨k3, hk3⟩
    rw [hd3'] at this
    simpa using this
  obtain ⟨k4, hk4⟩ := h2a
  exact ⟨-k4, by linear_combination -2 * t00 - (α * δ - β * γ) * hk4⟩


/-- The four facts with s = t − x in place of N. -/
theorem int_facts_sG {N : ℕ} {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈ NormG
  Γ) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} {γp : SL(2, ℝ)} (hγp : γp ∈ Γ)
    (hγm : (γp : Matrix (Fin 2) (Fin 2) ℝ) = !![(x : ℝ), y; N, t]) :
    (α * δ - β * γ) ∣ (t - x) * (β * γ) ∧
      (α * δ - β * γ) * (η : ℤ) ∣ (t - x) * (α * β) ∧
      (α * δ - β * γ) * N ∣ ((t - x) * (η : ℤ)) * (γ * δ) ∧
      (α * δ - β * γ) * (ε : ℤ) ∣ (2 * (t - x)) * (β * γ) := by
  have hh : η ≠ 0 := D.h_pos.ne'
  obtain ⟨P, hε⟩ := InLe_s D hgN hg he hγp hγm
  obtain ⟨a4, b4, c4, d4, j00, j01, j10, j11, hc4, hd4⟩ := P.entries
  rw [Phi_E22 hh] at j00 j01 j10 j11
  have t00 := int_eq_of_real (X := -((t - x) * (β * γ))) he (by rw [← j00]; simp; ring)
  have t01 := int_eq_of_real_div (X := (t - x) * (α * β)) he hh
    (by rw [← j01]; simp; ring)
  have t10 := int_eq_of_real (X := -((t - x) * (η : ℤ) * (γ * δ))) he
    (by rw [← j10]; simp; ring)
  have t11 := int_eq_of_real (X := (t - x) * (α * δ)) he (by rw [← j11]; simp; ring)
  obtain ⟨c4', rfl⟩ := hc4
  obtain ⟨k4, hk4⟩ := hd4
  have hd4' : d4 - a4 = (t - x) - 2 * a4 := mul_left_cancel₀ he (by linear_combination -t11 - t00)
  refine ⟨⟨-a4, by linear_combination -t00⟩, ⟨b4, by linear_combination t01⟩,
    ⟨-c4', by linear_combination -t10⟩, ?_⟩
  have h2a : (ε : ℤ) ∣ 2 * a4 := by
    have : (ε : ℤ) ∣ (t - x) - (d4 - a4) := dvd_sub hε ⟨k4, hk4⟩
    rw [hd4'] at this
    simpa using this
  obtain ⟨k5, hk5⟩ := h2a
  exact ⟨-k5, by linear_combination -2 * t00 - (α * δ - β * γ) * hk5⟩

/-- The local conclusion at a prime p. -/
theorem local_conclusionG {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hgN : g ∈
  NormG Γ) {κ : ℝ}
    {α β γ δ : ℤ} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ)
    (he : α * δ - β * γ ≠ 0)
    (hprim : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ))
    {p : ℕ} (hp : p.Prime) :
    let B := vz p (α * δ - β * γ) + N.factorization p + 1
    (vz p (α * δ - β * γ) = 0 ∧ (nOf N η).factorization p ≤ vv B p γ) ∨
      (vz p (α * δ - β * γ) = (nOf N η).factorization p ∧
        (nOf N η).factorization p ≤ vv B p α ∧ (nOf N η).factorization p ≤ vv B p γ ∧
        (nOf N η).factorization p ≤ vv B p δ) := by
  intro B
  have hN := NeZero.ne N
  have hNz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hhz : (η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 D.h_pos.ne'
  have hn0 : nOf N η ≠ 0 := by
    intro h0
    have := D.n_mul_sq
    rw [h0, zero_mul] at this
    exact hN this.symm
  have hε0 : ε ≠ 0 := (Nat.pos_of_dvd_of_pos D.eps_dvd (Nat.pos_of_ne_zero hN)).ne'
  -- the local constants
  set ν := N.factorization p with hν
  set j := (ε).factorization p with hj
  set k := (η).factorization p with hk
  set nν := (nOf N η).factorization p with hnν
  set δ₀ := vz p (α * δ - β * γ) with hδ₀
  have hkj : k = min j (ν / 2) := D.h_fact p
  have hnk : nν + 2 * k = ν := D.factorization_n hN p
  have hjν : j ≤ ν := (Nat.factorization_le_iff_dvd hε0 hN).2 D.eps_dvd p
  -- valuations of the constants
  have vN : vz p (N : ℤ) = ν := vz_natCast p N
  have vh : vz p (η : ℤ) = k := vz_natCast p _
  have vn : vz p (nOf N η : ℤ) = nν := vz_natCast p _
  have v1 : vz p (1 : ℤ) = 0 := by simp [vz]
  -- shorthand for the valuations of the entries
  set a := vv B p α
  set b := vv B p β
  set c := vv B p γ
  set d := vv B p δ
  -- primitivity
  have prim : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    by_contra hcon
    push Not at hcon
    apply hprim p hp
    have key : ∀ x : ℤ, vv B p x ≠ 0 → (p : ℤ) ∣ x := by
      intro x hx
      by_cases h0 : x = 0
      · rw [h0]; exact dvd_zero _
      · rw [vv_of_ne h0] at hx
        have := (pow_dvd_iff_le_vz hp h0 1).2 (Nat.pos_of_ne_zero hx)
        simpa using this
    exact ⟨key α hcon.1, key β hcon.2.1, key γ hcon.2.2.1, key δ hcon.2.2.2⟩
  -- ultrametric relation
  have u1 := (ultra_vv (B := B) hp he (by simp only [B]; omega)).1
  obtain ⟨_, F2, F3, _, _, F6, F7, _, _, F10, F11, _⟩ := int_factsG D hgN hg he
  have vX : ∀ X : ℤ, X ≠ 0 → vz p ((α * δ - β * γ) * X) = δ₀ + vz p X := fun _ hX =>
    vz_mul he hX
  have hBe : vz p (α * δ - β * γ) ≤ B := by simp only [B]; omega
  have hBN : vz p ((α * δ - β * γ) * N) ≤ B := by rw [vX _ hNz, vN]; simp only [B]; omega
  have hBh : vz p ((α * δ - β * γ) * (η : ℤ)) ≤ B := by
    rw [vX _ hhz, vh]; simp only [B]
    omega
  have c2 := le_vv_sq (B := B) one_ne_zero hBe F2
  have c3 := le_vv_sq (B := B) (pow_ne_zero 2 hhz) hBN F3
  have c6 := le_vv_sq (B := B) (Nat.cast_ne_zero.2 hn0) hBe F6
  have c7 := le_vv_sq (B := B) one_ne_zero hBe F7
  have c10 := le_vv2 (B := B) hNz hBh F10
  have c11 := le_vv2 (B := B) (mul_ne_zero hNz hhz) hBN F11
  simp only [vX _ hNz, vX _ hhz, vz_mul hNz hhz, vz_mul hhz hhz, pow_two, vN, vh, vn, v1]
    at c2 c3 c6 c7 c10 c11
  obtain ⟨C10, C11⟩ : δ₀ + k ≤ j + a + b ∧ δ₀ + ν ≤ j + k + c + d := by
    by_cases hνj : ν = j
    · exact ⟨by omega, by omega⟩
    have hpN : p ∣ N := by
      by_contra hpN
      have : ν = 0 := Nat.factorization_eq_zero_of_not_dvd hpN
      omega
    obtain ⟨x, y, t, _, ⟨γp, hγp, hγm⟩, hs0, hvs⟩ := D.gamma p hp hpN (by omega)
    obtain ⟨_, S10, S11, _⟩ := int_facts_sG D hgN hg he hγp hγm
    have s10 := le_vv2 (B := B) hs0 hBh S10
    have s11 := le_vv2 (B := B) (mul_ne_zero hs0 hhz) hBN S11
    simp only [vX _ hNz, vX _ hhz, vz_mul hs0 hhz, hvs, vh, vN] at s10 s11
    exact ⟨by omega, by omega⟩
  have := local_form_gen ν j k δ₀ a b c d hkj prim u1 (by omega) (by omega) (by omega)
    (by omega) C10 C11
  have hn2 : ν - 2 * k = nν := by omega
  rw [hn2] at this
  exact this

/-- **Newman's argument for Γ**: every element of the normalizer of Γ has the form `IsNewmanFormH`
with parameter η. -/
theorem newmanG {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (D : NewmanData N Γ ε η) (hg : g ∈ NormG Γ) :
    IsNewmanFormH N η g := by
  obtain ⟨κ, α, β, γ, δ, hκ, hprim, hgm⟩ := exists_prim_formG D hg
  have hh : η ≠ 0 := D.h_pos.ne'
  have hhr : (η : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hN := NeZero.ne N
  have hgS : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (η) α β γ δ := by rw [hgm]; rfl
  have hdet : κ ^ 2 * ((α * δ - β * γ : ℤ) : ℝ) = 1 := by
    have := g.2
    rw [hgS, det_smul, Fintype.card_fin, det_Smat hh] at this
    exact this
  have he : α * δ - β * γ ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hepos : 0 < α * δ - β * γ := by
    have hκ2 : 0 < κ ^ 2 := by positivity
    have : (0 : ℝ) < ((α * δ - β * γ : ℤ) : ℝ) := by
      by_contra hc
      push Not at hc
      nlinarith
    exact_mod_cast this
  have hloc := fun (p : ℕ) (hp : p.Prime) => local_conclusionG D hg hgS he hprim hp
  have hn0 : nOf N η ≠ 0 := by
    intro h0
    have := D.n_mul_sq
    rw [h0, zero_mul] at this
    exact hN this.symm
  have hnz : (nOf N η : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  -- e ∣ n, n ∣ γ, e ∣ α, e ∣ δ
  have hen : (α * δ - β * γ) ∣ (nOf N η : ℤ) := by
    refine dvd_of_forall_vz_le he hnz (fun p hp => ?_)
    have := hloc p hp
    simp only at this
    rw [vz_natCast]
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hnγ : (nOf N η : ℤ) ∣ γ := by
    by_cases hγ : γ = 0
    · rw [hγ]; exact dvd_zero _
    refine dvd_of_forall_vz_le hnz hγ (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hγ] at this
    rw [vz_natCast]
    rcases this with ⟨-, h2⟩ | ⟨-, -, h2, -⟩ <;> omega
  have heα : (α * δ - β * γ) ∣ α := by
    by_cases hα : α = 0
    · rw [hα]; exact dvd_zero _
    refine dvd_of_forall_vz_le he hα (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hα] at this
    rcases this with ⟨h1, -⟩ | ⟨h1, h2, -⟩ <;> omega
  have heδ : (α * δ - β * γ) ∣ δ := by
    by_cases hδ : δ = 0
    · rw [hδ]; exact dvd_zero _
    refine dvd_of_forall_vz_le he hδ (fun p hp => ?_)
    have := hloc p hp
    simp only [vv_of_ne hδ] at this
    rcases this with ⟨h1, -⟩ | ⟨h1, -, -, h2⟩ <;> omega
  obtain ⟨a', ha'⟩ := heα
  obtain ⟨d', hd'⟩ := heδ
  obtain ⟨c', hc'⟩ := hnγ
  obtain ⟨m, hm⟩ := hen
  set E := α * δ - β * γ with hE
  -- e as a natural number
  set e : ℕ := E.toNat with he_def
  have hEe : (e : ℤ) = E := Int.toNat_of_nonneg hepos.le
  have he0 : 0 < e := by omega
  have her : (e : ℝ) = (E : ℝ) := by exact_mod_cast hEe
  have hsq : Real.sqrt e * Real.sqrt e = e := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hs0 : Real.sqrt e ≠ 0 := (Real.sqrt_pos.2 (Nat.cast_pos.2 he0)).ne'
  refine ⟨a', β, c', d', e, he0, ⟨m.toNat, ?_⟩, ?_, κ * Real.sqrt e, ?_, ?_⟩
  · have hm0 : 0 ≤ m := by
      by_contra hneg
      push Not at hneg
      have : (nOf N η : ℤ) < 0 := by rw [hm]; exact mul_neg_of_pos_of_neg hepos hneg
      omega
    have : ((nOf N η : ℕ) : ℤ) = ((e * m.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hm0, hEe]
      exact hm
    exact_mod_cast this
  · rw [hEe]
    have h1 : E = α * δ - β * γ := rfl
    rw [ha', hd', hc'] at h1
    simp only [nOf] at h1 ⊢
    linear_combination -h1
  · have h1 : (κ * Real.sqrt e) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), her]
      exact hdet
    have h2 : (κ * Real.sqrt e) * (κ * Real.sqrt e) = 1 := by rw [← pow_two]; exact h1
    exact mul_self_eq_one_iff.1 h2
  · have hNr : (N : ℝ) = nOf N η * (η : ℝ) ^ 2 := by
      exact_mod_cast D.n_mul_sq.symm
    have hα' : (α : ℝ) = a' * e := by rw [her, ha']; push_cast; ring
    have hγ' : (γ : ℝ) = nOf N η * c' := by rw [hc']; push_cast; ring
    have hδ' : (δ : ℝ) = d' * e := by rw [her, hd']; push_cast; ring
    rw [hgm, mul_div_assoc, div_self hs0, mul_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hα', hγ', hδ', hNr] ; field_simp

end

end CongruenceNormalizers
