/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanFacts
public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanLocal

/-!
# T2: Newman's theorem

Every g ∈ Norm(Γ₀(N)) has the form (8′).  Write g = κ·[[α, β/h], [hγ, δ]] with α, β, γ, δ ∈ ℤ
coprime (`exists_prim_form`), e = αδ − βγ.  The divisibilities F1–F12 (for g and g⁻¹, and with
s = t − x from the element γ_p of Lemma 3) give, at every prime p, the valuation inequalities of
`local_form`, whose conclusion says: either v_p(e) = 0 and p^{v_p(n)} ∣ γ, or v_p(e) = v_p(n) and
p^{v_p(n)} divides α, γ, δ.  Hence e ∣ n, n ∣ γ, e ∣ α, e ∣ δ, which is (8′).
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

theorem dvd_of_forall_vz_le {m x : ℤ} (hm : m ≠ 0) (hx : x ≠ 0)
    (h : ∀ p : ℕ, p.Prime → vz p m ≤ vz p x) : m ∣ x := by
  rw [← Int.natAbs_dvd_natAbs]
  rw [← Nat.factorization_le_iff_dvd (Int.natAbs_ne_zero.2 hm) (Int.natAbs_ne_zero.2 hx)]
  intro p
  by_cases hp : p.Prime
  · exact h p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem vz_int_natCast (p n : ℕ) : vz p (n : ℤ) = n.factorization p := vz_natCast p n

/-- The local conclusion at a prime p. -/
theorem local_conclusion {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ}
    {α β γ δ : ℤ} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (hginv : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      κ • Smat (hPart N) δ (-β) (-γ) α)
    (he : α * δ - β * γ ≠ 0)
    (hprim : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ β ∧ (p : ℤ) ∣ γ ∧ (p : ℤ) ∣ δ))
    {p : ℕ} (hp : p.Prime) :
    let B := vz p (α * δ - β * γ) + N.factorization p + 1
    (vz p (α * δ - β * γ) = 0 ∧ (nPart N).factorization p ≤ vv B p γ) ∨
      (vz p (α * δ - β * γ) = (nPart N).factorization p ∧
        (nPart N).factorization p ≤ vv B p α ∧ (nPart N).factorization p ≤ vv B p γ ∧
        (nPart N).factorization p ≤ vv B p δ) := by
  intro B
  have hN := NeZero.ne N
  have hNz : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hhz : (hPart N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (hPart_pos N).ne'
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N hN
    rw [h0, zero_mul] at this
    exact hN this.symm
  have hnz : (nPart N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  have hεz : (epsPart N : ℤ) ≠ 0 := by
    have : epsPart N ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.gcd_pos_of_pos_right _ (by norm_num))
    exact Nat.cast_ne_zero.2 this
  -- the local constants
  set ν := N.factorization p with hν
  set j := (epsPart N).factorization p with hj
  set k := (hPart N).factorization p with hk
  set e₂ := (2 : ℕ).factorization p with he₂
  set nν := (nPart N).factorization p with hnν
  set δ₀ := vz p (α * δ - β * γ) with hδ₀
  obtain ⟨hcases, hkj⟩ := local_constants (p := p) hN
  have hnk : nν + 2 * k = ν := factorization_nPart hN
  have hjν : j ≤ ν := by
    rw [hj, factorization_epsPart hN]
    exact min_le_left _ _
  -- valuations of the constants
  have vN : vz p (N : ℤ) = ν := vz_natCast p N
  have vh : vz p (hPart N : ℤ) = k := vz_natCast p _
  have vn : vz p (nPart N : ℤ) = nν := vz_natCast p _
  have vε : vz p (epsPart N : ℤ) = j := vz_natCast p _
  have v2 : vz p (2 : ℤ) = e₂ := by
    have := vz_natCast p 2
    simpa using this
  have v1 : vz p (1 : ℤ) = 0 := by simp [vz]
  have two0 : (2 : ℤ) ≠ 0 := by norm_num
  -- shorthand for the valuations of the entries
  set a := vv B p α
  set b := vv B p β
  set c := vv B p γ
  set d := vv B p δ
  have hb' : vv B p (-β) = b := vv_neg B p β
  have hc' : vv B p (-γ) = c := vv_neg B p γ
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
  obtain ⟨u1, u2⟩ := ultra_vv (B := B) hp he (by simp only [B]; omega)
  -- the facts
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12⟩ := int_facts hgN hg he
  have he' : δ * α - -β * -γ = α * δ - β * γ := by ring
  have he'0 : δ * α - -β * -γ ≠ 0 := by rw [he']; exact he
  obtain ⟨G1, G2, G3, G4, G5, G6, G7, G8, G9, G10, G11, G12⟩ :=
    int_facts (inv_mem hgN) hginv he'0
  rw [he'] at G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
  -- valuations of the moduli
  have vX : ∀ X : ℤ, X ≠ 0 → vz p ((α * δ - β * γ) * X) = δ₀ + vz p X := fun X hX =>
    vz_mul he hX
  have hBe : vz p (α * δ - β * γ) ≤ B := by simp only [B]; omega
  have hBN : vz p ((α * δ - β * γ) * N) ≤ B := by rw [vX _ hNz, vN]; simp only [B]; omega
  have hBε : vz p ((α * δ - β * γ) * (epsPart N : ℤ)) ≤ B := by
    rw [vX _ hεz, vε]; simp only [B]; omega
  have hBh : vz p ((α * δ - β * γ) * (hPart N : ℤ)) ≤ B := by
    rw [vX _ hhz, vh]; simp only [B]
    rcases hcases with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> omega
  -- the inequalities from g
  have c1 := le_vv2 (B := B) hhz hBe F1
  have c2 := le_vv_sq (B := B) one_ne_zero hBe F2
  have c3 := le_vv_sq (B := B) (pow_ne_zero 2 hhz) hBN F3
  have c4 := le_vv2 (B := B) (mul_ne_zero two0 hhz) hBε F4
  have c5 := le_vv2 (B := B) (mul_ne_zero hnz hhz) hBe F5
  have c6 := le_vv_sq (B := B) hnz hBe F6
  have c7 := le_vv_sq (B := B) one_ne_zero hBe F7
  have c8 := le_vv2 (B := B) (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε F8
  have c9 := le_vv2 (B := B) hNz hBe F9
  have c10 := le_vv2 (B := B) hNz hBh F10
  have c11 := le_vv2 (B := B) (mul_ne_zero hNz hhz) hBN F11
  have c12 := le_vv2 (B := B) (mul_ne_zero two0 hNz) hBε F12
  -- and from g⁻¹
  have d1 := le_vv2 (B := B) hhz hBe G1
  have d2 := le_vv_sq (B := B) one_ne_zero hBe G2
  have d4 := le_vv2 (B := B) (mul_ne_zero two0 hhz) hBε G4
  have d5 := le_vv2 (B := B) (mul_ne_zero hnz hhz) hBe G5
  have d7 := le_vv_sq (B := B) one_ne_zero hBe G7
  have d8 := le_vv2 (B := B) (mul_ne_zero (mul_ne_zero two0 hnz) hhz) hBε G8
  have d10 := le_vv2 (B := B) hNz hBh G10
  have d11 := le_vv2 (B := B) (mul_ne_zero hNz hhz) hBN G11
  simp only [hb', hc'] at d1 d4 d5 d8 d10 d11
  simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul two0 hhz, vz_mul hnz hhz,
    vz_mul (mul_ne_zero two0 hnz) hhz, vz_mul two0 hnz, vz_mul hNz hhz, vz_mul two0 hNz,
    vz_mul hhz hhz, pow_two, vN, vh, vn, vε, v2, v1] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12
  simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul two0 hhz, vz_mul hnz hhz,
    vz_mul (mul_ne_zero two0 hnz) hhz, vz_mul two0 hnz, vz_mul hNz hhz,
    vN, vh, vn, vε, v2, v1] at d1 d2 d4 d5 d7 d8 d10 d11
  -- the conditions C9–C12, C17, C18 with j: from N if ν = j, from γ_p otherwise
  obtain ⟨C9, C10, C11, C12, C17, C18⟩ : δ₀ ≤ j + b + c ∧ δ₀ + k ≤ j + a + b ∧
      δ₀ + ν ≤ j + k + c + d ∧ δ₀ ≤ e₂ + b + c ∧ δ₀ + k ≤ j + b + d ∧ δ₀ + ν ≤ j + k + c + a := by
    by_cases hνj : ν = j
    · refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    have hpN : p ∣ N := by
      by_contra hpN
      have : ν = 0 := Nat.factorization_eq_zero_of_not_dvd hpN
      omega
    obtain ⟨x, y, t, hdet, hs⟩ := exists_gamma_p hN hp hpN
    rcases hs with hs | ⟨hs0, hvs⟩
    · exact absurd hs hνj
    obtain ⟨S9, S10, S11, S12⟩ := int_facts_s hgN hg he hdet
    obtain ⟨T9, T10, T11, T12⟩ := int_facts_s (inv_mem hgN) hginv he'0 hdet
    rw [he'] at T9 T10 T11 T12
    have s9 := le_vv2 (B := B) hs0 hBe S9
    have s10 := le_vv2 (B := B) hs0 hBh S10
    have s11 := le_vv2 (B := B) (mul_ne_zero hs0 hhz) hBN S11
    have s12 := le_vv2 (B := B) (mul_ne_zero two0 hs0) hBε S12
    have t10 := le_vv2 (B := B) hs0 hBh T10
    have t11 := le_vv2 (B := B) (mul_ne_zero hs0 hhz) hBN T11
    simp only [hb', hc'] at t10 t11
    simp only [vX _ hNz, vX _ hεz, vX _ hhz, vz_mul hs0 hhz, vz_mul two0 hs0, hvs, vh, vN, vε,
      v2] at s9 s10 s11 s12 t10 t11
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have := local_form p ν j k e₂ δ₀ a b c d hcases hkj prim u1 u2 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) C9 C10 C11 C12 (by omega) (by omega)
    (by omega) (by omega) C17 (by omega)
  have hn2 : ν - 2 * k = nν := by omega
  rw [hn2] at this
  exact this

/-- **T2 (Newman's theorem)**: every element of the normalizer has the form (8′). -/
theorem newman' {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) : IsNewmanForm N g := by
  obtain ⟨κ, α, β, γ, δ, hκ, hprim, hgm⟩ := exists_prim_form hg
  have hh : hPart N ≠ 0 := (hPart_pos N).ne'
  have hhr : (hPart N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hh
  have hN := NeZero.ne N
  have hgS : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ := by rw [hgm]; rfl
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
  have hginv : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      κ • Smat (hPart N) δ (-β) (-γ) α := by
    rw [coe_inv_of_coe_eq_smul hgm]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Smat] ; ring
  have hloc := fun (p : ℕ) (hp : p.Prime) => local_conclusion hg hgS hginv he hprim hp
  have hn0 : nPart N ≠ 0 := by
    intro h0
    have := hPart_sq_mul_nPart N hN
    rw [h0, zero_mul] at this
    exact hN this.symm
  have hnz : (nPart N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  -- e ∣ n, n ∣ γ, e ∣ α, e ∣ δ
  have hen : (α * δ - β * γ) ∣ (nPart N : ℤ) := by
    refine dvd_of_forall_vz_le he hnz (fun p hp => ?_)
    have := hloc p hp
    simp only at this
    rw [vz_natCast]
    rcases this with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hnγ : (nPart N : ℤ) ∣ γ := by
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
      have : (nPart N : ℤ) < 0 := by rw [hm]; exact mul_neg_of_pos_of_neg hepos hneg
      omega
    have : ((nPart N : ℕ) : ℤ) = ((e * m.toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hm0, hEe]
      exact hm
    exact_mod_cast this
  · rw [hEe]
    have h1 : E = α * δ - β * γ := rfl
    rw [ha', hd', hc'] at h1
    linear_combination -h1
  · have h1 : (κ * Real.sqrt e) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), her]
      exact hdet
    have h2 : (κ * Real.sqrt e) * (κ * Real.sqrt e) = 1 := by rw [← pow_two]; exact h1
    exact mul_self_eq_one_iff.1 h2
  · have hNr : (N : ℝ) = nPart N * (hPart N : ℝ) ^ 2 := by
      exact_mod_cast (hPart_sq_mul_nPart N hN).symm
    have hα' : (α : ℝ) = a' * e := by rw [her, ha']; push_cast; ring
    have hγ' : (γ : ℝ) = nPart N * c' := by rw [hc']; push_cast; ring
    have hδ' : (δ : ℝ) = d' * e := by rw [her, hd']; push_cast; ring
    rw [hgm, mul_div_assoc, div_self hs0, mul_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hα', hγ', hδ', hNr] ; field_simp

end

end CongruenceNormalizers
