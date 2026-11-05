/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerDelta.NewmanGen

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

/-- The generic Newman hypotheses for Γ₀(N). -/
theorem newmanData_gamma0 (N : ℕ) :
    NewmanData N (Gamma0R N) (epsPart N) (hPart N) where
  le := le_refl _
  T_mem := matT_mem N
  U_mem := matU_mem N
  inL := fun _ h => InL.of_mem h
  eps_dvd := epsPart_dvd N
  h_pos := hPart_pos N
  h_sq_dvd := by
    by_cases hN : N = 0
    · simp [hN]
    · exact hPart_sq_dvd hN
  h_fact := by
    intro p
    by_cases hN : N = 0
    · simp [hN, hPart]
    · exact (local_constants hN).2
  gamma := by
    intro p hp hpN hlt
    have hN : N ≠ 0 := by
      intro hN
      simp [hN] at hlt
    obtain ⟨x, y, t, hdet, hs⟩ := exists_gamma_p hN hp hpN
    have hs' : t - x ≠ 0 ∧ vz p (t - x) = (epsPart N).factorization p := by
      rcases hs with heq | hs
      · omega
      · exact hs
    let γp : SL(2, ℝ) := ⟨!![(x : ℝ), y; N, t], by
      rw [det_fin_two_of]
      exact_mod_cast hdet⟩
    exact ⟨x, y, t, hdet,
      ⟨γp, mem_Gamma0R_of_entries x y N t rfl (dvd_refl _), rfl⟩, hs'⟩

theorem InL.entries {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) :
    ∃ a b c d : ℤ, M 0 0 = a ∧ M 0 1 = b ∧ M 1 0 = c ∧ M 1 1 = d ∧ (N : ℤ) ∣ c ∧
      (epsPart N : ℤ) ∣ d - a := by
  exact InLe.entries h

theorem phi_InL {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ) {Y : SL(2, ℝ)}
    (hY : Y ∈ Gamma0R N) : InL N (Phi (hPart N) α β γ δ (Y : Matrix (Fin 2) (Fin 2) ℝ)) := by
  exact phi_InLe (newmanData_gamma0 N) hgN hg hY

theorem InL.nsmul' {N : ℕ} {M : Matrix (Fin 2) (Fin 2) ℝ} (h : InL N M) (m : ℕ) :
    InL N ((m : ℝ) • M) := by
  exact InLe.nsmul' h m

theorem InL_basic {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) :
    InL N (Phi (hPart N) α β γ δ !![0, 1; 0, 0]) ∧
      InL N ((N : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 1, 0]) ∧
      InL N ((N : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 0, 1]) := by
  exact InLe_basic (newmanData_gamma0 N) hgN hg he

theorem InL_s {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} (hdet : x * t - y * N = 1) :
    InL N (((t - x : ℤ) : ℝ) • Phi (hPart N) α β γ δ !![0, 0; 0, 1]) ∧
      (epsPart N : ℤ) ∣ t - x := by
  let γp : SL(2, ℝ) := ⟨!![(x : ℝ), y; N, t], by
    rw [det_fin_two_of]
    exact_mod_cast hdet⟩
  have hγp : γp ∈ Gamma0R N := mem_Gamma0R_of_entries x y N t rfl (dvd_refl _)
  exact InLe_s (newmanData_gamma0 N) hgN hg he hγp rfl

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
  exact int_factsG (newmanData_gamma0 N) hgN hg he

theorem int_facts_s {N : ℕ} {g : SL(2, ℝ)} (hgN : g ∈ Norm0 N) {κ : ℝ} {α β γ δ : ℤ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = κ • Smat (hPart N) α β γ δ)
    (he : α * δ - β * γ ≠ 0) {x y t : ℤ} (hdet : x * t - y * N = 1) :
    (α * δ - β * γ) ∣ (t - x) * (β * γ) ∧
      (α * δ - β * γ) * (hPart N : ℤ) ∣ (t - x) * (α * β) ∧
      (α * δ - β * γ) * N ∣ ((t - x) * (hPart N : ℤ)) * (γ * δ) ∧
      (α * δ - β * γ) * (epsPart N : ℤ) ∣ (2 * (t - x)) * (β * γ) := by
  let γp : SL(2, ℝ) := ⟨!![(x : ℝ), y; N, t], by
    rw [det_fin_two_of]
    exact_mod_cast hdet⟩
  have hγp : γp ∈ Gamma0R N := mem_Gamma0R_of_entries x y N t rfl (dvd_refl _)
  exact int_facts_sG (newmanData_gamma0 N) hgN hg he hγp rfl

end

end CongruenceNormalizers
