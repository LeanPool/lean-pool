/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Fermions.CauchyBinet
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The aufbau principle for non-interacting lattice fermions

For a symmetric single-particle Hamiltonian `h` with an orthonormal eigenbasis `φ_a` (energies
`ε_a`):
* `slaterSub_eigen`: the Slater determinant of any `N` orbitals `S` is a many-body eigenvector of
  `Γ h` with energy `E_S = Σ_{a ∈ S} ε_a`;
* `qf_gamma_ge`: `⟨Ψ, Γ h Ψ⟩ ≥ min_S E_S · ‖Ψ‖²` for every many-body state (the Slater determinants
  form an orthonormal basis);
* `aufbau`: the non-interacting ground-state energy is the smallest sum of `N` orbital energies, and
  the Slater determinant of a minimising set of orbitals is a ground state.
-/

@[expose] public section

namespace DFT

open Matrix

variable {M N : ℕ}

/-- Total energy of the orbitals selected by `S`. -/
def orbEnergy (ε : Fin M → ℝ) (S : Conf M N) : ℝ := ∑ j, ε (τs S j)

theorem slaterSub_eigen (h : Matrix (Fin M) (Fin M) ℝ) {φ : Fin M → Fin M → ℝ} {ε : Fin M → ℝ}
    (hφ : ∀ a, h *ᵥ φ a = ε a • φ a) (S : Conf M N) :
    (Γ h : Matrix (Conf M N) (Conf M N) ℝ) *ᵥ slaterSub φ S = orbEnergy ε S • slaterSub φ S :=
  gamma_slater h (fun j => φ (τs S j)) (fun j => ε (τs S j)) (fun _ => hφ _)

section
variable (φ : Fin M → Fin M → ℝ)

/-- Matrix whose columns are the Slater determinants of all orbital subsets. -/
def slaterMat : Matrix (Conf M N) (Conf M N) ℝ := fun s S => slaterSub φ S s

variable {φ}

lemma slaterMat_orth (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) :
    (slaterMat (N := N) φ)ᵀ * slaterMat φ = 1 := by
  ext S T
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [transpose_apply, slaterMat]
  exact slater_orthonormal hON S T

lemma dot_slaterMat (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0)
    (x y : Conf M N → ℝ) : (slaterMat φ *ᵥ x) ⬝ᵥ (slaterMat φ *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, slaterMat_orth hON, vecMul_one]

end

/-- **Variational lower bound by the smallest orbital-sum energy.** -/
theorem qf_gamma_ge (h : Matrix (Fin M) (Fin M) ℝ) {φ : Fin M → Fin M → ℝ} {ε : Fin M → ℝ}
    (hφ : ∀ a, h *ᵥ φ a = ε a • φ a) (hON : ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0)
    {E : ℝ} (hE : ∀ S : Conf M N, E ≤ orbEnergy ε S) (v : Conf M N → ℝ) :
    E * (v ⬝ᵥ v) ≤ qf (Γ h) v := by
  set P := slaterMat (N := N) φ
  have hPP : P * Pᵀ = 1 := mul_eq_one_comm.mp (slaterMat_orth hON)
  obtain ⟨c, rfl⟩ : ∃ c, v = P *ᵥ c := ⟨Pᵀ *ᵥ v, by rw [mulVec_mulVec, hPP, one_mulVec]⟩
  have hGP : (Γ h : Matrix (Conf M N) (Conf M N) ℝ) * P = P * diagonal (orbEnergy ε) := by
    ext s S
    have := congrFun (slaterSub_eigen h hφ S) s
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [P, slaterMat, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [this, mul_comm]
  have hq : qf (Γ h) (P *ᵥ c) = c ⬝ᵥ (diagonal (orbEnergy ε) *ᵥ c) := by
    unfold qf
    rw [mulVec_mulVec, hGP, ← mulVec_mulVec, dot_slaterMat hON]
  rw [hq, dot_slaterMat hON]
  simp only [dotProduct, mulVec, diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ,
    ite_true, Finset.mul_sum]
  apply Finset.sum_le_sum; intro S _
  nlinarith [hE S, mul_self_nonneg (c S)]

/-- Orthonormal eigenvectors of a symmetric real matrix (spectral theorem). -/
theorem exists_eigenbasis (h : Matrix (Fin M) (Fin M) ℝ) (hS : h.IsSymm) :
    ∃ (ε : Fin M → ℝ) (φ : Fin M → Fin M → ℝ), (∀ a, h *ᵥ φ a = ε a • φ a) ∧
      ∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0 := by
  have hH : h.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_eq_transpose_of_trivial]; exact hS
  refine ⟨hH.eigenvalues, fun a => ⇑(hH.eigenvectorBasis a), fun a => hH.mulVec_eigenvectorBasis a,
      ?_⟩
  intro a b
  have h1 := (orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal) a b
  rw [← h1, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

lemma conf_nonempty (hN : N ≤ M) : Nonempty (Conf M N) := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin M))) (n := N)
    (by simpa using hN)
  exact ⟨⟨t, ht⟩⟩

/-- **Aufbau theorem.** The ground-state energy of `N` non-interacting fermions with single-particle
Hamiltonian `h` is the smallest sum of `N` orbital energies, attained by the Slater determinant of
the corresponding orbitals, which is a many-body ground state. -/
theorem aufbau (h : Matrix (Fin M) (Fin M) ℝ) (hS : h.IsSymm) (hN : N ≤ M) :
    ∃ (ε : Fin M → ℝ) (φ : Fin M → Fin M → ℝ) (S0 : Conf M N),
      (∀ a, h *ᵥ φ a = ε a • φ a) ∧
      (∀ a b, ∑ x, φ a x * φ b x = if a = b then 1 else 0) ∧
      (∀ S : Conf M N, orbEnergy ε S0 ≤ orbEnergy ε S) ∧
      IsGroundState (Γ h) (slaterSub φ S0) ∧
      ∀ v : Conf M N → ℝ, orbEnergy ε S0 * (v ⬝ᵥ v) ≤ qf (Γ h) v := by
  obtain ⟨ε, φ, hφ, hON⟩ := exists_eigenbasis h hS
  have := conf_nonempty hN
  obtain ⟨S0, -, hmin⟩ :=
      Finset.exists_min_image Finset.univ (orbEnergy (N := N) ε) Finset.univ_nonempty
  have hmin' : ∀ S, orbEnergy ε S0 ≤ orbEnergy ε S := fun S => hmin S (Finset.mem_univ S)
  have hlow := qf_gamma_ge h hφ hON hmin'
  have hnorm : slaterSub φ S0 ⬝ᵥ slaterSub φ S0 = 1 := by
    have := slater_orthonormal hON S0 S0
    simpa [dotProduct] using this
  refine ⟨ε, φ, S0, hφ, hON, hmin', ⟨?_, fun w => ?_⟩, hlow⟩
  · intro h0; rw [h0] at hnorm; simp at hnorm
  · have hq : qf (Γ h) (slaterSub φ S0) = orbEnergy ε S0 := by
      unfold qf; rw [slaterSub_eigen h hφ S0, dotProduct_smul, hnorm, smul_eq_mul, mul_one]
    rw [hq, hnorm, mul_one]
    exact hlow w

end DFT

namespace DFT

variable {M N : ℕ}

lemma orbEnergy_eq_sum (ε : Fin M → ℝ) (S : Conf M N) : orbEnergy ε S = ∑ a ∈ S.1, ε a := by
  unfold orbEnergy τs
  have hmap : Finset.univ.map (S.1.orderEmbOfFin S.2).toEmbedding = S.1 := by
    ext a; simp
  conv_rhs => rw [← hmap]
  rw [Finset.sum_map]; rfl

/-- Exchange inequality: if every element of `A` is below every element of `B` and `|A| = |B|`, then
`Σ_A ε ≤ Σ_B ε`. -/
lemma sum_le_sum_of_forall_le {A B : Finset (Fin M)} (ε : Fin M → ℝ) (hc : A.card = B.card)
    (h : ∀ a ∈ A, ∀ b ∈ B, ε a ≤ ε b) : ∑ a ∈ A, ε a ≤ ∑ b ∈ B, ε b := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · rw [Finset.card_empty, eq_comm, Finset.card_eq_zero] at hc; simp [hc]
  · set m := A.sup' hA ε
    obtain ⟨a0, ha0, hm⟩ := Finset.exists_mem_eq_sup' hA ε
    calc ∑ a ∈ A, ε a ≤ ∑ _a ∈ A, m := Finset.sum_le_sum fun a ha => Finset.le_sup' ε ha
      _ = ∑ _b ∈ B, m := by simp [hc]
      _ ≤ ∑ b ∈ B, ε b :=
          Finset.sum_le_sum fun b hb => by rw [show m = ε a0 from hm]; exact h a0 ha0 b hb

/-- **Aufbau: the minimising orbital sets are exactly the sets of lowest orbitals.** A set `S` of
`N` orbitals minimises the total orbital energy iff no unoccupied orbital lies strictly below an
occupied one (arbitrary choices among degenerate orbitals at the Fermi level are allowed). -/
theorem aufbau_lowest (ε : Fin M → ℝ) (S : Conf M N) :
    (∀ T : Conf M N, orbEnergy ε S ≤ orbEnergy ε T) ↔ ∀ a ∈ S.1, ∀ b ∉ S.1, ε a ≤ ε b := by
  simp only [orbEnergy_eq_sum]
  constructor
  · intro hmin a ha b hb
    by_contra hlt
    push Not at hlt
    have hcard : (insert b (S.1.erase a)).card = N := by
      rw [Finset.card_insert_of_notMem (fun h => hb (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem ha, S.2]
      have : 0 < N := S.2 ▸ Finset.card_pos.mpr ⟨a, ha⟩
      omega
    have h1 := hmin ⟨_, hcard⟩
    simp only at h1
    rw [Finset.sum_insert (fun h => hb (Finset.mem_of_mem_erase h))] at h1
    have h2 := Finset.add_sum_erase S.1 ε ha
    linarith
  · intro hlow T
    have hS := Finset.sum_sdiff (Finset.inter_subset_left : S.1 ∩ T.1 ⊆ S.1) (f := ε)
    have hT := Finset.sum_sdiff (Finset.inter_subset_right : S.1 ∩ T.1 ⊆ T.1) (f := ε)
    rw [Finset.sdiff_inter_self_left] at hS
    rw [Finset.sdiff_inter_self_right] at hT
    have hc : (S.1 \ T.1).card = (T.1 \ S.1).card := by
      have h1 := Finset.card_sdiff_add_card_inter S.1 T.1
      have h2 := Finset.card_sdiff_add_card_inter T.1 S.1
      rw [Finset.inter_comm] at h2
      rw [S.2] at h1; rw [T.2] at h2
      omega
    have := sum_le_sum_of_forall_le ε hc fun a ha b hb =>
      hlow a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).2
    linarith

end DFT
