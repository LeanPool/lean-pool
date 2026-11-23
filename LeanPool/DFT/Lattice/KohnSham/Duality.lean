/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Basic.Spectral
public import LeanPool.DFT.Lattice.HK.Basic
public import Mathlib.Analysis.Convex.Function
meta import Mathlib.Tactic.Linarith
meta import Mathlib.Tactic.Ring

/-!
# Lieb's functional and convex duality

Setting: configurations `C`, sites `V`, symmetric `H0`, occupations `n`; `E(v)` is the ground-state
energy of `H(v) = hamN H0 n v`.
* `DensDomain n`: densities `ρ = Σ_c λ_c n(c)` with `λ` a probability vector (ensemble densities of
  configurations).
* `lieb ρ = sup_v [E(v) − v·ρ]`: Lieb's universal functional (Legendre transform of `E`).
* `lieb_duality`: `E(v) = min_{ρ ∈ DensDomain} [F(ρ) + v·ρ]`, the minimum being attained at the
  density of any ground state of `H(v)`.
* `lieb_convexOn`: `F` is convex on the density domain.
-/

@[expose] public section

namespace DFT

open Matrix

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [Nonempty C]

/-- Ground-state energy as a function of the potential. -/
noncomputable def Egs (H0 : Matrix C C ℝ) (n : V → C → ℝ) (v : V → ℝ) : ℝ := gsEnergy (hamN H0 n v)

/-- Nonnegative finite weights of total mass one. -/
def probVec (C : Type*) [Fintype C] : Set (C → ℝ) :=
  {lam | (∀ c, 0 ≤ lam c) ∧ ∑ c, lam c = 1}

/-- Ensemble densities of configurations. -/
def DensDomain (n : V → C → ℝ) : Set (V → ℝ) :=
  (fun lam : C → ℝ => fun i => ∑ c, lam c * n i c) '' probVec C

/-- **Lieb's universal functional.** -/
noncomputable def lieb (H0 : Matrix C C ℝ) (n : V → C → ℝ) (ρ : V → ℝ) : ℝ :=
  sSup (Set.range fun v : V → ℝ => Egs H0 n v - v ⬝ᵥ ρ)

lemma Egs_le_config {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) (c : C) :
    Egs H0 n v ≤ H0 c c + ∑ i, v i * n i c := by
  have h := gsEnergy_le (hamN_isSymm hH0 n v) (φ := Pi.single c 1) (by simp)
  unfold Egs
  refine h.trans (le_of_eq ?_)
  rw [qf_hamN]
  simp [qf, dens, Pi.single_apply, mulVec, dotProduct]

lemma lieb_bdd {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ρ : V → ℝ}
    (hρ : ρ ∈ DensDomain n) : BddAbove (Set.range fun v : V → ℝ => Egs H0 n v - v ⬝ᵥ ρ) := by
  obtain ⟨lam, ⟨hl0, hl1⟩, rfl⟩ := hρ
  refine ⟨∑ c, lam c * H0 c c, ?_⟩
  rintro _ ⟨v, rfl⟩
  have : Egs H0 n v = ∑ c, lam c * Egs H0 n v := by rw [← Finset.sum_mul, hl1, one_mul]
  have hdot : v ⬝ᵥ (fun i => ∑ c, lam c * n i c) = ∑ c, lam c * ∑ i, v i * n i c := by
    simp only [dotProduct, Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro i _; ring
  simp only
  rw [this, hdot, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum; intro c _
  have := Egs_le_config hH0 n v c
  nlinarith [hl0 c]

lemma le_lieb {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) {ρ : V → ℝ}
    (hρ : ρ ∈ DensDomain n) (v : V → ℝ) : Egs H0 n v - v ⬝ᵥ ρ ≤ lieb H0 n ρ :=
  le_csSup (lieb_bdd hH0 n hρ) ⟨v, rfl⟩

omit [DecidableEq C] [Fintype V] [Nonempty C] in
lemma dens_mem_domain (n : V → C → ℝ) {ψ : C → ℝ} (hn : ψ ⬝ᵥ ψ = 1) : dens n ψ ∈ DensDomain n := by
  refine ⟨fun c => ψ c ^ 2, ⟨fun c => sq_nonneg _, by simpa [dotProduct, sq] using hn⟩, ?_⟩
  funext i; simp [dens, mul_comm]

/-- **Lieb duality.** `E(v) ≤ F(ρ) + v·ρ` on the density domain, with equality at ground-state
densities. -/
theorem lieb_duality {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) (v : V → ℝ) :
    (∀ ρ ∈ DensDomain n, Egs H0 n v ≤ lieb H0 n ρ + v ⬝ᵥ ρ) ∧
    ∀ ψ, IsGroundState (hamN H0 n v) ψ → ψ ⬝ᵥ ψ = 1 →
      Egs H0 n v = lieb H0 n (dens n ψ) + v ⬝ᵥ dens n ψ := by
  refine ⟨fun ρ hρ => by linarith [le_lieb hH0 n hρ v], fun ψ hψ hn => ?_⟩
  have hdom := dens_mem_domain n hn
  have hE : Egs H0 n v = qf H0 ψ + v ⬝ᵥ dens n ψ := by
    unfold Egs
    rw [← qf_groundState_eq (hamN_isSymm hH0 n v) hψ hn, qf_hamN]
    simp [dotProduct]
  have hle : lieb H0 n (dens n ψ) ≤ qf H0 ψ := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨v', rfl⟩
    have := gsEnergy_le (hamN_isSymm hH0 n v') hn
    rw [qf_hamN] at this
    unfold Egs
    have hd : ∑ i, v' i * dens n ψ i = v' ⬝ᵥ dens n ψ := rfl
    linarith
  have hge := le_lieb hH0 n hdom v
  linarith

omit [DecidableEq C] [Fintype V] [Nonempty C] in
/-- The density domain is convex for any occupation map. -/
theorem convex_densDomain (n : V → C → ℝ) : Convex ℝ (DensDomain n) := by
  rintro ρ ⟨l1, ⟨h10, h11⟩, rfl⟩ ρ' ⟨l2, ⟨h20, h21⟩, rfl⟩ a b ha hb hab
  refine ⟨fun c => a * l1 c + b * l2 c,
    ⟨fun c => add_nonneg (mul_nonneg ha (h10 c)) (mul_nonneg hb (h20 c)), ?_⟩, ?_⟩
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, h11, h21, hab]
  · funext i; simp [Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

/-- **Convexity of Lieb's functional.** -/
theorem lieb_convexOn {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) (n : V → C → ℝ) :
    ConvexOn ℝ (DensDomain n) (lieb H0 n) := by
  refine ⟨convex_densDomain n, ?_⟩
  intro ρ hρ ρ' hρ' a b ha hb hab
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have h1 := le_lieb hH0 n hρ v
  have h2 := le_lieb hH0 n hρ' v
  simp only [smul_eq_mul]
  have hd : v ⬝ᵥ (a • ρ + b • ρ') = a * (v ⬝ᵥ ρ) + b * (v ⬝ᵥ ρ') := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hd]
  have : Egs H0 n v = a * Egs H0 n v + b * Egs H0 n v := by rw [← add_mul, hab, one_mul]
  nlinarith

end DFT
