/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorBall

/-!
# Integration by parts for two tuples differing in one slot

The Bedford–Taylor integration-by-parts identity of `BedfordTaylorStepP` pairs a
smooth test `φ` against the mixed limit of a tuple by moving `φ` into the last
slot: the resulting measures carry `φ + C‖z‖²` and `‖z‖²` in that slot and do
not depend on the tuple's own function there. Consequently two tuples that
differ only in the last slot have mixed limits whose test integrals differ by an
explicit pairing of the two slot functions against those fixed measures.

This is the local form of `∫ ddᶜ(a - b) ∧ T = 0` used in the compact
total-mass argument: the right-hand side is linear in the slot function, and on
a compact manifold a partition of unity makes the corresponding sum telescope.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- The unweighted convergence claim holds at every level. -/
theorem pClaim_of_le (q : ℕ) : PClaim n q := by
  induction q with
  | zero => exact pClaim_zero
  | succ q ih => exact pClaim_succ ih (wClaim_of_pClaim ih)

/-- Admissible families for a tuple stay admissible after putting a smooth
positive semidefinite function in one slot. -/
theorem IsAdmissible.update_smoothPsd {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (i₀ : Fin n) {a : ComplexModel n → ℝ}
    (ha : IsSmoothPsdOn U a) :
    IsAdmissible n U (Function.update u i₀ a) (Function.update F i₀ fun _ ↦ a) := by
  classical
  refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i = i₀
  · subst h; simpa using isDecApprox_const ha
  · simpa [Function.update_of_ne h] using hF.1 i

open scoped Distributions in
/-- **Integration by parts in the last slot.** Two tuples differing only in the
last slot have mixed limits whose integrals against a smooth test differ by the
pairing of the two slot functions against the fixed measures `μ₁`, `μ₂`. The
data are inputs, so the identity can be summed over a family of tests. -/
theorem integral_sub_eq_ibp {U : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {i₀ : Fin n} (hlast : (i₀ : ℕ) + 1 = n)
    {a b : ComplexModel n → ℝ} {μa μb : Measure (ComplexModel n)}
    (hμa : ∀ F, IsAdmissible n U (Function.update v i₀ a) F → TendstoMixed U F μa)
    (hμb : ∀ F, IsAdmissible n U (Function.update v i₀ b) F → TendstoMixed U F μb)
    (hexa : ∃ F, IsAdmissible n U (Function.update v i₀ a) F)
    (hexb : ∃ F, IsAdmissible n U (Function.update v i₀ b) F)
    {φ : ComplexModel n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U)
    {C : ℝ} (hC : IsSmoothPsdOn ⊤ fun z ↦ φ z + C * ‖z‖ ^ 2)
    (χ : 𝓓(U, ℝ)) (hχ1 : ∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1)
    {μ₁ μ₂ : Measure (ComplexModel n)}
    (h1c : μ₁ (U : Set (ComplexModel n))ᶜ = 0)
    (h1f : ∀ K, IsCompact K → K ⊆ U → μ₁ K < ⊤)
    (h1P : ∀ F, IsAdmissible (i₀ : ℕ) U
      (Function.update v i₀ fun z ↦ φ z + C * ‖z‖ ^ 2) F → TendstoMixed U F μ₁)
    (h2c : μ₂ (U : Set (ComplexModel n))ᶜ = 0)
    (h2f : ∀ K, IsCompact K → K ⊆ U → μ₂ K < ⊤)
    (h2P : ∀ F, IsAdmissible (i₀ : ℕ) U
      (Function.update v i₀ fun z : ComplexModel n ↦ ‖z‖ ^ 2) F → TendstoMixed U F μ₂) :
    (∫ z, φ z ∂μa) - ∫ z, φ z ∂μb =
      ((∫ z, χ z * a z ∂μ₁) - ∫ z, χ z * b z ∂μ₁) -
        C * ((∫ z, χ z * a z ∂μ₂) - ∫ z, χ z * b z ∂μ₂) := by
  classical
  set q : ℕ := (i₀ : ℕ) with hq_def
  have hq : q < n := by omega
  have hi : (⟨q, hq⟩ : Fin n) = i₀ := Fin.ext rfl
  have hW : WClaim n q := wClaim_of_pClaim (pClaim_of_le q)
  have hupd (c : ComplexModel n → ℝ) :
      Function.update (Function.update v i₀ a) ⟨q, hq⟩ c = Function.update v i₀ c := by
    rw [hi, Function.update_idem]
  have hupdb (c : ComplexModel n → ℝ) :
      Function.update (Function.update v i₀ b) ⟨q, hq⟩ c = Function.update v i₀ c := by
    rw [hi, Function.update_idem]
  obtain ⟨Fa, hFa⟩ := hexa
  obtain ⟨Fb, hFb⟩ := hexb
  have hFa' : IsAdmissible (q + 1) U (Function.update v i₀ a) Fa := by
    rw [show q + 1 = n from hlast]; exact hFa
  have hFb' : IsAdmissible (q + 1) U (Function.update v i₀ b) Fb := by
    rw [show q + 1 = n from hlast]; exact hFb
  have hlima := tendsto_smoothTest_ibp hW hq (Function.update v i₀ a) hφ hφc hφU hC χ hχ1
    h1c h1f (by rw [hupd]; exact h1P) h2c h2f (by rw [hupd]; exact h2P) Fa hFa'
  have hlimb := tendsto_smoothTest_ibp hW hq (Function.update v i₀ b) hφ hφc hφU hC χ hχ1
    h1c h1f (by rw [hupdb]; exact h1P) h2c h2f (by rw [hupdb]; exact h2P) Fb hFb'
  have hslota : (Function.update v i₀ a) ⟨q, hq⟩ = a := by rw [hi]; simp
  have hslotb : (Function.update v i₀ b) ⟨q, hq⟩ = b := by rw [hi]; simp
  rw [hslota] at hlima
  rw [hslotb] at hlimb
  have ea := tendsto_nhds_unique (hμa Fa hFa φ hφ.continuous hφc hφU) hlima
  have eb := tendsto_nhds_unique (hμb Fb hFb φ hφ.continuous hφc hφU) hlimb
  rw [ea, eb]
  ring

/-! ## Slot permutation

The integration-by-parts comparison above moves the compared slot into the last
position, because the Bedford–Taylor recursion is built on the last slot. The
mixed density is a symmetric function of the slots, so this is no restriction:
the whole tuple may be permuted first. -/

/-- A top-level admissible family stays admissible after permuting the slots.
The constancy clause is vacuous at level `n`. -/
theorem IsAdmissible.comp_perm {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (τ : Equiv.Perm (Fin n)) :
    IsAdmissible n U (fun i => u (τ i)) (fun i => F (τ i)) :=
  ⟨fun i => hF.1 (τ i), fun i hi => absurd i.isLt (not_lt.mpr hi)⟩

/-- Weak convergence of the mixed densities is symmetric in the slots. -/
theorem TendstoMixed.comp_perm {U : Opens (ComplexModel n)}
    {F : Fin n → ℕ → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (h : TendstoMixed U F μ) (τ : Equiv.Perm (Fin n)) :
    TendstoMixed U (fun i => F (τ i)) μ := by
  intro φ hφ hφc hφU
  have hd : ∀ k, mixedDensity (fun i => F (τ i) k) = mixedDensity (fun i => F i k) :=
    fun k => funext fun z => mixedDensity_perm (fun i => F i k) τ z
  simpa only [hd] using h φ hφ hφc hφU

/-- **The mixed limit of a tuple is a symmetric function of the tuple.** A
measure characterized as the limit of every admissible family for `u` is also
the limit of every admissible family for any permutation of `u`. -/
theorem tendstoMixed_comp_perm {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ) (τ : Equiv.Perm (Fin n)) :
    ∀ F, IsAdmissible n U (fun i => u (τ i)) F → TendstoMixed U F μ := by
  intro F hF
  have hF' : IsAdmissible n U u (fun i => F (τ.symm i)) := by
    refine ⟨fun i => ?_, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
    simpa using hF.1 (τ.symm i)
  simpa using (hμ _ hF').comp_perm τ

theorem exists_isAdmissible_comp_perm {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (h : ∃ F, IsAdmissible n U u F)
    (τ : Equiv.Perm (Fin n)) : ∃ F, IsAdmissible n U (fun i => u (τ i)) F := by
  obtain ⟨F, hF⟩ := h
  exact ⟨fun i => F (τ i), hF.comp_perm τ⟩

/-- Updating one slot commutes with permuting the slots. -/
theorem update_comp_perm {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    (a : ComplexModel n → ℝ) (τ : Equiv.Perm (Fin n)) :
    (fun i => Function.update u i₀ a (τ i)) =
      Function.update (fun i => u (τ i)) (τ.symm i₀) a := by
  simpa only [τ.apply_symm_apply, Function.comp_def] using
    Function.update_comp_eq_of_injective u τ.injective (τ.symm i₀) a

/-- The last slot of a nonempty tuple, named by one of its members. -/
def lastSlot {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1, Nat.sub_lt i.pos Nat.one_pos⟩

theorem lastSlot_val_succ {n : ℕ} (i : Fin n) : (lastSlot i : ℕ) + 1 = n :=
  Nat.succ_pred_eq_of_pos i.pos

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
