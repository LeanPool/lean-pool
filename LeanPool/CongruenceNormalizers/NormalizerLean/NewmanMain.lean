/-
Copyright (c) 2026 Filip Najman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Najman
-/
module

public import LeanPool.CongruenceNormalizers.NormalizerLean.NewmanFacts

/-!
# Newman's theorem for Γ₀(N)

The primitive representative and local valuation argument is proved for arbitrary subgroups in
`NormalizerDelta/NewmanGen`. Here it is instantiated with `newmanData_gamma0`, which supplies
Γ₀(N)'s lattice, unipotents and valuation witnesses. The existing specialized local and final
theorems retain their statements as wrappers around that shared argument.
-/

@[expose] public section

open Matrix MatrixGroups

namespace CongruenceNormalizers

noncomputable section

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
  exact local_conclusionG (newmanData_gamma0 N) hgN hg hginv he hprim hp

theorem newman' {N : ℕ} [NeZero N] {g : SL(2, ℝ)} (hg : g ∈ Norm0 N) : IsNewmanForm N g := by
  exact newmanG (newmanData_gamma0 N) hg

end

end CongruenceNormalizers
