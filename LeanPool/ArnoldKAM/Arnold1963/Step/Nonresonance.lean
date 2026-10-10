/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierParameter
public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.Parameters
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingTorus

/-!
Supporting results for the analytic Hamiltonian KAM construction.
-/

@[expose] public section
noncomputable section
open Set
namespace KamProject.Arnold1963

/-- Finite-cutoff lower bounds on all retained nonzero integer frequency pairings. -/
def FiniteNonresonant {n : ℕ} (ω : ComplexSpace n) (K N : ℝ) : Prop :=
  ∀ k ∈ lowModes n N, K / indexLength k ^ (n + 1) ≤ ‖indexPairing k ω‖

/-- The action subdomain satisfying the finite-cutoff nonresonance condition. -/
def nonresonantDomain {n : ℕ} (G : Set (ComplexSpace n))
    (ω : ComplexSpace n → ComplexSpace n) (K N : ℝ) : Set (ComplexSpace n) :=
  {p | p ∈ G ∧ FiniteNonresonant (ω p) K N}

theorem FiniteNonresonant.ne_zero {n : ℕ} {ω : ComplexSpace n} {K N : ℝ}
    (h : FiniteNonresonant ω K N) (hK : 0 < K) {k : FourierIndex n}
    (hk : k ∈ lowModes n N) : indexPairing k ω ≠ 0 := by
  have hk0 := (mem_lowModes.mp hk).1
  exact norm_pos_iff.mp ((div_pos hK (pow_pos hk0 _)).trans_le (h k hk))

@[simp] theorem indexLength_neg {n : ℕ} (k : FourierIndex n) :
    indexLength (-k) = indexLength k := by simp [indexLength]

theorem neg_mem_lowModes {n : ℕ} {k : FourierIndex n} {N : ℝ} :
    -k ∈ lowModes n N ↔ k ∈ lowModes n N := by simp

theorem indexPairing_conj {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) :
    indexPairing k (conjVec z) = star (indexPairing k z) := by
  simp [indexPairing, conjVec]

@[simp] theorem indexPairing_neg {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) :
    indexPairing (-k) z = -indexPairing k z := by simp [indexPairing, neg_mul]

theorem FiniteNonresonant.conj {n : ℕ} {ω : ComplexSpace n} {K N : ℝ}
    (h : FiniteNonresonant ω K N) : FiniteNonresonant (conjVec ω) K N := by
  intro k hk
  rw [indexPairing_conj, norm_star]
  exact h k hk

theorem nonresonantDomain_conj {n : ℕ} {G : Set (ComplexSpace n)}
    {ω : ComplexSpace n → ComplexSpace n} {K N : ℝ} (hG : ConjInvariant G)
    (hω : ∀ p ∈ G, ω (conjVec p) = conjVec (ω p)) :
    ConjInvariant (nonresonantDomain G ω K N) := by
  intro p hp
  refine ⟨hG p hp.1, ?_⟩
  rw [hω p hp.1]
  exact hp.2.conj

theorem analyticAt_indexPairing {n : ℕ} (k : FourierIndex n) (z : ComplexSpace n) :
    AnalyticAt ℂ (indexPairing k) z := by
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin n => ℂ) j).analyticAt z)

end KamProject.Arnold1963
