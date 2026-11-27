/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListCodeBridge
public import LeanPool.KLRandomness.SparseListSearchEffective

/-!
# Effective sparse rank-preserving lists

The actual partial-recursive exhaustive search, specialized to the polynomial
parameters of Lemma 4, halts for every sufficiently large rank. Every returned
finite list meets the sparse incidence and simultaneous rank-preservation
requirements. Both effectiveness and eventual termination are proved.
-/

@[expose] public section

namespace Klr.SparseListConstruction

open SparseListSearch

/-- The paper's parameter choice, with the rational thresholds fixed. -/
def parameters (τ θ : ℚ) (r : ℕ) : Parameters :=
  (SparseParameters.blockSize r, SparseParameters.supportSize r, r,
    SparseParameters.listSize r, τ, θ)

theorem computable_pow_const (k : ℕ) : Computable (fun r : ℕ => r ^ k) := by
  induction k with
  | zero => simpa using (Computable.const (1 : ℕ) : Computable (fun _ : ℕ => 1))
  | succ k ih =>
    have h := Primrec.nat_mul.to_comp.comp ih Computable.id
    exact h.of_eq fun r => (pow_succ r k).symm

theorem computable_parameters (τ θ : ℚ) : Computable (parameters τ θ) := by
  have hM := computable_pow_const 8
  have hm := computable_pow_const 2
  have hJ := (computable_pow_const 3).comp hM
  have hc := hM.pair (hm.pair (Computable.id.pair
    (hJ.pair ((Computable.const τ).pair (Computable.const θ)))))
  exact hc.of_eq fun _ => rfl

/-- The effective candidate-list construction. Smaller ranks may diverge. -/
def construct (τ θ : ℚ) (r : ℕ) : Part CodeList := search (parameters τ θ r)

theorem partrec_construct (τ θ : ℚ) : Partrec (construct τ θ) :=
  partrec_search.comp (computable_parameters τ θ)

/-- Every output has the prescribed size, support cardinalities, full-rank
matrices, sparse incidences, and rank preservation for every dense unread set. -/
theorem construct_spec {τ θ : ℚ} {r : ℕ} {L : CodeList} (hL : L ∈ construct τ θ r) :
    Good (SparseParameters.blockSize r) (SparseParameters.supportSize r)
      r (SparseParameters.listSize r) τ θ L := search_spec hL

/-- The effective part of Lemma 4: for fixed positive rational parameters,
the actual list-producing computation halts at every sufficiently large rank. -/
theorem eventually_construct_halts (τ θ : ℚ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in Filter.atTop, (construct τ θ r).Dom := by
  filter_upwards [SparseListCode.eventually_exists_goodCode τ θ hτ hθ] with r hr
  exact (search_dom_iff (parameters τ θ r)).mpr hr

/-- Eventual termination together with the complete specification of the returned list. -/
theorem eventually_construct_good (τ θ : ℚ) (hτ : 0 < τ) (hθ : 0 < θ) :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ L : CodeList, L ∈ construct τ θ r ∧
      Good (SparseParameters.blockSize r) (SparseParameters.supportSize r)
        r (SparseParameters.listSize r) τ θ L := by
  filter_upwards [eventually_construct_halts τ θ hτ hθ] with r hr
  obtain ⟨L, hL⟩ := Part.dom_iff_mem.mp hr
  exact ⟨L, hL, construct_spec hL⟩

/-- One actual Mathlib program implements the construction at the fixed
rational thresholds. No bound on its fixed header size is needed here. -/
theorem exists_construct_program (τ θ : ℚ) : ∃ e : Nat.Partrec.Code, ∀ r : ℕ,
    e.eval r = (construct τ θ r).map Encodable.encode := by
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp (partrec_construct τ θ)
  refine ⟨e, fun r => ?_⟩
  rw [he]
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some]

end Klr.SparseListConstruction
