/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SparseListConstruction
public import LeanPool.KLRandomness.SparseCandidateWeights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small support weight in the executable sparse-list output

The finite verifier's integer incidence inequalities and rational rank-failure
counts directly imply the deterministic support-weight bounds.  All sums and
counts retain list multiplicities.  The selected entry is an actual member of
the returned coded list; no reverse decoding into abstract candidates is needed.
-/

@[expose] public section

namespace Klr.SparseListWeights

open SparseListSearch SparseListCode SparseSearch
open scoped BigOperators

variable {M m r J : ℕ} {τ θ : ℚ} {L : CodeList}

/-- The actual pool support described by a coded entry's Boolean mask. -/
def support (M : ℕ) (a : Entry) : Finset (Fin M) := maskSet M a.1

/-- The total weight on the support of a coded entry. -/
def supportWeight (w : Fin M → ℝ) (a : Entry) : ℝ := ∑ i ∈ support M a, w i

theorem supportWeight_nonneg (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) (a : Entry) :
    0 ≤ supportWeight w a := Finset.sum_nonneg fun i _ => hw i

/-- List counts equal counts over the finite type of list positions. -/
theorem countP_eq_card_filter_get {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p =
      (Finset.univ.filter (fun j : Fin l.length => p (l.get j) = true)).card := by
  simpa only [List.ofFn_get] using countP_ofFn l.get p

/-- The sparse-support API counts the same occurrences as the executable checker. -/
theorem incidence_eq_countP (L : CodeList) (i : Fin M) :
    Sparse.incidence (fun j : Fin L.length => support M (L.get j)) i =
      L.countP (fun a => a.1.getD i.val false) := by
  classical
  rw [countP_eq_card_filter_get]
  unfold Sparse.incidence
  congr 1
  ext j
  simp [support]

/-- The verifier's denominator-free incidence inequality gives the real-valued
incidence bound needed for deterministic averaging. -/
theorem incidence_le_of_good (hL : Good M m r J τ θ L) (i : Fin M) :
    (Sparse.incidence (fun j : Fin L.length => support M (L.get j)) i : ℝ) ≤
      2 * ((m : ℝ) / M) * J := by
  rw [incidence_eq_countP]
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : (M : ℝ) * L.countP (fun a => a.1.getD i.val false) ≤
      2 * (m : ℝ) * J := by
    exact_mod_cast hL.2.2.1 i.val i.isLt
  calc
    _ ≤ (2 * (m : ℝ) * J) / M := (le_div_iff₀ hM).mpr (by nlinarith)
    _ = _ := by ring

/-- Average support weight in the actual checked code list. -/
theorem average_supportWeight_le (hL : Good M m r J τ θ L) (hJ : 0 < J)
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : ∑ i, (w i) ^ 2 ≤ C) :
    (∑ j : Fin L.length, supportWeight w (L.get j)) / J ≤
      (2 * ((m : ℝ) / M)) * Real.sqrt ((M : ℝ) * C) := by
  have hlen : 0 < L.length := by rw [hL.1]; exact hJ
  have : Nonempty (Fin L.length) := ⟨⟨0, hlen⟩⟩
  have hi : ∀ i, (Sparse.incidence (fun j : Fin L.length => support M (L.get j)) i : ℝ) ≤
      (2 * ((m : ℝ) / M)) * Fintype.card (Fin L.length) := by
    intro i
    simpa only [Fintype.card_fin, hL.1] using incidence_le_of_good hL i
  simpa only [supportWeight, Fintype.card_fin, hL.1] using
    Sparse.average_support_weights_le (fun j : Fin L.length => support M (L.get j))
      w (2 * ((m : ℝ) / M)) C hw (by positivity) hi hC

/-- A dense unread mask has a rank-preserving entry of small support weight
in every checked nonempty code list. -/
theorem exists_rank_good_small_weight (hL : Good M m r J τ θ L) (hJ : 0 < J)
    (hθ : θ < 1) (d : List Bool) (hd : d.length = M)
    (hdense : τ * (M : ℚ) ≤ (d.countP id : ℚ))
    (w : Fin M → ℝ) (C : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : ∑ i, (w i) ^ 2 ≤ C) :
    ∃ a ∈ L, maskedFullRank a.2 d = true ∧ supportWeight w a ≤
      ((2 * ((m : ℝ) / M)) / (1 - (θ : ℝ))) * Real.sqrt ((M : ℝ) * C) := by
  classical
  let G := {j : Fin L.length // maskedFullRank (L.get j).2 d = true}
  have hGcard : Fintype.card G = L.countP (fun a => maskedFullRank a.2 d) := by
    simpa only [G, Fintype.card_subtype] using
      (countP_eq_card_filter_get L (fun a => maskedFullRank a.2 d)).symm
  have hpartition : L.countP (fun a => !maskedFullRank a.2 d) + Fintype.card G = J := by
    rw [hGcard, ← hL.1]
    simpa [Nat.add_comm] using
      (List.length_eq_countP_add_countP (fun a : Entry => maskedFullRank a.2 d) (l := L)).symm
  have hpartition' : (L.countP (fun a => !maskedFullRank a.2 d) : ℝ) +
      Fintype.card G = J := by exact_mod_cast hpartition
  have hbad : (L.countP (fun a => !maskedFullRank a.2 d) : ℝ) ≤ (θ : ℝ) * J := by
    exact_mod_cast hL.2.2.2 d hd hdense
  have hgood : (1 - (θ : ℝ)) * J ≤ (Fintype.card G : ℝ) := by linarith
  have hθpos : 0 < 1 - (θ : ℝ) := by exact_mod_cast (sub_pos.mpr hθ)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hGpos : 0 < Fintype.card G := by
    have h := (mul_pos hθpos hJpos).trans_le hgood
    exact_mod_cast h
  have : Nonempty G := Fintype.card_pos_iff.mp hGpos
  have hδ : 0 ≤ 2 * ((m : ℝ) / M) := by positivity
  have hi : ∀ i, (Sparse.incidence (fun j : G => support M (L.get j.val)) i : ℝ) ≤
      ((2 * ((m : ℝ) / M)) / (1 - (θ : ℝ))) * Fintype.card G := by
    intro i
    have hi0 : (Sparse.incidence (fun j : G => support M (L.get j.val)) i : ℝ) ≤
        (Sparse.incidence (fun j : Fin L.length => support M (L.get j)) i : ℝ) := by
      exact_mod_cast SparseCandidateWeights.incidence_subtype_le
        (fun j : Fin L.length => support M (L.get j))
        (fun j => maskedFullRank (L.get j).2 d = true) i
    calc
      _ ≤ 2 * ((m : ℝ) / M) * J := hi0.trans (incidence_le_of_good hL i)
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hθpos).mpr
        nlinarith [mul_le_mul_of_nonneg_left hgood hδ]
  obtain ⟨j, hj⟩ := Sparse.exists_small_support (fun j : G => support M (L.get j.val))
    w ((2 * ((m : ℝ) / M)) / (1 - (θ : ℝ))) C hw
      (div_nonneg hδ hθpos.le) hi hC
  exact ⟨L.get j.val, List.get_mem L j.val, j.property,
    by simpa only [supportWeight, Fintype.card_fin] using hj⟩

/-- The choice theorem applies directly to every output of the actual partial-recursive
construction, with the paper's polynomial pool and support sizes. -/
theorem exists_rank_good_small_weight_of_construct {τ θ : ℚ} {r : ℕ} {L : CodeList}
    (hL : L ∈ SparseListConstruction.construct τ θ r) (hr : 0 < r) (hθ : θ < 1)
    (d : List Bool) (hd : d.length = SparseParameters.blockSize r)
    (hdense : τ * (SparseParameters.blockSize r : ℚ) ≤ (d.countP id : ℚ))
    (w : Fin (SparseParameters.blockSize r) → ℝ) (C : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : ∑ i, (w i) ^ 2 ≤ C) :
    ∃ a ∈ L, maskedFullRank a.2 d = true ∧ supportWeight w a ≤
      ((2 * ((SparseParameters.supportSize r : ℝ) / SparseParameters.blockSize r)) /
        (1 - (θ : ℝ))) * Real.sqrt ((SparseParameters.blockSize r : ℝ) * C) := by
  have hJ : 0 < SparseParameters.listSize r := by
    unfold SparseParameters.listSize SparseParameters.blockSize
    positivity
  exact exists_rank_good_small_weight (SparseListConstruction.construct_spec hL)
    hJ hθ d hd hdense w C hw hC

end Klr.SparseListWeights
