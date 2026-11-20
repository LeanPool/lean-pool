/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/

module

public import LeanPool.WordRepTensor.WindowChecks
public import Mathlib.Data.Fin.VecNotation

/-!
# Proofs of `MycielskiOddCycleNotWR` and `ExtMycielskiOddCycleNotWR`

(Written by Claude, 2026-09-28.) The window of column `i` of `mu n` is the map `winMap i`
from the seven window labels to the vertices. For `n ≥ 5` it is injective and its adjacency is
the window edge list; the chord condition then holds on every window, and the colours of the
states flip from each column to the next (`WRWindow`), which is impossible for odd `n`.
For `n = 3` the chord condition fails for every orientation of `mu 3`.
-/

@[expose] public section

namespace WordRepTensor

open SimpleGraph

section Window

variable {n : ℕ} [NeZero n]

theorem cyc_facts (hn : 5 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i + 1) ∧ (cycleGraph n).Adj (i + 1) (i + 1 + 1) ∧
      ¬ (cycleGraph n).Adj i (i + 1 + 1) ∧ i ≠ i + 1 ∧ i + 1 ≠ i + 1 + 1 ∧ i ≠ i + 1 + 1 := by
  have hi := i.isLt
  have hi1 := (i + 1).isLt
  have hi2 := (i + 1 + 1).isLt
  have h1 := fin_val_add_one (by omega : 2 ≤ n) i
  have h2 := fin_val_add_one (by omega : 2 ≤ n) (i + 1)
  have a1 : i.val + 1 < n → (i + 1).val = i.val + 1 := fun h => by rw [h1]; simp [h]
  have b1 : ¬ i.val + 1 < n → (i + 1).val = 0 := fun h => by rw [h1]; simp [h]
  have a2 : (i + 1).val + 1 < n → (i + 1 + 1).val = (i + 1).val + 1 := fun h => by
    rw [h2]; simp [h]
  have b2 : ¬ (i + 1).val + 1 < n → (i + 1 + 1).val = 0 := fun h => by rw [h2]; simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cyc_adj_iff' (by omega)]
    omega
  · rw [cyc_adj_iff' (by omega)]
    omega
  · rw [cyc_adj_iff' (by omega)]
    omega
  · intro h
    have := congrArg Fin.val h
    omega
  · intro h
    have := congrArg Fin.val h
    omega
  · intro h
    have := congrArg Fin.val h
    omega

/-- The seven vertices of the window of column `i`. -/
def winMap (i : Fin n) : Fin 7 → (Fin n ⊕ Fin n ⊕ Unit) :=
  ![.inr (.inr ()), .inl i, .inl (i + 1), .inl (i + 1 + 1), .inr (.inl i), .inr (.inl (i + 1)),
    .inr (.inl (i + 1 + 1))]

theorem winMap_inj (hn : 5 ≤ n) (i : Fin n) : Function.Injective (winMap i) := by
  obtain ⟨_, _, _, d01, d12, d02⟩ := cyc_facts hn i
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [winMap, Ne.symm d01, Ne.symm d12, Ne.symm d02]

theorem winMap_adj_mu (hn : 5 ≤ n) (i : Fin n) (x y : Fin 7) :
    (mu n).Adj (winMap i x) (winMap i y) ↔ wadjOf winMuEdges x y = true := by
  obtain ⟨h01, h12, h02, d01, d12, d02⟩ := cyc_facts hn i
  have h20 : ¬ (cycleGraph n).Adj (i + 1 + 1) i := fun h => h02 h.symm
  fin_cases x <;> fin_cases y <;>
    simp (config := { decide := true }) [winMap, mu, myc_adj_inl_inl, myc_adj_inl_sh,
      myc_adj_sh_inl, myc_not_adj_inl_root, myc_not_adj_root_inl, myc_not_adj_sh_sh,
      myc_adj_sh_root, myc_adj_root_sh, h01, h12, h01.symm, h12.symm, h02, h20]

theorem winMap_adj_ext (hn : 5 ≤ n) (i : Fin n) (x y : Fin 7) :
    (muExt n).Adj (winMap i x) (winMap i y) ↔ wadjOf winExtEdges x y = true := by
  obtain ⟨h01, h12, h02, d01, d12, d02⟩ := cyc_facts hn i
  have h20 : ¬ (cycleGraph n).Adj (i + 1 + 1) i := fun h => h02 h.symm
  fin_cases x <;> fin_cases y <;>
    simp (config := { decide := true }) [winMap, muExt, ext_adj_inl_inl, ext_adj_inl_sh,
      ext_adj_sh_inl, ext_not_adj_inl_root, ext_not_adj_root_inl, ext_not_adj_sh_sh,
      ext_adj_sh_root, ext_adj_root_sh, h01, h12, h01.symm, h12.symm, h02, h20, d01, d12, d02,
      Ne.symm d01, Ne.symm d12, Ne.symm d02]

theorem state_shift_mu (w : List (Fin n ⊕ Fin n ⊕ Unit)) (i : Fin n) :
    stateOf (orient w (winMap i) winMuEdges) winMuS1 =
      stateOf (orient w (winMap (i + 1)) winMuEdges) winMuS0 := rfl

theorem mu_not_wr_of_ge5 (hn : 5 ≤ n) (hodd : n % 2 = 1) : ¬ WordRepresentable (mu n) := by
  rintro ⟨w, hw⟩
  refine no_flip_cycle hodd
    (fun i => colOf winMuCol (stateOf (orient w (winMap i) winMuEdges) winMuS0)) ?_
  intro i
  have hc := cond3_of_word hw (winMap i) (winMap_inj hn i) winMuEdges
    (winMap_adj_mu hn i) winMuPats winMu_valid
  have hf := flip_of_flipOK winMu_flip (orient w (winMap i) winMuEdges)
    (orient_out w (winMap i) winMuEdges) hc
  rw [state_shift_mu] at hf
  exact hf

theorem ext_not_wr_of_ge5 (hn : 5 ≤ n) (hodd : n % 2 = 1) : ¬ WordRepresentable (muExt n) := by
  rintro ⟨w, hw⟩
  refine no_flip_cycle hodd
    (fun i => colOf winMuCol (stateOf (orient w (winMap i) winMuEdges) winMuS0)) ?_
  intro i
  have hflip := extended_window_colour_flip hw (winMap i) (winMap_inj hn i) (winMap_adj_ext hn i)
  rw [state_shift_mu] at hflip
  exact hflip

end Window

/-! ## The seven-vertex case `n = 3` -/

/-- Label the root, top row and shadows of the three-cycle Mycielskian. -/
def mu3Map : Fin 7 → (Fin 3 ⊕ Fin 3 ⊕ Unit) :=
  ![.inr (.inr ()), .inl 0, .inl 1, .inl 2, .inr (.inl 0), .inr (.inl 1), .inr (.inl 2)]

theorem mu3Map_inj : Function.Injective mu3Map := by decide

theorem mu3Map_adj_mu : ∀ x y, (mu 3).Adj (mu3Map x) (mu3Map y) ↔ wadjOf mu3Edges x y = true := by
  decide

theorem mu3Map_adj_ext :
    ∀ x y, (muExt 3).Adj (mu3Map x) (mu3Map y) ↔ wadjOf mu3Edges x y = true := by
  decide

theorem mu3_not_wr : ¬ WordRepresentable (mu 3) := by
  rintro ⟨w, hw⟩
  have hc := cond3_of_word hw mu3Map mu3Map_inj mu3Edges mu3Map_adj_mu mu3Pats mu3_valid
  have hn := none_of_noneOK mu3_none (orient w mu3Map mu3Edges) (orient_out w mu3Map mu3Edges)
  rw [hc] at hn
  exact Bool.noConfusion hn

theorem ext3_not_wr : ¬ WordRepresentable (muExt 3) := by
  rintro ⟨w, hw⟩
  have hc := cond3_of_word hw mu3Map mu3Map_inj mu3Edges mu3Map_adj_ext mu3Pats mu3_valid
  have hn := none_of_noneOK mu3_none (orient w mu3Map mu3Edges) (orient_out w mu3Map mu3Edges)
  rw [hc] at hn
  exact Bool.noConfusion hn

/-! ## The frozen statements -/

theorem mycielskiOddCycleNotWR :
  ∀ k : ℕ, 1 ≤ k → ¬ WordRepresentable (mu (2 * k + 1)) := by
  intro k hk
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    exact mu3_not_wr
  · exact mu_not_wr_of_ge5 (by omega) (by omega)

theorem extMycielskiOddCycleNotWR :
  ∀ k : ℕ, 1 ≤ k → ¬ WordRepresentable (muExt (2 * k + 1)) := by
  intro k hk
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    exact ext3_not_wr
  · exact ext_not_wr_of_ge5 (by omega) (by omega)

end WordRepTensor
