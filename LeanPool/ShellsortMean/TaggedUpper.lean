/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.ChainBitCounts
public import LeanPool.ShellsortMean.OwnerSlice
public import LeanPool.ShellsortMean.TaggedDisplacement

/-! Uniform two-pass footrule bounds from tagged threshold displacement. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Reindexing actual original positions into their actual finite h-chains
preserves the complete independent product law, including short boundary chains. -/
theorem fullBits_mean_chainBits (n h : ℕ) (hh : 0 < h) (t : ℝ)
    (F : (∀ s : Fin h, Fin (sourceTrialLength (n / h) (n % h) s.val) → Bool) → ℝ) :
    mean (productWeight (fun _ : Fin n => bernoulliWeight t)) (fun z => F (chainBits hh z)) =
      mean (conditionalSourceWeight h (n / h) (n % h) t) F := by
  apply mean_transport_equiv (positionBitsEquiv n h hh) _ _ F
  intro z
  change (∏ a : Fin n, bernoulliWeight t (z a)) =
    ∏ s : Fin h, ∏ v : Fin (sourceTrialLength (n / h) (n % h) s.val),
      bernoulliWeight t (chainBits hh z s v)
  calc
    _ = ∏ c : ChainCoordinate n h,
        bernoulliWeight t (z ((positionChainEquiv n h hh).symm c)) :=
      ((positionChainEquiv n h hh).symm.prod_comp _).symm
    _ = _ := Fintype.prod_sigma _

/-- The exact subset displacement is the conditional source expression with
its owner count computed from the actual owner chain, excluding the tag bit. -/
theorem fullBits_displacement_eq_source {n h : ℕ} (hh : 0 < h) (g : ℕ)
    (i : Fin n) (z : Fin n → Bool) :
    taggedSubsetDisplacement h g i (fullBitsSubset i z) =
      conditionalSourceDisplacement h g (n / h) (n % h)
        (((positionChainEquiv n h hh) i).1)
        (ownerBitCount (((positionChainEquiv n h hh) i).2)
          (chainBits hh z (((positionChainEquiv n h hh) i).1)))
        (chainBits hh z) := by
  let owner := ((positionChainEquiv n h hh) i).1
  let o := ((positionChainEquiv n h hh) i).2
  let y := ownerBitCount o (chainBits hh z owner)
  have howner : owner.val = i.val % h := rfl
  have hy : chainLowerCount (fullBitsSubset i z) h owner.val = y :=
    owner_fullBits_chain_count hh i z
  have hj : taggedSubsetTarget h g i (fullBitsSubset i z) = (owner.val + h * y) % g := by
    unfold taggedSubsetTarget
    rw [← howner, hy]
  change taggedSubsetDisplacement h g i (fullBitsSubset i z) =
    conditionalSourceDisplacement h g (n / h) (n % h) owner y (chainBits hh z)
  unfold taggedSubsetDisplacement conditionalSourceDisplacement
  rw [hj, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  unfold conditionalSourceResidual
  by_cases hs : s = owner
  · simp only [hs, ite_true, hy]
  · have hsval : s.val ≠ i.val % h := by
      intro he
      exact hs (Fin.ext (he.trans howner.symm))
    rw [nonowner_fullBits_chain_count hh i z s hsval]
    simp only [hs, ite_false]

/-- Uniform L1 bound under independent bits at the original positions.
The tag bit is ignored, and the owner slice is averaged without conditioning quotients. -/
theorem fullBits_tagged_absMean_bound {n : ℕ} (h g : ℕ) (hh : 0 < h)
    (hg : 0 < g) (hc : Nat.Coprime h g) (i : Fin n) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    mean (productWeight (fun _ : Fin n => bernoulliWeight t))
      (fun z => |taggedSubsetDisplacement h g i (fullBitsSubset i z)|) ≤
      ((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2 := by
  simp_rw [fullBits_displacement_eq_source hh g i]
  rw [fullBits_mean_chainBits n h hh t
    (fun x => |conditionalSourceDisplacement h g (n / h) (n % h)
      (((positionChainEquiv n h hh) i).1)
      (ownerBitCount (((positionChainEquiv n h hh) i).2)
        (x (((positionChainEquiv n h hh) i).1))) x|)]
  exact owner_selected_source_absMean_bound h g (n / h) (n % h) t
    (((positionChainEquiv n h hh) i).1)
    (ownerBitCount (((positionChainEquiv n h hh) i).2))
    ht (Nat.le_of_lt (Nat.mod_lt n hh)) hg hc

/-- Genuine uniform-permutation bound for the key initially occupying position i. -/
theorem uniform_twoPass_tag_abs_bound {n : ℕ} (h g : ℕ) (hh : 0 < h)
    (hg : 0 < g) (hc : Nat.Coprime h g) (i : Fin n) :
    uniformAverage (fun p : RankPlacement n =>
      |((gapSort (gapSort p h) g (p.symm i)).val : ℝ) - ((p.symm i).val : ℝ)|) ≤
      ((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2 := by
  simp_rw [actual_tagged_displacement_eq _ h g hh hg i]
  apply uniform_tagged_mean_le_of_full_bernoulli_bound i
    (fun B => |taggedSubsetDisplacement h g i B.val|)
  intro t ht0 ht1
  exact fullBits_tagged_absMean_bound h g hh hg hc i t ⟨ht0, ht1⟩

/-- End-to-end finite displacement theorem: uniform random permutations and the
actual two local sorting transitions, with no distribution or moment hypothesis. -/
theorem uniform_twoPass_footrule_bound (n h g : ℕ) (hh : 0 < h)
    (hg : 0 < g) (hc : Nat.Coprime h g) :
    uniformAverage (n := n) (fun p => footrule (gapSort (gapSort p h) g)) ≤
      (n : ℝ) * (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) := by
  rw [uniform_twoPass_footrule_by_original_positions]
  calc
    _ ≤ ∑ _i : Fin n, (((g : ℝ) - 1) * Real.sqrt ((h : ℝ) + 3) / 2) :=
      Finset.sum_le_sum (fun i _ => uniform_twoPass_tag_abs_bound h g hh hg hc i)
    _ = _ := by simp

end Shellsort
end
