/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Development.Geometry.Foundations.AreaCertificateInputs

/-!
# Gerver cap area certificate

The fan shoelace sum can be checked one grid block at a time.
The kernel checks each subtotal before the integer bound is assembled.
-/

public section

namespace MovingSofa.GerverAreaCert

private def blockSum (summand : ℕ → ℤ) (start length : ℕ) : ℤ :=
  ((List.range' start length).map summand).sum

private theorem foldl_interval_lower (interval : ℕ → SI) (indices : List ℕ) (initial : SI) :
    (indices.foldl (fun acc index => SI.add acc (interval index)) initial).lo =
      initial.lo + (indices.map fun index => (interval index).lo).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons index indices ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    exact add_assoc _ _ _

private def capLower (index : ℕ) : ℤ := (crossZ index).lo

private theorem foldl_range_crossZ_lower (length : ℕ) :
    ((List.range length).foldl (fun acc index => SI.add acc (crossZ index)) SI.zero).lo =
      blockSum capLower 0 length := by
  unfold blockSum capLower
  rewrite [foldl_interval_lower, List.range_eq_range']
  exact zero_add _

private theorem capDoubledZ_fold :
    capDoubledZ = (List.range (fanCount - 1)).foldl
      (fun acc index => SI.add acc (crossZ index)) SI.zero := rfl

-- Project the fold equation after naming it to avoid evaluating the closed interval sum.
private theorem capDoubledZ_lower :
    capDoubledZ.lo = blockSum capLower 0 (fanCount - 1) :=
  (congrArg SI.lo capDoubledZ_fold).trans (foldl_range_crossZ_lower (fanCount - 1))

private theorem blockSum_append (summand : ℕ → ℤ) (start left right : ℕ) :
    blockSum summand start (left + right) =
      blockSum summand start left + blockSum summand (start + left) right := by
  unfold blockSum
  rw [← List.range'_append_1, List.map_append, List.sum_append]

private theorem blockSum_split (summand : ℕ → ℤ) :
    blockSum summand 0 639 =
      blockSum summand 0 64 + blockSum summand 64 64 + blockSum summand 128 64 +
      blockSum summand 192 64 + blockSum summand 256 64 + blockSum summand 320 64 +
      blockSum summand 384 64 + blockSum summand 448 64 + blockSum summand 512 64 +
      blockSum summand 576 63 := by
  rw [blockSum_append _ 0 64 575, blockSum_append _ 64 64 511,
    blockSum_append _ 128 64 447, blockSum_append _ 192 64 383,
    blockSum_append _ 256 64 319, blockSum_append _ 320 64 255,
    blockSum_append _ 384 64 191, blockSum_append _ 448 64 127,
    blockSum_append _ 512 64 63]
  simp only [Nat.reduceAdd, add_assoc]

private theorem capBlock0 : blockSum capLower 0 64 = -333692128541 := by
  decide +kernel

private theorem capBlock1 : blockSum capLower 64 64 = 2345195516565672560433008557893 := by
  decide +kernel

private theorem capBlock2 : blockSum capLower 128 64 = 457513910196354824145321987955 := by
  decide +kernel

private theorem capBlock3 : blockSum capLower 192 64 = 844609069416278788588291316528 := by
  decide +kernel

private theorem capBlock4 : blockSum capLower 256 64 = 20514898991741712193211264935 := by
  decide +kernel

private theorem capBlock5 : blockSum capLower 320 64 = 1633039680555141233969789230422 := by
  decide +kernel

private theorem capBlock6 : blockSum capLower 384 64 = 303430692394246802210481664679 := by
  decide +kernel

private theorem capBlock7 : blockSum capLower 448 64 = 57095350875586586163522922520 := by
  decide +kernel

private theorem capBlock8 : blockSum capLower 512 64 = 60504290736227028939875516284 := by
  decide +kernel

private theorem capBlock9 : blockSum capLower 576 63 = -126 := by
  decide +kernel

/-- The lower interval endpoint certifies the cap threshold. -/
theorem cap_bound_checked : 2 * 28609 * M ≤ 10000 * capDoubledZ.lo := by
  rewrite [capDoubledZ_lower, show fanCount - 1 = 639 from rfl, blockSum_split,
    capBlock0, capBlock1, capBlock2, capBlock3, capBlock4,
    capBlock5, capBlock6, capBlock7, capBlock8, capBlock9]
  norm_num [M]

end MovingSofa.GerverAreaCert
