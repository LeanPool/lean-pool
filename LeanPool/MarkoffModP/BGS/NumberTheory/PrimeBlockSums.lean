/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.Prime -- shake: keep

/-!
# Shared prime-block sums for the explicit divisor bounds

Evaluate the prime indices independently of the penalty function. The tenth- and
weighted twentieth-moment estimates can then reuse the same primality certificates
and reduce only their short sums of penalties.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- The prime-index sum in the block `[0, 64)`. -/
theorem sum_prime_block_0 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (0 * 64 + p) then f (0 * 64 + p) else 0) =
      f 2 + f 3 + f 5 + f 7 + f 11 + f 13 + f 17 + f 19 + f 23 + f 29 + f 31 + f 37 +
        f 41 + f 43 + f 47 + f 53 + f 59 + f 61 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[64, 128)`. -/
theorem sum_prime_block_1 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (1 * 64 + p) then f (1 * 64 + p) else 0) =
      f 67 + f 71 + f 73 + f 79 + f 83 + f 89 + f 97 + f 101 + f 103 + f 107 +
        f 109 + f 113 + f 127 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[128, 192)`. -/
theorem sum_prime_block_2 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (2 * 64 + p) then f (2 * 64 + p) else 0) =
      f 131 + f 137 + f 139 + f 149 + f 151 + f 157 + f 163 + f 167 + f 173 + f 179 +
        f 181 + f 191 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[192, 256)`. -/
theorem sum_prime_block_3 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (3 * 64 + p) then f (3 * 64 + p) else 0) =
      f 193 + f 197 + f 199 + f 211 + f 223 + f 227 + f 229 + f 233 + f 239 + f 241 +
        f 251 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[256, 320)`. -/
theorem sum_prime_block_4 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (4 * 64 + p) then f (4 * 64 + p) else 0) =
      f 257 + f 263 + f 269 + f 271 + f 277 + f 281 + f 283 + f 293 + f 307 + f 311 +
        f 313 + f 317 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[320, 384)`. -/
theorem sum_prime_block_5 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (5 * 64 + p) then f (5 * 64 + p) else 0) =
      f 331 + f 337 + f 347 + f 349 + f 353 + f 359 + f 367 + f 373 + f 379 + f 383 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[384, 448)`. -/
theorem sum_prime_block_6 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (6 * 64 + p) then f (6 * 64 + p) else 0) =
      f 389 + f 397 + f 401 + f 409 + f 419 + f 421 + f 431 + f 433 + f 439 + f 443 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[448, 512)`. -/
theorem sum_prime_block_7 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (7 * 64 + p) then f (7 * 64 + p) else 0) =
      f 449 + f 457 + f 461 + f 463 + f 467 + f 479 + f 487 + f 491 + f 499 + f 503 +
        f 509 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[512, 576)`. -/
theorem sum_prime_block_8 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (8 * 64 + p) then f (8 * 64 + p) else 0) =
      f 521 + f 523 + f 541 + f 547 + f 557 + f 563 + f 569 + f 571 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[576, 640)`. -/
theorem sum_prime_block_9 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (9 * 64 + p) then f (9 * 64 + p) else 0) =
      f 577 + f 587 + f 593 + f 599 + f 601 + f 607 + f 613 + f 617 + f 619 + f 631 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[640, 704)`. -/
theorem sum_prime_block_10 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (10 * 64 + p) then f (10 * 64 + p) else 0) =
      f 641 + f 643 + f 647 + f 653 + f 659 + f 661 + f 673 + f 677 + f 683 + f 691 +
        f 701 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[704, 768)`. -/
theorem sum_prime_block_11 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (11 * 64 + p) then f (11 * 64 + p) else 0) =
      f 709 + f 719 + f 727 + f 733 + f 739 + f 743 + f 751 + f 757 + f 761 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[768, 832)`. -/
theorem sum_prime_block_12 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (12 * 64 + p) then f (12 * 64 + p) else 0) =
      f 769 + f 773 + f 787 + f 797 + f 809 + f 811 + f 821 + f 823 + f 827 + f 829 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[832, 896)`. -/
theorem sum_prime_block_13 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (13 * 64 + p) then f (13 * 64 + p) else 0) =
      f 839 + f 853 + f 857 + f 859 + f 863 + f 877 + f 881 + f 883 + f 887 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[896, 960)`. -/
theorem sum_prime_block_14 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (14 * 64 + p) then f (14 * 64 + p) else 0) =
      f 907 + f 911 + f 919 + f 929 + f 937 + f 941 + f 947 + f 953 := by
  norm_num [Finset.sum_range_succ]

/-- The prime-index sum in the block `[960, 1024)`. -/
theorem sum_prime_block_15 (f : ℕ → ℕ) :
    (∑ p ∈ Finset.range 64, if Nat.Prime (15 * 64 + p) then f (15 * 64 + p) else 0) =
      f 967 + f 971 + f 977 + f 983 + f 991 + f 997 + f 1009 + f 1013 + f 1019 +
        f 1021 := by
  norm_num [Finset.sum_range_succ]

end BGS.NumberTheory
