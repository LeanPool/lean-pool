/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.SampleConcentration
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn

/-!
# Boolean support masks and finite list counts

These exact identities connect Boolean list encodings used by the computable
sparse-list verifier to finite supports and the counts in the sampling theorem.
-/

@[expose] public section

namespace Klr.SparseListCode

variable {M J : ℕ}

/-- Count a Boolean predicate in a list generated from a finite index type. -/
theorem countP_ofFn {α : Type*} (f : Fin J → α) (p : α → Bool) :
    (List.ofFn f).countP p =
      (Finset.univ.filter (fun j => p (f j) = true)).card :=
  List.countP_ofFn f p

/-- The width-`M` Boolean membership mask of a finite pool subset. -/
def mask (D : Finset (Fin M)) : List Bool := List.ofFn (fun a => decide (a ∈ D))

@[simp] theorem length_mask (D : Finset (Fin M)) : (mask D).length = M := by
  simp [mask]

theorem getD_mask (D : Finset (Fin M)) (a : Fin M) :
    (mask D).getD a.val false = decide (a ∈ D) := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [mask]

/-- Counting true bits in the support mask recovers the exact support size. -/
@[simp] theorem countP_mask (D : Finset (Fin M)) : (mask D).countP id = D.card := by
  simp [mask]

/-- Decode the first `M` bits of a mask, with missing entries treated as false. -/
def maskSet (M : ℕ) (d : List Bool) : Finset (Fin M) :=
  Finset.univ.filter (fun a => d.getD a.val false = true)

@[simp] theorem mem_maskSet (M : ℕ) (d : List Bool) (a : Fin M) :
    a ∈ maskSet M d ↔ d.getD a.val false = true := by
  simp [maskSet]

/-- Encoding and then decoding a support is exact. -/
@[simp] theorem maskSet_mask (D : Finset (Fin M)) : maskSet M (mask D) = D := by
  ext a
  rw [mem_maskSet, getD_mask, decide_eq_true_eq]

/-- Decoding and then encoding a mask of the prescribed width is exact. -/
theorem mask_maskSet (M : ℕ) (d : List Bool) (hd : d.length = M) :
    mask (maskSet M d) = d := by
  apply List.ext_getElem (by simpa using hd.symm)
  intro i hi hi'
  have hiM : i < M := by simpa using hi
  have h := getD_mask (maskSet M d) (⟨i, hiM⟩ : Fin M)
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi',
    mem_maskSet, Bool.decide_eq_true] using h

/-- Decoding a mask of length `M` preserves its count of true bits. -/
theorem card_maskSet (M : ℕ) (d : List Bool) (hd : d.length = M) :
    (maskSet M d).card = d.countP id := by
  have h := countP_mask (maskSet M d)
  rw [mask_maskSet M d hd] at h
  exact h.symm

/-- The verifier's Boolean list count equals the actual sample count whenever
the Boolean predicate correctly recognizes the candidate event. -/
theorem countP_ofFn_eq_sampleCount {Ω α : Type*} (z : Fin J → Ω)
    (f : Ω → α) (p : α → Bool) (A : Set Ω)
    (h : ∀ c, p (f c) = true ↔ c ∈ A) :
    (List.ofFn (fun j => f (z j))).countP p = SampleConcentration.count A z := by
  classical
  rw [countP_ofFn]
  unfold SampleConcentration.count
  congr 1
  ext j
  simp [h]

end Klr.SparseListCode
