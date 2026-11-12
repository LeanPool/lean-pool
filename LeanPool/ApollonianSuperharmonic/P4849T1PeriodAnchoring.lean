/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Finset.Nat

-- [TABLET NODE: P4849T1PeriodAnchoring]

/-!
# P4849T1PeriodAnchoring

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4849T1PeriodAnchoring (g : IntegerLatticeFunction)
    (u v : GaussianInt) (R : Finset GaussianInt)
    (hres : ∀ z, ∃ r ∈ R, ∃ a b : ℤ, z = r + a • u + b • v)
    (hper : ∀ a b : ℤ, ∀ x,
      FourNeighborLaplacian g (x + a • u + b • v) = FourNeighborLaplacian g x)
    (hfamily : ∀ N : ℕ, ∃ C : Set GaussianInt,
      FourNeighborConnected C ∧
      (∀ x, FourNeighborLaplacian
        (fun y => g y + Set.indicator C (fun _ => (1 : ℤ)) y) x ≤ 1) ∧
      ∃ z a : GaussianInt, z ∉ C ∧ a ∈ C ∧ FourNeighborAdjacent z a ∧
        ∃ F : Finset GaussianInt, (↑F : Set GaussianInt) ⊆ C ∧ N < F.card) :
    ∃ z a : GaussianInt, ∃ C : ℕ → Set GaussianInt,
      FourNeighborAdjacent z a ∧
      ∀ n, z ∉ C n ∧ a ∈ C n ∧ FourNeighborConnected (C n) ∧
        (∀ x, FourNeighborLaplacian
          (fun y => g y + Set.indicator (C n) (fun _ => (1 : ℤ)) y) x ≤ 1) ∧
        ∃ F : Finset GaussianInt, (↑F : Set GaussianInt) ⊆ C n ∧ n < F.card := by
-- BODY
  classical
  have translate_adj (t x y : GaussianInt) :
      FourNeighborAdjacent (x + t) (y + t) ↔ FourNeighborAdjacent x y := by
    have h₁ : x + t + 1 = x + 1 + t := by abel
    have h₂ : x + t - 1 = x - 1 + t := by abel
    have h₃ : x + t + ⟨0, 1⟩ = x + ⟨0, 1⟩ + t := by abel
    have h₄ : x + t - ⟨0, 1⟩ = x - ⟨0, 1⟩ + t := by abel
    simp only [FourNeighborAdjacent, h₁, h₂, h₃, h₄, add_left_inj]
  have translate_conn (A : Set GaussianInt) (t : GaussianInt)
      (hA : FourNeighborConnected A) : FourNeighborConnected {x | x + t ∈ A} := by
    obtain ⟨a, ha⟩ := hA.1
    refine ⟨⟨a - t, by simpa using ha⟩, ?_⟩
    intro x hx y hy
    obtain ⟨p, hphead, hplast, hpmem, hpedge⟩ := hA.2 (x + t) hx (y + t) hy
    refine ⟨p.map (fun w => w - t), ?_, ?_, ?_, ?_⟩
    · simp [List.head?_map, hphead]
    · simp [List.getLast?_map, hplast]
    · intro w hw
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
      simpa using hpmem b hb
    · intro a b l₁ l₂ hp
      have heq := congrArg (List.map (fun w : GaussianInt => w + t)) hp
      simp only [List.map_map, List.map_append, List.map_cons, Function.comp_def] at heq
      have hid : (fun w : GaussianInt => (w - t) + t) = id := by
        funext w
        exact sub_add_cancel w t
      rw [hid, List.map_id] at heq
      exact (translate_adj t a b).mp (hpedge _ _ _ _ heq)
  choose A hAconn hAlap z a hz ha hza F hF hcard using hfamily
  choose r hr α β hzrep using fun n => hres (z n)
  let t (n : ℕ) : GaussianInt := α n • u + β n • v
  let B (n : ℕ) : Set GaussianInt := {x | x + t n ∈ A n}
  let b (n : ℕ) : GaussianInt := a n - t n
  have hzrt (n : ℕ) : z n = r n + t n := by
    simpa only [t, add_assoc] using hzrep n
  have hb (n : ℕ) : b n ∈ B n := by
    simpa [B, b] using ha n
  have hmiss (n : ℕ) : r n ∉ B n := by
    simpa [B, ← hzrt n] using hz n
  have hadj (n : ℕ) : FourNeighborAdjacent (r n) (b n) := by
    apply (translate_adj (t n) _ _).mp
    simpa [b, ← hzrt n] using hza n
  have hconn (n : ℕ) : FourNeighborConnected (B n) :=
    translate_conn (A n) (t n) (hAconn n)
  have hlap (n : ℕ) (x : GaussianInt) : FourNeighborLaplacian
      (fun y => g y + Set.indicator (B n) (fun _ => (1 : ℤ)) y) x ≤ 1 := by
    have h := hAlap n (x + t n)
    have ht : FourNeighborLaplacian g (x + t n) = FourNeighborLaplacian g x := by
      simpa only [t, add_assoc] using hper (α n) (β n) x
    have hI (w : GaussianInt) :
        Set.indicator (B n) (fun _ => (1 : ℤ)) w =
          Set.indicator (A n) (fun _ => (1 : ℤ)) (w + t n) := by
      by_cases hw : w + t n ∈ A n <;> simp [B, hw]
    simp only [FourNeighborLaplacian, hI] at h ⊢
    simp only [FourNeighborLaplacian] at ht
    have h₁ : x + t n + 1 = x + 1 + t n := by abel
    have h₂ : x + t n - 1 = x - 1 + t n := by abel
    have h₃ : x + t n + ⟨0, 1⟩ = x + ⟨0, 1⟩ + t n := by abel
    have h₄ : x + t n - ⟨0, 1⟩ = x - ⟨0, 1⟩ + t n := by abel
    rw [h₁, h₂, h₃, h₄] at h ht
    linarith
  have hsize (n : ℕ) : ∃ K : Finset GaussianInt,
      (↑K : Set GaussianInt) ⊆ B n ∧ n < K.card := by
    refine ⟨(F n).image (fun w => w - t n), ?_, ?_⟩
    · intro w hw
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
      simpa [B] using hF n hc
    · rw [Finset.card_image_of_injective _ (fun x y h => by
        simpa using congrArg (fun w => w + t n) h)]
      exact hcard n
  let S : Finset (GaussianInt × GaussianInt) := R.biUnion
    (fun r => {(r, r + 1), (r, r - 1), (r, r + ⟨0, 1⟩), (r, r - ⟨0, 1⟩)})
  have hS (n : ℕ) : (r n, b n) ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨r n, hr n, ?_⟩
    have h := hadj n
    rcases h with h | h | h | h <;> simp [h]
  let label (n : ℕ) : {p // p ∈ S} := ⟨(r n, b n), hS n⟩
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber label
  have hinf : {n : ℕ | label n = p}.Infinite := Set.infinite_coe_iff.mp hp
  choose k hk hkn using fun n => hinf.exists_gt n
  have hlabel (n : ℕ) : (r (k n), b (k n)) = p.val :=
    congrArg Subtype.val (hk n)
  refine ⟨p.val.1, p.val.2, fun n => B (k n), ?_, ?_⟩
  · rw [← hlabel 0]
    exact hadj (k 0)
  · intro n
    have hrn : r (k n) = p.val.1 := congrArg Prod.fst (hlabel n)
    have hbn : b (k n) = p.val.2 := congrArg Prod.snd (hlabel n)
    refine ⟨hrn ▸ hmiss (k n), hbn ▸ hb (k n), hconn (k n), hlap (k n), ?_⟩
    obtain ⟨K, hK, hKcard⟩ := hsize (k n)
    exact ⟨K, hK, lt_trans (hkn n) hKcard⟩

end ApollonianSuperharmonic

end
