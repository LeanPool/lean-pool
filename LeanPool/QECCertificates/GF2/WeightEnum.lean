/-
Copyright (c) 2026 Shuoming An. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuoming An
-/
module

public import LeanPool.QECCertificates.GF2.Basic

/-!
# Enumeration by bounded weight: shrinking the search space from $2^n$ to $\sum_{k\le w}\binom nk$
    (scaling, and the size of the certificate)

A lower-bound certificate can be built from a full-space enumeration
(`Finset.univ : Finset (Vec n)`): coverage then comes for free from `Finset.mem_univ`, but
the cost is $2^n$. In measurements $n \le 9$ runs in seconds while $n = 15$ takes over
three minutes, so that route stalls around $n \approx 12$.

This module takes a different route: **enumerate only the vectors of weight $\le w$**.
A lower bound only has to exclude operators of weight $< d$, so $w = d - 1$ suffices, and

* the candidate space drops from $2^n$ to $\sum_{k \le w}\binom nk$ (for fixed $d$, a
  polynomial of degree $d-1$ in $n$)
* for $n = 15$ and $d = 3$: $2^{15} = 32768 \to \binom{15}{\le 2} = 121$ (**a factor of
  270**).

The price is that **coverage of the enumeration is no longer free**: the main theorem of
this module, `mem_lightVecs`, is exactly that coverage lemma, and `length_lightVecs` gives
the **exact count**. Together they state the complexity characterisation, namely that the
reduced size of a distance-decision certificate is exactly $\sum_{k<d}\binom nk$.

## Construction

The enumeration and the weight are defined by **the same recursion**, so coverage can be
proved by structural induction:

```
wtRec : the last coordinate counts 1 when nonzero and 0 when zero, recursing on the prefix
lightVecs (n+1) (w+1) = (lightVecs n (w+1)).map (pad a zero at the last position)
                      ++ (lightVecs n w).map (pad a one at the last position)
```

`lightVecs` is **exact and without repetition**: its length is
$\sum_{k\le w}\binom nk$.

## Main results

* `mem_lightVecs`: **coverage**; every vector of weight $\le w$ occurs in the enumeration.
* `wtRec_eq_hammingNorm`: `wtRec` agrees with the standard `hammingNorm` (the bridge to
  the public interface).
* `length_lightVecs`: the **exact count**; the length of the enumeration is
  $\sum_{k \le w}\binom nk$.
-/

@[expose] public section

namespace QECCertificates

open scoped BigOperators

variable {n : ℕ}

/-! ## Padding the last coordinate -/

/-- "Pad the last coordinate": the first `n` coordinates take `u` and the `n+1`-st takes
`b`.

**Deliberately written as an explicit `if` branch rather than `Fin.snoc`**, for the same
reason as `Fin.append`: an `if` branch reduces coordinate by coordinate in the kernel, so
`by decide` can compute with it. -/
def snocV {n : ℕ} (u : Vec n) (b : ZMod 2) : Vec (n + 1) :=
  fun i => if h : (i : ℕ) < n then u ⟨i, h⟩ else b

@[simp] lemma snocV_castSucc {u : Vec n} {b : ZMod 2} (i : Fin n) :
    snocV u b i.castSucc = u i := by
  simp only [snocV]
  rw [dite_eq_left (show ((i.castSucc : Fin (n + 1)) : ℕ) < n from i.isLt)]
  exact congrArg u (Fin.ext rfl)

@[simp] lemma castSuccEmb_apply (i : Fin n) : Fin.castSuccEmb i = i.castSucc := rfl

@[simp] lemma snocV_last {u : Vec n} {b : ZMod 2} : snocV u b (Fin.last n) = b := by
  simp only [snocV]
  rw [dite_eq_right (show ¬ ((Fin.last n : Fin (n + 1)) : ℕ) < n from by simp)]

/-- A zero vector padded with a zero at the last position is still the zero vector. -/
@[simp] lemma snocV_zero_zero : snocV (0 : Vec n) (0 : ZMod 2) = 0 := by
  funext i
  by_cases h : (i : ℕ) < n
  · rw [snocV, dite_eq_left h]; rfl
  · rw [snocV, dite_eq_right h]; rfl

/-- Every vector of `n+1` coordinates is reconstructed from its prefix and its last
coordinate. -/
lemma snocV_prefix_last (v : Vec (n + 1)) :
    snocV (fun i : Fin n => v i.castSucc) (v (Fin.last n)) = v := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
  · rw [hj, snocV_castSucc]
  · rw [hj, snocV_last]

/-! ## Recursive weight and enumeration -/

/-- **Recursive weight**: a definition isomorphic to `lightVecs`, so that the coverage
proof can proceed by structural induction.

The last coordinate counts 1 when nonzero and 0 when zero, with recursion on the prefix
this agrees with `hammingNorm` (`wtRec_eq_hammingNorm`). -/
def wtRec : (n : ℕ) → Vec n → ℕ
  | 0, _ => 0
  | n + 1, v => wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1)

@[simp] lemma wtRec_zero (v : Vec 0) : wtRec 0 v = 0 := by rw [wtRec.eq_1]

lemma wtRec_succ (v : Vec (n + 1)) :
    wtRec (n + 1) v
      = wtRec n (fun i => v i.castSucc) + (if v (Fin.last n) = 0 then 0 else 1) := by
  rw [wtRec.eq_2]

/-- **All vectors of weight $\le w$** (a computable enumeration, exact and without
repetition).

Recursion: the vectors of $n+1$ coordinates split into two classes according to their last
coordinate. Those whose last coordinate is zero come from padding the vectors of $n$
coordinates of weight $\le w+1$ with a zero, and those whose last coordinate is 1 come
from padding the vectors of $n$ coordinates of weight $\le w$ with a one. -/
def lightVecs : (n w : ℕ) → List (Vec n)
  | 0, _ => [0]
  | _ + 1, 0 => [0]
  | n + 1, w + 1 =>
      (lightVecs n (w + 1)).map (fun u => snocV u 0) ++ (lightVecs n w).map (fun u => snocV u 1)

@[simp] lemma lightVecs_nil (w : ℕ) : lightVecs 0 w = [0] := by rw [lightVecs.eq_1]

lemma lightVecs_zero (n : ℕ) : lightVecs n 0 = [0] := by
  cases n with
  | zero => rw [lightVecs.eq_1]
  | succ n => rw [lightVecs.eq_2]

lemma lightVecs_succ_succ (n w : ℕ) :
    lightVecs (n + 1) (w + 1) = (lightVecs n (w + 1)).map (fun u => snocV u 0)
      ++ (lightVecs n w).map (fun u => snocV u 1) := by
  rw [lightVecs.eq_3]

/-! ## Weight zero means the zero vector -/

theorem wtRec_eq_zero_iff (v : Vec n) : wtRec n v = 0 ↔ v = 0 := by
  induction n with
  | zero =>
      refine ⟨fun _ => ?_, fun _ => by simp⟩
      funext i
      exact i.elim0
  | succ n ih =>
      rw [wtRec_succ]
      constructor
      · intro h
        have hb : v (Fin.last n) = 0 := by
          by_contra hb
          rw [ite_eq_right hb] at h
          omega
        rw [ite_eq_left hb, add_zero] at h
        have hpre : (fun i : Fin n => v i.castSucc) = 0 := (ih _).mp h
        rw [← snocV_prefix_last v, hb, hpre, snocV_zero_zero]
      · intro h
        rw [h]
        simp only [Pi.zero_apply, ite_true, add_zero]
        exact (ih 0).mpr rfl

/-! ## Coverage -/

/-- **Coverage**: every vector of weight $\le w$ occurs in `lightVecs n w`.

The proof follows the recursive structure of `lightVecs` by looking at the last
coordinate. If the last coordinate is nonzero then the weight of the prefix must be
$\le w$; if it is zero then the prefix need only have weight $\le w+1$. Each case lands in
the corresponding half of the enumeration. -/
theorem mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), wtRec n v ≤ w → v ∈ lightVecs n w := by
  intro n
  induction n with
  | zero =>
      intro w v _
      rw [lightVecs_nil]
      simp only [List.mem_singleton]
      funext i
      exact i.elim0
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          have hv0 : v = 0 := (wtRec_eq_zero_iff v).mp (Nat.le_zero.mp hv)
          rw [hv0, lightVecs_zero]; simp
      | succ w =>
          rw [← snocV_prefix_last v, lightVecs_succ_succ]
          rw [wtRec_succ] at hv
          by_cases hb : v (Fin.last n) = 0
          · rw [hb] at hv ⊢
            rw [ite_eq_left rfl] at hv
            refine List.mem_append_left _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih (w + 1) _ hv, rfl⟩
          · rw [ite_eq_right hb] at hv
            have hb1 : v (Fin.last n) = 1 := eq_one_of_ne_zero hb
            rw [hb1]
            refine List.mem_append_right _ ?_
            rw [List.mem_map]
            exact ⟨fun i : Fin n => v i.castSucc, ih w _ (by omega), rfl⟩

/-! ## Bridge to the standard weight -/

/-- **Soundness**: `lightVecs` contains only vectors of weight $\le w$, the other half of
the coverage statement `mem_lightVecs`.

With both halves, the claim that the candidate set is empty is closed in both directions:
coverage says nothing is missed, soundness says everything that is left really is light. -/
theorem wt_le_of_mem_lightVecs : ∀ (n w : ℕ) (v : Vec n), v ∈ lightVecs n w → wtRec n v ≤ w := by
  intro n
  induction n with
  | zero =>
      intro w v hv
      rw [lightVecs_nil, List.mem_singleton] at hv
      subst hv
      have h0 : wtRec 0 (0 : Vec 0) = 0 := wtRec_zero 0
      rw [h0]
      omega
  | succ n ih =>
      intro w v hv
      cases w with
      | zero =>
          rw [lightVecs_zero, List.mem_singleton] at hv
          subst hv
          have h0 : wtRec (n + 1) (0 : Vec (n + 1)) = 0 :=
            (wtRec_eq_zero_iff (0 : Vec (n + 1))).mpr rfl
          rw [h0]
      | succ w =>
          rw [lightVecs_succ_succ, List.mem_append] at hv
          rcases hv with hv | hv
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih (w + 1) u hu
            have heq : wtRec (n + 1) (snocV u 0) = wtRec n u := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega
          · rw [List.mem_map] at hv
            obtain ⟨u, hu, huv⟩ := hv
            subst huv
            have h := ih w u hu
            have heq : wtRec (n + 1) (snocV u 1) = wtRec n u + 1 := by
              rw [wtRec_succ, snocV_last]
              simp
            rw [heq]
            omega

/-- `wtRec` is the size of the support (agreeing with `support` and `hammingNorm`). -/
theorem wtRec_eq_card_support (v : Vec n) : wtRec n v = (support v).card := by
  induction n with
  | zero => simp [wtRec, support]
  | succ n ih =>
      rw [wtRec_succ, ih]
      have hsupp : support v =
          (support (fun i : Fin n => v i.castSucc)).map Fin.castSuccEmb
            ∪ (if v (Fin.last n) = 0 then ∅ else {Fin.last n}) := by
        ext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hj
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_inj, Fin.castSucc_ne_last]
        · rw [hj, mem_support]
          by_cases hb : v (Fin.last n) = 0 <;>
            simp [support, castSuccEmb_apply, hb, Fin.castSucc_ne_last]
      rw [hsupp, Finset.card_union_of_disjoint, Finset.card_map]
      · by_cases hb : v (Fin.last n) = 0 <;> simp [hb]
      · rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_map] at ha
        obtain ⟨j, _, hj⟩ := ha
        rw [← hj] at hb
        by_cases h0 : v (Fin.last n) = 0
        · simp [h0] at hb
        · simp only [h0, ite_false, Finset.mem_singleton] at hb
          exact Fin.castSucc_ne_last j hb

/-- `wtRec` agrees with the standard `hammingNorm` (the bridge to the public
interface). -/
theorem wtRec_eq_hammingNorm (v : Vec n) : wtRec n v = hammingNorm v := by
  rw [wtRec_eq_card_support, weight_eq_hammingNorm]

/-! ## The exact count (size of the certificate) -/

/-- **The exact length of the enumeration**: `lightVecs n w` has exactly
$\sum_{k \le w}\binom nk$ elements.

This is the concrete content of the size of a distance-decision certificate: since a lower
bound only has to exclude operators of weight $< d$, taking $w = d-1$ makes the
**candidate space exactly $\sum_{k<d}\binom nk$**, a polynomial of degree $d-1$ in $n$
rather than the $2^n$ of the full space. -/
theorem length_lightVecs : ∀ (n w : ℕ),
    (lightVecs n w).length = ∑ k ∈ Finset.range (w + 1), n.choose k := by
  intro n
  induction n with
  | zero =>
      intro w
      rw [lightVecs_nil]
      rw [Finset.sum_eq_single 0]
      · exact Nat.choose_self 0
      · intro b _ hb
        exact Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos w)) h
  | succ n ih =>
      intro w
      cases w with
      | zero =>
          rw [lightVecs_zero, Finset.sum_range_one, Nat.choose_zero_right]
          rfl
      | succ w =>
          rw [lightVecs_succ_succ, List.length_append, List.length_map, List.length_map,
            ih (w + 1), ih w]
          rw [Finset.sum_range_succ' (fun j => (n + 1).choose j) (w + 1)]
          rw [Finset.sum_congr rfl (fun j _ => Nat.choose_succ_succ n j), Finset.sum_add_distrib]
          rw [Finset.sum_range_succ' (fun j => n.choose j) (w + 1)]
          rw [Finset.sum_range_succ (fun j => n.choose j) w]
          rw [Nat.choose_zero_right n, Nat.choose_zero_right (n + 1)]
          ring

end QECCertificates
