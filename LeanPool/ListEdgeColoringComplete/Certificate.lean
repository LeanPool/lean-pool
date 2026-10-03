/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.ListEdgeColoringComplete.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Fin

/-! # The Häggkvist--Janssen local rank certificate

For the complete graph on the labels `0, …, n-1`, the edge `{u, v}` lies in the two
extended star cliques `C_u` and `C_v`. A *certificate* assigns to every ordered pair
`(u, v)` with `u ≠ v` a local rank (out-degree inside `C_u`), such that

* in every star `C_u` the ranks of the `n - 1` actual edges, together with the blocked
  value `blockedRank n u` (rank of the artificial vertex), are exactly `0, …, n-1`;
* the two local ranks of an edge add up to `targetDegree n u v`.

This file gives the closed-form certificate `localRank` and proves that it is the
*unique* certificate (`certificate_unique`). It supplies the combinatorial step
in our alternative presentation of the proof, rather than implementing the
article's Algorithm 3.2 as a separate procedure.

## Correspondence with the source

For distinct labels below `n`, write `d = (u + v) mod (n - 1)`
(`diagIndex`, the "diagonal" of the remark after
Algorithm 3.2). The canonical ranks of the edge are `⌊d/2⌋` (at its *low end*) and
`targetDegree - ⌊d/2⌋` (at the other end). The low end is the larger endpoint when `d` is
even and the smaller endpoint when `d` is odd (`IsLowEnd`).

The printed closed form of `α` on page 306 is incorrect in the case `i + j ≥ n - 1`: for
`n = 6` and the edge `(2,5)` it gives `(6,1)`, whose entries do not add up to
`ρ(2,5) = 5` (and `6` is not even a rank). The formula used here gives `(4,1)`, which is
what Algorithm 3.2 produces.

Algorithm 3.2 assigns the edges in the order: first by the low rank `⌊d/2⌋` (the loop
variable `i`), then by decreasing low end (`b = n - 1 - t`); the four stages of one
iteration are exactly four consecutive ranges of low ends. This is the order `Precedes`.
The uniqueness proof uses induction on this order and the arithmetic lemma `forcing`.
The article is the source of the theorem and certificate construction; the direct
rank-and-polynomial proof here is not a line-by-line formalization of its proof.
-/

@[expose] public section

namespace LeanPool.ListEdgeColoringComplete

/-- The diagonal `(u + v) mod (n - 1)` of the edge `{u, v}`, for `u, v < n`, `u ≠ v`. -/
def diagIndex (n u v : ℕ) : ℕ :=
  if n - 1 ≤ u + v then u + v - (n - 1) else u + v

/-- `u` is the low end of the edge `{u, v}` (the endpoint receiving the small rank). -/
def IsLowEnd (n u v : ℕ) : Prop :=
  (diagIndex n u v % 2 = 0 ↔ v < u)

instance (n u v : ℕ) : Decidable (IsLowEnd n u v) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The canonical local rank of the edge `{u, v}` inside the star clique `C_u`. -/
def localRank (n u v : ℕ) : ℕ :=
  if IsLowEnd n u v then diagIndex n u v / 2 else targetDegree n u v - diagIndex n u v / 2

/-- The canonical rank row of the extended star `C_u`: the diagonal entry is the rank of
the artificial vertex, i.e. the blocked value. -/
def fullRank (n u v : ℕ) : ℕ :=
  if u = v then blockedRank n u else localRank n u v

/-- The low end of the edge `{u, v}`. -/
def lowEnd (n u v : ℕ) : ℕ :=
  if IsLowEnd n u v then u else v

/-- The edge `{u, v}` is processed strictly before `{u', v'}` by Algorithm 3.2. -/
def Precedes (n u v u' v' : ℕ) : Prop :=
  diagIndex n u v / 2 < diagIndex n u' v' / 2 ∨
    (diagIndex n u v / 2 = diagIndex n u' v' / 2 ∧ lowEnd n u' v' < lowEnd n u v)

/-- A numerical key whose order refines `Precedes`. -/
def edgeKey (n u v : ℕ) : ℕ :=
  diagIndex n u v / 2 * n + (n - 1 - lowEnd n u v)

section Arithmetic

variable {n u v w : ℕ}

theorem targetDegree_comm (n u v : ℕ) : targetDegree n u v = targetDegree n v u := by
  unfold targetDegree
  rw [Nat.add_comm]

theorem diagIndex_comm (n u v : ℕ) : diagIndex n u v = diagIndex n v u := by
  unfold diagIndex
  rw [Nat.add_comm]

theorem isLowEnd_iff_not (hv : v < n) (huv : u ≠ v) :
    IsLowEnd n u v ↔ ¬ IsLowEnd n v u := by
  unfold IsLowEnd diagIndex
  split_ifs <;> omega

theorem lowEnd_comm (n u v : ℕ) :
    lowEnd n u v = lowEnd n v u := by
  unfold lowEnd IsLowEnd diagIndex
  split_ifs <;> omega

theorem lowEnd_lt (hu : u < n) (hv : v < n) : lowEnd n u v < n := by
  unfold lowEnd
  split_ifs <;> omega

theorem edgeKey_comm (n u v : ℕ) :
    edgeKey n u v = edgeKey n v u := by
  unfold edgeKey
  rw [diagIndex_comm n u v, lowEnd_comm n u v]

theorem edgeKey_lt_of_precedes {u' v' : ℕ} (hu : u < n) (hv : v < n) (hu' : u' < n)
    (hv' : v' < n) (h : Precedes n u v u' v') : edgeKey n u v < edgeKey n u' v' := by
  have h1 := lowEnd_lt (n := n) hu hv
  have h2 := lowEnd_lt (n := n) hu' hv'
  unfold edgeKey
  rcases h with h | ⟨h, h'⟩
  · have : diagIndex n u v / 2 * n + n ≤ diagIndex n u' v' / 2 * n := by
      have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
      simpa [Nat.succ_mul] using this
    omega
  · rw [h]
    omega

/-- The two local ranks of an edge add up to the target degree `ρ`. -/
theorem localRank_add (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v + localRank n v u = targetDegree n u v := by
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega

theorem localRank_lt (hu : u < n) (hv : v < n) : localRank n u v < n := by
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega

/-- No actual edge of `C_u` receives the blocked rank. -/
theorem localRank_ne_blockedRank (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    localRank n u v ≠ blockedRank n u := by
  unfold localRank IsLowEnd targetDegree diagIndex blockedRank
  split_ifs <;> omega

/-- Distinct edges of `C_u` receive distinct ranks. -/
theorem localRank_injective (hu : u < n) (hv : v < n) (hw : w < n) (huv : u ≠ v)
    (huw : u ≠ w) (h : localRank n u v = localRank n u w) : v = w := by
  revert h
  unfold localRank IsLowEnd targetDegree diagIndex
  split_ifs <;> omega

theorem fullRank_lt (hu : u < n) (hv : v < n) : fullRank n u v < n := by
  unfold fullRank
  split_ifs with h
  · unfold blockedRank
    split_ifs <;> omega
  · exact localRank_lt hu hv

theorem fullRank_injective (hu : u < n) (hv : v < n) (hw : w < n)
    (h : fullRank n u v = fullRank n u w) : v = w := by
  unfold fullRank at h
  split_ifs at h with h1 h2 h2
  · omega
  · exact absurd h.symm (localRank_ne_blockedRank hu hw h2)
  · exact absurd h (localRank_ne_blockedRank hu hv h1)
  · exact localRank_injective hu hv hw h1 h2 h

/-- **Forced choice.** This is the arithmetic heart of the uniqueness argument of
pages 305--306. Let `{a, b}` be an edge with low end `b`. Suppose that some other edge
`{a, l}`, not processed before `{a, b}`, received the rank of `{a, b}` in `C_a`; then
the complementary rank at `l` is already used in `C_l` by an edge `{l, x}` that *was*
processed before `{a, b}`. -/
theorem forcing {a b l x : ℕ} (ha : a < n) (hb : b < n) (hl : l < n) (hx : x < n)
    (hab : ¬ IsLowEnd n a b) (hlb : l ≠ b) (hxl : x ≠ l) (hxa : x ≠ a)
    (hk : ¬ Precedes n a l a b)
    (hsum : localRank n l x + localRank n a b = targetDegree n a l) :
    Precedes n l x a b := by
  unfold Precedes lowEnd localRank at *
  unfold IsLowEnd targetDegree diagIndex at *
  split_ifs at * <;> omega

end Arithmetic

/-! ## Existence and uniqueness of the certificate on `Fin n` -/

section FinCertificate

variable {n : ℕ}

/-- The canonical rank row of the extended star `C_i`, as a map `Fin n → Fin n`. -/
def canonicalRow (i : Fin n) (j : Fin n) : Fin n :=
  ⟨fullRank n i j, fullRank_lt i.isLt j.isLt⟩

theorem canonicalRow_injective (i : Fin n) : Function.Injective (canonicalRow i) := by
  intro j k h
  exact Fin.ext (fullRank_injective i.isLt j.isLt k.isLt (congrArg Fin.val h))

/-- **Existence**: the canonical rows form a certificate. -/
theorem canonicalRow_spec :
    (∀ i : Fin n, Function.Injective (canonicalRow i)) ∧
    (∀ i : Fin n, (canonicalRow i i : ℕ) = blockedRank n i) ∧
    (∀ i j : Fin n, i ≠ j →
      (canonicalRow i j : ℕ) + canonicalRow j i = targetDegree n i j) := by
  refine ⟨canonicalRow_injective, fun i => by simp [canonicalRow, fullRank], ?_⟩
  intro i j hij
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [canonicalRow, fullRank, hij', (Ne.symm hij'), ite_false]
  exact localRank_add i.isLt j.isLt hij'

/-- **Uniqueness of the certificate.** Any family of rank rows (one bijection
`Fin n → Fin n` per extended star clique) that gives the artificial vertex of `C_i` its
blocked value and whose two local ranks at each edge add up to `ρ` is the canonical one. -/
theorem certificate_unique (r : Fin n → Fin n → Fin n)
    (hinj : ∀ i, Function.Injective (r i))
    (hdiag : ∀ i, (r i i : ℕ) = blockedRank n i)
    (hsum : ∀ i j, i ≠ j → (r i j : ℕ) + r j i = targetDegree n i j) :
    r = canonicalRow := by
  -- claim for an unordered edge
  let C : Fin n → Fin n → Prop := fun u v =>
    (r u v : ℕ) = localRank n u v ∧ (r v u : ℕ) = localRank n v u
  have hsurj : ∀ i, Function.Surjective (r i) := fun i =>
    Finite.injective_iff_surjective.mp (hinj i)
  have hcanSurj : ∀ i, Function.Surjective (canonicalRow (n := n) i) := fun i =>
    Finite.injective_iff_surjective.mp (canonicalRow_injective i)
  have key : ∀ k, ∀ u v : Fin n, u ≠ v → edgeKey n u v = k → C u v := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
    intro u v huv hk
    have IH' : ∀ u' v' : Fin n, u' ≠ v' → ∀ a b : Fin n, a ≠ b →
        edgeKey n a b = k → Precedes n u' v' a b → C u' v' := by
      intro u' v' huv' a b _ hab hp
      exact IH _ (hab ▸ edgeKey_lt_of_precedes u'.isLt v'.isLt a.isLt b.isLt hp) u' v'
        huv' rfl
    -- the main step, for an orientation `(a, b)` with low end `b`
    have step : ∀ a b : Fin n, a ≠ b → edgeKey n a b = k → ¬ IsLowEnd n a b →
        (r a b : ℕ) = localRank n a b := by
      intro a b hab hk' hlow
      have habv : (a : ℕ) ≠ b := fun h => hab (Fin.ext h)
      obtain ⟨l, hl⟩ := hsurj a ⟨localRank n a b, localRank_lt a.isLt b.isLt⟩
      have hl' : (r a l : ℕ) = localRank n a b := congrArg Fin.val hl
      by_cases hlb : l = b
      · subst hlb; exact hl'
      exfalso
      have hlbv : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
      have hla : l ≠ a := by
        intro h
        rw [h] at hl'
        exact localRank_ne_blockedRank a.isLt b.isLt habv (hl' ▸ hdiag a)
      have halv : (a : ℕ) ≠ l := fun h => hla (Fin.ext h).symm
      by_cases hp : Precedes n a l a b
      · have := (IH' a l (Ne.symm hla) a b hab hk' hp).1
        exact hlbv (localRank_injective a.isLt l.isLt b.isLt halv habv (this ▸ hl'))
      · have hs := hsum a l (Ne.symm hla)
        obtain ⟨x, hx⟩ := hcanSurj l (r l a)
        have hxv : (canonicalRow l x : ℕ) = r l a := congrArg Fin.val hx
        have hxl : x ≠ l := by
          intro h
          rw [h] at hxv
          have : r l l = r l a := by
            apply Fin.ext; rw [hdiag, ← hxv]; simp [canonicalRow, fullRank]
          exact hla (hinj l this)
        have hxlv : (x : ℕ) ≠ l := fun h => hxl (Fin.ext h)
        have hxr : localRank n l x = r l a := by
          rw [← hxv]; simp [canonicalRow, fullRank, Ne.symm hxlv]
        have hxa : x ≠ a := by
          intro h
          rw [h] at hxr
          have h1 := localRank_add a.isLt l.isLt halv
          have : localRank n a l = localRank n a b := by omega
          exact hlbv (localRank_injective a.isLt l.isLt b.isLt halv habv this)
        have hxav : (x : ℕ) ≠ a := fun h => hxa (Fin.ext h)
        have hf := forcing a.isLt b.isLt l.isLt x.isLt hlow hlbv hxlv hxav hp (by omega)
        have := (IH' l x (Ne.symm hxl) a b hab hk' hf).1
        exact hxa (hinj l (Fin.ext (by rw [this, hxr])))
    have huvv : (u : ℕ) ≠ v := fun h => huv (Fin.ext h)
    have hkey := edgeKey_comm n u v
    by_cases hlow : IsLowEnd n u v
    · have hvu := (isLowEnd_iff_not v.isLt huvv).mp hlow
      have h2 := step v u (Ne.symm huv) (hkey ▸ hk) hvu
      have hs := hsum u v huv
      have ha := localRank_add u.isLt v.isLt huvv
      exact ⟨by omega, h2⟩
    · have h1 := step u v huv hk hlow
      have hs := hsum u v huv
      have ha := localRank_add u.isLt v.isLt huvv
      exact ⟨h1, by omega⟩
  funext i j
  apply Fin.ext
  by_cases hij : i = j
  · subst hij
    rw [hdiag]
    simp [canonicalRow, fullRank]
  · have hijv : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rw [(key _ i j hij rfl).1]
    simp [canonicalRow, fullRank, hijv]

end FinCertificate

end LeanPool.ListEdgeColoringComplete
