/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.ListEndpointFacts

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: SimpleGridPathEndpointPairUnique]

/-!
# SimpleGridPathEndpointPairUnique

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace EndpointPairProof

private theorem endpoint_edge :
    ∀ (r : List GaussianInt), ∀ (z : GaussianInt), r.Nodup → 2 ≤ r.length → r.head? = some z →
      ∀ e : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) →
        z ∈ e →
        ∃ t s, r = z :: t :: s ∧ e = {z, t} := by
  classical
  intro r z hr hrl hz e he hze
  rcases he with ⟨a, b, l₁, l₂, hrab, he⟩
  have hmem : z ∈ ({a, b} : Finset GaussianInt) := by simpa [he] using hze
  have hcases : z = a ∨ z = b := by simpa using hmem
  have hsub : [a, b] <:+: r := by
    refine ⟨l₁, l₂, ?_⟩
    simpa [List.cons_append] using hrab.symm
  have hrne : r ≠ [] := by
    intro hrnil
    rw [hrnil] at hrl
    simp at hrl
  have hzhead : r.head hrne = z := by
    simpa [List.head?_eq_some_head hrne] using hz
  have hheadmem : r.head hrne ∈ [a, b] := by
    rcases hcases with hza | hzb
    · simp [hzhead, hza]
    · simp [hzhead, hzb]
  have hprefix : [a, b] <+: r :=
    hr.prefix_of_head_mem_of_infix hsub hheadmem
  rcases hprefix with ⟨tail, hrtail⟩
  have hab : r = [a, b] ++ tail := hrtail.symm
  have hza : z = a := by
    rw [hab] at hz
    simpa using hz.symm
  subst a
  refine ⟨b, tail, ?_, ?_⟩
  · simp [hab]
  · simpa using he

private abbrev split_mem :=
  @ListEndpointFacts.splitMembership GaussianInt

private theorem endpoint_unique :
    (∀ (r : List GaussianInt), ∀ (z : GaussianInt), r.Nodup → 2 ≤ r.length → r.head? = some z → ∀
        e : Finset GaussianInt, (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → z ∈ e → ∃ t
        s, r = z :: t :: s ∧ e = {z, t}) → (∀ (r : List GaussianInt), ∀ (z : GaussianInt),
        r.Nodup → 2 ≤ r.length → r.head? = some z →
      ∀ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) →
        z ∈ e₁ →
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) →
        z ∈ e₂ → e₁ = e₂) := by
  classical
  intro endpoint_edge r z hr hrl hz e₁ e₂ he₁ hze₁ he₂ hze₂
  rcases endpoint_edge r z hr hrl hz e₁ he₁ hze₁ with ⟨t₁, s₁, hr₁, he₁'⟩
  rcases endpoint_edge r z hr hrl hz e₂ he₂ hze₂ with ⟨t₂, s₂, hr₂, he₂'⟩
  have hsame : z :: t₁ :: s₁ = z :: t₂ :: s₂ := hr₁.symm.trans hr₂
  have ht : t₁ = t₂ := by
    have htail : t₁ :: s₁ = t₂ :: s₂ := by injection hsame
    have hheads := congrArg List.head? htail
    simpa using hheads
  simp [he₁', he₂', ht]

private theorem interior_edges :
    (∀ (r : List GaussianInt), ∀ (z : GaussianInt), z ∈ r → ∃ l t, r = l ++ z :: t) → (∀ (r :
        List GaussianInt), ∀ (z : GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), r.Nodup
        → r.head? = some u → r.getLast? = some v →
      z ∈ r → z ≠ u → z ≠ v →
      ∃ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) ∧
        z ∈ e₁ ∧
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) ∧
        z ∈ e₂ ∧ e₁ ≠ e₂) := by
  classical
  intro split_mem r z u v hr hu hv hz hzu hzv
  rcases split_mem r z hz with ⟨l, t, hrt⟩
  have hl : l ≠ [] := by
    intro he
    subst l
    rw [hrt] at hu
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hu
    exact hzu hu
  have ht : t ≠ [] := by
    intro he
    subst t
    rw [hrt] at hv
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hv
    exact hzv hv
  let a := l.getLast hl
  let l₀ := l.dropLast
  have hlt : l₀ ++ [a] = l := List.dropLast_append_getLast hl
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil ht
  refine ⟨{a, z}, {z, b}, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨a, z, l₀, b :: t, ?_, rfl⟩
    calc
      r = l ++ z :: b :: t := hrt
      _ = (l₀ ++ [a]) ++ z :: b :: t := by rw [hlt]
      _ = l₀ ++ a :: z :: b :: t := by simp [List.append_assoc]
  · simp
  · refine ⟨z, b, l, t, ?_, rfl⟩
    exact hrt
  · simp
  · intro heq
    have hamem : a ∈ ({z, b} : Finset GaussianInt) := by
      rw [← heq]
      simp
    have hab : a = z ∨ a = b := by simpa using hamem
    rcases hab with haz | hab
    · subst a
      have hbad := hr
      rw [hrt, ← hlt] at hbad
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.nodup_append,
          List.nodup_cons, List.mem_cons, not_or, ne_eq, forall_eq_or_imp] at hbad
      exact hbad.2.1.1.1 haz
    · subst b
      have hbad := hr
      rw [hrt, ← hlt] at hbad
      simp [List.nodup_append] at hbad

private theorem endpoint_class :
    ∀ (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y :
        GaussianInt), ∀ (p : List GaussianInt), (p.Nodup) → ((p.head? = some x) → ((p.getLast? =
        some y) → ((V = (↑p.toFinset : Set GaussianInt)) → ((∀ (e : Finset GaussianInt), e ∈ E ↔
        ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p
        = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List GaussianInt), (q.Nodup) → (((2 : ℕ) ≤
        q.length) → ((V = (↑q.toFinset : Set GaussianInt)) → ((∀ (e : Finset GaussianInt), e ∈ E
        ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt),
        q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (r : List GaussianInt), ∀ (z : GaussianInt),
        r.Nodup → 2 ≤ r.length → r.head? = some z → ∀ e₁ e₂ : Finset GaussianInt, (∃ a b l₁ l₂, r
        = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) → z ∈ e₁ → (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂
        = {a, b}) → z ∈ e₂ → e₁ = e₂) → ((∀ (r : List GaussianInt), ∀ (z : GaussianInt), ∀ (u :
        GaussianInt), ∀ (v : GaussianInt), r.Nodup → r.head? = some u → r.getLast? = some v → z ∈
        r → z ≠ u → z ≠ v → ∃ e₁ e₂ : Finset GaussianInt, (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧
        e₁ = {a, b}) ∧ z ∈ e₁ ∧ (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) ∧ z ∈ e₂ ∧ e₁
        ≠ e₂) → (∀ z : GaussianInt,
      z ∈ q → q.head? = some z → z = x ∨ z = y))))))))))) := by
  classical
  intro V E x y p hp hx hy hV hE q hq hqlen hV' hE' endpoint_unique interior_edges z hzq hzh
  have hzp : z ∈ p := by
    have hzset : z ∈ (p.toFinset : Set GaussianInt) := by
      rw [← hV, hV']
      simpa [List.mem_toFinset] using hzq
    simpa [List.mem_toFinset] using hzset
  by_contra hn
  push Not at hn
  rcases interior_edges p z x y hp hx hy hzp hn.1 hn.2 with
    ⟨e₁, e₂, he₁, hze₁, he₂, hze₂, hne⟩
  apply hne
  apply endpoint_unique q z hq hqlen hzh e₁ e₂
  · exact (hE' e₁).1 ((hE e₁).2 he₁)
  · exact hze₁
  · exact (hE' e₂).1 ((hE e₂).2 he₂)
  · exact hze₂

private theorem reverse_raw :
    ∀ (r : List GaussianInt), ∀ (e : Finset GaussianInt), (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧
        e = {a, b}) →
      ∃ a b l₁ l₂, r.reverse = l₁ ++ a :: b :: l₂ ∧ e = {a, b} := by
  classical
  intro r e he
  rcases he with ⟨a, b, l₁, l₂, hr, he⟩
  refine ⟨b, a, l₂.reverse, l₁.reverse, ?_, ?_⟩
  · rw [hr]
    simp [List.reverse_append, List.append_assoc]
  · simpa [Finset.pair_comm] using he

private theorem endpoint_unique_last :
    (∀ (r : List GaussianInt), ∀ (z : GaussianInt), r.Nodup → 2 ≤ r.length → r.head? = some z → ∀
        e₁ e₂ : Finset GaussianInt, (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) → z ∈ e₁
        → (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) → z ∈ e₂ → e₁ = e₂) → ((∀ (r : List
        GaussianInt), ∀ (e : Finset GaussianInt), (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e = {a,
        b}) → ∃ a b l₁ l₂, r.reverse = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (r : List
        GaussianInt), ∀ (z : GaussianInt), r.Nodup → 2 ≤ r.length → r.getLast? = some z →
      ∀ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) →
        z ∈ e₁ →
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) →
        z ∈ e₂ → e₁ = e₂)) := by
  classical
  intro endpoint_unique reverse_raw r z hr hrl hz e₁ e₂ he₁ hze₁ he₂ hze₂
  have hrevnodup : r.reverse.Nodup := List.nodup_reverse.mpr hr
  have hrevlen : 2 ≤ r.reverse.length := by simpa using hrl
  have hrevhead : r.reverse.head? = some z := by
    simpa using hz
  apply endpoint_unique r.reverse z hrevnodup hrevlen hrevhead e₁ e₂
  · exact reverse_raw r e₁ he₁
  · exact hze₁
  · exact reverse_raw r e₂ he₂
  · exact hze₂

private theorem endpoint_class_last :
    ∀ (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y :
        GaussianInt), ∀ (p : List GaussianInt), (p.Nodup) → ((p.head? = some x) → ((p.getLast? =
        some y) → ((V = (↑p.toFinset : Set GaussianInt)) → ((∀ (e : Finset GaussianInt), e ∈ E ↔
        ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p
        = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List GaussianInt), (q.Nodup) → (((2 : ℕ) ≤
        q.length) → ((V = (↑q.toFinset : Set GaussianInt)) → ((∀ (e : Finset GaussianInt), e ∈ E
        ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt),
        q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (r : List GaussianInt), ∀ (z : GaussianInt), ∀
        (u : GaussianInt), ∀ (v : GaussianInt), r.Nodup → r.head? = some u → r.getLast? = some v
        → z ∈ r → z ≠ u → z ≠ v → ∃ e₁ e₂ : Finset GaussianInt, (∃ a b l₁ l₂, r = l₁ ++ a :: b ::
        l₂ ∧ e₁ = {a, b}) ∧ z ∈ e₁ ∧ (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) ∧ z ∈ e₂
        ∧ e₁ ≠ e₂) → ((∀ (r : List GaussianInt), ∀ (z : GaussianInt), r.Nodup → 2 ≤ r.length →
        r.getLast? = some z → ∀ e₁ e₂ : Finset GaussianInt, (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂
        ∧ e₁ = {a, b}) → z ∈ e₁ → (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) → z ∈ e₂ →
        e₁ = e₂) → (∀ z : GaussianInt,
      z ∈ q → q.getLast? = some z → z = x ∨ z = y))))))))))) := by
  classical
  intro V E x y p hp hx hy hV hE q hq hqlen hV' hE' interior_edges endpoint_unique_last z hzq hzl
  have hzp : z ∈ p := by
    have hzset : z ∈ (p.toFinset : Set GaussianInt) := by
      rw [← hV, hV']
      simpa [List.mem_toFinset] using hzq
    simpa [List.mem_toFinset] using hzset
  by_contra hn
  push Not at hn
  rcases interior_edges p z x y hp hx hy hzp hn.1 hn.2 with
    ⟨e₁, e₂, he₁, hze₁, he₂, hze₂, hne⟩
  apply hne
  apply endpoint_unique_last q z hq hqlen hzl e₁ e₂
  · exact (hE' e₁).1 ((hE e₁).2 he₁)
  · exact hze₁
  · exact (hE' e₂).1 ((hE e₂).2 he₂)
  · exact hze₂

private theorem endpoint_ne :
    ∀ (r : List GaussianInt), ∀ (u : GaussianInt), ∀ (v : GaussianInt), r.Nodup → 2 ≤ r.length →
        r.head? = some u →
      r.getLast? = some v → u ≠ v := by
  classical
  intro r u v hr hrl hu hv huv
  have hrne : r ≠ [] := by
    intro he
    subst r
    simp at hrl
  have heq : r.head hrne = r.getLast hrne := by
    have hh := List.head?_eq_some_head hrne
    have ht := List.getLast?_eq_some_getLast hrne
    rw [hh] at hu
    rw [ht] at hv
    have hhead : r.head hrne = u := by injection hu
    have hlast : r.getLast hrne = v := by injection hv
    exact hhead.trans (huv.trans hlast.symm)
  have hsingle : ∃ w, r = [w] :=
    (List.Nodup.head_eq_getLast_iff hrne hr).mp heq
  rcases hsingle with ⟨w, rfl⟩
  simp at hrl

private theorem hx'q :
    (by
      classical
      exact
        ∀ (x' : GaussianInt) (q : List GaussianInt),
          (2 : ℕ) ≤ q.length → q.head? = some x' → x' ∈ q) := by
  classical
  intro x' q hqlen hx'
  cases q with
  | nil => simp at hqlen
  | cons a r =>
    simp only [List.head?_cons, Option.some.injEq] at hx'
    simp [hx']

private theorem hy'q :
    ∀ (y' : GaussianInt), ∀ (q : List GaussianInt), (q.getLast? = some y') → ((q ≠ []) → (y' ∈
        q)) := by
  classical
  intro y' q hy' hqne
  have hlast : q.getLast hqne = y' := by
    simpa [List.getLast?_eq_some_getLast hqne] using hy'
  exact hlast ▸ List.getLast_mem hqne

end EndpointPairProof

theorem SimpleGridPathEndpointPairUnique
    {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
    {x y x' y' : GaussianInt}
    (h : SimpleGridPathBetween V E x y)
    (h' : SimpleGridPathBetween V E x' y') :
    ({x, y} : Finset GaussianInt) = {x', y'} := by
-- BODY
  rcases h with ⟨p, hp, hlen, hx, hy, hV, hstep, hE⟩
  rcases h' with ⟨q, hq, hqlen, hx', hy', hV', hstep', hE'⟩
  have hqne : q ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hpform : ∃ r, p = x :: r := List.head?_eq_some_iff.mp hx
  have hqform : ∃ r, q = x' :: r := List.head?_eq_some_iff.mp hx'
  have endpoint_edge : ∀ (r : List GaussianInt) (z : GaussianInt),
      r.Nodup → 2 ≤ r.length → r.head? = some z →
      ∀ e : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) →
        z ∈ e →
        ∃ t s, r = z :: t :: s ∧ e = {z, t} := EndpointPairProof.endpoint_edge
  have split_mem : ∀ (r : List GaussianInt) (z : GaussianInt),
      z ∈ r → ∃ l t, r = l ++ z :: t := EndpointPairProof.split_mem
  have endpoint_unique : ∀ (r : List GaussianInt) (z : GaussianInt),
      r.Nodup → 2 ≤ r.length → r.head? = some z →
      ∀ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) →
        z ∈ e₁ →
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) →
        z ∈ e₂ → e₁ = e₂ := EndpointPairProof.endpoint_unique endpoint_edge
  have interior_edges : ∀ (r : List GaussianInt) (z u v : GaussianInt),
      r.Nodup → r.head? = some u → r.getLast? = some v →
      z ∈ r → z ≠ u → z ≠ v →
      ∃ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) ∧
        z ∈ e₁ ∧
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) ∧
        z ∈ e₂ ∧ e₁ ≠ e₂ := EndpointPairProof.interior_edges split_mem
  have endpoint_class : ∀ z : GaussianInt,
      z ∈ q → q.head? = some z → z = x ∨ z = y := EndpointPairProof.endpoint_class V E x y p hp
          hx hy hV hE q hq hqlen hV' hE' endpoint_unique interior_edges
  have reverse_raw : ∀ (r : List GaussianInt) (e : Finset GaussianInt),
      (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) →
      ∃ a b l₁ l₂, r.reverse = l₁ ++ a :: b :: l₂ ∧ e = {a, b} := EndpointPairProof.reverse_raw
  have endpoint_unique_last : ∀ (r : List GaussianInt) (z : GaussianInt),
      r.Nodup → 2 ≤ r.length → r.getLast? = some z →
      ∀ e₁ e₂ : Finset GaussianInt,
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₁ = {a, b}) →
        z ∈ e₁ →
        (∃ a b l₁ l₂, r = l₁ ++ a :: b :: l₂ ∧ e₂ = {a, b}) →
        z ∈ e₂ → e₁ = e₂ := EndpointPairProof.endpoint_unique_last endpoint_unique reverse_raw
  have endpoint_class_last : ∀ z : GaussianInt,
      z ∈ q → q.getLast? = some z → z = x ∨ z = y := EndpointPairProof.endpoint_class_last V E x
          y p hp hx hy hV hE q hq hqlen hV' hE' interior_edges endpoint_unique_last
  have endpoint_ne : ∀ (r : List GaussianInt) (u v : GaussianInt),
      r.Nodup → 2 ≤ r.length → r.head? = some u →
      r.getLast? = some v → u ≠ v := EndpointPairProof.endpoint_ne
  have hx'q : x' ∈ q := EndpointPairProof.hx'q x' q hqlen hx'
  have hy'q : y' ∈ q := EndpointPairProof.hy'q y' q hy' hqne
  have hxclass : x' = x ∨ x' = y := endpoint_class x' hx'q hx'
  have hyclass : y' = x ∨ y' = y := endpoint_class_last y' hy'q hy'
  have hxy' : x' ≠ y' := endpoint_ne q x' y' hq hqlen hx' hy'
  rcases hxclass with rfl | rfl <;> rcases hyclass with rfl | rfl
  · exact False.elim (hxy' rfl)
  · simp [Finset.pair_comm]
  · simp [Finset.pair_comm]
  · exact False.elim (hxy' rfl)

end ApollonianSuperharmonic

end
