/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **small-box allocation residual**, by a nibble on the placement hypergraph

This file discharges `Nibble.AX1.BoxAllocationResidual`, the single remaining hypothesis of AX1
after `Nibble.AX1.ax1_of_boxAllocation` (`Nibble.CoarseCellCoupled`).

The proof is a weighted nibble on the placement hypergraph of `Nibble.BoxPlacementGraph`: the
vertices are the cell-pair slots of the cluster pairs together with one token per copy, the edges
are the placements of the copies, and the weight of a placement is the reciprocal of the number of
placements of its copy, so that every copy carries total weight `1`.  The three inputs of
`Nibble.fracNibble_leUniform` are

* *capacity*: the load of a slot of the cluster pair `(S,T)` is `boxDemand cl sz S T / P² ≤ 1 - ε`,
  which is literally the hypothesis of the residual, and the load of a token is `1`;
* *bounded edge size*: a placement occupies `1 + ∑_a sz(c,a)·sz(c,a+1) ≤ 1 + 3s₀²` vertices;
* *small codegrees*: two placements sharing two prescribed vertices are pinned down in one further
  coordinate, so every weighted codegree is `O(s₀/P) = O(θ)` — this is where the small-box
  restriction `s₀ ≤ θ·P` is used, and it is what fixes the threshold `θ` in terms of `ε` and `s₀`.

The matching produced is a partial allocation: distinct edges of a matching have distinct tokens,
hence belong to distinct copies, and their rectangles are disjoint in every shared cluster pair.
The copies it misses form the set `bad`; the nibble bounds their number by `β·(∑w + |X|) + C` with
`β = ε/(18 s₀²)`, and each of them has area at most `3s₀²`, whence the bound
`ε·(#clusters)²·P²` on the total area of `bad`.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.BoxPlacementGraph

/-! # Weighted nibble for box placement -/

@[expose] public section

open Finset

namespace Nibble.AX1

namespace BoxPlace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {P : ℕ}
  {cl : κ → ZMod 3 → ι} {sz : κ → ZMod 3 → ℕ}

omit [DecidableEq κ] in
/-- **There are not too many copies.**  Every copy demands at least one cell pair in the cluster
pair of its first two clusters, so the number of copies is at most the total capacity. -/
theorem card_copies_le {ε : ℝ} (hε0 : 0 ≤ ε) (hcl : ∀ c, Function.Injective (cl c))
    (hsz1 : ∀ c a, 1 ≤ sz c a)
    (hdem : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) :
    (Fintype.card κ : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  classical
  have hfib : ∀ p : ι × ι,
      ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card : ℝ) ≤ (P : ℝ) ^ 2 := by
    rintro ⟨S, T⟩
    by_cases hex : ∃ c : κ, (cl c 0, cl c 1) = (S, T)
    · obtain ⟨c0, hc0⟩ := hex
      have hST : S ≠ T := by
        intro h
        have e0 : cl c0 0 = S := congrArg Prod.fst hc0
        have e1 : cl c0 1 = T := congrArg Prod.snd hc0
        have h01 : (0 : ZMod 3) = 1 := hcl c0 (by rw [e0, e1, h])
        exact absurd h01 (by decide +kernel)
      have hstep : ∀ c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)),
          (1 : ℝ) ≤ boxDemandC cl sz c S T := by
        intro c hc
        rw [Finset.mem_filter] at hc
        have e0 : cl c 0 = S := congrArg Prod.fst hc.2
        have e1 : cl c 1 = T := congrArg Prod.snd hc.2
        have a0 : (1 : ℝ) ≤ (sz c 0 : ℝ) := by exact_mod_cast hsz1 c 0
        have a1 : (1 : ℝ) ≤ (sz c 1 : ℝ) := by exact_mod_cast hsz1 c 1
        have h01 : (1 : ℝ) ≤ (sz c 0 : ℝ) * (sz c 1 : ℝ) := by nlinarith
        exact le_trans h01 (sz_mul_le_boxDemandC e0 e1)
      have hle : ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T))).card : ℝ)
          ≤ boxDemand cl sz S T := by
        rw [boxDemand_eq_sum]
        calc ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T))).card : ℝ)
            = ∑ _c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)), (1 : ℝ) := by
              simp
          _ ≤ ∑ c ∈ Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)),
              boxDemandC cl sz c S T := Finset.sum_le_sum hstep
          _ ≤ ∑ c : κ, boxDemandC cl sz c S T :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun c _ _ => boxDemandC_nonneg c S T)
      refine le_trans hle (le_trans (hdem S T hST) ?_)
      nlinarith [sq_nonneg (P : ℝ)]
    · push Not at hex
      have hemp : Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = (S, T)) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
        rw [Finset.mem_filter] at hc
        exact hex c hc.2
      rw [hemp]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hcard : Fintype.card κ
      = ∑ p : ι × ι, (Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun c _ => Finset.mem_univ _)
  rw [hcard]
  push_cast
  calc ∑ p : ι × ι, ((Finset.univ.filter (fun c : κ => (cl c 0, cl c 1) = p)).card : ℝ)
      ≤ ∑ _p : ι × ι, (P : ℝ) ^ 2 := Finset.sum_le_sum fun p _ => hfib p
    _ = (Fintype.card (ι × ι) : ℝ) * (P : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
        rw [Fintype.card_prod]
        push_cast
        ring

/-- The default allocation of a copy: an initial segment of the cells of the right size. -/
def defaultAlloc (P : ℕ) (sz : κ → ZMod 3 → ℕ) (hszP : ∀ c a, sz c a ≤ P) (c : κ) :
    ZMod 3 → Finset (Fin P) :=
  fun a =>
    (Finset.range (sz c a)).attachFin (fun _ hm => lt_of_lt_of_le (mem_range.mp hm) (hszP c a))

omit [Fintype κ] [DecidableEq κ] in
theorem defaultAlloc_mem (hszP : ∀ c a, sz c a ≤ P) (c : κ) :
    defaultAlloc P sz hszP c ∈ BoxCount.plc P (sz c) := by
  rw [BoxCount.mem_plc]
  intro a
  simp [defaultAlloc]

end BoxPlace

open BoxPlace

private theorem bad_area_le {κ : Type} [Fintype κ] [DecidableEq κ]
    (sz : κ → ZMod 3 → ℕ) (good : Finset κ) (s₀ P n : ℕ) (ε β C θ : ℝ)
    (hs : ∀ c a, sz c a ≤ s₀) (hs₀ : (0 : ℝ) < (s₀ : ℝ))
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hθC : θ ≤ ε / (6 * C))
    (hsP : (s₀ : ℝ) ≤ θ * (P : ℝ)) (hn : (1 : ℝ) ≤ (n : ℝ))
    (hC : 0 < C) (hε : 0 < ε) (hβ : β = ε / (18 * (s₀ : ℝ) ^ 2))
    (hbad : ((Finset.univ \ good).card : ℝ)
      ≤ 3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C) :
    (∑ c ∈ Finset.univ \ good, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
      ≤ ε * (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  have harea : (∑ c ∈ Finset.univ \ good, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
      ≤ ((Finset.univ \ good).card : ℝ) * (3 * (s₀ : ℝ) ^ 2) := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro c _
    have hb : ∀ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ) ≤ (s₀ : ℝ) ^ 2 := by
      intro a
      have h1 : (sz c a : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs c a
      have h2 : (sz c (a + 1) : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs c (a + 1)
      have h3 : (0 : ℝ) ≤ (sz c a : ℝ) := Nat.cast_nonneg _
      have h4 : (0 : ℝ) ≤ (sz c (a + 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ)
        ≤ ∑ _a : ZMod 3, (s₀ : ℝ) ^ 2 := Finset.sum_le_sum (fun a _ => hb a)
      _ = 3 * (s₀ : ℝ) ^ 2 := by simp [ZMod.card]
  refine le_trans harea ?_
  have hs₀ne : (s₀ : ℝ) ≠ 0 := ne_of_gt hs₀
  have hCpos : (0 : ℝ) < 6 * C := by linarith
  have h2a : θ * θ ≤ θ * (ε / (6 * C)) := mul_le_mul_of_nonneg_left hθC hθ.le
  have h2b : θ * (ε / (6 * C)) ≤ 1 * (ε / (6 * C)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : θ ^ 2 ≤ ε / (6 * C) := by linarith only [h2a, h2b]
  have h1 : (s₀ : ℝ) * (s₀ : ℝ) ≤ (θ * (P : ℝ)) * (θ * (P : ℝ)) :=
    mul_self_le_mul_self hs₀.le hsP
  have h1' : (s₀ : ℝ) ^ 2 ≤ θ ^ 2 * (P : ℝ) ^ 2 := by linarith only [h1]
  have hst : (s₀ : ℝ) ^ 2 ≤ ε / (6 * C) * (P : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right h2 (sq_nonneg (P : ℝ))
    linarith only [h1', hmul]
  have h3 : 3 * (s₀ : ℝ) ^ 2 * C ≤ 3 * (ε / (6 * C) * (P : ℝ) ^ 2) * C := by
    have hmul := mul_le_mul_of_nonneg_right hst hC.le
    linarith only [hmul]
  have h4 : 3 * (ε / (6 * C) * (P : ℝ) ^ 2) * C = ε / 2 * (P : ℝ) ^ 2 := by
    field_simp; ring
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn]
  have h5 : (P : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
    nlinarith only [hn2, sq_nonneg (P : ℝ)]
  have hkey : 3 * (s₀ : ℝ) ^ 2 * C ≤ ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ ε / 2)
    linarith only [h3, h4, hmul]
  have hβs : 3 * β * (3 * (s₀ : ℝ) ^ 2) = ε / 2 := by
    rw [hβ]; field_simp; ring
  calc ((Finset.univ \ good).card : ℝ) * (3 * (s₀ : ℝ) ^ 2)
      ≤ (3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C) * (3 * (s₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hbad (by positivity)
    _ = (3 * β * (3 * (s₀ : ℝ) ^ 2)) * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2)
        + 3 * (s₀ : ℝ) ^ 2 * C := by ring
    _ = ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + 3 * (s₀ : ℝ) ^ 2 * C := by rw [hβs]
    _ ≤ ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + ε / 2 * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) := by
        linarith only [hkey]
    _ = ε * (n : ℝ) ^ 2 * (P : ℝ) ^ 2 := by ring

/-- **The small-box allocation residual, for a fixed accuracy and a fixed box bound.** -/
theorem boxAllocationResidual_main (ε : ℝ) (hε : 0 < ε) (s₀ : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∀ P : ℕ, 0 < P → (s₀ : ℝ) ≤ θ * (P : ℝ) →
      ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
        (cl : κ → ZMod 3 → ι) (sz : κ → ZMod 3 → ℕ),
        (∀ c, Function.Injective (cl c)) →
        (∀ c a, 1 ≤ sz c a) → (∀ c a, sz c a ≤ s₀) →
        (∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (1 - ε) * (P : ℝ) ^ 2) →
        ∃ (bad : Finset κ) (I : κ → ZMod 3 → Finset (Fin P)),
          (∀ c a, #(I c a) = sz c a) ∧
          (∀ c ∉ bad, ∀ c' ∉ bad, c ≠ c' → ∀ a b a' b' : ZMod 3, a ≠ b → a' ≠ b' →
            cl c a = cl c' a' → cl c b = cl c' b' →
            Disjoint (I c a) (I c' a') ∨ Disjoint (I c b) (I c' b')) ∧
          (∑ c ∈ bad, ∑ a : ZMod 3, (sz c a : ℝ) * (sz c (a + 1) : ℝ))
            ≤ ε * (Fintype.card ι : ℝ) ^ 2 * (P : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos s₀ with hs0 | hs0
  · -- no copies at all
    refine ⟨1, one_pos, le_rfl, ?_⟩
    intro P hP hsP ι κ _ _ _ _ cl sz hcl hsz1 hs hdem
    have hempty : IsEmpty κ := ⟨fun c => by have h1 := hsz1 c 0; have h2 := hs c 0; omega⟩
    refine ⟨∅, fun c => hempty.elim c, fun c => hempty.elim c,
      fun c _ => hempty.elim c, ?_⟩
    simp only [Finset.sum_empty]
    positivity
  · -- the main case
    have hs0R : (0 : ℝ) < (s₀ : ℝ) := by exact_mod_cast hs0
    have hs1R : (1 : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs0
    obtain ⟨γ, hγ, C, hC, hnib⟩ :=
      fracNibble_leUniform (1 + 3 * s₀ ^ 2) (by nlinarith only [hs0]) (ε / (18 * (s₀ : ℝ) ^ 2))
        (by positivity)
    set β : ℝ := ε / (18 * (s₀ : ℝ) ^ 2) with hβdef
    have hβ : 0 < β := by rw [hβdef]; positivity
    refine ⟨min (1 / 2) (min (γ / 18) (ε / (6 * C))), lt_min (by norm_num)
      (lt_min (by positivity) (by positivity)),
      le_trans (min_le_left _ _) (by norm_num), ?_⟩
    set θ : ℝ := min (1 / 2) (min (γ / 18) (ε / (6 * C))) with hθdef
    have hθ12 : θ ≤ 1 / 2 := min_le_left _ _
    have hθγ : θ ≤ γ / 18 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hθC : θ ≤ ε / (6 * C) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hθ0 : 0 < θ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    intro P hP hsP ι κ _ _ _ _ cl sz hcl hsz1 hs hdem
    have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    -- `P` is large
    have h2PR : (2 : ℝ) ≤ (P : ℝ) := by nlinarith only [hsP, hθ12, hs1R, hPR]
    have h2P : 2 ≤ P := by exact_mod_cast h2PR
    have hs0P : s₀ ≤ P := by
      have : (s₀ : ℝ) ≤ (P : ℝ) := by nlinarith only [hsP, hθ12, hPR]
      exact_mod_cast this
    have hszP : ∀ c a, sz c a ≤ P := fun c a => le_trans (hs c a) hs0P
    -- an injective indexing of the clusters
    set idx : ι → ℕ := fun S => ((Fintype.equivFin ι S : Fin (Fintype.card ι)) : ℕ) with hidxdef
    have hidx : Function.Injective idx := by
      intro S T h
      have : (Fintype.equivFin ι) S = (Fintype.equivFin ι) T := by
        apply Fin.ext; exact h
      exact (Fintype.equivFin ι).injective this
    set n : ℕ := Fintype.card ι with hndef
    set K := placeFam P idx cl sz with hKdef
    set w : Finset (PlaceVtx ι κ P) → ℝ := placeWt P sz with hwdef
    have hdemP : ∀ S T : ι, S ≠ T → boxDemand cl sz S T ≤ (P : ℝ) ^ 2 := by
      intro S T hST
      refine le_trans (hdem S T hST) ?_
      nlinarith [sq_nonneg (P : ℝ)]
    -- the hypotheses of the nibble
    have hedge : ∀ U ∈ K, U.Nonempty ∧ #U ≤ 1 + 3 * s₀ ^ 2 :=
      fun U hU => placeFam_edge_size hidx hcl hsz1 hs U hU
    have hw0 : ∀ U, 0 ≤ w U := fun U => placeWt_nonneg U
    have hload : ∀ v : PlaceVtx ι κ P, Slack.wLoad K w v ≤ 1 := by
      rintro (⟨S, T, i, j⟩ | c)
      · by_cases hlt : idx S < idx T
        · have hST : S ≠ T := by
            intro h; rw [h] at hlt; exact lt_irrefl _ hlt
          refine le_trans (wLoad_inl_le hidx hcl hsz1 hszP hP S T i j) ?_
          rw [div_le_one (by positivity)]
          exact hdemP S T hST
        · rw [wLoad_inl_of_not_lt hidx hcl hsz1 hlt]; norm_num
      · rw [wLoad_inr hidx hcl hsz1 hszP]
    have hbound : 18 * (s₀ : ℝ) / (P : ℝ) ≤ γ := by
      have hsθ : (s₀ : ℝ) / (P : ℝ) ≤ θ := by
        rw [div_le_iff₀ hPR]; linarith only [hsP]
      calc 18 * (s₀ : ℝ) / (P : ℝ) = 18 * ((s₀ : ℝ) / (P : ℝ)) := by ring
        _ ≤ 18 * θ := by linarith
        _ ≤ γ := by linarith only [hθγ]
    obtain ⟨M, hM, hMcard⟩ := hnib K w hedge hw0 hload (by
      intro x z hxz
      refine le_trans (le_of_eq ?_)
        (le_trans (codeg_le hidx hcl hsz1 hszP h2P hs hs0P hdemP x z hxz) hbound)
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext U
      simp only [Finset.mem_filter]
      tauto)
    -- the copies that the matching places
    set good : Finset κ := M.biUnion Finset.toRight with hgooddef
    have htoRight : ∀ U ∈ M, ∃ c : κ, U.toRight = {c} := by
      intro U hU
      obtain ⟨c, A, -, rfl⟩ := mem_placeFam (hM.subset hU)
      exact ⟨c, placeEdge_toRight⟩
    have hpwd : ∀ U ∈ M, ∀ V ∈ M, U ≠ V → Disjoint U.toRight V.toRight := by
      intro U hU V hV hUV
      obtain ⟨c, hc⟩ := htoRight U hU
      obtain ⟨d, hd⟩ := htoRight V hV
      rw [hc, hd, Finset.disjoint_singleton]
      intro hcd
      subst hcd
      have hdisj := hM.disjoint U hU V hV hUV
      have hcU : (Sum.inr c : PlaceVtx ι κ P) ∈ U := by
        have : c ∈ U.toRight := by rw [hc]; exact Finset.mem_singleton_self c
        rwa [Finset.mem_toRight] at this
      have hcV : (Sum.inr c : PlaceVtx ι κ P) ∈ V := by
        have : c ∈ V.toRight := by rw [hd]; exact Finset.mem_singleton_self c
        rwa [Finset.mem_toRight] at this
      exact absurd hcV (Finset.disjoint_left.mp hdisj hcU)
    have hgoodcard : #good = #M := by
      have hcb := Finset.card_biUnion (s := M) (t := fun U : Finset (PlaceVtx ι κ P) => U.toRight)
        (fun U hU V hV hUV => hpwd U hU V hV hUV)
      rw [hgooddef, hcb]
      rw [Finset.sum_congr rfl (fun U hU => ?_), Finset.sum_const, smul_eq_mul, mul_one]
      obtain ⟨c, hc⟩ := htoRight U hU
      change #U.toRight = 1
      rw [hc, Finset.card_singleton]
    -- the placement of each copy
    have hchoice : ∀ c : κ, ∃ A : ZMod 3 → Finset (Fin P), A ∈ BoxCount.plc P (sz c) ∧
        (c ∈ good → placeEdge idx cl c A ∈ M) := by
      intro c
      by_cases hc : c ∈ good
      · rw [hgooddef, Finset.mem_biUnion] at hc
        obtain ⟨U, hU, hcU⟩ := hc
        obtain ⟨c', A, hA, rfl⟩ := mem_placeFam (hM.subset hU)
        have : c = c' := by
          have := placeEdge_toRight (idx := idx) (cl := cl) (c := c') (A := A)
          rw [this, Finset.mem_singleton] at hcU
          exact hcU
        subst this
        exact ⟨A, hA, fun _ => hU⟩
      · exact ⟨defaultAlloc P sz hszP c, defaultAlloc_mem hszP c, fun h => absurd h hc⟩
    choose A hAmem hAM using hchoice
    have hAcard : ∀ c a, #(A c a) = sz c a := fun c a => (BoxCount.mem_plc.mp (hAmem c)) a
    have hAne : ∀ c a, (A c a).Nonempty := by
      intro c a
      rw [← Finset.card_pos, hAcard]
      exact hsz1 c a
    refine ⟨Finset.univ \ good, A, hAcard, ?_, ?_⟩
    · -- the rectangles of two placed copies are disjoint
      intro c hc c' hc' hcc a b a' b' hab ha'b' hSa hSb
      have hcg : c ∈ good := by
        by_contra h
        exact hc (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, h⟩)
      have hcg' : c' ∈ good := by
        by_contra h
        exact hc' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c', h⟩)
      have hE : placeEdge idx cl c (A c) ∈ M := hAM c hcg
      have hE' : placeEdge idx cl c' (A c') ∈ M := hAM c' hcg'
      have hEne : placeEdge idx cl c (A c) ≠ placeEdge idx cl c' (A c') := by
        intro h
        exact hcc (placeEdge_inj hidx (hcl c) (hcl c') (hAne c) (hAne c') h).1
      have hdisj := hM.disjoint _ hE _ hE' hEne
      by_contra hcon
      push Not at hcon
      obtain ⟨hd1, hd2⟩ := hcon
      obtain ⟨i, hi, hi'⟩ := Finset.not_disjoint_iff.mp hd1
      obtain ⟨j, hj, hj'⟩ := Finset.not_disjoint_iff.mp hd2
      have hmem : (Sum.inl (orient idx (cl c a) (cl c b) i j) : PlaceVtx ι κ P)
          ∈ placeEdge idx cl c (A c) := mem_placeEdge_orient hidx (hcl c) hab hi hj
      have hmem' : (Sum.inl (orient idx (cl c a) (cl c b) i j) : PlaceVtx ι κ P)
          ∈ placeEdge idx cl c' (A c') := by
        have : orient idx (cl c a) (cl c b) i j = orient idx (cl c' a') (cl c' b') i j := by
          rw [hSa, hSb]
        rw [this]
        exact mem_placeEdge_orient hidx (hcl c') ha'b' hi' hj'
      exact (Finset.disjoint_left.mp hdisj hmem) hmem'
    · -- the copies left out have small total area
      rcases isEmpty_or_nonempty κ with hκ | hκ
      · have : (Finset.univ : Finset κ) \ good = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro c _
          exact hκ.elim c
        rw [this, Finset.sum_empty]
        positivity
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have : 0 < n := by
            rw [hndef]
            exact Fintype.card_pos_iff.mpr ⟨cl hκ.some 0⟩
          exact_mod_cast this
        -- the number of unplaced copies
        have hbadcard : ((Finset.univ \ good).card : ℝ) = (Fintype.card κ : ℝ) - (#M : ℝ) := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hgoodcard]
          have hMle : #M ≤ Fintype.card κ := by
            rw [← hgoodcard, ← Finset.card_univ]
            exact Finset.card_le_card (Finset.subset_univ _)
          rw [Finset.card_univ, Nat.cast_sub hMle]
        have hsumw : ∑ U ∈ K, w U = (Fintype.card κ : ℝ) := sum_placeWt hidx hcl hsz1 hszP
        have hX : (Fintype.card (PlaceVtx ι κ P) : ℝ)
            = (n : ℝ) ^ 2 * (P : ℝ) ^ 2 + (Fintype.card κ : ℝ) := by
          simp only [PlaceVtx, Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hndef]
          push_cast
          ring
        have hκle : (Fintype.card κ : ℝ) ≤ (n : ℝ) ^ 2 * (P : ℝ) ^ 2 :=
          card_copies_le hε.le hcl hsz1 hdem
        rw [hsumw, hX] at hMcard
        -- so the number of unplaced copies is at most `3β n²P² + C`
        have hbad : ((Finset.univ \ good).card : ℝ)
            ≤ 3 * β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) + C := by
          have hmul : β * (Fintype.card κ : ℝ) ≤ β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hκle hβ.le
          have hexp : (1 - β) * (Fintype.card κ : ℝ)
              - β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2 + (Fintype.card κ : ℝ)) - C
              = (Fintype.card κ : ℝ) - 2 * (β * (Fintype.card κ : ℝ))
                - β * ((n : ℝ) ^ 2 * (P : ℝ) ^ 2) - C := by ring
          rw [hexp] at hMcard
          rw [hbadcard]
          linarith only [hMcard, hmul]
        -- each unplaced copy has area at most `3s₀²`
        exact bad_area_le sz good s₀ P n ε β C θ hs hs0R hθ0 (by linarith) hθC hsP hn1 hC hε
          hβdef hbad

/-- **The small-box allocation residual.** -/
theorem boxAllocationResidual_holds : BoxAllocationResidual :=
  fun ε hε s₀ => boxAllocationResidual_main ε hε s₀

end Nibble.AX1
