/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14t

/-!
# Graph Minors XIX, Section 14: the outline `τ`

Here we define `τ` on the sectors and the hub sectors, as in the paper, and we check that the
marches correspond.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {Da Db : TangleDatum cap χ} {𝒲a 𝒲b : Set
    (Set Shat)}

/-- An arm with nothing in it. -/
def trivialArm (Γ : Painting S) : Arm Γ where
  minus := Γ.toHypergraph
  compl := ⟨∅, ∅, fun _ _ ↦ False, fun _ _ h ↦ h.elim, fun _ _ h ↦ h.elim, finite_empty,
    finite_empty⟩
  isSeparation := by
    refine ⟨le_refl _, ⟨empty_subset _, empty_subset _, fun e he ↦ he.elim⟩, ?_, inter_empty _⟩
    refine Hypergraph.ext (union_empty _) (union_empty _) ?_
    funext e v
    apply propext
    change _ ∨ False ↔ _
    simp
  π := []
  π_nodup := List.nodup_nil
  π_set := by
    ext v
    simp only [mem_ofPred_eq, List.not_mem_nil, false_iff]
    exact fun h ↦ h.2.elim

/-- The march of the image of a sector corresponds to the march of the sector. -/
theorem Stair.back_π {Wa Wb : Set Shat} {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {θ : ℕ → ℕ}
  (h : Stair a b θ (rtOf a b)) {q : ℕ} (hq : q < b.R.k)
    (hmove : q + 1 < b.R.k → θ (q + 1) = θ q + 1) (hlast : b.R.k ≤ q + 1 → θ q + 1 = a.R.k)
      (hc : b.code q = a.code (θ q)) :
    (b.secArm q).π.length = (a.secArm (θ q)).π.length ∧ ∀ (n : ℕ) (hn : n < (a.secArm
      (θ q)).π.length) (hn' : n < (b.secArm q).π.length),
      Stair.Back a b θ (rtOf a b) (cap.emb (b.secArm q).π[n]) (cap.emb (a.secArm (θ q)).π[n]) := by
  have hl := congrArg (fun c : WheelFrame.CodeT ↦ c.2.2.2.2.2) hc
  simp only [WheelFrame.code] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_map] at hlen
  refine ⟨hlen, fun n hn hn' ↦ ?_⟩
  have he : b.addr q (b.secArm q).π[n] = a.addr (θ q) (a.secArm (θ q)).π[n] := by
    have := List.getElem_of_eq hl (i := n) (by simpa using hn')
    simpa using this
  have hlev₂ : ∀ t, t ≤ b.top (q + 1) → b.levV (q + 1) t = b.levV (q + 1) t → Stair.Lev a b θ
    (b.levV (q + 1) t) (a.levV (θ q + 1) t) := by
    intro t ht _
    by_cases hq₁ : q + 1 < b.R.k
    · exact ⟨q + 1, hq₁, t, ht, rfl, by rw [hmove hq₁]⟩
    · have h₁ : q + 1 = 0 + b.R.k := by omega
      have h₂ := hlast (by omega)
      have hb : b.R.vert (q + 1) = b.R.vert 0 := by rw [h₁]; exact b.R.vert_add_k 0
      have ha : a.R.vert (θ q + 1) = a.R.vert 0 := by
        rw [h₂, show a.R.k = 0 + a.R.k by omega]
        exact a.R.vert_add_k 0
      exact ⟨0, by omega, t, by rw [← b.top_congr hb]; exact ht,
        b.levV_congr hb t, by rw [h.zero]; exact a.levV_congr ha t⟩
  rcases b.addr_spec (List.getElem_mem hn') with ⟨t, ht, e, ey⟩ | ⟨t, ht, e, ey⟩ | ⟨j, e, ey⟩ <;>
    rcases a.addr_spec (List.getElem_mem hn) with
    ⟨t', ht', e', ex⟩ | ⟨t', ht', e', ex⟩ | ⟨j', e', ex⟩ <;>
    rw [e, e'] at he <;>
    simp only [Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, false_and, Sum.inr.injEq, true_and,
      Bool.false_eq_true, Bool.true_eq_false] at he
  · obtain rfl := he
    exact .inl ⟨q, hq, t, ht, ey, ex⟩
  · obtain rfl := he
    rw [ey, ex]
    exact .inl (hlev₂ t ht rfl)
  · obtain rfl := he
    exact .inr (.inl ⟨j, ey, ex⟩)

theorem Stair.exists_top {Wa Wb : Set Shat} {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {θ : ℕ
  → ℕ} {R : Shat → Shat → Prop} (h : Stair a b θ R) {p : ℕ} (hp : p < a.R.k) :
    ∃ q < b.R.k, θ q = p ∧ (q + 1 < b.R.k → θ (q + 1) = θ q + 1) ∧ (b.R.k ≤ q + 1 → θ q + 1
      = a.R.k) := by
  classical
  obtain ⟨q₀, hq₀, e₀⟩ := h.surj hp
  have hex : ∃ q, q < b.R.k ∧ θ q = p := ⟨q₀, hq₀, e₀⟩
  have hbd : ∀ q, (q < b.R.k ∧ θ q = p) → q ≤ b.R.k := fun q hq ↦ hq.1.le
  let q := Nat.findGreatest (fun q ↦ q < b.R.k ∧ θ q = p) b.R.k
  have hs : q < b.R.k ∧ θ q = p := Nat.findGreatest_spec (P := fun q ↦ q < b.R.k ∧ θ q = p)
    (hbd q₀ ⟨hq₀, e₀⟩) ⟨hq₀, e₀⟩
  refine ⟨q, hs.1, hs.2, fun hq ↦ ?_, fun hq ↦ ?_⟩
  · rcases h.step q hq with e | e
    · have : q + 1 ≤ q := Nat.le_findGreatest (P := fun q ↦ q < b.R.k ∧ θ q
        = p) hq.le ⟨hq, e.trans hs.2⟩
      omega
    · exact e
  · have h₁ : q = b.R.k - 1 := by have := hs.1; omega
    rw [h₁, h.last]
    have := a.R.two
    omega

/-- The hypotheses of the outline, for two sequences of wheels. -/
structure OutlineData (fa : ∀ W : ↥𝒲a, WheelFrame Da W.1) (fb : ∀ W : ↥𝒲b, WheelFrame Db W.1)
  (p : ↥𝒲a → ↥𝒲b) (Out : Shat → Shat → Prop) (Sym : ↥𝒲a → ℕ → ℕ → Prop) {β : Type*}
    (Ω : QuasiOrder β)
    (ξa : Arm Da.P.Γ → β) (ξb : Arm Db.P.Γ → β) : Prop where
  p_bij : Function.Bijective p
  out_fun : ∀ {y x x'}, Out y x → Out y x' → x = x'
  walk : ∀ W, RimWalk (fa W) (fb (p W)) Out (Sym W)
  sym_le : ∀ W q i, Sym W q i → Ω.le (ξa ((fa W).secArm i)) (ξb ((fb (p W)).secArm q))
  hub : ∀ W (hc : (fa W).H.V.ncard ≠ 1), ∃ hc' : (fb (p W)).H.V.ncard ≠ 1, Ω.le (ξa
    ((fa W).hubArm hc)) (ξb ((fb (p W)).hubArm hc'))
  out_hat : ∀ {y x}, Out y x → y ∈ Db.P.Γ.hatV cap ∧ x ∈ Da.P.Γ.hatV cap
  out_off_b : ∀ {y x}, Out y x → ∀ W : ↥𝒲b, y ∉ discInt W.1
  out_off_a : ∀ {y x}, Out y x → ∀ W : ↥𝒲a, x ∉ discInt W.1
  out_ne : ∀ x ∈ Da.P.Γ.hatV cap, (∀ W : ↥𝒲a, x ∉ discInt W.1) → ∃ y, Out y x
  out_conn : ∀ {y y' x}, Out y x → Out y' x → Relation.ReflTransGen (OutStep fb Out x) y y'

/-- **The outline of (14.1).** -/
theorem OutlineData.exists_outline {fa : ∀ W : ↥𝒲a, WheelFrame Da W.1} {fb : ∀ W : ↥𝒲b, WheelFrame
  Db W.1} {p : ↥𝒲a → ↥𝒲b} {Out : Shat → Shat → Prop} {Sym : ↥𝒲a → ℕ → ℕ
    → Prop} {β : Type*} {Ω : QuasiOrder β}
    {ξa : Arm Da.P.Γ → β} {ξb : Arm Db.P.Γ → β} (h : OutlineData fa fb p Out Sym Ω ξa ξb)
      (hd : χ.IsDisjoint) (hfa : 𝒲a.Finite) (hda : 𝒲a.PairwiseDisjoint id) (hfb : 𝒲b.Finite)
        (hdb : 𝒲b.PairwiseDisjoint id)
    (σe : Set S → Set S)
    (hem : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, σe e ∈ (coverLoc 𝒲b hfb hdb fb).M.edgeSet)
    (hsize : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, (tilde (σe e)).ncard = (tilde e).ncard)
    (hinj : InjOn σe (coverLoc 𝒲a hfa hda fa).M.edgeSet)
    (hends : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, ∀ (i : ℕ) (hi : i < (Da.P.Γ.γ e).length)
      (hi' : i < (Db.P.Γ.γ (σe e)).length),
      Out (cap.emb (Db.P.Γ.γ (σe e))[i]) (cap.emb (Da.P.Γ.γ e)[i]))
    (hle : ∀ e ∈ (coverLoc 𝒲a hfa hda fa).M.edgeSet, χ.unionLE (Da.P.φ e) (Db.P.φ (σe e))) :
    ∃ τ : Arm Da.P.Γ → Arm Db.P.Γ, IsOutline (⟨hd, Da.P, coverLoc 𝒲a hfa hda fa⟩ : Place χ) ⟨hd,
      Db.P, coverLoc 𝒲b hfb hdb fb⟩ τ ∧
      ∀ A ∈ (coverLoc 𝒲a hfa hda fa).arms, Ω.le (ξa A) (ξb (τ A)) := by
  classical
  have hst : ∀ W, ∃ θ, Stair (fa W) (fb (p W)) θ (rtOf (fa W) (fb (p W))) ∧ (∀ q < (fb
    (p W)).R.k, Out ((fb (p W)).R.vert q) ((fa W).R.vert (θ q))) ∧
      (∀ q, q + 1 < (fb (p W)).R.k → θ (q + 1) = θ q + 1 → Sym W q (θ q)) := fun W ↦
        (h.walk W).exists_stair
  choose θ hθ hrim hsym using hst
  have hsys : StairSystem fa fb p θ (fun W ↦ rtOf (fa W) (fb (p W))) Out :=
    ⟨h.p_bij, hθ, h.out_fun, h.out_hat, h.out_off_b, h.out_off_a, hrim, h.out_ne, h.out_conn⟩
  have hS : ∀ W q, q < (fb (p W)).R.k → (q + 1 < (fb (p W)).R.k → θ W (q + 1) = θ W q + 1)
    → Sym W q (θ W q) := fun W q hq hm ↦ by
    by_cases hq₁ : q + 1 < (fb (p W)).R.k
    · exact hsym W q hq₁ (hm hq₁)
    · have e : q = (fb (p W)).R.k - 1 := by omega
      rw [e, (hθ W).last]
      exact (h.walk W).last_sym
  let rel : Arm Da.P.Γ → Arm Db.P.Γ → Prop := fun A A' ↦
    (∃ W, ∃ q, q < (fb (p W)).R.k ∧ A = (fa W).secArm (θ W q) ∧ A' = (fb (p W)).secArm q ∧ (q + 1 <
      (fb (p W)).R.k → θ W (q + 1) = θ W q + 1) ∧ ((fb (p W)).R.k ≤ q + 1 → θ W q + 1 =
        (fa W).R.k)) ∨
      ∃ W, ∃ (hc : (fa W).H.V.ncard ≠ 1) (hc' : (fb (p W)).H.V.ncard ≠ 1), A = (fa W).hubArm hc
        ∧ A' = (fb (p W)).hubArm hc' ∧ Ω.le (ξa ((fa W).hubArm hc)) (ξb ((fb (p W)).hubArm hc'))
  have hrel : ∀ A ∈ (coverLoc 𝒲a hfa hda fa).arms, ∃ A', rel A A' := by
    intro A hA
    obtain ⟨W, hW⟩ := mem_iUnion.mp hA
    rcases hW with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩
    · obtain ⟨q, hq, rfl, h₁, h₂⟩ := (hθ W).exists_top hi
      exact ⟨_, .inl ⟨W, q, hq, rfl, rfl, h₁, h₂⟩⟩
    · obtain ⟨hc', hl⟩ := h.hub W hc
      exact ⟨_, .inr ⟨W, hc, hc', rfl, rfl, hl⟩⟩
  let τ : Arm Da.P.Γ → Arm Db.P.Γ := fun A ↦ if hA : ∃ A', rel A A' then hA.choose else trivialArm _
  have hτ : ∀ A ∈ (coverLoc 𝒲a hfa hda fa).arms, rel A (τ A) := fun A hA ↦ by
    simp only [τ, dite_eq_left (hrel A hA)]
    exact (hrel A hA).choose_spec
  have hmemS : ∀ W i, i < (fa W).R.k → (fa W).secArm i ∈ (coverLoc 𝒲a hfa hda fa).arms
    := fun W i hi ↦ mem_iUnion.mpr ⟨W, .inl ⟨i, hi, rfl⟩⟩
  have hmemH : ∀ W hc, (fa W).hubArm hc ∈ (coverLoc 𝒲a hfa hda fa).arms
    := fun W hc ↦ mem_iUnion.mpr ⟨W, .inr ⟨hc, rfl⟩⟩
  have hτS : ∀ W, ∀ i < (fa W).R.k, ∃ q < (fb (p W)).R.k, θ W q = i ∧ (q + 1 < (fb (p W)).R.k → θ W
    (q + 1) = θ W q + 1) ∧ ((fb (p W)).R.k ≤ q + 1 → θ W q + 1 = (fa W).R.k) ∧ τ ((fa W).secArm i)
      = (fb (p W)).secArm q := by
    intro W i hi
    rcases hτ _ (hmemS W i hi) with ⟨W', q, hq, e, e', h₁, h₂⟩ | ⟨W', hc, hc', e, -, -⟩
    · have hin := (hθ W').lt hq
      obtain rfl : W = W' := arm_wheel (Db := Da) hda (fb := fa) (.inl ⟨i, hi, rfl⟩)
        (e ▸ .inl ⟨_, hin, rfl⟩)
      obtain rfl := (fa W).secArm_inj hi hin e
      exact ⟨q, hq, rfl, h₁, h₂, e'⟩
    · obtain rfl : W = W' := arm_wheel (Db := Da) hda (fb := fa) (.inl ⟨i, hi, rfl⟩)
        (e ▸ .inr ⟨hc, rfl⟩)
      exact absurd e (sec_ne_hub _ hc i)
  have hτH : ∀ W (hc : (fa W).H.V.ncard ≠ 1), ∃ hc' : (fb (p W)).H.V.ncard ≠ 1, τ
    ((fa W).hubArm hc) = (fb (p W)).hubArm hc' ∧ Ω.le (ξa ((fa W).hubArm hc)) (ξb ((fb
      (p W)).hubArm hc')) := by
    intro W hc
    rcases hτ _ (hmemH W hc) with ⟨W', q, hq, e, -, -, -⟩ | ⟨W', hc₁, hc', e, e', hl⟩
    · have hin := (hθ W').lt hq
      obtain rfl : W = W' := arm_wheel (Db := Da) hda (fb := fa) (.inr ⟨hc, rfl⟩)
        (e ▸ .inl ⟨_, hin, rfl⟩)
      exact absurd e.symm (sec_ne_hub _ hc _)
    · obtain rfl : W = W' := arm_wheel (Db := Da) hda (fb := fa) (.inr ⟨hc, rfl⟩)
        (e ▸ .inr ⟨hc₁, rfl⟩)
      exact ⟨hc', e', hl⟩
  have hπ : ∀ W, ∀ A ∈ (fa W).arms, (τ A).π.length = A.π.length ∧ ∀ (i : ℕ) (hi : i < A.π.length)
    (hi' : i < (τ A).π.length),
      Stair.Back (fa W) (fb (p W)) (θ W) (rtOf (fa W) (fb (p W))) (cap.emb (τ A).π[i])
        (cap.emb A.π[i]) := by
    rintro W _ (⟨i, hi, rfl⟩ | ⟨hc, rfl⟩)
    · obtain ⟨q, hq, rfl, h₁, h₂, e⟩ := hτS W i hi
      rw [e]
      exact (hθ W).back_π hq h₁ h₂ ((h.walk W).sym_code _ _ (hS W q hq h₁))
    · obtain ⟨hc', e, -⟩ := hτH W hc
      rw [e]
      have hl := (h.walk W).hub_len
      rw [(fb (p W)).hubList_of hc', (fa W).hubList_of hc, List.length_map, List.length_map] at hl
      refine ⟨hl, fun n hn hn' ↦ .inr (.inl ⟨n, ?_, ?_⟩)⟩
      · rw [(fb (p W)).hubList_of hc', List.getElem?_map, List.getElem?_eq_getElem hn']
        rfl
      · rw [(fa W).hubList_of hc, List.getElem?_map, List.getElem?_eq_getElem hn]
        rfl
  refine ⟨τ, hsys.isOutline hd hfa hda hfb hdb τ σe (fun W i hi ↦ ?_)
    (fun W hc ↦ ?_) hπ hem hsize hinj hends hle, fun A hA ↦ ?_⟩
  · obtain ⟨q, hq, h₁, h₂, -, e⟩ := hτS W i hi
    exact ⟨q, hq, h₁, h₂, e⟩
  · obtain ⟨hc', e, -⟩ := hτH W hc
    exact ⟨hc', e⟩
  · obtain ⟨W, hW⟩ := mem_iUnion.mp hA
    rcases hW with ⟨i, hi, rfl⟩ | ⟨hc, rfl⟩
    · obtain ⟨q, hq, rfl, h₁, -, e⟩ := hτS W i hi
      rw [e]
      exact h.sym_le W q _ (hS W q hq h₁)
    · obtain ⟨hc', e, hl⟩ := hτH W hc
      rw [e]
      exact hl

end GraphMinor.GM19
