/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14s

/-!
# Graph Minors XIX, Section 14: a staircase from a walk around the rim

We walk around the rim of a wheel of `Γ_j` and follow the inflation. At each step we stay at the
same vertex of the rim of `Γ_i`, or we
move to the next one, and then the two sectors have the same code. This gives a staircase in the
sense of `Stair`.
-/

@[expose] public section

namespace GraphMinor.GM19

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α} {D Da Db : TangleDatum cap χ} {W Wa Wb :
    Set Shat}

namespace TangleDatum.WheelFrame

theorem spoke_len_of_inner (fr : WheelFrame D W) {i j : ℕ} (h : fr.R.inner fr.sp i
  = fr.R.inner fr.sp j) : (fr.R.spoke fr.sp i).length = (fr.R.spoke fr.sp j).length := by
  have key : ∀ {v₁ v₂ h₁ h₂ : Shat} (K₁ : GraphWalk D.rad.G.toGraph v₁ h₁)
    (K₂ : GraphWalk D.rad.G.toGraph v₂ h₂), h₁ = h₂ → v₁ ∈ D.P.Γ.hatV cap → v₂ ∈ D.P.Γ.hatV cap →
      D.IsSpokeWalk W fr.H K₁ → D.IsSpokeWalk W fr.H K₂ → K₁.length = K₂.length := by
    rintro v₁ v₂ h₁ h₂ K₁ K₂ rfl h₃ h₄ h₅ h₆
    exact spoke_length_eq fr.hW h₃ h₄ h₅ h₆
  exact key _ _ h (fr.vert_hatV i) (fr.vert_hatV j) (fr.spoke_spoke i) (fr.spoke_spoke j)

theorem lev_top_eq_inner (fr : WheelFrame D W) {i : ℕ} (h : fr.levV i
  (fr.top i) ∈ fr.hubList) : fr.levV i (fr.top i) = fr.R.inner fr.sp i ∧ Even
    (fr.R.spoke fr.sp i).length := by
  have hK := fr.spoke_spoke i
  have hin : fr.levV i (fr.top i) ∈ hubSet D fr.H ∩ (walkDrawing D.rad.G (fr.R.spoke fr.sp i)).U :=
    ⟨(fr.hW.hubSet_facts).2.2.2 (fr.mem_hubList.mp h).1, (mem_walkDrawing_U _ _).mpr (.inl
      (fr.levV_support le_rfl))⟩
  rw [fr.hW.hubSet_inter_spoke hK] at hin
  have hmemV : fr.R.inner fr.sp i ∈ D.rad.G.V := GraphWalk.support_mem_V _
    (GraphWalk.end_mem_support (fr.R.spoke fr.sp i))
  have hlen : GraphWalk.vertexAt (fr.R.spoke fr.sp i) (fr.R.spoke fr.sp i).length
    = fr.R.inner fr.sp i := GraphWalk.vertexAt_length _ hmemV
  have htl : 2 * fr.top i ≤ (fr.R.spoke fr.sp i).length := by
    rw [top]
    omega
  have e : 2 * fr.top i = (fr.R.spoke fr.sp i).length := GraphWalk.vertexAt_inj _ hK.1 htl le_rfl
    (hin.trans hlen.symm)
  exact ⟨hin, ⟨fr.top i, by omega⟩⟩

theorem lev_top_of_even (fr : WheelFrame D W) {i : ℕ} (h : Even (fr.R.spoke fr.sp i).length) :
  fr.levV i (fr.top i) = fr.R.inner fr.sp i := by
  have hmemV : fr.R.inner fr.sp i ∈ D.rad.G.V := GraphWalk.support_mem_V _
    (GraphWalk.end_mem_support (fr.R.spoke fr.sp i))
  have hlen : GraphWalk.vertexAt (fr.R.spoke fr.sp i) (fr.R.spoke fr.sp i).length
    = fr.R.inner fr.sp i := GraphWalk.vertexAt_length _ hmemV
  rw [← hlen, levV, top]
  obtain ⟨c, hc⟩ := h
  congr 1
  omega

/-- Two spokes with the same inner end have the same place in the hub list. -/
theorem hIdx_of_reg (fr : WheelFrame D W) {i j : ℕ} (h : fr.R.inner fr.sp i
  = fr.R.inner fr.sp j) : fr.hIdx i = fr.hIdx j := by
  classical
  have hl := fr.spoke_len_of_inner h
  by_cases h₁ : fr.levV i (fr.top i) ∈ fr.hubList
  · obtain ⟨e, ev⟩ := fr.lev_top_eq_inner h₁
    have e' := fr.lev_top_of_even (i := j) (hl ▸ ev)
    simp only [hIdx]
    rw [e, e', h]
  · by_cases h₂ : fr.levV j (fr.top j) ∈ fr.hubList
    · obtain ⟨e, ev⟩ := fr.lev_top_eq_inner h₂
      have e' := fr.lev_top_of_even (i := i) (hl.symm ▸ ev)
      rw [e', h, ← e] at h₁
      exact absurd h₂ h₁
    · simp only [hIdx]
      rw [List.idxOf_of_notMem h₁, List.idxOf_of_notMem h₂]

theorem hIdx_congr (fr : WheelFrame D W) {i j : ℕ} (h : fr.R.vert i = fr.R.vert j) : fr.hIdx i
  = fr.hIdx j := by
  classical
  simp only [hIdx]
  rw [fr.top_congr h, fr.levV_congr h]

end TangleDatum.WheelFrame

open TangleDatum.WheelFrame in
/-- The pairing of the vertices of `Γ` on two hubs. -/
def rtOf (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (y x : Shat) : Prop
  := ∃ j : ℕ, b.hubList[j]? = some y ∧ a.hubList[j]? = some x

/-- The walk around the rim, in the form that the inflation gives. -/
structure RimWalk (a : WheelFrame Da Wa) (b : WheelFrame Db Wb) (Out : Shat → Shat → Prop) (Sym : ℕ
  → ℕ → Prop) : Prop where
  out_fun : ∀ {y x x'}, Out y x → Out y x' → x = x'
  base : Out (b.R.vert 0) (a.R.vert 0)
  last : Out (b.R.vert (b.R.k - 1)) (a.R.vert (a.R.k - 1))
  step : ∀ q p, q + 1 < b.R.k → p < a.R.k → Out (b.R.vert q) (a.R.vert p) →
    (Out (b.R.vert (q + 1)) (a.R.vert p) ∧ b.Reg q) ∨ (p + 1 < a.R.k ∧ Out (b.R.vert (q + 1))
      (a.R.vert (p + 1)) ∧ Sym q p)
  last_sym : Sym (b.R.k - 1) (a.R.k - 1)
  sym_code : ∀ q p, Sym q p → b.code q = a.code p
  hub_len : b.hubList.length = a.hubList.length

theorem RimWalk.exists_stair {a : WheelFrame Da Wa} {b : WheelFrame Db Wb} {Out : Shat → Shat
  → Prop} {Sym : ℕ → ℕ → Prop} (h : RimWalk a b Out Sym) :
    ∃ θ, Stair a b θ (rtOf a b) ∧ (∀ q < b.R.k, Out (b.R.vert q) (a.R.vert (θ q))) ∧
      (∀ q, q + 1 < b.R.k → θ (q + 1) = θ q + 1 → Sym q (θ q)) := by
  classical
  have ha2 := a.R.two
  have hb2 := b.R.two
  have hex : ∀ q < b.R.k, ∃ p, p < a.R.k ∧ Out (b.R.vert q) (a.R.vert p) := by
    intro q
    induction q with
    | zero => exact fun _ ↦ ⟨0, by omega, h.base⟩
    | succ q ih =>
      intro hq
      obtain ⟨p, hp, ho⟩ := ih (by omega)
      rcases h.step q p hq hp ho with ⟨h₁, -⟩ | ⟨h₁, h₂, -⟩
      · exact ⟨p, hp, h₁⟩
      · exact ⟨p + 1, h₁, h₂⟩
  choose! θ hθ hO using hex
  have huniq : ∀ q p, q < b.R.k → p < a.R.k → Out (b.R.vert q) (a.R.vert p) → θ q = p
    := fun q p hq hp ho ↦
    a.R.vert_inj (hθ q hq) hp (h.out_fun (hO q hq) ho)
  have hcase : ∀ q, q + 1 < b.R.k → (θ (q + 1) = θ q ∧ b.Reg q) ∨ (θ (q + 1) = θ q + 1 ∧ Sym q
    (θ q)) := by
    intro q hq
    have hq' : q < b.R.k := by omega
    rcases h.step q (θ q) hq (hθ q hq') (hO q hq') with ⟨h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩
    · exact .inl ⟨huniq _ _ hq (hθ q hq') h₁, h₂⟩
    · exact .inr ⟨huniq _ _ hq h₁ h₂, h₃⟩
  have hc := h.sym_code _ _ h.last_sym
  have hk : ∀ {D' : TangleDatum cap χ} {W' : Set Shat} (fr : WheelFrame D' W'), fr.R.vert
    (fr.R.k - 1 + 1) = fr.R.vert 0 := fun fr ↦ by
    have := fr.R.two
    rw [show fr.R.k - 1 + 1 = 0 + fr.R.k by omega]
    exact fr.R.vert_add_k 0
  simp only [WheelFrame.code, Prod.mk.injEq] at hc
  obtain ⟨-, ct, -, ci, cs, -⟩ := hc
  have hsym : ∀ {q p}, Sym q p → (b.top q = a.top p ∧ b.top (q + 1) = a.top (p + 1)) ∧ (b.hIdx q
    = a.hIdx p ∧ b.hIdx (q + 1) = a.hIdx (p + 1)) ∧ b.same q = a.same p := fun hs ↦ by
    have := h.sym_code _ _ hs
    simp only [WheelFrame.code, Prod.mk.injEq] at this
    exact ⟨⟨this.1, this.2.1⟩, ⟨this.2.2.1, this.2.2.2.1⟩, this.2.2.2.2.1⟩
  have h0 : θ 0 = 0 := huniq 0 0 (by omega) (by omega) h.base
  have hl : θ (b.R.k - 1) = a.R.k - 1 := huniq _ _ (by omega) (by omega) h.last
  have htop : ∀ q < b.R.k, b.top q = a.top (θ q) ∧ b.hIdx q = a.hIdx (θ q) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [h0, ← b.top_congr (hk b), ← a.top_congr (hk a), ← b.hIdx_congr (hk b),
        ← a.hIdx_congr (hk a)]
      exact ⟨ct, ci⟩
    | succ q ih =>
      intro hq
      obtain ⟨i₁, i₂⟩ := ih (by omega)
      rcases hcase q hq with ⟨e, hr⟩ | ⟨e, hs⟩
      · rw [e, ← i₁, ← i₂]
        exact ⟨(b.top_eq_of_inner hr).symm, (b.hIdx_of_reg hr).symm⟩
      · rw [e]
        exact ⟨(hsym hs).1.2, (hsym hs).2.1.2⟩
  have hsame : ∀ {D' : TangleDatum cap χ} {W' : Set Shat} (fr : WheelFrame D' W') (i t : ℕ), t
    ≤ fr.top i → (t ∈ fr.same i ↔ fr.levV i t = fr.levV (i + 1) t) := fun fr i t ht ↦ by
    simp only [WheelFrame.same, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨by omega, h'⟩⟩
  have hget : ∀ {D' : TangleDatum cap χ} {W' : Set Shat} (fr : WheelFrame D' W') {j : ℕ} {x :
    Shat}, fr.hubList[j]? = some x → x ∈ fr.hubList ∧ fr.hubList.idxOf x = j := fun fr j x hj ↦ by
    obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.mp hj
    have hm : x ∈ fr.hubList := e ▸ List.getElem_mem hlt
    refine ⟨hm, ?_⟩
    rw [← e]
    exact fr.hubList_nodup.idxOf_getElem _ hlt
  refine ⟨θ, ⟨h0, hl, fun q hq ↦ ?_, fun q hq ↦ (htop q hq).1, fun q hq hs ↦ ?_,
    fun q hq hm t ht ↦ ?_, fun t ht ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hO, fun q hq hm ↦ ?_⟩
  · rcases hcase q hq with ⟨e, -⟩ | ⟨e, -⟩
    · exact .inl e
    · exact .inr e
  · rcases hcase q hq with ⟨e, hr⟩ | ⟨e, -⟩
    · exact hr
    · omega
  · rcases hcase q hq with ⟨e, -⟩ | ⟨-, hs⟩
    · omega
    · rw [← hsame b q t ht, (hsym hs).2.2,
        hsame a (θ q) t (by rw [← (htop q (by omega)).1]; exact ht)]
  · have ht' : t ≤ a.top (a.R.k - 1) := by rw [← hl, ← (htop _ (by omega)).1]; exact ht
    rw [← b.levV_congr (hk b), ← a.levV_congr (hk a), ← hsame b _ t ht, cs, hsame a _ t ht']
  · rintro y x x' ⟨j, h₁, h₂⟩ ⟨j', h₃, h₄⟩
    have e : j = j' := ((hget b h₁).2).symm.trans (hget b h₃).2
    subst e
    exact Option.some.inj (h₂.symm.trans h₄)
  · rintro y y' x ⟨j, h₁, h₂⟩ ⟨j', h₃, h₄⟩
    have e : j = j' := ((hget a h₂).2).symm.trans (hget a h₄).2
    subst e
    exact Option.some.inj (h₁.symm.trans h₃)
  · rintro y x ⟨j, h₁, h₂⟩
    have := b.mem_hubList.mp (hget b h₁).1
    have := a.mem_hubList.mp (hget a h₂).1
    tauto
  · intro y hy hV
    have hm := b.mem_hubList.mpr ⟨hy, hV⟩
    have hlt := List.idxOf_lt_length_iff.mpr hm
    refine ⟨a.hubList[b.hubList.idxOf y]'(h.hub_len ▸ hlt), _, ?_, List.getElem?_eq_getElem _⟩
    rw [List.getElem?_eq_getElem hlt]
    simp
  · intro x hx hV
    have hm := a.mem_hubList.mpr ⟨hx, hV⟩
    have hlt := List.idxOf_lt_length_iff.mpr hm
    refine ⟨b.hubList[a.hubList.idxOf x]'(h.hub_len ▸ hlt), _, List.getElem?_eq_getElem _, ?_⟩
    rw [List.getElem?_eq_getElem hlt]
    simp
  · rintro y x ⟨j, h₁, h₂⟩ q hq t ht
    obtain ⟨hmb, eb⟩ := hget b h₁
    obtain ⟨hma, ea⟩ := hget a h₂
    obtain ⟨e₁, e₂⟩ := htop q hq
    rw [a.hub_lev hma (i := θ q) (by rw [← e₁]; exact ht), b.hub_lev hmb ht, ea, eb, e₁, e₂]
  · rcases hcase q hq with ⟨e, -⟩ | ⟨-, hs⟩
    · omega
    · exact hs

end GraphMinor.GM19
