/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section14aa

/-!
# Graph Minors XIX, Section 14: two wheels covers and an inflation

Take two members of the sequence in `Σ'`, with the same frame `Φ'`, and a linear inflation of `Γ'`
of the first in `Γ'` of the second. We walk around each rim of the second painting and
read off the staircase that the paper describes. The vertices of the frame stay where they are, and
at a regular place the walk either stays or moves on with a border edge.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 TangleDatum

universe w

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space S] [T2Space Shat] {α
  : Type w}
  {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace Slice

variable {T : Set S} {Da Db : TangleDatum cap χ}

/-- The wheel of the second cover on the cuff of a wheel of the first. -/
noncomputable def wmap (sa : Slice T Da) (sb : Slice T Db) (W : ↥sa.𝒲) : ↥sb.𝒲 :=
  (sb.exists_wheel ⟨sa.cf W, sa.cf_mem W.2⟩).choose

theorem cf_wmap (sa : Slice T Da) (sb : Slice T Db) (W : ↥sa.𝒲) : sa.cf W = sb.cf (sa.wmap sb W) :=
  (sb.exists_wheel ⟨sa.cf W, sa.cf_mem W.2⟩).choose_spec

theorem cf_nonempty (s : Slice T Da) (W : ↥s.𝒲) : (s.cf W).Nonempty := ⟨_, s.vx_cf W 0⟩

theorem wmap_bij (sa : Slice T Da) (sb : Slice T Db) : Function.Bijective (sa.wmap sb) := by
  constructor
  · intro W₁ W₂ h
    obtain ⟨x, hx⟩ := sa.cf_nonempty W₁
    have h₂ : x ∈ sa.cf W₂ := by
      rw [sa.cf_wmap sb, ← h, ← sa.cf_wmap sb]
      exact hx
    exact sa.wheel_eq hx h₂
  · intro W'
    obtain ⟨W, hW⟩ := sa.exists_wheel ⟨sb.cf W', sb.cf_mem W'.2⟩
    refine ⟨W, ?_⟩
    obtain ⟨x, hx⟩ := sb.cf_nonempty W'
    have h₁ : x ∈ sa.cf W := hW ▸ hx
    rw [sa.cf_wmap sb] at h₁
    exact sb.wheel_eq h₁ hx

/-- The relation that holds the inflation outside the wheels. -/
def Out (sa : Slice T Da) (sb : Slice T Db) (σv : ↥Tᶜ → Set ↥Tᶜ) (y x : Shat) : Prop :=
  ∃ x' y', x = sa.e x' ∧ y = sb.e y' ∧ x' ∈ sa.N ∧ y' ∈ σv x'

end Slice

/-- Two members of the sequence, and a linear inflation. -/
structure CutPair {T : Set S} {Da Db : TangleDatum cap χ} [Nonempty ↥Tᶜ] (sa : Slice T Da)
  (sb : Slice T Db) (ε : Set ↥Tᶜ → Bool) (Φ' : Frame ↥Tᶜ) (Z : Set ↥Tᶜ)
    (σv : ↥Tᶜ → Set ↥Tᶜ) (σe : Set ↥Tᶜ → Set ↥Tᶜ) {β : Type*} (Ω : QuasiOrder β) (ξa : Arm Da.P.Γ
      → β) (ξb : Arm Db.P.Γ → β) (cola : ↥sa.𝒲 → ℕ → α) (colb : ↥sb.𝒲 → ℕ → α) (a₀ : α)
        (Ωc : QuasiOrder α) : Prop where
  hFa : sa.IsCutFrame Φ' Z ε
  hFb : sb.IsCutFrame Φ' Z ε
  dira : ∀ W i, arcMarch sa.isSurface (flipOf ε (sa.arc W i)) (sa.arc W i) = [sa.vx W i, sa.vx W
    (i + 1)]
  dirb : ∀ W i, arcMarch sb.isSurface (flipOf ε (sb.arc W i)) (sb.arc W i) = [sb.vx W i, sb.vx W
    (i + 1)]
  infl : IsLinearInflation (sa.paint ε) (sb.paint ε) σv σe
  resp : RespectsFrame Φ' (sa.paint ε) σe
  le_int : ∀ e ∈ (sa.paint ε).E, Painting.IsInternal e → χ.unionLE (sa.cutφ cola a₀ Z e)
    (sb.cutφ colb a₀ Z (σe e))
  le_long : ∀ e ∈ (sa.paint ε).E, Painting.IsBorder e → ∀ c ∈ Φ'.sides, Φ'.isLong c → e ⊆ c → Ωc.le
    (sa.cutφ cola a₀ Z e) (sb.cutφ colb a₀ Z (σe e))
  col_le : ∀ W p W' q, Ωc.le (cola W p) (colb W' q) → (sb.fr W').code q = (sa.fr W).code p ∧ Ω.le
    (ξa ((sa.fr W).secArm p)) (ξb ((sb.fr W').secArm q))
  tag : ∀ W p, p ∈ sa.sing W → ∀ W' q, q ∈ sb.sing W' → sa.zx W p = sb.zx W' q →
    (p + 1 = (sa.fr W).R.k ↔ q + 1 = (sb.fr W').R.k) ∧ (sb.fr W').code q = (sa.fr W).code p ∧ Ω.le
      (ξa ((sa.fr W).secArm p)) (ξb ((sb.fr W').secArm q)) ∧
      (sb.fr W').hubList.length = (sa.fr W).hubList.length ∧ ∀ hc : (sa.fr W).H.V.ncard ≠ 1, ∃ hc'
        : (sb.fr W').H.V.ncard ≠ 1, Ω.le (ξa ((sa.fr W).hubArm hc)) (ξb ((sb.fr W').hubArm hc'))

namespace CutPair

variable {T : Set S} {Da Db : TangleDatum cap χ} [Nonempty ↥Tᶜ] {sa : Slice T Da} {sb : Slice T Db}
  {ε : Set ↥Tᶜ → Bool} {Φ' : Frame ↥Tᶜ} {Z : Set ↥Tᶜ}
  {σv : ↥Tᶜ → Set ↥Tᶜ} {σe : Set ↥Tᶜ → Set ↥Tᶜ} {β : Type*} {Ω : QuasiOrder β} {ξa : Arm Da.P.Γ
    → β} {ξb : Arm Db.P.Γ → β} {cola : ↥sa.𝒲 → ℕ → α} {colb : ↥sb.𝒲 → ℕ
      → α} {a₀ : α} {Ωc : QuasiOrder α}
  (h : CutPair sa sb ε Φ' Z σv σe Ω ξa ξb cola colb a₀ Ωc)
include h

theorem markN_eq : sa.markN = sb.markN := h.hFa.V_eq.symm.trans h.hFb.V_eq

theorem markZ_eq : sa.markZ = sb.markZ := h.hFa.Z_eq.symm.trans h.hFb.Z_eq

theorem mem_self {v : ↥Tᶜ} (hv : v ∈ sa.markN) : v ∈ σv v :=
  mem_σv_of_frame sa.isSurface (sa.paint_fits h.hFa) (sb.paint_fits h.hFb) h.infl.toIsInflation
    h.resp (h.hFa.V_eq ▸ hv)

theorem out_uniq {x₁ x₂ y : ↥Tᶜ} (h₁ : x₁ ∈ sa.N) (h₂ : x₂ ∈ sa.N) (hy₁ : y ∈ σv x₁)
  (hy₂ : y ∈ σv x₂) : x₁ = x₂ := by
  by_contra hne
  rw [← sa.paint_V ε] at h₁ h₂
  exact disjoint_left.mp (h.infl.vertex_disjoint _ h₁ _ h₂ hne) hy₁ hy₂

theorem exists_match (W : ↥sa.𝒲) {p : ℕ} (hp : p ∈ sa.sing W) : ∃ q ∈ sb.sing
  (sa.wmap sb W), sa.zx W p = sb.zx (sa.wmap sb W) q ∧ sa.arc W p = sb.arc (sa.wmap sb W) q
    ∧ sa.vx W p = sb.vx (sa.wmap sb W) q ∧ sa.vx W (p + 1) = sb.vx (sa.wmap sb W) (q + 1) := by
  have hz : sa.zx W p ∈ sa.markZ := mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hp, rfl⟩⟩
  rw [h.markZ_eq] at hz
  obtain ⟨W', hz⟩ := mem_iUnion.mp hz
  obtain ⟨q, hq, hz⟩ := mem_iUnion₂.mp hz
  have hz' : sa.zx W p = sb.zx W' q := hz
  have hc : sa.zx W p ∈ sa.cf W := sa.arc_cf W p (sa.zx_arc W p)
  rw [sa.cf_wmap sb] at hc
  obtain rfl : sa.wmap sb W = W' := sb.wheel_eq hc (hz' ▸ sb.arc_cf W' q (sb.zx_arc W' q))
  have harc : sa.arc W p = sb.arc (sa.wmap sb W) q := by
    have h₁ := sa.arc_side hp
    rw [h.markN_eq] at h₁
    exact arcComp_eq_of_mem h₁ (sb.arc_side hq) (sa.zx_arc W p) (hz' ▸ sb.zx_arc _ q)
  have hl : [sa.vx W p, sa.vx W (p + 1)] = [sb.vx (sa.wmap sb W) q, sb.vx (sa.wmap sb W) (q + 1)]
    := by
    rw [← h.dira W p, ← h.dirb _ q, ← harc]
  simp only [List.cons.injEq, and_true] at hl
  exact ⟨q, hq, hz', harc, hl.1, hl.2⟩

theorem exists_match' (W : ↥sa.𝒲) {q : ℕ} (hq : q ∈ sb.sing (sa.wmap sb W)) : ∃ p ∈ sa.sing W,
  sa.zx W p = sb.zx (sa.wmap sb W) q := by
  have hz : sb.zx (sa.wmap sb W) q ∈ sb.markZ := mem_iUnion.mpr ⟨_, mem_iUnion₂.mpr ⟨_, hq, rfl⟩⟩
  rw [← h.markZ_eq] at hz
  obtain ⟨W', hz⟩ := mem_iUnion.mp hz
  obtain ⟨p, hp, hz⟩ := mem_iUnion₂.mp hz
  have hz' : sb.zx (sa.wmap sb W) q = sa.zx W' p := hz
  have hc : sb.zx (sa.wmap sb W) q ∈ sa.cf W := by
    rw [sa.cf_wmap sb]
    exact sb.arc_cf _ q (sb.zx_arc _ q)
  obtain rfl : W' = W := sa.wheel_eq (hz' ▸ sa.arc_cf W' p (sa.zx_arc W' p)) hc
  exact ⟨p, hp, hz'.symm⟩

omit [Nonempty ↑Tᶜ] h in
/-- At a place of `Σ'` where the two rims agree, the relation `Out` is the inflation. -/
theorem out_vx {W : ↥sa.𝒲} {W' : ↥sb.𝒲} {p q : ℕ} : Slice.Out sa sb σv ((sb.fr W').R.vert q)
  ((sa.fr W).R.vert p) ↔ sb.vx W' q ∈ σv (sa.vx W p) := by
  constructor
  · rintro ⟨x', y', e₁, e₂, -, hy⟩
    rw [← sa.e_vx] at e₁
    rw [← sb.e_vx] at e₂
    rw [sa.isEmbedding.injective e₁, sb.isEmbedding.injective e₂]
    exact hy
  · intro hy
    exact ⟨_, _, (sa.e_vx W p).symm, (sb.e_vx W' q).symm, (sa.vx_N W p).1, hy⟩

theorem out_frame {W : ↥sa.𝒲} {W' : ↥sb.𝒲} {p q : ℕ} (e : sa.vx W p = sb.vx W' q)
  (hm : sa.vx W p ∈ sa.markN) : Slice.Out sa sb σv ((sb.fr W').R.vert q) ((sa.fr W).R.vert p) :=
  (out_vx (sa := sa) (sb := sb) (σv := σv)).mpr (e ▸ h.mem_self hm)

theorem last_match (W : ↥sa.𝒲) : sa.vx W ((sa.fr W).R.k - 1) = sb.vx (sa.wmap sb W) ((sb.fr
  (sa.wmap sb W)).R.k - 1) ∧ sa.vx W 0 = sb.vx (sa.wmap sb W) 0 ∧
    (sb.fr (sa.wmap sb W)).code ((sb.fr (sa.wmap sb W)).R.k - 1) = (sa.fr W).code
      ((sa.fr W).R.k - 1) ∧
    Ω.le (ξa ((sa.fr W).secArm ((sa.fr W).R.k - 1))) (ξb ((sb.fr (sa.wmap sb W)).secArm ((sb.fr
      (sa.wmap sb W)).R.k - 1))) ∧
    (sb.fr (sa.wmap sb W)).hubList.length = (sa.fr W).hubList.length ∧ ∀ hc :
      (sa.fr W).H.V.ncard ≠ 1, ∃ hc' : (sb.fr (sa.wmap sb W)).H.V.ncard ≠ 1, Ω.le (ξa
        ((sa.fr W).hubArm hc)) (ξb ((sb.fr (sa.wmap sb W)).hubArm hc')) := by
  have h2 := (sa.fr W).R.two
  have hl := sa.last_sing W
  obtain ⟨q, hq, hz, -, e₁, e₂⟩ := h.exists_match W hl
  obtain ⟨hk, hc, hle, hlen, hhub⟩ := h.tag W _ hl _ q hq hz
  have hq' : q = (sb.fr (sa.wmap sb W)).R.k - 1 := by
    have := hk.mp (by omega)
    omega
  subst hq'
  refine ⟨e₁, ?_, hc, hle, hlen, hhub⟩
  rw [← sa.vx_succ_last W, ← sb.vx_succ_last, e₂]

omit [Nonempty ↑Tᶜ] h in
theorem vx_mem_sing {W : ↥sa.𝒲} {p : ℕ} (hp : p ∈ sa.sing W) : sa.vx W p ∈ sa.markN ∧ sa.vx W
  (p + 1) ∈ sa.markN :=
  ⟨mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_, hp, .inl rfl⟩⟩, mem_iUnion.mpr ⟨W, mem_iUnion₂.mpr ⟨_,
    hp, .inr rfl⟩⟩⟩

/-- The symmetry of two sectors. -/
def _root_.GraphMinor.GM19.CutPair.Sym (_ : CutPair sa sb ε Φ' Z σv σe Ω ξa ξb cola colb a₀ Ωc)
  (W : ↥sa.𝒲) (q p : ℕ) : Prop :=
  (sb.fr (sa.wmap sb W)).code q = (sa.fr W).code p ∧ Ω.le (ξa ((sa.fr W).secArm p)) (ξb ((sb.fr
    (sa.wmap sb W)).secArm q))

theorem step_sing (W : ↥sa.𝒲) {q p : ℕ} (hq₁ : q + 1 < (sb.fr (sa.wmap sb W)).R.k) (hp : p <
  (sa.fr W).R.k) (ho : Slice.Out sa sb σv ((sb.fr (sa.wmap sb W)).R.vert q) ((sa.fr W).R.vert p))
    (hs : q ∈ sb.sing (sa.wmap sb W)) : p + 1 < (sa.fr W).R.k ∧ Slice.Out sa sb σv ((sb.fr
      (sa.wmap sb W)).R.vert (q + 1)) ((sa.fr W).R.vert (p + 1)) ∧ h.Sym W q p := by
  obtain ⟨p', hp', hz⟩ := h.exists_match' W hs
  obtain ⟨q', hq', hz', -, e₁, e₂⟩ := h.exists_match W hp'
  obtain rfl : q' = q := by
    have h₁ : sb.arc (sa.wmap sb W) q' = sb.arc (sa.wmap sb W) q := by
      have e' : sb.zx (sa.wmap sb W) q' = sb.zx (sa.wmap sb W) q := hz'.symm.trans hz
      exact arcComp_eq_of_mem (sb.arc_mem _ q') (sb.arc_mem _ q) (sb.zx_arc _ q')
        (e' ▸ sb.zx_arc _ q)
    exact sb.arc_pos _ hq'.1 hs.1 h₁
  obtain ⟨hk, hc, hle, -, -⟩ := h.tag W _ hp' _ _ hs hz
  have hm := vx_mem_sing (sa := sa) hp'
  have hop := h.out_frame (W := W) (W' := sa.wmap sb W) (p := p') (q := q') e₁ hm.1
  have e : p = p' := sa.vx_inj W hp hp'.1 (h.out_uniq (sa.vx_N W p).1 (sa.vx_N W p').1 ((out_vx (sa
    := sa) (sb := sb) (σv := σv)).mp ho) ((out_vx (sa := sa) (sb := sb) (σv := σv)).mp hop))
  subst e
  refine ⟨?_, h.out_frame e₂ hm.2, hc, hle⟩
  by_contra hn
  have : p + 1 = (sa.fr W).R.k := by omega
  have := hk.mp this
  omega

omit h in
theorem arc_E_a (W : ↥sa.𝒲) (i : ℕ) : sa.arc W i ∈ (sa.paint ε).E := sa.arc_E ε (sa.arc_mem W i)

omit h in
theorem arc_E_b (W : ↥sb.𝒲) (i : ℕ) : sb.arc W i ∈ (sb.paint ε).E := sb.arc_E ε (sb.arc_mem W i)

omit h in
omit [Nonempty ↑Tᶜ] in
theorem arc_border (s : Slice T Da) (W : ↥s.𝒲) (i : ℕ) : Painting.IsBorder (s.arc W i) := by
  obtain ⟨x, hx, -⟩ := s.arc_reg W i
  exact ⟨x, hx, ((s.arc_mem W i).2.1 hx).1⟩

theorem γ_a (W : ↥sa.𝒲) (i : ℕ) : (sa.paint ε).γ (sa.arc W i) = [sa.vx W i, sa.vx W (i + 1)] := by
  rw [sa.γ_arc ε (sa.arc_mem W i), h.dira]

theorem γ_b (W : ↥sb.𝒲) (i : ℕ) : (sb.paint ε).γ (sb.arc W i) = [sb.vx W i, sb.vx W (i + 1)] := by
  rw [sb.γ_arc ε (sb.arc_mem W i), h.dirb]

/-- The edge of the first painting whose image is an arc of the second rim is an arc of the first
rim with the same ends. -/
theorem exists_pre (W : ↥sa.𝒲) {q : ℕ} {e₀ : Set ↥Tᶜ} (he₀ : e₀ ∈ (sa.paint ε).E) (he : σe e₀
  = sb.arc (sa.wmap sb W) q) :
    ∃ p₀, p₀ < (sa.fr W).R.k ∧ e₀ = sa.arc W p₀ ∧ sb.vx (sa.wmap sb W) q ∈ σv (sa.vx W p₀) ∧ sb.vx
      (sa.wmap sb W) (q + 1) ∈ σv (sa.vx W (p₀ + 1)) := by
  obtain ⟨z, hz, -⟩ := sb.arc_reg (sa.wmap sb W) q
  have hzc : z ∈ sb.cf (sa.wmap sb W) := sb.arc_cf _ q hz
  have hmem : sa.cf W ∈ cuffs ↥Tᶜ := sa.cf_mem W.2
  have hne : (σe e₀ ∩ sa.cf W).Nonempty := ⟨z, he ▸ hz, by rw [sa.cf_wmap sb]; exact hzc⟩
  obtain ⟨y, hy, hyc⟩ := (h.infl.borders_iff e₀ he₀ _ hmem).mpr hne
  have hb : Painting.IsBorder e₀ := ⟨y, hy, sa.cf_sub_bd W.2 hyc⟩
  obtain ⟨p₀, hp₀, rfl⟩ := sa.arc_cover W (sa.border_arc ε he₀ hb) hy hyc
  have hγ : ∀ (i : ℕ) (hi : i < ((sa.paint ε).γ (sa.arc W p₀)).length) (hi' : i < ((sb.paint ε).γ
    (σe (sa.arc W p₀))).length), ((sb.paint ε).γ (σe (sa.arc W p₀)))[i] ∈ σv ((sa.paint ε).γ
      (sa.arc W p₀))[i] :=
    h.infl.ends _ he₀
  have key : ∀ (l : List ↥Tᶜ) (_ : l = (sb.paint ε).γ (σe (sa.arc W p₀))) (l' : List ↥Tᶜ) (_ : l' =
    (sa.paint ε).γ (sa.arc W p₀)), l = [sb.vx (sa.wmap sb W) q, sb.vx (sa.wmap sb W) (q + 1)] → l'
      = [sa.vx W p₀, sa.vx W (p₀ + 1)] → sb.vx (sa.wmap sb W) q ∈ σv (sa.vx W p₀) ∧ sb.vx
        (sa.wmap sb W) (q + 1) ∈ σv (sa.vx W (p₀ + 1)) := by
    rintro _ rfl _ rfl e₁ e₂
    have h₀ := hγ 0 (by simp [e₂]) (by simp [e₁])
    have h₁ := hγ 1 (by simp [e₂]) (by simp [e₁])
    simp only [e₁, e₂] at h₀ h₁
    exact ⟨h₀, h₁⟩
  obtain ⟨h₀, h₁⟩ := key _ rfl _ rfl (by rw [he, h.γ_b]) (h.γ_a W p₀)
  exact ⟨p₀, hp₀, rfl, h₀, h₁⟩

/-- A regular arc of the first rim is an edge of a long side. -/
theorem exists_long_side (W : ↥sa.𝒲) {p : ℕ} (hp : p < (sa.fr W).R.k)
  (hns : p ∉ sa.sing W) : ∃ c ∈ Φ'.sides, Φ'.isLong c ∧ sa.arc W p ⊆ c := by
  have hsub : sa.arc W p ⊆ bd ↥Tᶜ \ Φ'.V := by
    rw [h.hFa.V_eq]
    exact fun x hx ↦ ⟨((sa.arc_mem W p).2.1 hx).1, fun hm ↦ ((sa.arc_mem W p).2.1 hx).2
      (sa.markN_sub hm)⟩
  obtain ⟨c, hc, hsubc⟩ := exists_arcComp_superset (sa.arc_mem W p).2.2.1 hsub
  refine ⟨c, hc, (h.hFa.long_iff c).mpr ?_, hsubc⟩
  rw [h.hFa.Z_eq]
  refine disjoint_left.mpr fun z hzc hz ↦ ?_
  obtain ⟨W', hz⟩ := mem_iUnion.mp hz
  obtain ⟨i, hi, rfl⟩ := mem_iUnion₂.mp hz
  have hc' : c ∈ arcComponentsIn (bd ↥Tᶜ \ sa.markN) := h.hFa.V_eq ▸ hc
  obtain rfl : c = sa.arc W' i := arcComp_eq_of_mem hc' (sa.arc_side hi) hzc (sa.zx_arc W' i)
  obtain ⟨x, hx, -⟩ := sa.arc_reg W p
  have e := arcComp_eq_of_mem (sa.arc_mem W p) (sa.arc_mem W' i) hx (hsubc hx)
  obtain rfl := sa.arc_wheel e
  exact hns (sa.arc_pos W hp hi.1 e ▸ hi)

/-- If `e₀` is a singular arc then so is its image. -/
theorem sing_of_sing (W : ↥sa.𝒲) {p q : ℕ} (hp : p ∈ sa.sing W) (hq : q < (sb.fr
  (sa.wmap sb W)).R.k) (he : σe (sa.arc W p) = sb.arc (sa.wmap sb W) q) : q ∈ sb.sing
    (sa.wmap sb W) := by
  obtain ⟨q', hq', -, harc, -, -⟩ := h.exists_match W hp
  have hc : sa.arc W p ∈ Φ'.sides := by
    have := sa.arc_side hp
    rwa [← h.hFa.V_eq] at this
  have hsub : σe (sa.arc W p) ⊆ sa.arc W p := ((h.resp _ (arc_E_a (sa := sa) (ε := ε) W p)
    (arc_border sa W p)).2 _ hc).mp subset_rfl
  rw [he, harc] at hsub
  obtain ⟨x, hx, -⟩ := sb.arc_reg (sa.wmap sb W) q
  have e := arcComp_eq_of_mem (sb.arc_mem _ q) (sb.arc_mem _ q') hx (hsub hx)
  exact sb.arc_pos _ hq hq'.1 e ▸ hq'

theorem step_reg (W : ↥sa.𝒲) {q p : ℕ} (hq₁ : q + 1 < (sb.fr (sa.wmap sb W)).R.k) (hp : p <
  (sa.fr W).R.k) (ho : Slice.Out sa sb σv ((sb.fr (sa.wmap sb W)).R.vert q) ((sa.fr W).R.vert p))
    (hs : q ∉ sb.sing (sa.wmap sb W)) :
    (Slice.Out sa sb σv ((sb.fr (sa.wmap sb W)).R.vert (q + 1)) ((sa.fr W).R.vert p) ∧ (sb.fr
      (sa.wmap sb W)).Reg q) ∨
      (p + 1 < (sa.fr W).R.k ∧ Slice.Out sa sb σv ((sb.fr (sa.wmap sb W)).R.vert (q + 1))
        ((sa.fr W).R.vert (p + 1)) ∧ h.Sym W q p) := by
  classical
  have hy := (out_vx (sa := sa) (sb := sb) (σv := σv)).mp ho
  have hreg : (sb.fr (sa.wmap sb W)).Reg q := by
    by_contra hn
    exact hs ⟨by omega, .inr hn⟩
  by_cases hc : sb.arc (sa.wmap sb W) q ∈ σe '' (sa.paint ε).E
  · obtain ⟨e₀, he₀, he⟩ := hc
    obtain ⟨p₀, hp₀, rfl, h₀, h₁⟩ := h.exists_pre W he₀ he
    obtain rfl : p₀ = p := sa.vx_inj W hp₀ hp (h.out_uniq (sa.vx_N W p₀).1 (sa.vx_N W p).1 h₀ hy)
    have hns : p₀ ∉ sa.sing W := fun hsing ↦ hs (h.sing_of_sing W hsing (by omega) he)
    have hp₁ : p₀ + 1 < (sa.fr W).R.k := by
      by_contra hn
      exact hns ⟨hp, .inl (by omega)⟩
    refine .inr ⟨hp₁, (out_vx (sa := sa) (sb := sb) (σv := σv)).mpr h₁, ?_⟩
    obtain ⟨c, hc, hl, hsub⟩ := h.exists_long_side W hp hns
    have hle := h.le_long _ he₀ (arc_border sa W p₀) c hc hl hsub
    have hdisZ : Disjoint c Z := (h.hFa.long_iff c).mp hl
    have hni : ∀ {s₀ : Slice T Da} {W₀ : ↥s₀.𝒲} {i : ℕ}, ¬ Painting.IsInternal (s₀.arc W₀ i)
      := fun {s₀ W₀ i} hi ↦ isInternal_iff_not_border.mp hi (arc_border s₀ W₀ i)
    have hsub' : sb.arc (sa.wmap sb W) q ⊆ c := by
      rw [← he]
      exact ((h.resp _ (arc_E_a (sa := sa) (ε := ε) W p₀) (arc_border sa W p₀)).2 _ hc).mp hsub
    have hni' : ¬ Painting.IsInternal (sb.arc (sa.wmap sb W) q) := fun hi ↦
      isInternal_iff_not_border.mp hi (arc_border sb _ q)
    rw [he, Slice.cutφ, Slice.cutφ, ite_eq_right hni, ite_eq_right hni', ite_eq_left
      (hdisZ.mono_left hsub), ite_eq_left (hdisZ.mono_left hsub'), sa.borderCol_arc _ _ hp,
        sb.borderCol_arc _ _ (by omega)] at hle
    exact h.col_le _ _ _ _ hle
  · obtain ⟨v, hv, hsub⟩ := h.infl.border_edge _ (arc_E_b (sb := sb) (ε := ε) _ q)
      (arc_border sb _ q) hc
    rw [sb.tilde_arc] at hsub
    have h₁ : sb.vx (sa.wmap sb W) q ∈ σv v := hsub (.inl rfl)
    have h₂ : sb.vx (sa.wmap sb W) (q + 1) ∈ σv v := hsub (.inr rfl)
    have hvN : v ∈ sa.N := by rwa [sa.paint_V] at hv
    obtain rfl := h.out_uniq hvN (sa.vx_N W p).1 h₁ hy
    exact .inl ⟨(out_vx (sa := sa) (sb := sb) (σv := σv)).mpr h₂, hreg⟩

/-- **The walk around a rim.** -/
theorem rimWalk (W : ↥sa.𝒲) : RimWalk (sa.fr W) (sb.fr (sa.wmap sb W)) (Slice.Out sa sb σv)
  (h.Sym W) := by
  have hO : ∀ {y x x'}, Slice.Out sa sb σv y x → Slice.Out sa sb σv y x' → x = x' := by
    rintro _ _ _ ⟨x, y, rfl, rfl, hx, hy⟩ ⟨x', y', rfl, e, hx', hy'⟩
    obtain rfl := sb.isEmbedding.injective e
    rw [h.out_uniq hx hx' hy hy']
  obtain ⟨e₁, e₀, hc, hle, hlen, -⟩ := h.last_match W
  have hl := sa.last_sing W
  have hm := vx_mem_sing (sa := sa) hl
  refine ⟨hO, h.out_frame e₀ (sa.vx_succ_last W ▸ hm.2), h.out_frame e₁ hm.1,
    fun q p hq hp ho ↦ ?_, ⟨hc, hle⟩, fun _ _ h' ↦ h'.1, hlen⟩
  by_cases hs : q ∈ sb.sing (sa.wmap sb W)
  · exact .inr (h.step_sing W hq hp ho hs)
  · exact h.step_reg W hq hp ho hs

end CutPair

end GraphMinor.GM19
