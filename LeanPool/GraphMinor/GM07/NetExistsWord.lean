/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section2MinVal
public import LeanPool.GraphMinor.GM07.MinimalNet
public import LeanPool.GraphMinor.Surface.CutNull
public import LeanPool.GraphMinor.Surface.WordSurface
public import LeanPool.GraphMinor.Surface.CellFamily

/-!
# From one word to a net

A word in which each label is on at most two sides, and which presents a surface `S` with at least
two cuffs, is a net
for `S` (`exists_net_of_word`). The closed disc of the net is the unit disc of the plane, the pairs
of the net are the
pairs of sides with one label, and the seam is the image of the unit circle. This is the end of the
sketch on page 216
of Graph Minors VII.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

universe u

local notation "𝕀" => unitInterval

/-- The closed unit disc of the plane, in the universe `u`. -/
abbrev UDisc : Type u := ULift.{u} (closedBall (0 : ℂ) 1)

/-- The point of `UDisc` at `z`, if `z` is in the disc. -/
noncomputable def toU (z : ℂ) : UDisc.{u} :=
  open Classical in if h : z ∈ closedBall (0 : ℂ) 1 then ⟨⟨z, h⟩⟩ else ⟨⟨0, by simp⟩⟩

theorem toU_val {z : ℂ} (h : z ∈ closedBall (0 : ℂ) 1) : (toU.{u} z).down.1 = z := by
  simp [toU, h]

theorem toU_down (x : UDisc.{u}) : toU.{u} x.down.1 = x := by
  have h := x.down.2
  simp only [toU, h, dite_true]

theorem continuousOn_toU : ContinuousOn toU.{u} (closedBall (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (closedBall (0 : ℂ) 1).domRestrict toU.{u} = ULift.up := by
    funext x
    have hx := x.2
    simp only [domRestrict_apply, toU, hx, dite_true]
  rw [h]
  exact continuous_uliftUp

theorem continuous_val : Continuous fun x : UDisc.{u} => x.down.1 :=
  continuous_subtype_val.comp continuous_uliftDown

/-- The homeomorphism from the closed disc of the paper to `UDisc`. -/
noncomputable def discHomeo : ClosedUnitDisc ≃ₜ UDisc.{u} :=
  ((complexPlane.toHomeomorph.symm.subtype (p := fun x => x ∈ ClosedUnitDisc)
    (q := fun z => z ∈ closedBall (0 : ℂ) 1) (fun x => by
      simp [ClosedUnitDisc]))).trans Homeomorph.ulift.symm

/-- The word with `n` different letters. -/
def freeW (n : ℕ) : List Letter := (List.range n).map fun k => (k, true)

theorem freeW_length (n : ℕ) : (freeW n).length = n := by simp [freeW]

theorem stp_empty_of_unique {w : List Letter} (h : ∀ (p q k : ℕ) (e e' : Bool), w[p]? = some (k, e)
  → w[q]? = some (k, e') → p = q)
    (a b : ℕ × ℂ) : ¬ Stp (sW w) a b := by
  rintro ⟨i, j, p, q, k, e, e', t, h1, h2, h3, -⟩
  obtain ⟨rfl, h1'⟩ := sW_get h1
  obtain ⟨rfl, h2'⟩ := sW_get h2
  exact h3 (by rw [h _ _ _ _ _ h1' h2'])

theorem prel_eq_of_no_stp {W : ℕ → List Letter} (h : ∀ a b, ¬ Stp W a b) {a b : ℕ × ℂ}
  (hr : PRel W a b) : a = b := by
  induction hr with
  | rel _ _ hs => exact absurd hs (h _ _)
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ h1 h2 => exact h1.trans h2

theorem mem_dsk_sW {w : List Letter} {a : ℕ × ℂ} (ha : a ∈ Dsk (sW w)) : a.1 = 0 ∧ a.2 ∈ closedBall
  (0 : ℂ) 1 := by
  obtain ⟨h1, h2⟩ := ha
  refine ⟨?_, by simpa using h2⟩
  by_contra h
  exact h1 (by simp [sW, h, nW])

theorem dsk_sW_mk {w : List Letter} (hw : w ≠ []) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
  ((0 : ℕ), z) ∈ Dsk (sW w) :=
  ⟨by simpa [sW_zero] using hw, by simpa using hz⟩

theorem presents_freeW {n : ℕ} (hn : 0 < n) : Presents (sW (freeW n)) (fun a => toU.{u} a.2) := by
  have hne : freeW n ≠ [] := by
    intro h
    have := freeW_length n
    simp [h] at this
    omega
  refine ⟨continuousOn_toU.comp continuous_snd.continuousOn fun a ha => (mem_dsk_sW ha).2, ?_,
    fun a ha b hb => ?_⟩
  · refine eq_univ_of_forall fun x => ⟨(0, x.down.1), dsk_sW_mk hne x.down.2, toU_down x⟩
  · obtain ⟨h1, h2⟩ := mem_dsk_sW ha
    obtain ⟨h3, h4⟩ := mem_dsk_sW hb
    constructor
    · intro he
      have : a.2 = b.2 := by
        have h5 := congrArg (fun x : UDisc.{u} => x.down.1) he
        simpa only [toU_val h2, toU_val h4] using h5
      rw [show a = b from Prod.ext (h1.trans h3.symm) this]
      exact .refl _
    · intro hr
      have huniq : ∀ (p q k : ℕ) (e e' : Bool), (freeW n)[p]? = some (k, e) → (freeW n)[q]? = some
        (k, e') → p = q := by
        intro p q k e e' h5 h6
        simp only [freeW, List.getElem?_map, Option.map_eq_some_iff] at h5 h6
        obtain ⟨x, hx, hx'⟩ := h5
        obtain ⟨y, hy, hy'⟩ := h6
        have hxp := (List.getElem?_eq_some_iff.mp hx).choose_spec
        have hyq := (List.getElem?_eq_some_iff.mp hy).choose_spec
        simp only [List.getElem_range] at hxp hyq
        have e1 : x = k := congrArg Prod.fst hx'
        have e2 : y = k := congrArg Prod.fst hy'
        omega
      rw [prel_eq_of_no_stp (stp_empty_of_unique huniq) hr]

theorem isSurface_uDisc : IsSurface UDisc.{u} :=
  (surface_of_presents (finW_sW _) (isPaired_sW (w := freeW 2) (fun c => by
    have : (freeW 2) = [(0, true), (1, true)] := rfl
    rw [this]
    simp only [cnt, List.countP_cons, List.countP_nil, beq_iff_eq]
    split_ifs <;> omega)) (presents_freeW (by norm_num))).1

theorem good_freeW2 : Good (freeW 2) := fun c => by
  have : (freeW 2) = [(0, true), (1, true)] := rfl
  rw [this]
  simp only [cnt, List.countP_cons, List.countP_nil, beq_iff_eq]
  split_ifs <;> omega

theorem unique_freeW2 (p q k : ℕ) (e e' : Bool) (h5 : (freeW 2)[p]? = some (k, e)) (h6 :
  (freeW 2)[q]? = some (k, e')) :
    p = q := by
  have hp := (List.getElem?_eq_some_iff.mp h5).1
  have hq := (List.getElem?_eq_some_iff.mp h6).1
  rw [freeW_length] at hp hq
  have : (freeW 2) = [(0, true), (1, true)] := rfl
  rw [this] at h5 h6
  interval_cases p <;> interval_cases q
  · rfl
  · simp at h5 h6
    omega
  · simp at h5 h6
    omega
  · rfl

theorem bd_uDisc : bd UDisc.{u} = {x | ‖x.down.1‖ = 1} := by
  have hf := presents_freeW.{u} (n := 2) (by norm_num)
  rw [(surface_of_presents (finW_sW _) (isPaired_sW good_freeW2) hf).2]
  ext x
  constructor
  · rintro ⟨a, ⟨i, p, u, -, -, -, rfl⟩, rfl⟩
    have hz : per (sW (freeW 2) i).length (p + u) ∈ closedBall (0 : ℂ) 1 := by simp [norm_per]
    change ‖(toU.{u} (per (sW (freeW 2) i).length (p + u))).down.1‖ = 1
    rw [toU_val hz, norm_per]
  · intro hx
    have hx' : ‖x.down.1‖ = 1 := hx
    obtain ⟨p, hp, t, ht, he⟩ := exists_side_of_sphere (n := 2) (by norm_num) (fun _ => true) hx'
    refine ⟨spt (sW (freeW 2)) 0 p t, ⟨0, p, t, by simpa [sW_zero, freeW_length] using hp,
      fun j q k e e' h1 h2 => ?_, ht, rfl⟩, ?_⟩
    · obtain ⟨-, h1'⟩ := sW_get h1
      obtain ⟨hj, h2'⟩ := sW_get h2
      rw [unique_freeW2 _ _ _ _ _ h1' h2', hj]
    · have e1 : spt (sW (freeW 2)) 0 p t = (0, x.down.1) := by
        rw [← he]
        simp [spt, sW_zero, freeW_length, sdPt]
      rw [e1]
      exact toU_down x

theorem sdPt_inj {n p : ℕ} (hn : 2 ≤ n) (hp : p < n) (ε : Bool) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
  (ht : t ∈ Icc (0 : ℝ) 1)
    (he : sdPt n p ε s = sdPt n p ε t) : s = t := by
  have hmain : ∀ {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 → per n (p + u) = per n (p + v)
    → u = v := by
    intro u v hu hv huv
    by_cases hu' : u ∈ Ioo (0 : ℝ) 1
    · exact (side_unique hp hp hu' hv huv).2
    by_cases hv' : v ∈ Ioo (0 : ℝ) 1
    · exact (side_unique hp hp hv' hu huv.symm).2.symm
    have hu2 : u = 0 ∨ u = 1 := by
      by_contra hc
      push Not at hc
      exact hu' ⟨lt_of_le_of_ne hu.1 (Ne.symm hc.1), lt_of_le_of_ne hu.2 hc.2⟩
    have hv2 : v = 0 ∨ v = 1 := by
      by_contra hc
      push Not at hc
      exact hv' ⟨lt_of_le_of_ne hv.1 (Ne.symm hc.1), lt_of_le_of_ne hv.2 hc.2⟩
    have hn0 : 0 < n := by omega
    have key : per n (p : ℝ) ≠ per n (p + 1) := by
      intro h
      by_cases hp1 : p + 1 < n
      · have h1 : (p : ℝ) ∈ Ico (0 : ℝ) n := ⟨Nat.cast_nonneg p, by exact_mod_cast hp⟩
        have h2 : (p : ℝ) + 1 ∈ Ico (0 : ℝ) n := ⟨by positivity, by exact_mod_cast hp1⟩
        have := per_injOn hn0 h1 h2 h
        linarith
      · have hp2 : (p : ℝ) + 1 = n := by
          have : p + 1 = n := by omega
          exact_mod_cast this
        have h3 : per n (n : ℝ) = per n 0 := by simpa using per_add_self (m := n) hn0.ne' 0
        rw [hp2, h3] at h
        have h1 : (p : ℝ) ∈ Ico (0 : ℝ) n := ⟨Nat.cast_nonneg p, by exact_mod_cast hp⟩
        have h2 : (0 : ℝ) ∈ Ico (0 : ℝ) n := ⟨le_rfl, by exact_mod_cast hn0⟩
        have := per_injOn hn0 h1 h2 h
        have hp0 : p = 0 := by exact_mod_cast this
        have : n = 1 := by
          have : p + 1 = n := by omega
          omega
        omega
    rcases hu2 with rfl | rfl <;> rcases hv2 with rfl | rfl
    · rfl
    · exact absurd (by simpa using huv) key
    · exact absurd (by simpa using huv.symm) key
    · rfl
  rw [sdPt_eq, sdPt_eq] at he
  have := hmain (ofs_mem hs) (ofs_mem ht) he
  have h2 := congrArg (ofs ε) this
  rwa [ofs_ofs, ofs_ofs] at h2

/-- The side at `p` as a curve in the disc. -/
noncomputable def sideC (n p : ℕ) (ε : Bool) : Curve UDisc.{u} :=
  ⟨fun t => toU.{u} (sdPt n p ε t), by
    refine continuousOn_univ.mp (continuousOn_toU.comp ?_ fun t _ => ?_)
    · refine Continuous.continuousOn ?_
      simp only [sdPt_eq]
      apply (continuous_per n).comp
      cases ε <;> simp only [ofs, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    · simp [sdPt, norm_per]⟩

theorem sideC_val (n p : ℕ) (ε : Bool) (t : 𝕀) : (sideC.{u} n p ε t).down.1 = sdPt n p ε t :=
  toU_val (by simp [sdPt, norm_per])

private theorem side_pairs_generate_surface_identifications
    {w : List Letter}
    (n : ℕ)
    (hsl : (sW w 0).length = n)
    (hP : IsPaired (sW w))
    (Ps : Set ℕ)
    (hPs : Ps = {c | ∃ (p q : ℕ) (ε ε' : Bool),
      p < q ∧ w[p]? = some (c, ε) ∧ w[q]? = some (c, ε')})
    (e : ↑Ps ≃ Fin (Nat.card ↑Ps))
    (x : ↑Ps → ℕ × ℕ × Bool × Bool)
    (hx1 : ∀ (c : ↑Ps), (x c).1 < (x c).2.1)
    (hx2 : ∀ (c : ↑Ps), w[(x c).1]? = some (↑c, (x c).2.2.1))
    (hx3 : ∀ (c : ↑Ps), w[(x c).2.1]? = some (↑c, (x c).2.2.2))
    (f : Fin (Nat.card ↑Ps) → Curve UDisc)
    (h : Fin (Nat.card ↑Ps) → Curve UDisc)
    (hf : ∀ i, f i = sideC n (x (e.symm i)).1 (x (e.symm i)).2.2.1)
    (hh : ∀ i, h i = sideC n (x (e.symm i)).2.1 (x (e.symm i)).2.2.2)
    (hsw : ∀ {p : ℕ} {l : Letter}, w[p]? = some l → (sW w 0)[p]? = some l) :
    ∀ (a b : ℕ × ℂ), PRel (sW w) a b → a ∈ Dsk (sW w) → Relation.EqvGen (fun a b => ∃ i t, a = (f
      i) t ∧ b = (h i) t) (toU a.2) (toU b.2) := by
  intro a b hab
  induction hab with
  | rel a b hs =>
    intro _
    obtain ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩ := hs
    obtain ⟨rfl, h1'⟩ := sW_get h1
    obtain ⟨rfl, h2'⟩ := sW_get h2
    have hpq : p ≠ q := fun he => h3 (by rw [he])
    have hk : k ∈ Ps := by
      rw [hPs]
      rcases lt_or_gt_of_ne hpq with hl | hl
      · exact ⟨p, q, ε, ε', hl, h1', h2'⟩
      · exact ⟨q, p, ε', ε, hl, h2', h1'⟩
    set c : Ps := ⟨k, hk⟩ with hc
    have h4 := hP.third (hsw (hx2 c)) (hsw (hx3 c)) h1 (fun he => (hx1 c).ne
      (congrArg Prod.snd he))
    have h5 := hP.third (hsw (hx2 c)) (hsw (hx3 c)) h2 (fun he => (hx1 c).ne
      (congrArg Prod.snd he))
    have he1 : (x c).1 = p ∨ (x c).2.1 = p := by
      rcases h4 with h4 | h4
      · exact .inl (congrArg Prod.snd h4).symm
      · exact .inr (congrArg Prod.snd h4).symm
    have he2 : (x c).1 = q ∨ (x c).2.1 = q := by
      rcases h5 with h5 | h5
      · exact .inl (congrArg Prod.snd h5).symm
      · exact .inr (congrArg Prod.snd h5).symm
    let i' := e c
    have hi' : e.symm i' = c := e.symm_apply_apply c
    let t' : 𝕀 := ⟨t, ht⟩
    have hfv : f i' t' = toU (sdPt n (x c).1 (x c).2.2.1 t) := by
      simp only [hf, hi']
      rfl
    have hhv : h i' t' = toU (sdPt n (x c).2.1 (x c).2.2.2 t) := by
      simp only [hh, hi']
      rfl
    have hsgn : ∀ {r : ℕ} {s s' : Bool}, w[r]? = some (k, s) → w[r]? = some (k, s') → s = s' := by
      intro r s s' h6 h7
      rw [h6] at h7
      exact congrArg Prod.snd (Option.some.inj h7)
    rw [hsl]
    rcases he1 with rfl | rfl
    · have hq' : (x c).2.1 = q := he2.resolve_left hpq
      subst hq'
      have s1 := hsgn h1' (hx2 c)
      have s2 := hsgn h2' (hx3 c)
      subst s1 s2
      exact .rel _ _ ⟨i', t', hfv.symm, hhv.symm⟩
    · have hq' : (x c).1 = q := he2.resolve_right hpq
      subst hq'
      have s1 := hsgn h1' (hx3 c)
      have s2 := hsgn h2' (hx2 c)
      subst s1 s2
      exact .symm _ _ (.rel _ _ ⟨i', t', hfv.symm, hhv.symm⟩)
  | refl a => exact fun _ => .refl _
  | symm a b hr ih => exact fun ha => .symm _ _ (ih ((prel_mem_iff hr).mpr ha))
  | trans a b c h1 h2 i1 i2 => exact fun ha => .trans _ _ _ (i1 ha) (i2 ((prel_mem_iff h1).mp ha))

private theorem side_path_identifications_have_same_image
    {S : Type u}
    (φ : UDisc → S)
    (Ps : Set ℕ)
    (f : Fin (Nat.card ↑Ps) → Curve UDisc)
    (h : Fin (Nat.card ↑Ps) → Curve UDisc)
    (hpast : ∀ (i : Fin (Nat.card ↑Ps)) (t : 𝕀), φ ((f i) t) = φ ((h i) t)) :
    ∀ (a b : UDisc), Relation.EqvGen (fun a b => ∃ i t, a = (f i) t ∧ b = (h i) t) a b →
      φ a = φ b := by
  intro a b hab
  induction hab with
  | rel a b hs =>
    obtain ⟨i, t, rfl, rfl⟩ := hs
    exact hpast i t
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ i1 i2 => exact i1.trans i2

/-- **From one word to a net.** A word of length at least two with each label on at most two sides,
which presents a
surface with at least two cuffs, is a net for this surface. Its seam is the image of the unit
circle. -/
theorem exists_net_of_word {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (hc : 2 ≤
  (cuffs S).ncard) {w : List Letter}
    (hlen : 2 ≤ w.length) (hG : Good w) {g : ℕ × ℂ → S} (hg : Presents (sW w) g) :
    ∃ N : Net S, 0 < N.r ∧ N.seamU ⊆ (fun z => g (0, z)) '' sphere 0 1 := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hne : w ≠ [] := fun h => by simp [h] at hlen
  set n := w.length with hn
  have hsl : (sW w 0).length = n := by rw [sW_zero]
  have hP := isPaired_sW hG
  have hm : ∀ x : UDisc.{u}, ((0 : ℕ), x.down.1) ∈ Dsk (sW w) := fun x => dsk_sW_mk hne x.down.2
  let φ : UDisc.{u} → S := fun x => g (0, x.down.1)
  have hφc : Continuous φ := by
    refine continuousOn_univ.mp (hg.1.comp (t := Dsk (sW w)) ?_ fun x _ => hm x)
    exact (continuous_const.prodMk continuous_val).continuousOn
  have hφs : Function.Surjective φ := fun y => by
    obtain ⟨a, ha, rfl⟩ : y ∈ g '' Dsk (sW w) := hg.2.1 ▸ mem_univ y
    obtain ⟨h1, h2⟩ := mem_dsk_sW ha
    refine ⟨⟨⟨a.2, h2⟩⟩, ?_⟩
    exact congrArg g (Prod.ext h1.symm rfl)
  let Ps : Set ℕ := {c | ∃ (p q : ℕ) (ε ε' : Bool), p < q ∧ w[p]? = some (c, ε) ∧ w[q]? = some
    (c, ε')}
  have hPf : Ps.Finite := by
    refine (w.map Prod.fst).toFinset.finite_toSet.subset ?_
    rintro c ⟨p, -, ε, -, -, h1, -⟩
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨(c, ε), List.mem_of_getElem? h1, rfl⟩
  have := hPf.to_subtype
  let e := Finite.equivFin Ps
  have hsel : ∀ c : Ps, ∃ x : ℕ × ℕ × Bool × Bool, x.1 < x.2.1 ∧ w[x.1]? = some (c.1, x.2.2.1)
    ∧ w[x.2.1]? = some (c.1, x.2.2.2) := by
    rintro ⟨c, p, q, ε, ε', h1, h2, h3⟩
    exact ⟨(p, q, ε, ε'), h1, h2, h3⟩
  choose x hx1 hx2 hx3 using hsel
  have hlab : ∀ {a : ℕ} {c c' : ℕ} {ε ε' : Bool}, w[a]? = some (c, ε) → w[a]? = some (c', ε') → c
    = c' := by
    intro a c c' ε ε' h1 h2
    rw [h1] at h2
    exact congrArg Prod.fst (Option.some.inj h2)
  have hltp : ∀ c, (x c).1 < n := fun c => lt_length (W := sW w) (i := 0)
    (by simpa [sW_zero] using hx2 c) |> fun h => by simpa [sW_zero] using h
  have hltq : ∀ c, (x c).2.1 < n := fun c => lt_length (W := sW w) (i := 0)
    (by simpa [sW_zero] using hx3 c) |> fun h => by simpa [sW_zero] using h
  let f : Fin (Nat.card Ps) → Curve UDisc.{u} := fun i => sideC n (x (e.symm i)).1 (x
    (e.symm i)).2.2.1
  let h : Fin (Nat.card Ps) → Curve UDisc.{u} := fun i => sideC n (x (e.symm i)).2.1 (x
    (e.symm i)).2.2.2
  have hinj : ∀ {p : ℕ} (ε : Bool), p < n → Function.Injective (sideC.{u} n p ε) := by
    intro p ε hp s t hst
    have h1 : sdPt n p ε s = sdPt n p ε t := by
      rw [← sideC_val.{u}, ← sideC_val.{u}, hst]
    exact Subtype.ext (sdPt_inj hlen hp ε s.2 t.2 h1)
  have hbd : ∀ (p : ℕ) (ε : Bool) (t : 𝕀), sideC.{u} n p ε t ∈ bd UDisc.{u} := by
    intro p ε t
    rw [bd_uDisc]
    change ‖(sideC.{u} n p ε t).down.1‖ = 1
    rw [sideC_val, sdPt_eq, norm_per]
  have hdis : ∀ {p p' : ℕ} (ε ε' : Bool), p < n → p' < n → ∀ t ∈ Ioo (0 : 𝕀) 1, sideC.{u} n p ε t ∈
    range (sideC.{u} n p' ε') → p = p' := by
    rintro p p' ε ε' hp hp' t ⟨h0, h1⟩ ⟨t', ht'⟩
    have h2 : sdPt n p' ε' t' = sdPt n p ε t := by
      rw [← sideC_val.{u}, ← sideC_val.{u}, ht']
    rw [sdPt_eq, sdPt_eq] at h2
    have ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
    exact (side_unique hp hp' (ofs_Ioo ε ht) (ofs_mem t'.2) h2.symm).1
  have hsw : ∀ {p : ℕ} {l : Letter}, w[p]? = some l → (sW w 0)[p]? = some l := fun {p l} hp
    => by rwa [sW_zero]
  have hstep : ∀ (c : Ps) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → Stp (sW w) (0, sdPt n (x c).1 (x c).2.2.1 t)
    (0, sdPt n (x c).2.1 (x c).2.2.2 t) := by
    intro c t ht
    refine ⟨0, 0, _, _, c.1, _, _, t, hsw (hx2 c), hsw (hx3 c), fun he => ?_, ht, by rw [hsl],
      by rw [hsl]⟩
    have := congrArg Prod.snd he
    exact (hx1 c).ne this
  have hpast : ∀ (i : Fin (Nat.card Ps)) (t : 𝕀), φ (f i t) = φ (h i t) := by
    intro i t
    have h1 := (hg.2.2 _ (hm (f i t)) _ (hm (h i t))).mpr (by
      change PRel (sW w) (0, (sideC.{u} n _ _ t).down.1) (0, (sideC.{u} n _ _ t).down.1)
      rw [sideC_val, sideC_val]
      exact .rel _ _ (hstep (e.symm i) t t.2))
    exact h1
  have hforth : ∀ a b, PRel (sW w) a b → a ∈ Dsk (sW w) → Relation.EqvGen (fun a b : UDisc.{u} => ∃
    (i : Fin (Nat.card Ps)) (t : 𝕀), a = f i t ∧ b = h i t) (toU a.2) (toU b.2) := by
    exact side_pairs_generate_surface_identifications (w := w) n hsl hP Ps rfl e x hx1 hx2 hx3 f h
      (fun _ => rfl) (fun _ => rfl) hsw
  have hback : ∀ a b : UDisc.{u}, Relation.EqvGen (fun a b : UDisc.{u} => ∃ (i : Fin (Nat.card Ps))
    (t : 𝕀), a = f i t ∧ b = h i t) a b → φ a = φ b := by
    exact side_path_identifications_have_same_image (S := S) φ Ps f h hpast
  have hunit : ∀ x : UDisc.{u}, x ∉ bd UDisc.{u} → ‖x.down.1‖ < 1 := by
    intro x hx
    rw [bd_uDisc] at hx
    exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp x.down.2) hx
  have hr : 0 < Nat.card Ps := by
    by_contra hr0
    have hemp : IsEmpty Ps := by
      have h0 : Nat.card Ps = 0 := by omega
      exact (Nat.card_eq_zero.mp h0).resolve_right (not_infinite_iff_finite.mpr inferInstance)
    have huniq : ∀ (p q k : ℕ) (ε ε' : Bool), w[p]? = some (k, ε) → w[q]? = some (k, ε') → p = q
      := by
      intro p q k ε ε' h1 h2
      by_contra hpq
      rcases lt_or_gt_of_ne hpq with hl | hl
      · exact hemp.false ⟨k, p, q, ε, ε', hl, h1, h2⟩
      · exact hemp.false ⟨k, q, p, ε', ε, hl, h2, h1⟩
    have hbdS : bd S = (fun z => g (0, z)) '' sphere 0 1 := by
      rw [(surface_of_presents (finW_sW _) hP hg).2]
      ext y
      constructor
      · rintro ⟨_, ⟨i, p, u, hp, -, hu, rfl⟩, rfl⟩
        have hi : i = 0 := by
          by_contra hi
          simp [sW, hi, nW] at hp
        subst hi
        exact ⟨_, by simp [norm_per], rfl⟩
      · rintro ⟨z, hz, rfl⟩
        have hn0 : 0 < n := by omega
        obtain ⟨p, hp, t, ht, he⟩ := exists_side_of_sphere hn0 (fun _ => true) (z := z)
          (by simpa using hz)
        refine ⟨spt (sW w) 0 p t, ⟨0, p, t, by rwa [hsl], fun j q k e' e'' h1 h2 => ?_, ht, rfl⟩,
          ?_⟩
        · obtain ⟨-, h1'⟩ := sW_get h1
          obtain ⟨hj, h2'⟩ := sW_get h2
          rw [huniq _ _ _ _ _ h1' h2', hj]
        · have e1 : spt (sW w) 0 p t = (0, z) := by
            rw [← he, spt, hsl]
            simp [sdPt]
          simp only [e1]
    have hconn : IsPreconnected (bd S) := by
      rw [hbdS]
      have hcz : ContinuousOn (fun z : ℂ => g (0, z)) (sphere 0 1) :=
        hg.1.comp (by fun_prop) fun z hz => dsk_sW_mk hne (sphere_subset_closedBall hz)
      have hsph : IsPreconnected (sphere (0 : ℂ) 1) := by
        rw [← per_image (n := n) (by omega)]
        exact isPreconnected_Icc.image _ (continuous_per n).continuousOn
      exact hsph.image _ hcz
    have hsub : (cuffs S).Subsingleton := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact hconn.connectedComponentIn ha |>.trans (hconn.connectedComponentIn hb).symm
    rcases hsub.eq_empty_or_singleton with h0 | ⟨C, h0⟩
    · rw [h0, Set.ncard_empty] at hc
      omega
    · rw [h0, Set.ncard_singleton] at hc
      omega
  refine ⟨{ D := UDisc.{u}
            isSurface_D := isSurface_uDisc
            isClosedDisc_D := ⟨discHomeo.trans (Homeomorph.Set.univ _).symm⟩
            r := Nat.card Ps
            f := f
            g := h
            φ := φ
            injective_f := fun i => hinj _ (hltp _)
            range_f_subset_bd := fun i => range_subset_iff.mpr (hbd _ _)
            injective_g := fun i => hinj _ (hltq _)
            range_g_subset_bd := fun i => range_subset_iff.mpr (hbd _ _)
            internally_disjoint_ff := fun i j hij t ht hmem => by
              have h1 := hdis _ _ (hltp _) (hltp _) t ht hmem
              have h2 := hx2 (e.symm i)
              rw [h1] at h2
              exact hij (e.symm.injective (Subtype.ext (hlab h2 (hx2 (e.symm j)))))
            internally_disjoint_gg := fun i j hij t ht hmem => by
              have h1 := hdis _ _ (hltq _) (hltq _) t ht hmem
              have h2 := hx3 (e.symm i)
              rw [h1] at h2
              exact hij (e.symm.injective (Subtype.ext (hlab h2 (hx3 (e.symm j)))))
            internally_disjoint_fg := fun i j t ht hmem => by
              have h1 := hdis _ _ (hltp _) (hltq _) t ht hmem
              have h2 := hx2 (e.symm i)
              rw [h1] at h2
              have h3 : e.symm i = e.symm j := Subtype.ext (hlab h2 (hx3 (e.symm j)))
              have h4 := hx1 (e.symm i)
              rw [h1, h3] at h4
              exact lt_irrefl _ h4
            internally_disjoint_gf := fun i j t ht hmem => by
              have h1 := hdis _ _ (hltq _) (hltp _) t ht hmem
              have h2 := hx3 (e.symm i)
              rw [h1] at h2
              have h3 : e.symm i = e.symm j := Subtype.ext (hlab h2 (hx2 (e.symm j)))
              have h4 := hx1 (e.symm i)
              rw [h1, h3] at h4
              exact lt_irrefl _ h4
            quotientMap_φ := hφc.isClosedMap.isQuotientMap hφc hφs
            pasting_eq := hpast
            interior_inj := fun a ha b hab => by
              have h1 := (hg.2.2 _ (hm a) _ (hm b)).mp hab
              have h2 := h1.eq_of_lt (hunit a ha)
              have h3 : b.down.1 = a.down.1 := congrArg Prod.snd h2
              exact (ULift.ext (Subtype.ext h3)).symm
            bd_eq_iff := fun a b => ⟨fun hab => by
              have h1 := hforth _ _ ((hg.2.2 _ (hm a) _ (hm b)).mp hab) (hm a)
              simpa only [toU_down] using h1, hback a b⟩ }, hr, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have ha' : ‖(a : UDisc.{u}).down.1‖ = 1 := (Set.ext_iff.mp bd_uDisc.{u} a).mp ha
  exact ⟨(a : UDisc.{u}).down.1, by simpa using ha', rfl⟩

end GraphMinor.GM07
