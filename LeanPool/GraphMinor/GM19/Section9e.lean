/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section9d
public import LeanPool.GraphMinor.GM19.Section5a
public import Mathlib.Data.Set.Finite.List

/-!
# Graph Minors XIX, (9.3) and (9.4)

The paper omits both proofs. For (9.3) we number the arms of each place and pass to a subsequence
on which the arms look alike: the same number of arms, and the march of each arm in the same
positions of `π(ℒ)`. Then we use the second hypothesis on a subsequence along which the labels
increase.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Function Topology GraphMinor.Surface

universe u w v

variable {S : Type u} [TopologicalSpace S] {α : Type w}

namespace QuasiOrder

variable {β : Type v}

/-- A sequence in a well-quasi-order has an increasing subsequence. -/
theorem IsWQO.exists_mono_subseq {Ω : QuasiOrder β} (h : Ω.IsWQO) (f : ℕ → β)
    (hf : ∀ i, f i ∈ Ω.E) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ m n, m ≤ n → Ω.le (f (g m)) (f (g n)) := by
  let : Preorder {x // x ∈ Ω.E} :=
    { le := fun a b ↦ Ω.le a.1 b.1
      le_refl := fun a ↦ Ω.refl a.1 a.2
      le_trans := fun a b c h₁ h₂ ↦ Ω.trans a.1 a.2 b.1 b.2 c.1 c.2 h₁ h₂ }
  have hw : WellQuasiOrdered (α := {x // x ∈ Ω.E}) (· ≤ ·) := fun F ↦ h (fun n ↦ (F n).1) fun n ↦
    (F n).2
  obtain ⟨g, hg⟩ := hw.exists_monotone_subseq (fun n ↦ ⟨f n, hf n⟩)
  exact ⟨g, g.strictMono, fun m n hmn ↦ hg m n hmn⟩

/-- Sequences of `k`-tuples in a well-quasi-order have a subsequence that increases in each
coordinate. -/
theorem IsWQO.exists_mono_tuple {Ω : QuasiOrder β} (h : Ω.IsWQO) (k : ℕ) (x : ℕ → ℕ → β)
    (hx : ∀ i, ∀ t < k, x i t ∈ Ω.E) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ m n, m ≤ n → ∀ t < k, Ω.le (x (g m) t) (x (g n) t) := by
  induction k with
  | zero => exact ⟨id, strictMono_id, fun _ _ _ _ ht ↦ absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨g, hg, hle⟩ := ih fun i t ht ↦ hx i t (ht.trans (Nat.lt_succ_self k))
    obtain ⟨g', hg', hle'⟩ := h.exists_mono_subseq (fun n ↦ x (g n) k)
      fun i ↦ hx _ _ (Nat.lt_succ_self k)
    refine ⟨g ∘ g', hg.comp hg', fun m n hmn t ht ↦ ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact hle _ _ (hg'.monotone hmn) t ht
    · exact hle' m n hmn

end QuasiOrder

/-- The arm with `A⁻ = Γ` and no complement. -/
def Arm.top (Γ : Painting S) : Arm Γ where
  minus := Γ.toHypergraph
  compl :=
    { vertexSet := ∅
      edgeSet := ∅
      Inc := fun _ _ ↦ False
      vertex_mem_of_inc := fun _ _ h ↦ h.elim
      edge_mem_of_inc := fun _ _ h ↦ h.elim
      vertexSet_finite := finite_empty
      edgeSet_finite := finite_empty }
  isSeparation :=
    { left_le := le_rfl
      right_le := ⟨empty_subset _, empty_subset _, fun _ h ↦ h.elim⟩
      union_eq := by
        apply Hypergraph.ext
        · exact union_empty _
        · exact union_empty _
        · funext e v
          exact propext (or_iff_left id)
      edgeSet_inter_eq := inter_empty _ }
  π := []
  π_nodup := List.nodup_nil
  π_set := by
    ext v
    simp only [mem_ofPred_eq, List.not_mem_nil, false_iff]
    exact fun h ↦ h.2

section

variable {χ : ColourScheme S α}

/-- **Graph Minors XIX, (9.3).** "**9.3.** *Let $\chi$ be a disjoint colour scheme, and let
$\mathscr{P}$ be a set of $\chi$-places. For each $(\Gamma, \phi, \mathscr{L}) \in \mathscr{P}$ let
$\pi(\mathscr{L})$ be a march with
$\bar{\pi}(\mathscr{L}) = \bigcup (\bar{\pi}(A) : A \in \mathscr{L})$. Suppose that*
• *there exist $m, n$ such that $|\mathscr{L}| \le m$ and $|\bar{\pi}(\mathscr{L})| \le n$ for all
  $(\Gamma, \phi, \mathscr{L}) \in \mathscr{P}$,* ...
• *for every countable sequence $(\Gamma_i, \phi_i, \mathscr{L}_i)$ $(i = 1, 2, \dots)$ of members
  of $\mathscr{P}$ there exist $j > i \ge 1$ and an inflation $\sigma$ of $M(\Gamma_i,
  \mathscr{L}_i)$
  in $\Gamma_j$, such that*
  ◦ *for each $v \in V(M(\Gamma_i, \mathscr{L}_i)), V(\sigma(v)) \subseteq V(M(\Gamma_j,
  \mathscr{L}_j))$,*
  ◦ *for each $e \in E(M(\Gamma_i, \mathscr{L}_i)), \sigma(e) \in E(M(\Gamma_j, \mathscr{L}_j))$ and
    $\phi_i(e) \le \phi_j(\sigma(e))$,*
  ◦ $|\bar{\pi}(\mathscr{L}_i)| = |\bar{\pi}(\mathscr{L}_j)|$, *and for*
    $1 \le h \le |\bar{\pi}(\mathscr{L}_i)|$ *if* $v$ *is the* $h$th *term of* $\pi(\mathscr{L}_i)$
    *then* $\sigma(v)$ *contains the* $h$th *term of* $\pi(\mathscr{L}_j)$.
*Then $\mathscr{P}$ is well-behaved.*" -/
theorem theorem_9_3_proof {Pl : Set (Place χ)} (πL : Place χ → List S)
    (hsub : ∀ X ∈ Pl, ∀ A ∈ X.L.arms, ∀ v ∈ A.π, v ∈ πL X) {m n : ℕ}
    (hm : ∀ X ∈ Pl, X.L.arms.ncard ≤ m) (hn : ∀ X ∈ Pl, (πL X).length ≤ n)
    (hseq : ∀ seq : ℕ → Place χ, (∀ i, seq i ∈ Pl) → ∃ i j, i < j ∧ ∃ σv σe,
      IsSubInflationIn (seq i).P.Γ (seq i).L.M (seq j).P.Γ σv σe ∧
      (∀ v ∈ (seq i).L.M.vertexSet, σv v ⊆ (seq j).L.M.vertexSet) ∧
      (∀ e ∈ (seq i).L.M.edgeSet, σe e ∈ (seq j).L.M.edgeSet ∧
        χ.unionLE ((seq i).P.φ e) ((seq j).P.φ (σe e))) ∧
      (πL (seq i)).length = (πL (seq j)).length ∧
      ∀ (h : ℕ) (h₁ : h < (πL (seq i)).length) (h₂ : h < (πL (seq j)).length),
        (πL (seq j))[h] ∈ σv (πL (seq i))[h]) :
    IsWellBehavedPlaces Pl := by
  classical
  intro β Ω hΩ seq hPl ξ hξ
  let Code : Type := {c : List (Fin (n + 1)) // c.length ≤ n}
  have : Finite Code := (List.finite_length_le (Fin (n + 1)) n).to_subtype
  let toFin : ℕ → Fin (n + 1) := fun x ↦ ⟨min x n, by omega⟩
  let code : ∀ i, Arm (seq i).P.Γ → Code := fun i A ↦
    ⟨(A.π.map fun v ↦ toFin ((πL (seq i)).idxOf v)).take n, List.length_take_le _ _⟩
  let as : ∀ i, List (Arm (seq i).P.Γ) := fun i ↦ (seq i).L.finite_arms.toFinset.toList
  have has_nd : ∀ i, (as i).Nodup := fun i ↦ Finset.nodup_toList _
  have has_mem : ∀ i (A : Arm (seq i).P.Γ), A ∈ as i ↔ A ∈ (seq i).L.arms := fun i A ↦ by
    simp [as]
  have has_len : ∀ i, (as i).length ≤ m := fun i ↦ by
    have h := hm _ (hPl i)
    rw [ncard_eq_toFinset_card _ (seq i).L.finite_arms] at h
    simpa [as] using h
  let Lst : Type := {l : List Code // l.length ≤ m}
  have : Finite Lst := (List.finite_length_le Code m).to_subtype
  let l : ℕ → Lst := fun i ↦ ⟨((as i).map (code i)).take m, List.length_take_le _ _⟩
  obtain ⟨l₀, hl₀⟩ := Finite.exists_infinite_fiber l
  have hI : (l ⁻¹' {l₀}).Infinite := infinite_coe_iff.mp hl₀
  let g₀ : ℕ → ℕ := Nat.nth (· ∈ l ⁻¹' {l₀})
  have hg₀ : StrictMono g₀ := Nat.nth_strictMono hI
  have hg₀l : ∀ i, l (g₀ i) = l₀ := fun i ↦ Nat.nth_mem_of_infinite hI i
  have hlval : ∀ i, l i = ⟨(as i).map (code i), by simpa using has_len i⟩ := fun i ↦
    Subtype.ext (List.take_of_length_le (by simpa using has_len i))
  let k := l₀.1.length
  have hlen : ∀ i, (as (g₀ i)).length = k := fun i ↦ by
    have h := congrArg (fun c : Lst ↦ c.1.length) ((hlval _).symm.trans (hg₀l i))
    simpa using h
  let y₀ : β := ξ 0 (Arm.top _)
  let x : ℕ → ℕ → β := fun i t ↦
    if h : t < (as (g₀ i)).length then ξ (g₀ i) (as (g₀ i))[t] else y₀
  have hx : ∀ i, ∀ t < k, x i t ∈ Ω.E := fun i t ht ↦ by
    have h : t < (as (g₀ i)).length := (hlen i).symm ▸ ht
    simp only [x, dite_eq_left h]
    exact hξ _ _ ((has_mem _ _).1 (List.getElem_mem h))
  obtain ⟨g₁, hg₁, hmono⟩ := hΩ.exists_mono_tuple k x hx
  obtain ⟨a, b, hab, σv, σe, hinf, hV, hE, hlenπ, hroots⟩ :=
    hseq (fun i ↦ seq (g₀ (g₁ i))) fun i ↦ hPl _
  have hlenπA : ∀ i, ∀ A ∈ (seq i).L.arms, A.π.length ≤ (πL (seq i)).length := fun i A hA ↦
    (A.π_nodup.subperm fun v hv ↦ hsub _ (hPl i) A hA v hv).length_le
  have hidx : ∀ i, ∀ A ∈ (seq i).L.arms, ∀ v ∈ A.π, (πL (seq i)).idxOf v < (πL (seq i)).length :=
    fun i A hA v hv ↦ List.idxOf_lt_length_iff.2 (hsub _ (hPl i) A hA v hv)
  have hdisj : ∀ {x v v'}, v ∈ (seq (g₀ (g₁ a))).L.M.vertexSet →
      v' ∈ (seq (g₀ (g₁ a))).L.M.vertexSet → x ∈ σv v → x ∈ σv v' → v = v' := by
    intro x v v' hv hv' hx hx'
    by_contra hne
    exact disjoint_left.1 (hinf.vertex_disjoint v hv v' hv' hne) hx hx'
  generalize hIdef : g₀ (g₁ a) = I at *
  generalize hJdef : g₀ (g₁ b) = J at *
  have hIJ : I < J := hIdef ▸ hJdef ▸ hg₀ (hg₁ hab)
  have hlenI : (as I).length = k := hIdef ▸ hlen _
  have hlenJ : (as J).length = k := hJdef ▸ hlen _
  have hll : (as I).map (code I) = (as J).map (code J) := by
    have h₁ : l I = l₀ := hIdef ▸ hg₀l _
    have h₂ : l J = l₀ := hJdef ▸ hg₀l _
    exact congrArg Subtype.val ((hlval I).symm.trans (h₁.trans (h₂.symm.trans (hlval J))))
  let τ : Arm (seq I).P.Γ → Arm (seq J).P.Γ := fun A ↦
    if h : (as I).idxOf A < (as J).length then (as J)[(as I).idxOf A] else Arm.top _
  have hτ : ∀ A ∈ (seq I).L.arms, ∃ (h₁ : (as I).idxOf A < (as I).length)
      (h₂ : (as I).idxOf A < (as J).length), (as I)[(as I).idxOf A] = A ∧
        τ A = (as J)[(as I).idxOf A] := by
    intro A hA
    have h₁ : (as I).idxOf A < (as I).length := List.idxOf_lt_length_iff.2 ((has_mem _ _).2 hA)
    have h₂ : (as I).idxOf A < (as J).length := by omega
    exact ⟨h₁, h₂, List.getElem_idxOf h₁, dite_eq_left h₂⟩
  have hτmem : ∀ A ∈ (seq I).L.arms, τ A ∈ (seq J).L.arms := by
    intro A hA
    obtain ⟨h₁, h₂, -, hEq⟩ := hτ A hA
    rw [hEq]
    exact (has_mem _ _).1 (List.getElem_mem h₂)
  have hcode : ∀ A ∈ (seq I).L.arms, code I A = code J (τ A) := by
    intro A hA
    obtain ⟨h₁, h₂, hA', hEq⟩ := hτ A hA
    have h := List.getElem_of_eq hll (i := (as I).idxOf A) (by simpa using h₁)
    rw [List.getElem_map, List.getElem_map, hA', ← hEq] at h
    exact h
  have hmaps : ∀ A ∈ (seq I).L.arms,
      A.π.map (fun v ↦ toFin ((πL (seq I)).idxOf v)) =
        (τ A).π.map fun v ↦ toFin ((πL (seq J)).idxOf v) := by
    intro A hA
    have h := congrArg Subtype.val (hcode A hA)
    have hl₁ : A.π.length ≤ n := (hlenπA I A hA).trans (hn _ (hPl I))
    have hl₂ : (τ A).π.length ≤ n := (hlenπA J _ (hτmem A hA)).trans (hn _ (hPl J))
    simp only [code] at h
    rwa [List.take_of_length_le (by simpa using hl₁),
      List.take_of_length_le (by simpa using hl₂)] at h
  have hlenτ : ∀ A ∈ (seq I).L.arms, (τ A).π.length = A.π.length := by
    intro A hA
    simpa using (congrArg List.length (hmaps A hA)).symm
  have hterm : ∀ A ∈ (seq I).L.arms, ∀ (s : ℕ) (h₁ : s < A.π.length) (h₂ : s < (τ A).π.length),
      (τ A).π[s] ∈ σv A.π[s] := by
    intro A hA s h₁ h₂
    have h := List.getElem_of_eq (hmaps A hA) (i := s) (by simpa using h₁)
    rw [List.getElem_map, List.getElem_map] at h
    have hv₁ := List.getElem_mem h₁
    have hv₂ := List.getElem_mem h₂
    have hp₁ := hidx I A hA _ hv₁
    have hp₂ := hidx J _ (hτmem A hA) _ hv₂
    have hn₁ := hn _ (hPl I)
    have hn₂ := hn _ (hPl J)
    have hval : (πL (seq I)).idxOf A.π[s] = (πL (seq J)).idxOf (τ A).π[s] := by
      have h' := congrArg Fin.val h
      simp only [toFin] at h'
      omega
    have hr := hroots _ hp₁ (by rw [← hlenπ]; exact hp₁)
    rw [List.getElem_idxOf hp₁] at hr
    simp only [hval, List.getElem_idxOf hp₂] at hr
    exact hr
  refine ⟨I, J, hIJ, τ, ⟨hτmem, ?_, σv, σe, hinf, fun e he ↦ (hE e he).1,
    fun A hA ↦ ⟨hlenτ A hA, hterm A hA⟩, fun A hA v hv ↦ ?_, fun e he ↦ (hE e he).2⟩,
    fun A hA ↦ ?_⟩
  · intro A₁ hA₁ A₂ hA₂ heq
    obtain ⟨h₁, h₂, hA₁', hEq₁⟩ := hτ A₁ hA₁
    obtain ⟨h₃, h₄, hA₂', hEq₂⟩ := hτ A₂ hA₂
    rw [hEq₁, hEq₂] at heq
    have hij := (List.Nodup.getElem_inj_iff (has_nd J)).1 heq
    rw [← hA₁', ← hA₂']
    simp only [hij]
  · have hfin : (σv v ∩ (τ A).V).Finite :=
      ((seq J).P.Γ.finite_V.subset (hinf.vertex_subset v hv)).subset inter_subset_left
    refine (ncard_le_one hfin).2 ?_
    rintro x ⟨hx, hxV⟩ y ⟨hy, hyV⟩
    have hτA := hτmem A hA
    have hxπ := RootedLocation.mem_π_of_M hτA (hV v hv hx) hxV
    have hyπ := RootedLocation.mem_π_of_M hτA (hV v hv hy) hyV
    obtain ⟨s, hs', rfl⟩ := List.mem_iff_getElem.1 hxπ
    obtain ⟨t, ht', rfl⟩ := List.mem_iff_getElem.1 hyπ
    have hs : s < A.π.length := by rw [← hlenτ A hA]; exact hs'
    have ht : t < A.π.length := by rw [← hlenτ A hA]; exact ht'
    have h₁ := hdisj hv (RootedLocation.π_mem_M hA (List.getElem_mem hs)) hx (hterm A hA s hs hs')
    have h₂ := hdisj hv (RootedLocation.π_mem_M hA (List.getElem_mem ht)) hy (hterm A hA t ht ht')
    have hst : s = t := (List.Nodup.getElem_inj_iff A.π_nodup).1 (h₁.symm.trans h₂)
    subst hst
    rfl
  · obtain ⟨h₁, h₂, hA', hEq⟩ := hτ A hA
    have ht : (as I).idxOf A < k := by omega
    subst hIdef hJdef
    have hle := hmono a b hab.le _ ht
    simp only [x, dite_eq_left h₁, dite_eq_left h₂, hA', ← hEq] at hle
    exact hle

end

section

variable {S : Type} [TopologicalSpace S] [T2Space S] {α : Type w} {χ : ColourScheme S α}

omit [T2Space S] in
theorem IsPlaceHomeoImage.coloured {X Y : Place χ} {f : S ≃ₜ S} (h : IsPlaceHomeoImage X Y f) :
    IsColouredImage f X.P Y.P :=
  ⟨h.2.1.symm, h.2.2.1.symm, fun e he ↦ (h.2.2.2.1 e he).1, fun e he ↦ (h.2.2.2.1 e he).2⟩

omit [T2Space S] in
theorem IsPlaceHomeoImage.M_V {X Y : Place χ} {f : S ≃ₜ S} {g : Arm X.P.Γ → Arm Y.P.Γ}
    (hV : Y.P.Γ.V = f '' X.P.Γ.V) (hg : BijOn g X.L.arms Y.L.arms)
    (hc : ∀ A ∈ X.L.arms, (g A).compl.vertexSet = f '' A.compl.vertexSet) :
    Y.L.M.vertexSet = f '' X.L.M.vertexSet := by
  ext v
  constructor
  · rintro ⟨hv, hall⟩
    rw [hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    refine ⟨v₀, ⟨hv₀, fun A hA ↦ ?_⟩, rfl⟩
    have h := hall _ (hg.mapsTo hA)
    rw [hc A hA] at h
    obtain ⟨w, hw, hEq⟩ := h
    exact f.injective hEq ▸ hw
  · rintro ⟨v₀, ⟨hv₀, hall⟩, rfl⟩
    refine ⟨hV ▸ mem_image_of_mem _ hv₀, fun B hB ↦ ?_⟩
    obtain ⟨A, hA, rfl⟩ := hg.surjOn hB
    rw [hc A hA]
    exact mem_image_of_mem _ (hall A hA)

omit [T2Space S] in
theorem IsPlaceHomeoImage.M_E {X Y : Place χ} {f : S ≃ₜ S} {g : Arm X.P.Γ → Arm Y.P.Γ}
    (hE : Y.P.Γ.E = (fun e ↦ f '' e) '' X.P.Γ.E) (hg : BijOn g X.L.arms Y.L.arms)
    (hc : ∀ A ∈ X.L.arms, (g A).compl.edgeSet = (fun e ↦ f '' e) '' A.compl.edgeSet) :
    Y.L.M.edgeSet = (fun e ↦ f '' e) '' X.L.M.edgeSet := by
  have hinj : Injective fun e : Set S ↦ f '' e := f.injective.image_injective
  ext v
  constructor
  · rintro ⟨hv, hall⟩
    rw [hE] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    refine ⟨v₀, ⟨hv₀, fun A hA ↦ ?_⟩, rfl⟩
    have h := hall _ (hg.mapsTo hA)
    rw [hc A hA] at h
    obtain ⟨w, hw, hEq⟩ := h
    exact hinj hEq ▸ hw
  · rintro ⟨v₀, ⟨hv₀, hall⟩, rfl⟩
    refine ⟨hE ▸ mem_image_of_mem _ hv₀, fun B hB ↦ ?_⟩
    obtain ⟨A, hA, rfl⟩ := hg.surjOn hB
    rw [hc A hA]
    exact mem_image_of_mem _ (hall A hA)

omit [T2Space S] in
/-- An inflation of `M(Γ, ℒ)` carried over by homeomorphisms. -/
theorem IsSubInflationIn.image {X₁ X₂ Y₁ Y₂ : Place χ} {f₁ f₂ : S ≃ₜ S}
    (I₁ : IsColouredImage f₁ X₁.P Y₁.P) (I₂ : IsColouredImage f₂ X₂.P Y₂.P)
    (hV : Y₁.L.M.vertexSet = f₁ '' X₁.L.M.vertexSet)
    (hE : Y₁.L.M.edgeSet = (fun e ↦ f₁ '' e) '' X₁.L.M.edgeSet) {σv : S → Set S}
    {σe : Set S → Set S} (h : IsSubInflationIn X₁.P.Γ X₁.L.M X₂.P.Γ σv σe) :
    IsSubInflationIn Y₁.P.Γ Y₁.L.M Y₂.P.Γ (imgV f₁ f₂ σv) (imgE f₁ f₂ σe) := by
  refine
    { H_le := Y₁.L.M_le
      edge_mem := ?_
      edge_size := ?_
      edge_injOn := ?_
      vertex_nonempty := ?_
      vertex_subset := ?_
      vertex_connected := ?_
      vertex_disjoint := ?_
      ends := ?_ }
  · intro e he
    rw [hE] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only
    rw [imgE_image, I₂.E_eq]
    exact mem_image_of_mem _ (h.edge_mem c hc)
  · intro e he
    rw [hE] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only
    rw [imgE_image, ncard_tilde_image, ncard_tilde_image, h.edge_size c hc]
  · intro e he e' he' heq
    rw [hE] at he he'
    obtain ⟨c, hc, rfl⟩ := he
    obtain ⟨c', hc', rfl⟩ := he'
    simp only [imgE_image] at heq
    have := h.edge_injOn hc hc' (f₂.injective.image_injective heq)
    rw [this]
  · intro v hv
    rw [hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    rw [imgV_image]
    exact (h.vertex_nonempty v₀ hv₀).image _
  · intro v hv
    rw [hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    rw [imgV_image, I₂.V]
    exact image_mono (h.vertex_subset v₀ hv₀)
  · intro v hv
    rw [hV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    rw [imgV_image]
    let F : X₂.P.Γ.skAdj.induce (σv v₀) →g Y₂.P.Γ.skAdj.induce (f₂ '' σv v₀) :=
      ⟨fun x ↦ ⟨f₂ x.1, mem_image_of_mem _ x.2⟩, fun hxy ↦ skAdj_image I₂ hxy⟩
    refine (h.vertex_connected v₀ hv₀).map F ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro v hv w hw hne
    rw [hV] at hv hw
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    rw [imgV_image, imgV_image]
    exact (disjoint_image_iff f₂.injective).mpr
      (h.vertex_disjoint v₀ hv₀ w₀ hw₀ fun he ↦ hne (by rw [he]))
  · intro e he i hi hi'
    rw [hE] at he
    obtain ⟨c, hc, rfl⟩ := he
    have hcE := (X₁.L.M_le.edgeSet_subset hc : c ∈ X₁.P.Γ.E)
    simp only [imgE_image] at hi' ⊢
    have h₁ := I₁.γ c hcE
    have h₂ := I₂.γ _ (h.edge_mem c hc)
    simp only [h₁, h₂, List.length_map] at hi hi' ⊢
    simp only [List.getElem_map]
    rw [imgV_image]
    exact mem_image_of_mem _ (h.ends c hc i hi hi')

omit [T2Space S] in
/-- **Graph Minors XIX, (9.4).** "Let $\chi$ be a disjoint colour scheme, and let $\mathscr{C}$ be a
well-behaved set of
$\chi$-places. Let $\mathscr{C}'$ be the set of all images of members of $\mathscr{C}$ under
$\Phi_\chi$-preserving homeomorphisms of $\Sigma_\chi$. Then $\mathscr{C}'$ is well-behaved." -/
theorem theorem_9_4_proof {C : Set (Place χ)} (h : IsWellBehavedPlaces C) :
    IsWellBehavedPlaces {Y | ∃ X ∈ C, ∃ f, IsPlaceHomeoImage X Y f} := by
  classical
  intro β Ω hΩ seq hseq ξ hξ
  choose X hX f hf using hseq
  have I : ∀ i, IsColouredImage (f i) (X i).P (seq i).P := fun i ↦ IsPlaceHomeoImage.coloured (hf i)
  choose g hbij hg using fun i ↦ (hf i).2.2.2.2
  obtain ⟨i, j, hij, τ, ⟨hmem, hinj, σv, σe, hσ, hEM, hπ, hcap, hcol⟩, hle⟩ :=
    h Ω hΩ X hX (fun i A ↦ ξ i (g i A)) fun i A hA ↦ hξ i _ ((hbij i).mapsTo hA)
  have hMV : ∀ k, (seq k).L.M.vertexSet = f k '' (X k).L.M.vertexSet := fun k ↦
    IsPlaceHomeoImage.M_V (I k).V (hbij k) fun A hA ↦ (hg k A hA).2.2.1
  have hME : ∀ k, (seq k).L.M.edgeSet = (fun e ↦ f k '' e) '' (X k).L.M.edgeSet := fun k ↦
    IsPlaceHomeoImage.M_E (I k).E_eq (hbij k) fun A hA ↦ (hg k A hA).2.2.2.1
  let τ' : Arm (seq i).P.Γ → Arm (seq j).P.Γ := fun B ↦
    if hB : ∃ A ∈ (X i).L.arms, g i A = B then g j (τ hB.choose) else Arm.top _
  have hτ' : ∀ A ∈ (X i).L.arms, τ' (g i A) = g j (τ A) := by
    intro A hA
    have hex : ∃ A' ∈ (X i).L.arms, g i A' = g i A := ⟨A, hA, rfl⟩
    have hch := hex.choose_spec
    have heq : hex.choose = A := (hbij i).injOn hch.1 hA hch.2
    simp only [τ', dite_eq_left hex, heq]
  have hsurj : ∀ B ∈ (seq i).L.arms, ∃ A ∈ (X i).L.arms, g i A = B := fun B hB ↦ (hbij i).surjOn hB
  refine ⟨i, j, hij, τ', ⟨?_, ?_, imgV (f i) (f j) σv, imgE (f i) (f j) σe,
    IsSubInflationIn.image (I i) (I j) (hMV i) (hME i) hσ, ?_, fun B hB ↦ ?_, ?_, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := hsurj B hB
    rw [hτ' A hA]
    exact (hbij j).mapsTo (hmem A hA)
  · intro B hB B' hB' heq
    obtain ⟨A, hA, rfl⟩ := hsurj B hB
    obtain ⟨A', hA', rfl⟩ := hsurj B' hB'
    rw [hτ' A hA, hτ' A' hA'] at heq
    rw [hinj hA hA' ((hbij j).injOn (hmem A hA) (hmem A' hA') heq)]
  · intro e he
    rw [hME i] at he
    obtain ⟨c, hc, rfl⟩ := he
    simp only
    rw [imgE_image, hME j]
    exact mem_image_of_mem _ (hEM c hc)
  · obtain ⟨A, hA, rfl⟩ := hsurj B hB
    rw [hτ' A hA]
    have h₁ := (hg i A hA).2.2.2.2
    have h₂ := (hg j _ (hmem A hA)).2.2.2.2
    refine ⟨by simp [h₁, h₂, (hπ A hA).1], fun s hs hs' ↦ ?_⟩
    simp only [h₁, h₂, List.length_map] at hs hs' ⊢
    simp only [List.getElem_map]
    rw [imgV_image]
    exact mem_image_of_mem _ ((hπ A hA).2 s hs hs')
  · intro B hB v hv
    obtain ⟨A, hA, rfl⟩ := hsurj B hB
    rw [hMV i] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    rw [hτ' A hA, imgV_image]
    have hVeq : (g j (τ A)).V = f j '' (τ A).V := (hg j _ (hmem A hA)).1
    rw [hVeq, ← image_inter (f j).injective, ncard_image_of_injective _ (f j).injective]
    exact hcap A hA v₀ hv₀
  · intro e he
    rw [hME i] at he
    obtain ⟨c, hc, rfl⟩ := he
    have hcE : c ∈ (X i).P.Γ.E := (X i).L.M_le.edgeSet_subset hc
    simp only
    rw [imgE_image, (I i).φ c hcE, (I j).φ _ (hσ.edge_mem c hc)]
    exact hcol c hc
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := hsurj B hB
    rw [hτ' A hA]
    exact hle A hA

end

end GraphMinor.GM19
