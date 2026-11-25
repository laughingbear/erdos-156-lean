/-
Copyright 2026 Laughing Bear.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Erdős Problem 156: the greedy Sidon set in `[1, N]` has size `≫ N^{1/3}`

A proof of `Erdos156.erdos_156.variants.greedy_lower_bound` from
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/156.lean`).

The definitions `IsSidon`, `Finset.greedySidon.go`, `Finset.greedySidon.aux`,
`Finset.greedySidon`, `Finset.greedySidonBelow`, the `≫` notation, the supporting lemmas
`Set.IsSidon.insert`, `Finset.IsSidon.insert_ge_max'`, `Finset.IsSidon.exists_insert`,
`Finset.IsSidon.exists_insert_ge` (with their proofs) and the statement are copied verbatim from
formal-conjectures (`FormalConjecturesForMathlib/Combinatorics/Basic.lean`,
`FormalConjecturesForMathlib/Analysis/Asymptotics/Basic.lean`).

**Proof.** Let `A` be the set after `N` greedy steps; its maximum is at least `N + 1`.

* *Greedy invariant* (`GreedySidon.inv_aux`): every `1 ≤ y < max A` with `y ∉ A` is incompatible
  with the elements of `A` below `y`, because the greedy step (a `Nat.find`) skipped it.
* *Forbidden elements* (`GreedySidon.mem_forb`): if `S` is Sidon and `S ∪ {y}` is not, then
  `y = a + b - c` or `2y = a + b` with `a, b, c ∈ S`.

So every `y ∈ [1, N]` lies in `G = A ∩ [1, N]` or is forbidden by `G`. Hence
`N ≤ |G| + |G|³ + |G|² ≤ 3|G|³`, and `N^{1/3} ≤ 2|G|`.
-/

section Infra

open Function Set
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

theorem IsSidon.insert {A : Set α} {m : α} [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔ (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]



end Set

namespace Finset

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- If `A` is finite Sidon, then `A ∪ {s}` is also Sidon provided `s ≥ A.max + 1`. -/
theorem IsSidon.insert_ge_max' {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) {s : ℕ}
    (hs : 2 * A.max' h + 1 ≤ s) :
    IsSidon (A ∪ {s}) := by
  have h₁ {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
        a + b < 2 * A.max' h + 1 + c := by linarith [A.le_max' _ ha, A.le_max' _ hb]
  have : s ∉ A := by
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  exact (IsSidon.insert hA).2 <| by simpa [this] using fun a ha b hb ↦
    ⟨by linarith [A.le_max' _ ha, A.le_max' _ hb], fun c hc ↦ by linarith [h₁ hc hb ha]⟩

theorem IsSidon.exists_insert {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) :
    ∃ m ∉ A, IsSidon (A ∪ {m}) := by
  refine ⟨2 * A.max' h + 1, ?_, insert_ge_max' h hA le_rfl⟩
  exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
    linarith [A.le_max' _ ha]

theorem IsSidon.exists_insert_ge {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) (s : ℕ) :
    ∃ m ≥ s, m ∉ A ∧ IsSidon (A ∪ {m}) := by
  refine ⟨if s ≥ 2 * A.max' h + 1 then s else 2 * A.max' h + 1, ?_, ?_, ?_⟩
  · split_ifs <;> linarith
  · split_ifs <;>
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  · split_ifs with hs
    · exact insert_ge_max' h hA hs
    · exact insert_ge_max' h hA le_rfl

/-- Given a finite Sidon set `A` and a lower bound `m`, `go` finds the smallest number `m' ≥ m`
such that `A ∪ {m'}` is Sidon. If `A` is empty then this returns the value `m`. Note that
the lower bound is required to avoid `0` being a contender in some cases. -/
def greedySidon.go (A : Finset ℕ) (hA : IsSidon (A : Set ℕ)) (m : ℕ) :
    {m' : ℕ // m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ)} :=
  if h : A.Nonempty then
    have : ∃ m', m' ≥ m ∧ m' ∉ A ∧ IsSidon (↑(A ∪ {m'}) : Set ℕ) := by
      simpa [and_assoc] using Finset.IsSidon.exists_insert_ge h hA m
    ⟨Nat.find this, Nat.find_spec this⟩
  else ⟨m, by simp_all [IsSidon]⟩

/-- Main search loop for generating the greedy Sidon sequence. The return value for step `n` is the
finite set of numbers generated so far, a proof that it is Sidon, and the greatest element of
the finite set at that point. This is initialised at `{1}`, then `greedySidon.go` is
called iteratively using the lower bound `max + 1` to find the next smallest Sidon preserving
number. -/
def greedySidon.aux (n : ℕ) : ({A : Finset ℕ // IsSidon (A : Set ℕ)} × ℕ) :=
  match n with
  | 0 => (⟨{1}, by simp [IsSidon]⟩, 1)
  | k + 1 =>
    let (A, s) := greedySidon.aux k
    let s := if h : A.1.Nonempty then A.1.max' h + 1 else s
    let s' := greedySidon.go A.1 A.2 s
    (⟨A.1 ∪ {s'.1}, s'.2.2.2⟩, s'.1)

/-- `greedySidon` is the sequence obtained by the initial set $\{1\}$ and iteratively obtaining
the next smallest integer that preserves the Sidon property of the set. This gives the
sequence `1, 2, 4, 8, 13, 21, 31, ...`. -/
def greedySidon (n : ℕ) : ℕ := greedySidon.aux n |>.2

/-- The greedy Sidon set in `{1, …, N}`: starting from `∅`, iterate through `1, …, N` and
include `x` if and only if `A ∪ {x}` remains Sidon.
Alternatively, this is precisely the set of elements in the greedy Sidon sequence that are `≤ N`. -/
def greedySidonBelow (N : ℕ) : Finset ℕ :=
  (greedySidon.aux N).1.1.filter (· ≤ N)

end Finset

end Infra

notation f " ≫ " g => Asymptotics.IsBigO Filter.atTop (g : ℕ → ℝ) (f : ℕ → ℝ)

open Finset Filter

namespace GreedySidon

/-- Elements forbidden by a Sidon set `S`: `a + b - c` and `(a + b) / 2`. -/
def forb (S : Finset ℕ) : Finset ℕ :=
  ((S ×ˢ S) ×ˢ S).image (fun p => p.1.1 + p.1.2 - p.2) ∪ (S ×ˢ S).image (fun p => (p.1 + p.2) / 2)

lemma card_forb_le (S : Finset ℕ) : (forb S).card ≤ S.card ^ 3 + S.card ^ 2 := by
  refine (card_union_le _ _).trans (add_le_add (card_image_le.trans ?_) (card_image_le.trans ?_))
  · simp [card_product, pow_succ]
  · simp [card_product, sq]

lemma forb_mono {S T : Finset ℕ} (h : S ⊆ T) : forb S ⊆ forb T := by
  unfold forb
  exact union_subset_union (image_subset_image (product_subset_product
    (product_subset_product h h) h)) (image_subset_image (product_subset_product h h))

lemma mem_forb_of_three {S : Finset ℕ} {y a b c : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (h : y + c = a + b) : y ∈ forb S := by
  refine mem_union_left _ (mem_image.2 ⟨((a, b), c), by simp [ha, hb, hc], by simp; omega⟩)

lemma mem_forb_of_two {S : Finset ℕ} {y a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (h : y + y = a + b) : y ∈ forb S := by
  refine mem_union_right _ (mem_image.2 ⟨(a, b), by simp [ha, hb], by simp; omega⟩)

/-- If `S` is Sidon and adding `y ∉ S` breaks the Sidon property, `y` is forbidden by `S`. -/
lemma mem_forb {S : Finset ℕ} (hS : IsSidon (S : Set ℕ)) {y : ℕ} (hy : y ∉ S)
    (h : ¬ IsSidon ((S ∪ {y} : Finset ℕ) : Set ℕ)) : y ∈ forb S := by
  unfold IsSidon at h
  push Not at h
  obtain ⟨i₁, hi₁, j₁, hj₁, i₂, hi₂, j₂, hj₂, hsum, hl, hr⟩ := h
  simp only [coe_union, coe_singleton, Set.mem_union, mem_coe, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
  have hl' : ¬ (i₁ = j₁ ∧ i₂ = j₂) := fun h => by
    have := hl h.1; exact this h.2
  have hr' : ¬ (i₁ = j₂ ∧ i₂ = j₁) := fun h => by
    have := hr h.1; exact this h.2
  have hyS : ∀ {z}, z ∈ S → z = y → False := fun hz e => hy (e ▸ hz)
  rcases hi₁ with hi₁ | hi₁ <;> rcases hj₁ with hj₁ | hj₁ <;>
  rcases hi₂ with hi₂ | hi₂ <;> rcases hj₂ with hj₂ | hj₂
  -- SSSS
  · rcases hS i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum with h | h
    · exact absurd h hl'
    · exact absurd h hr'
  -- SSSy
  · exact mem_forb_of_three hi₁ hi₂ hj₁ (by omega)
  -- SSyS
  · exact mem_forb_of_three hj₁ hj₂ hi₁ (by omega)
  -- SSyy
  · exact absurd ⟨by omega, by omega⟩ hl'
  -- SySS
  · exact mem_forb_of_three hi₁ hi₂ hj₂ (by omega)
  -- SySy
  · exact mem_forb_of_two hi₁ hi₂ (by omega)
  -- SyyS
  · exact absurd ⟨by omega, by omega⟩ hr'
  -- Syyy
  · exact (hyS hi₁ (by omega)).elim
  -- ySSS
  · exact mem_forb_of_three hj₁ hj₂ hi₂ (by omega)
  -- ySSy
  · exact absurd ⟨by omega, by omega⟩ hr'
  -- ySyS
  · exact mem_forb_of_two hj₁ hj₂ (by omega)
  -- ySyy
  · exact (hyS hj₁ (by omega)).elim
  -- yySS
  · exact absurd ⟨by omega, by omega⟩ hl'
  -- yySy
  · exact (hyS hi₂ (by omega)).elim
  -- yyyS
  · exact (hyS hj₂ (by omega)).elim
  -- yyyy
  · exact absurd ⟨by omega, by omega⟩ hl'


open Finset.greedySidon in
lemma aux_succ (k : ℕ) : (aux (k + 1)).1.1 = (aux k).1.1 ∪
    {(go (aux k).1.1 (aux k).1.2
      (if h : (aux k).1.1.Nonempty then (aux k).1.1.max' h + 1 else (aux k).2)).1} := rfl

open Finset.greedySidon in
lemma go_spec {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (hne : A.Nonempty) (m : ℕ) :
    m ≤ (go A hA m).1 ∧ ∀ y, m ≤ y → y < (go A hA m).1 → y ∉ A →
      ¬ IsSidon ((A ∪ {y} : Finset ℕ) : Set ℕ) := by
  refine ⟨(go A hA m).2.1, fun y hmy hy hyA hS => ?_⟩
  unfold go at hy
  rw [dif_pos hne] at hy
  exact Nat.find_min _ hy ⟨hmy, hyA, hS⟩

/-- The greedy invariant: every `y < max` missing from the set is forbidden by the smaller
elements. -/
def Inv (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ hne : A.Nonempty, k + 1 ≤ A.max' hne ∧
    ∀ y, 1 ≤ y → y < A.max' hne → y ∉ A → ¬ IsSidon (((A.filter (· < y)) ∪ {y} : Finset ℕ) : Set ℕ)

open Finset.greedySidon in
lemma inv_aux (k : ℕ) : Inv (aux k).1.1 k := by
  induction k with
  | zero =>
    refine ⟨by simp [aux], by simp [aux], fun y hy1 hy hyA => ?_⟩
    simp [aux] at hy
    omega
  | succ k ih =>
    obtain ⟨hne, hmax, hmiss⟩ := ih
    set A := (aux k).1.1 with hA
    have hAS : IsSidon (A : Set ℕ) := (aux k).1.2
    have hneA : A.Nonempty := hne
    have hmaxA : k + 1 ≤ A.max' hneA := hmax
    have hmissA : ∀ y, 1 ≤ y → y < A.max' hneA → y ∉ A →
        ¬ IsSidon (((A.filter (· < y)) ∪ {y} : Finset ℕ) : Set ℕ) := hmiss
    clear hmax hmiss
    have hs : (if h : (aux k).1.1.Nonempty then (aux k).1.1.max' h + 1 else (aux k).2) =
        A.max' hneA + 1 := by
      rw [dif_pos hneA]
    obtain ⟨hge, hmin⟩ := go_spec hAS hneA (A.max' hneA + 1)
    set s := (go A hAS (A.max' hneA + 1)).1 with hsdef
    have hset : (aux (k + 1)).1.1 = A ∪ {s} := by rw [aux_succ, hs]
    rw [hset]
    have hne' : (A ∪ {s}).Nonempty := ⟨s, by simp⟩
    have hmax' : (A ∪ {s}).max' hne' = s := by
      apply le_antisymm
      · apply max'_le; intro z hz
        simp only [mem_union, mem_singleton] at hz
        rcases hz with hz | rfl
        · have := le_max' A z hz; omega
        · exact le_rfl
      · exact le_max' _ _ (by simp)
    refine ⟨hne', ?_, fun y hy1 hy hyA => ?_⟩
    · rw [hmax']; omega
    · rw [hmax'] at hy
      simp only [mem_union, mem_singleton, not_or] at hyA
      have hfilt : (A ∪ {s}).filter (· < y) = A.filter (· < y) := by
        ext z; simp only [mem_filter, mem_union, mem_singleton]
        constructor
        · rintro ⟨hz | rfl, hzy⟩
          · exact ⟨hz, hzy⟩
          · omega
        · rintro ⟨hz, hzy⟩; exact ⟨Or.inl hz, hzy⟩
      rw [hfilt]
      rcases lt_or_ge y (A.max' hneA) with hlt | hge'
      · exact hmissA y hy1 hlt hyA.1
      · have hy' : A.max' hneA < y := by
          rcases hge'.lt_or_eq with h | h
          · exact h
          · exact absurd (h ▸ max'_mem A hneA) hyA.1
        have hall : A.filter (· < y) = A := by
          ext z; simp only [mem_filter, and_iff_left_iff_imp]
          intro hz; have := le_max' A z hz; omega
        rw [hall]
        exact hmin y (by omega) hy hyA.1


open Finset.greedySidon in
lemma covers (N : ℕ) : Icc 1 N ⊆ greedySidonBelow N ∪ forb (greedySidonBelow N) := by
  intro y hy
  rw [mem_Icc] at hy
  by_cases hyG : y ∈ greedySidonBelow N
  · exact mem_union_left _ hyG
  apply mem_union_right
  obtain ⟨hne, hmax, hmiss⟩ := inv_aux N
  have hyA : y ∉ (aux N).1.1 := fun h => hyG (mem_filter.2 ⟨h, hy.2⟩)
  have hlt : y < (aux N).1.1.max' hne := by omega
  have hns := hmiss y hy.1 hlt hyA
  have hsub : (aux N).1.1.filter (· < y) ⊆ greedySidonBelow N := by
    intro z hz; simp only [mem_filter] at hz
    exact mem_filter.2 ⟨hz.1, by omega⟩
  have hSid : IsSidon (((aux N).1.1.filter (· < y) : Finset ℕ) : Set ℕ) := by
    intro i₁ h₁ j₁ h₂ i₂ h₃ j₂ h₄ h
    simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂ h₃ h₄
    exact (aux N).1.2 i₁ h₁.1 j₁ h₂.1 i₂ h₃.1 j₂ h₄.1 h
  have hyS : y ∉ (aux N).1.1.filter (· < y) := by simp
  exact forb_mono hsub (mem_forb hSid hyS hns)

lemma card_bound (N : ℕ) : N ≤ 3 * (greedySidonBelow N).card ^ 3 := by
  have h := card_le_card (covers N)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h
  have h2 := h.trans ((card_union_le _ _).trans (Nat.add_le_add_left (card_forb_le _) _))
  set g := (greedySidonBelow N).card
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0] at h2; simp at h2; omega
  · have : g ≤ g ^ 3 := by
      calc g = g ^ 1 := (pow_one g).symm
        _ ≤ g ^ 3 := Nat.pow_le_pow_right hpos (by norm_num)
    have : g ^ 2 ≤ g ^ 3 := Nat.pow_le_pow_right hpos (by norm_num)
    omega

end GreedySidon

namespace Erdos156

theorem erdos_156.variants.greedy_lower_bound :
    (fun N ↦ ((Finset.greedySidonBelow N).card : ℝ)) ≫ (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun N => ?_)
  set g : ℝ := ((Finset.greedySidonBelow N).card : ℝ) with hg
  have hg0 : 0 ≤ g := by positivity
  have hN : (N : ℝ) ≤ (2 * g) ^ 3 := by
    have h := GreedySidon.card_bound N
    have hR : (N : ℝ) ≤ 3 * g ^ 3 := by rw [hg]; exact_mod_cast h
    nlinarith [pow_nonneg hg0 3]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hg0]
  calc (N : ℝ) ^ (1 / 3 : ℝ) ≤ ((2 * g) ^ 3) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by norm_num)
    _ = 2 * g := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

end Erdos156
