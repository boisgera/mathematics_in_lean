import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Defs


open Set

universe u

example {α : Type u} {r s t : Set α} : r ⊆ s -> r ∩ t ⊆ s ∩ t :=
  fun hrs =>
    fun _x =>
      fun xrt =>
        match xrt with
          | And.intro xr xt =>
              And.intro (hrs xr) xt

example {α : Type u} {r s t : Set α} : r ⊆ s -> r ∩ t ⊆ s ∩ t :=
  fun hrs _x xrt =>
    let ⟨xr, xt⟩ := xrt
    let xs : _x ∈ s := hrs xr
    And.intro xs xt


example {α : Type u} {r s t : Set α} : r ⊆ s -> r ∩ t ⊆ s ∩ t := by
  intro hrs _x xrt
  simp at xrt
  cases xrt with | intro xr xt =>
  constructor
  . apply (Set.mem_of_subset_of_mem hrs)
    assumption
  . assumption

variable {s t u : Set α}

example (hst : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]
  repeat rw [inter_def]
  rw [subset_def] at hst
  simp only [mem_setOf]
  intro _ ⟨xs, xu⟩
  exact ⟨hst _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  intro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _ ⟨xs, xu⟩ => ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u :=
  fun _ ⟨hs, htu⟩ =>
    match htu with
      | Or.inl ht => Or.inl ⟨hs, ht⟩
      | Or.inr hu => Or.inr ⟨hs, hu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro _
  intro hstu
  simp [union_def] at hstu
  simp [union_def]
  cases hstu with | intro hs htu =>
  cases htu
  . apply Or.inl -- or "left"
    apply And.intro
    repeat assumption
  . apply Or.inr -- or "right"
    apply And.intro
    repeat assumption

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro _ ⟨⟨hs, hnt⟩, hnu⟩
  apply And.intro
  . assumption
  . rintro (ht | hu)
    . absurd ht
      assumption
    . absurd hu
      assumption

theorem difference_union {x: α} : x ∉ t ∪ u -> x ∉ t ∧ x ∉ u := by
  intro hntu
  constructor
  . intro ht
    exact hntu (Or.inl ht)
  . intro hu
    exact hntu (Or.inr hu)



example : s \ (t ∪ u) ⊆ (s \ t) \ u :=
  fun _ ⟨hs, hntu⟩ =>
    let ⟨hnt, hnu⟩ := difference_union hntu
    ⟨⟨hs, hnt⟩, hnu⟩

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro _ ⟨hs, hntu⟩
  let ⟨hnt, hnu⟩ := difference_union hntu
  simp ; repeat constructor ; repeat assumption

example : s ∩ (s ∪ t) = s := by
  ext _
  constructor
  . intro hs
    exact hs.1
  . intro hs
    constructor
    assumption
    exact Or.inl hs

example : s ∪ s ∩ t = s := by
  ext _
  constructor
  . intro hsst
    cases hsst with
      | inl hs => assumption
      | inr hst => exact hst.1
  . intro hs
    apply Or.inl
    assumption

theorem T₁ : s \ t ∪ t = s ∪ t := by
  ext _
  constructor
  . intro
    | Or.inl hst => exact Or.inl hst.1
    | Or.inr ht => exact Or.inr ht
  . intro hst
    simp -- this hides an excluded middle imho
    assumption

theorem T₂ : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . intro
    | Or.inl hst => exact Or.inl hst.1
    | Or.inr ht => exact Or.inr ht
  . intro hst
    exact
      match em (x ∈ t) with
      | Or.inl xt => Or.inr xt
      | Or.inr nxt =>
          match hst with
          | Or.inl ks => Or.inl ⟨ks, nxt⟩
          | Or.inr kt => absurd kt nxt

-- example : s \ t ∪ t = s ∪ t := by
--   ext _
--   constructor
--   . intro
--     | Or.inl hst => exact Or.inl hst.1
--     | Or.inr ht => exact Or.inr ht
--   . intro hst
--     admit

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  . intro hstts
    simp at hstts
    constructor
    . simp
      cases hstts with
      | inl ha => exact Or.inl ha.1
      | inr hb => exact Or.inr hb.1
    . simp
      intro hs
      cases hstts with
        | inl h => exact h.2
        | inr h => exact (absurd hs h.2)
  . let cxs := em (x ∈ s)
    intro hstst
    simp at hstst
    let ⟨hst₁, hst₂⟩ := hstst
    cases cxs with
    | inl h₁ =>
        exact Or.inl ⟨h₁, hst₂ h₁⟩
    | inr h₂ =>
        have ht : x ∈ t := by
          cases hst₁ with
          | inl hs => exact (absurd hs h₂)
          | inr ht => exact ht
        exact Or.inr ⟨ht, h₂⟩

--------------------------------------------------------------------------------

#print Even

example : Even 2 :=
  ⟨1, rfl⟩

def evens : Set ℕ := {n : ℕ | Even n}
def odds : Set ℕ := {n : ℕ | ¬Even n}

example : evens ∪ odds = univ := by
  ext n
  constructor
  . intro _
    exact trivial
  . intro _
    simp at *
    let even := em (Even n)
    assumption

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

#print Nat.Prime
#print Irreducible
#print Nat.add_mul
#print Nat.isUnit_iff

lemma one_neq_two : 1 ≠ 2 := by
  intro eq
  cases eq

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  intro hp2
  let ⟨hp, h2⟩ := hp2
  simp at hp
  let y := hp.isUnit_or_isUnit'
  rw [mem_setOf]
  intro hen
  let ⟨k, hk⟩ := hen
  have n2k : n = 2 * k := calc
    n = k + k := hk
    _ = 1 * k + 1 * k := by rw [Nat.one_mul]
    _ = (1 + 1) * k := by rw [<-Nat.add_mul]
    _ = 2 * k := by rfl
  let facto := y 2 k n2k
  cases facto with
    | inl nu2 =>
        let ui1 : (IsUnit 2) <-> 2 = 1 := Nat.isUnit_iff
        let zz := (ui1.mp nu2).symm
        exact one_neq_two zz
    | inr uk =>
        have k_eq_1 : k = 1 :=
          Nat.isUnit_iff.mp uk
        have n_eq_2 : n = 2 := by
          simp[k_eq_1] at n2k
          assumption
        simp at h2
        rw [n_eq_2] at h2
        absurd h2
        simp

--------------------------------------------------------------------------------

variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  admit

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  admit
