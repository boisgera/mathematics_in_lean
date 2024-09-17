import Mathlib.Data.Real.Basic -- provides ℕ (to begin with)

#eval 1+1

open Nat

#eval (1: ℕ)


--------------------------------------------------------------------------------

def A : Set ℕ := {0, 1} -- shit, eval doesn't work, I have 0 intell
                        -- on the underlying structure of A and
                        -- therefore I don't know how to prove anything! :(
-- #eval A -- Nope
#print A -- useless, the def is given "as is"
 A

-- Nah, OK, thanks to ChatGPT, I have learned that this is a syntactic sugar
-- for the intensional definition of the set, that is:

def A' := {n : ℕ | n = 0 ∨ n = 1}

-- I believe it, since their equality is established by refl.

example : A = A' :=
  rfl

-- OTOH, #reduce gives great intel here too:
#reduce A -- fun b => b = 0 ∨ b ∈ {1}

-- So to be precise, {0, 1} is a syntactic sugar for {n | n = 0 ∨ n ∈ {1}}
-- And recursively:

def S : Set ℕ := {1}
#reduce S -- fun b => b = 1 . Singletons have a very simple structure!

example : 0 ∈ A := -- We prove need to prove A 0, that is 0 = 0 ∨ 0 ∈ {1}
  Or.inl rfl

example : 1 ∈ A := -- we need to prove 1 = 0 ∨ 1 ∈ {1}
  Or.inr rfl -- proving 1 ∈ {1} amounts to proving 1=1; rfl will do.


def A'' : Set ℕ := insert 1 (insert 0 ∅)
#reduce A'' -- fun b => b = 1 ∨ b ∈ insert 0 ∅
def B'' : Set ℕ := insert 0 ∅
#reduce B''  -- fun b => b = 0 ∨ b ∈ ∅
#reduce (∅ : Set ℕ) -- fun x => False
#reduce (Set.univ : Set ℕ) -- fun _a => True
#reduce ({0, 0} : Set ℕ) -- fun b => b = 0 ∨ b ∈ {0}

#reduce ({} : Set ℕ) -- fun x => False

example : ({} : Set ℕ) = ∅ :=
  rfl

example : ∀ (n : ℕ), n ∉ (∅ : Set ℕ) :=
  fun n =>
    fun (hn : n ∈ ∅) =>
      hn

example : ∀ (n : ℕ), n ∉ (∅ : Set ℕ) := by
  intro n
  intro hn
  exact hn

example : ({0} : Set ℕ) = ({0, 0} : Set ℕ) :=
  Set.ext
    fun (n : ℕ) =>
      Iff.intro
        (fun (hn : n = 0) =>
          (Or.inl hn : n = 0 ∨ n ∈ {0})
        )
        (fun (hn : n ∈ {0, 0}) =>
           match hn with
            | Or.inl hn₁ => hn₁
            | Or.inr hn₂ => hn₂
        )

example : ({0} : Set ℕ) = ({0, 0} : Set ℕ) := by
  apply Set.ext
  intro x
  apply Iff.intro
  . intro x_in_z
    simp at x_in_z
    simp
    exact x_in_z
  . intro x_in_zz
    simp at x_in_zz
    simp
    exact x_in_zz

example : ({0, 1} : Set ℕ) = ({1, 0} : Set ℕ) :=
  Set.ext
    fun (n : ℕ) =>
      Iff.intro
        (fun (h : n ∈ {0, 1}) => (
          match h with
            | Or.inl (hl : n = 0) => (Or.inr hl : n ∈ {1, 0})
            | Or.inr (hr : n = 1) => (Or.inl hr : n ∈ {1, 0})
        ))
        (fun (h : n ∈ {1, 0}) => (
          match h with
            | Or.inl hl => Or.inr hl
            | Or.inr hr => Or.inl hr
        ))

theorem sub_sub_eq {A B : Set α} : A ⊆ B ∧ B ⊆ A -> A = B :=
  fun ⟨hab, hba⟩ =>
    Set.ext
      fun (x : α) =>
        Iff.intro
          (hab .) -- expose the sets as functions (unwrap abstraction)
          (hba (a := x)) -- or bind explicitly

#print Set.Subset


theorem sub_sub_eq' {A B : Set α} : A ⊆ B ∧ B ⊆ A -> A = B := by
  intro ⟨ha, hb⟩
  apply Set.ext
  intro x
  apply Iff.intro
  . intro h
    exact (ha h)
  . intro h
    exact (hb h)



example (m n : ℕ): ({m, n} : Set ℕ) ⊆ {n, m} :=
  fun (p : ℕ) =>
    sorry





example : A = A'' :=
  Set.ext -- we will prove that ∀ n : ℕ, n ∈ A <-> n in A'' and use ext
    fun n =>
      Iff.intro
        (sorry) -- n ∈ A -> n ∈ A''
        (sorry) -- n ∈ A -> n ∈ A''



def B := {n : ℕ | 0 ≤ n ∧ n ≤ 9}

def C : Set ℕ := {n | n % 2 = 0}

def D : Set ℕ := {1, 2, 3, 4, 5, 6}

def E : Set ℕ := Set.univ

def Z : Set ℕ := ∅

--------------------------------------------------------------------------------

example : (0 ∈ A) :=
  sorry

example : (0 ∈ A') :=
  sorry



example : (5 ∈ B) :=
  sorry

--------------------------------------------------------------------------------

namespace N₄

variable (A B C : Set α)

#check (A ⊆ B)
#print Set.Subset -- protected def Set.Subset.{u} : {α : Type u}
                  -- → Set α → Set α → Prop :=
                  -- fun {α} s₁ s₂ => ∀ ⦃a : α⦄, a ∈ s₁ → a ∈ s₂
-- a (the element) is strongly implicit
--  fun {α} s₁ s₂ => ∀ ⦃a : α⦄, a ∈ s₁ → a ∈ s₂

example : A ⊆ B -> A ∩ C ⊆ B ∩ C :=
  fun hAB =>
    fun x => -- this necessary x that is never used is weird!
             -- (actually, it is, but implicitly)
      fun hAC =>
        let ⟨hA, hC⟩ := hAC
        let hB := (hAB hA)
        And.intro hB hC

example : A ⊆ B -> A ∩ C ⊆ B ∩ C :=
  fun hAB =>
    fun _ =>
      fun hAC =>
        let ⟨hA, hC⟩ := hAC
        let hB := (hAB hA)
        And.intro hB hC

example : A ⊆ B -> A ∩ C ⊆ B ∩ C := by
  intro hAB
  intro _
  intro hAC
  let ⟨hA, hC⟩ := hAC
  apply And.intro
  . exact (hAB hA)
  . exact hC

end N₄

--------------------------------------------------------------------

namespace Ops

def S₁ : Set ℕ := {0} ∪ {1}

def S₂ : Set ℕ := {0, 1, 2} ∩ {2, 3, 4}

def S₃ : Set ℕ := {0, 1}ᶜ

#reduce 0 ∈ ({0, 1} : Set ℕ)

example : 0 ∉ ({0, 1}ᶜ : Set ℕ) := by
  intro h -- h : 0 ∈ {0, 1}ᶜ , i.e. h : 0 ∈ {0, 1} -> False
  exact h (Or.inl rfl)



theorem zero_neq_one : 0 ≠ 1 := by
  intro h
  cases h

example : {0, 1} \ {1} = ({0} : Set ℕ) := by
  ext x -- equivalent to Set.ext follow by intro x
  apply Iff.intro
  . intro
    | ⟨Or.inl h₁, _⟩ => exact h₁
    | ⟨Or.inr h₁, h₂⟩ => exact absurd h₁ h₂
  . intro h
    apply And.intro
    . exact Or.inl h
    . intro k
      let j := Eq.trans h.symm k
      apply zero_neq_one j

example : {0, 1} \ {1} = ({0} : Set ℕ) := by
  ext x
  simp [Set.mem_diff, Set.mem_singleton_iff, Set.mem_insert_iff, zero_ne_one]

open Set

example : {0, 1} \ {1} = ({0} : Set ℕ) := by
  ext x
  simp only [mem_diff, mem_singleton_iff, mem_insert_iff]
  simp -- (x = 0 ∨ x = 1) ∧ ¬x = 1 ↔ x = 0

end Ops
