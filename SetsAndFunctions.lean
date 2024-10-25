import Mathlib

open Function

universe u vw
variable {α : Sort u} {β : Sort v} {γ : Sort w}

#check id

#check Injective

example : Injective (id (α := α)) := by
  rw [Injective]
  intro a₁ a₂
  repeat rw [id]
  intro
  assumption

example {f : α → β} {g : β → γ} :
  (Injective f) ∧ (Injective g) -> (Injective (g ∘ f)) := by
  intro ⟨inj_f, inj_g⟩
  rw [Injective]
  intro a₁ a₂
  rw [comp]
  intro g_f_a1_eq_g_f_a2
  rw [Injective] at *
  have f_a1_eq_f_a2 : f a₁ = f a₂ := by
      exact inj_g g_f_a1_eq_g_f_a2
  exact inj_f f_a1_eq_f_a2

example : Surjective (id (α := α)) := by
  rw [Surjective]
  intro b
  use b
  rw [id]

example {f : α → β} {g : β → γ} :
  (Surjective f) ∧ (Surjective g) -> (Surjective (g ∘ f)) := by
  intro ⟨sur_f, sur_g⟩
  rw [Surjective] at *
  intro b
  have ⟨c, g_c_eq_b⟩ : ∃ c, g c = b := sur_g b
  have ⟨d, f_d_eq_c⟩ : ∃ d, f d = c := sur_f c
  use d
  rw [comp, f_d_eq_c, g_c_eq_b]

open Nat

example : Injective succ := by
  rw [Injective]
  intro a₁ a₂
  intro a1_succ_eq_a2_succ
  cases a1_succ_eq_a2_succ
  rfl

#print exists_add_one_eq -- OMG!

example : ¬Surjective succ := by
  intro surj_succ
  have h : ∃ n, succ n = 0 := surj_succ 0
  simp only [succ_eq_add_one, exists_add_one_eq] at h
  contradiction


variables (X Y : Type u)

example {f : X -> Y} {A : Set X} : A ⊆ f ⁻¹' (f '' A) := by
  intro a a_in_A
  rw [Set.preimage]
  simp only [Set.mem_image, Set.mem_setOf_eq]
  use a
