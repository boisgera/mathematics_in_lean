/-
 TODO:

- [x] define struct (not class) with Kuratowski axioms for topology
  (KuratowskiSpace ?) with "closeness"

- [x] shortcut for long name : KS

- [ ] function Topology => KS (caveat. Use of classical is required?)

- [ ] Iterate to improve (explicit/readable) the T2K implementation
      (a lot of black-box / low-level / redundancy / hammering so far)

- [ ] "(type)classify" this concept?

- [x] notation ν for being in closure

- [x] tune the appropriate tightness for notation (look at ∈ in source?)

- [ ] def for continuity at x

- [ ] show that KS -> TS and round-trip?

- [ ] show equivalence between classical def and k def of cont

- [ ] Solve bug: I never use explicitlu the property that an union of open set is open!

 -/

import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic

open TopologicalSpace

structure KuratowskiSpace (X : Type u) where
  close : X -> Set X -> Prop
  not_close_empty (x : X) : ¬close x ∅
  mem_close {x : X} {A : Set X} : x ∈ A -> close x A
  close_inter {x : X} {A B : Set X} : (close x A) ∨ (close x B) <-> close x (A ∪ B)
  close_close {x : X} {A : Set X} : close x {x' : X | close x' A} -> close x A

notation x " ν " A => KuratowskiSpace.close x A

open Set
-- open Classical

-- struggling here to relate something being non-empty and putting my hand on
-- one of the element.
-- Some of the documentation suggests that it it basically the same
--
-- > /-- The property `s.Nonempty` expresses the fact that the set `s` is not empty.
-- > It should be used in theorem assumptions instead of `∃ x, x ∈ s`
-- > or `s ≠ ∅` as it gives access to a nice API thanks
-- > to the dot notation. -/
-- > protected def Nonempty (s : Set α) : Prop :=
-- >  ∃ x, x ∈ s
--
-- But I fail to see why (unless classical is allowed???).
--
-- In any case, in our construction of T2K, it may be handy
-- to use the Nonempty version (it is "stronger"). Or, if we
-- dont want to mess everyting right now, we provide an external lemma.
-- (roughly speaking the lemma below)

theorem nonempty_of_ne_empty {A : Set α} : A ≠ ∅ -> ∃ x, x ∈ A := by
  intro A_not_empty -- A ≠ ∅
  have not_forall_x_not_x_in_A: ¬(∀ x, ¬(x ∈ A)) := by
    intro not_all_x_not_in_A
    have A_eq_empty : A = ∅ := by
      ext x
      apply Iff.intro
      . intro xinA
        exact absurd xinA (not_all_x_not_in_A x)
      . simp
    exact absurd A_eq_empty A_not_empty
  simp at not_forall_x_not_x_in_A -- ! before:
                                  --   ¬∀ (x : α), x ∉ A
                                  -- after:
                                  --   ∃ x, x ∈ A
                                  -- classically true? Nah that can't be!
                                  -- investigate the term of this subproof
  assumption

-- TODO: prove "manually"
lemma minimal {A : Set α} : ¬(∀ (x : α), x ∉ A) -> ∃ x, x ∈ A := by
  intro h
  simp at h
  assumption

#print minimal -- Yes, it refers to some Init.Classical._auxLemma.3 stuff.

def T2K (X : Type u) [TopologicalSpace X] : KuratowskiSpace X :=
  {
    close := fun x A => ∀ U : Set X, IsOpen U -> x ∈ U -> (U ∩ A) ≠ ∅,

    not_close_empty := fun x h => by
      simp at h
      let h' := h Set.univ
      simp at h'
      ,

    mem_close := by
      simp
      intro x A hxA U _ hxU
      intro hUA
      let h := congrArg (x ∈ ·) hUA
      simp at h
      exact absurd hxA (h hxU)
      ,

    close_inter := by
      intro x A B
      constructor
      . simp
        intro hUAUB
        intro U hUisOpen hxU hUAB
        cases hUAUB with
          | inl h =>
              have hr : ¬U ∩ A = ∅ := h U hUisOpen hxU
              have hUA : U ∩ A = ∅ := by
                ext y
                constructor
                . simp
                  intro hyU
                  intro hyA
                  have hyAB : y ∈ A ∪ B := Or.inl hyA
                  have hyUAB : y ∈ U ∩ (A ∪ B) := ⟨hyU, hyAB⟩
                  have beebop {z : X} : z ∈ U ∩ (A ∪ B) -> z ∈ (∅ : Set X) := by
                    rw [hUAB]
                    exact id
                  have yinvoid := beebop hyUAB
                  -- simp only [Set.mem_setOf] at yinvoid
                  assumption
                .simp
              exact (absurd hUA hr)
          | inr h' =>
              have hr : ¬U ∩ B = ∅ := h' U hUisOpen hxU
              have hUB : U ∩ B = ∅ := by
                ext y
                constructor
                . simp
                  intro hyU
                  intro hyB
                  have hyAB : y ∈ A ∪ B := Or.inr hyB
                  have hyUAB : y ∈ U ∩ (A ∪ B) := ⟨hyU, hyAB⟩
                  have beebop {z : X} : z ∈ U ∩ (A ∪ B) -> z ∈ (∅ : Set X) := by
                    rw [hUAB]
                    exact id
                  have yinvoid := beebop hyUAB
                  assumption
                .simp
              exact (absurd hUB hr)
      . simp
        contrapose
        intro h
        intro hc
        let ⟨hl, hr⟩ := not_or.mp h
        simp at hl hr
        let ⟨U, hU⟩ := hl
        let ⟨V, hV⟩ := hr
        let W := U ∩ V
        have W_U_V : W = U ∩ V := by
          simp
        have isOpenW := IsOpen.inter hU.1 hV.1 -- The key argument
        have xinW := And.intro hU.2.1 hV.2.1
        have W_cap_A_cup_B_empty : W ∩ (A ∪ B) = ∅ := by
          have U_cap_A_empty := hU.2.2
          have V_cap_B_empty := hV.2.2
          have U_cap_V_cap_A_empty : U ∩ V ∩ A = ∅ := by
            ext x
            constructor
            . intro hUVA
              simp at hUVA
              let ⟨⟨xU, _xV⟩, xA⟩ := hUVA
              have x_in_U_cap_A : x ∈ U ∩ A :=
                And.intro xU xA
              have zzz := congrArg (x ∈ ·) U_cap_A_empty
              dsimp at zzz
              rw[zzz] at x_in_U_cap_A
              assumption
            . simp
          have U_cap_V_cap_B_empty : U ∩ V ∩ B = ∅ := by
            ext x
            constructor
            . intro hUVB
              simp at hUVB
              let ⟨⟨_xU, xV⟩, xB⟩ := hUVB
              have x_in_V_cap_B : x ∈ V ∩ B :=
                And.intro xV xB
              have zzz := congrArg (x ∈ ·) V_cap_B_empty
              dsimp at zzz
              rw[zzz] at x_in_V_cap_B
              assumption
            . simp
          have W_cap_A_empty : W ∩ A = ∅ := by
            rw[<-W_U_V] at U_cap_V_cap_A_empty
            assumption
          have W_cap_B_empty : W ∩ B = ∅ := by
            rw[<-W_U_V] at U_cap_V_cap_A_empty
            assumption
          have W_cap_A_cup_W_cap_B_empty : (W ∩ A) ∪ (W ∩ B) = ∅ := by
            rw[W_cap_A_empty, W_cap_B_empty]
            simp
          rw[Set.inter_union_distrib_left]
          assumption
        have not_W_cap_A_cup_B_empty := hc W isOpenW xinW
        exact absurd W_cap_A_cup_B_empty not_W_cap_A_cup_B_empty
      ,

    close_close := by
      intro x A
      intro h_close_close
      simp at h_close_close
      intro U isOpenU xinU
      -- B := U ∩ {x' | ∀ (V : Set X), IsOpen V → x' ∈ V → ¬V ∩ A = ∅}
      have yB : (∃ (y : X), y ∈ U ∩ {x' | ∀ (V : Set X), IsOpen V → x' ∈ V → ¬V ∩ A = ∅}) := by
        apply nonempty_of_ne_empty
        exact h_close_close U isOpenU xinU
      let ⟨y, yinB⟩ := yB
      let ⟨h, h'⟩ := yinB
      simp at h'
      have := h' U isOpenU h
      assumption
      ,
  }
