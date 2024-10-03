/-
 TODO:

- [x] define struct (not class) with Kuratowski axioms for topology
  (KuratowskiSpace ?) with "closeness"

- [x] shortcut for long name : KS

- [ ] function Topology => KS (caveat. Use of classical is required?)

- [ ] Iterate to improve (explicit/readable) the T2K implementation
      (a lot of black-box / low-level / redundancy / hammering so far)

- [x] "(type)classify" this concept? (works smoothly! After that,
      the will infer what "x ν A" means when X has a topological
      structure)

- [x] notation ν for being in closure

- [x] tune the appropriate tightness for notation (look at ∈ in source?)

- [ ] def for continuity at x

- [ ] show that KS -> TS and round-trip?

- [ ] show equivalence between classical def and k def of cont

- [X] Explain "bug": I never use explicitlu the property that an
      union of open set is open! UPDATE: not a bug, a feature!

- [ ] Prove that ¬(x ν A) <-> x ∈ ⋃₀ {U : Set X | IsOpen U ∧ U ⊆ Aᶜ}

- [ ] class for topology base (and how it yields KS and TS)

- [ ] define topology base space (as TBS) (a class), relate to KS

-/

/-
Note: I have defined the the Kuratowski nearness operator using:

   x ν A <-> ∀ U : Set X, IsOpen U -> x ∈ U -> (U ∩ A) ≠ ∅

I could have used instead the characterization that the closure of A is the
smallest closed set that contains A. But not that this 2nd charac only makes
sense if an arbitrary intersection of a family of closed sets is closed.

OTOH the first charac does not force me to use the topology axiom that a union
of open set is an open set. It yields the second charac if we can use this
axiom. So what's interesting with the first charac is that we could use it
to get a KS even if this property does not hold. The round trip would not
"work" but instead associate to the initial collection "some" associated
topology.

Q: Can we be working with a topological BASIS here? (Need to check the defs)

-/

import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Defs.Basic

import Init.Classical
open Classical

open TopologicalSpace

def exists_sUnion_by {X : Type u} (S : Set (Set X)) (A : Set X) : Prop :=
  ∃ T, T ⊆ S ∧ ⋃₀ T = A

lemma subset_of_mem_and_sUnion {X : Type u} {A B: Set X} {C : Set (Set X)}:
  A ∈ C ∧ ⋃₀ C = B -> A ⊆ B := by
  rintro ⟨A_in_C, sUnion_C_eq_B⟩
  intro x x_in_A
  have : x ∈ ⋃₀ C := Set.mem_sUnion_of_mem x_in_A A_in_C
  rw [sUnion_C_eq_B] at this
  exact this

lemma sUnion_from_sUnion {X : Type u} (F G : Set (Set X)) :
 (∀ f, f ∈ F -> exists_sUnion_by G f) -> exists_sUnion_by G (⋃₀ F)
 := by
  intro sUnion_by_G
  let Gf (f : Set X) (f_in_F : f ∈ F) := choose (sUnion_by_G f f_in_F)
  let GUf := ⋃₀ { Gf f f_in_F| (f : Set X) (f_in_F : f ∈ F)}

  have {f : Set X} {f_in_F : f ∈ F} {x : X} :
    x ∈ f <-> ∃ G ∈ (Gf f f_in_F), x ∈ G := by
    have p : ⋃₀ choose (sUnion_by_G f f_in_F) = f :=
      (choose_spec (sUnion_by_G f f_in_F)).right
    apply Iff.intro
    . intro x_in_f
      have : (x ∈ f) = (x ∈ ⋃₀ choose (sUnion_by_G f f_in_F)) := by
        exact congrArg (x ∈ ·) p.symm
      rw [this] at x_in_f
      rw [Set.mem_sUnion] at x_in_f
      assumption
    . intro h
      let ⟨g, g_in_Gf, x_in_g⟩ := h
      have : g ⊆ f := by
        -- g is an element of a cover of f by definition (and choice)
        simp [Gf] at p
        simp [Gf] at g_in_Gf
        exact (subset_of_mem_and_sUnion (And.intro g_in_Gf p))
      exact this x_in_g

  -- TODO: still a lot of work...

  admit

structure TopologicalBasisSpace (X : Type u) where
  basic_open_sets : Set (Set X)
  isOpen_univ : exists_sUnion_by basic_open_sets Set.univ
  isOpen_inter {A B : Set X} :
    A ∈ basic_open_sets ∧ B ∈ basic_open_sets ->
    exists_sUnion_by basicOpenSets (A ∩ B)

def TBS2TB {X : Type u} (base: TopologicalBasisSpace X) : TopologicalSpace X :=
  {
    IsOpen :=
      fun U => exists_sUnion_by base.basic_open_sets U,

    isOpen_univ :=
      base.isOpen_univ,

    isOpen_inter := by
      dsimp only
      intro S T cover_S cover_T
      let ⟨F, F_basic_open, F_cover_union_s⟩ := cover_S
      let ⟨G, G_basic_open, G_covers_T⟩ := cover_T
      -- H is our cover of S ∩ T by basic open sets. Nope! We need to
      -- consider the elements of the cover of A ∩ B. This is harder :(
      -- and we need choice?
      -- have a look at <https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html>
      let H := { C : Set X | ∃ A ∈ F, ∃ B ∈ G, C = A ∩ B }
      -- TODO: 1. sets in H are basic open sets
      have H_basic_open : H ⊆ base.basic_open_sets := by -- Arf fuck, this is wrong
        intro h h_in_H
        let ⟨A, A_in_F, B, B_in_G, h_eq_A_cap_B⟩ := h_in_H
        admit
      -- TODO: 2. H covers S ∩ T
      have H_is_cover : ⋃₀ H = S ∩ T := by admit
      exact ⟨H, H_basic_open, H_is_cover⟩

    isOpen_sUnion := by
      dsimp only

      intro s cover_map -- ∀ t ∈ s, exists_sUnion_by base.basic_open_sets t
      -- goal: ⊢ exists_sUnion_by base.basic_open_sets (⋃₀ s)

      let cover_union_s : Set (Set X) := ⋃₀ {
        choose (cover_map t t_in_s) | (t : Set X) (t_in_s : t ∈ s)
      }
      apply Exists.intro cover_union_s
      have h₁ : cover_union_s ⊆ base.basic_open_sets := by
        intro c c_in_cover -- c ∈ cover_union_s
        -- decompose/interpret the ⋃₀
        let ⟨subcover, p, c_in_subcover⟩ := Set.mem_sUnion.mp c_in_cover
        dsimp at p -- x ∈ {y | p y} pattern
        let ⟨t, t_in_s, choice⟩ := p
        let ⟨h, _⟩ := choose_spec (cover_map t t_in_s)
        rw[choice] at h
        exact h c_in_subcover
      have h₂ : ⋃₀ cover_union_s = ⋃₀ s := by
          admit

      exact ⟨h₁, h₂⟩

  }

class KuratowskiSpace (X : Type u) where
  close : X -> Set X -> Prop
  not_close_empty (x : X) : ¬close x ∅
  mem_close {x : X} {A : Set X} : x ∈ A -> close x A
  close_inter {x : X} {A B : Set X} : (close x A) ∨ (close x B) <-> close x (A ∪ B)
  close_close {x : X} {A : Set X} : close x {x' : X | close x' A} -> close x A

notation x " ν " A => KuratowskiSpace.close x A

open Set

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

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------

instance {X : Type*} [TopologicalSpace X] : KuratowskiSpace X :=
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

lemma not_close_iff_in_union {X : Type*} [TopologicalSpace X] {A : Set X} {x : X}:
  ¬(x ν A) <-> x ∈ ⋃₀ {U : Set X | IsOpen U ∧ U ⊆ Aᶜ} := by
  constructor
  . intro not_x_in_A
    have h₁ : ¬ ∀ U : Set X, IsOpen U -> x ∈ U -> (U ∩ A) ≠ ∅ := by
      exact not_x_in_A
    have h₂ :  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ (U ∩ A) = ∅ := by
      simp at h₁
      exact h₁
    simp
    have h₃ : ∃ U, (IsOpen U ∧ U ⊆ Aᶜ) ∧ x ∈ U := by
      let ⟨U, hU⟩ := h₂
      have : U ⊆ Aᶜ := by
        have h: U ∩ A = ∅ := hU.2.2
        intro x xinU xinA
        have xinUA : x ∈ U ∩ A := by
          simp
          exact (And.intro xinU xinA)
        rw[h] at xinUA
        simp at xinUA
      exact Exists.intro U ⟨⟨hU.1, this⟩, hU.2.1⟩
    assumption
  . intro xinUU
    simp at xinUU
    let ⟨U, hUU⟩ := xinUU
    intro xnuA -- ∀ U : Set X, IsOpen U -> x ∈ U -> (U ∩ A) ≠ ∅
    have hUA := xnuA U hUU.1.1 hUU.2
    have hUAc := hUU.1.2
    let ⟨x, ⟨xU, xA⟩⟩ := nonempty_of_ne_empty hUA
    have z := hUAc xU
    exact absurd xA z



lemma close_inter_closed_sets {X : Type*} [TopologicalSpace X] {A : Set X} {x : X}:
  (x ν A) <-> x ∈ ⋂₀ {C : Set X | IsClosed C ∧ A ⊆ C} := by
  apply not_iff_not.mp -- goal: (¬x ν A) ↔ x ∉ ⋂₀ {C | IsClosed C ∧ A ⊆ C}
  have : (⋂₀ {C | IsClosed C ∧ A ⊆ C})ᶜ = ⋃₀ {O | IsOpen O ∧ O ∩ A ≠ ∅} := by
    ext x
    constructor
    . admit
    . admit
