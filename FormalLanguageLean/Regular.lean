import FormalLanguageLean.Equiv

import Mathlib.Data.Finset.NAry


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577


namespace Language


inductive IsRegLang {α : Type} : Language α → Prop
| char
  (a : α) :
  IsRegLang {[a]}

| epsilon :
  IsRegLang {[]}

| zero :
  IsRegLang ∅

| union
  (R1 R2 : Language α) :
  IsRegLang R1 →
  IsRegLang R2 →
  IsRegLang (R1 ∪ R2)

| concat
  (R1 R2 : Language α) :
  IsRegLang R1 →
  IsRegLang R2 →
  IsRegLang (concat R1 R2)

| kleene_closure
  (R : Language α) :
  IsRegLang R →
  IsRegLang (kleene_closure α R)


theorem derivative_of_reg_lang_wrt_char_is_reg_lang
  {α : Type}
  (R : Language α)
  (a : α)
  (h1 : IsRegLang R) :
  IsRegLang (derivative R [a]) :=
  by
    classical
    induction h1
    case char b =>
      by_cases c1 : a = b
      · rewrite [c1]
        rewrite [derivative_of_char_wrt_same_char]
        exact IsRegLang.epsilon
      · rewrite [derivative_of_char_wrt_diff_char a b c1]
        exact IsRegLang.zero
    case epsilon =>
      rewrite [derivative_of_eps_wrt_char]
      exact IsRegLang.zero
    case zero =>
      rewrite [derivative_of_empty_wrt_char]
      exact IsRegLang.zero
    case union R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      rewrite [derivative_of_union_wrt_char]
      apply IsRegLang.union
      · exact ih_3
      · exact ih_4
    case concat R1 R2 ih_1 ih_2 ih_3 ih_4 =>
      rewrite [derivative_of_concat_wrt_char]
      apply IsRegLang.union
      · apply IsRegLang.concat
        · exact ih_3
        · exact ih_2
      · apply IsRegLang.concat
        · unfold Language.nullify
          split
          case isTrue c1 =>
            exact IsRegLang.epsilon
          case isFalse c1 =>
            exact IsRegLang.zero
        · exact ih_4
    case kleene_closure R' ih_1 ih_2 =>
      rewrite [derivative_of_kleene_closure_wrt_char]
      apply IsRegLang.concat
      · exact ih_2
      · apply IsRegLang.kleene_closure
        exact ih_1


theorem derivative_of_reg_lang_wrt_str_is_reg_lang
  {α : Type}
  (R : Language α)
  (s : Str α)
  (h1 : IsRegLang R) :
  IsRegLang (derivative R s) :=
  by
    induction s generalizing R
    case nil =>
      unfold derivative
      simp only [List.nil_append, Set.setOf_mem_eq]
      exact h1
    case cons hd tl ih =>
      rewrite [derivative_wrt_cons]
      apply ih
      apply derivative_of_reg_lang_wrt_char_is_reg_lang
      exact h1


theorem all_derivative_of_reg_lang_wrt_str_mem_finset
  {α : Type}
  (L : Language α)
  (h1 : IsRegLang L) :
  ∃ (T : Finset (Language α)), ∀ (s : Str α), derivative L s ∈ T :=
  by
    classical
    induction h1
    case char c =>
      apply Exists.intro {{}, {[]}, {[c]}}
      intro s
      cases s
      case nil =>
        rewrite [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        cases tl
        case nil =>
          by_cases c1 : hd = c
          · rewrite [c1]
            rewrite [derivative_of_char_wrt_same_char c]
            apply Finset.mem_insert_of_mem
            apply Finset.mem_insert_self
          case neg =>
            rewrite [derivative_of_char_wrt_diff_char hd c c1]
            apply Finset.mem_insert_self
        case cons tl_hd tl_tl =>
          unfold derivative
          simp only [List.cons_append, Set.mem_singleton_iff, List.cons.injEq, reduceCtorEq, Finset.mem_insert, Finset.mem_singleton]
          left
          ext cs
          simp only [Set.mem_setOf_eq]
          constructor
          · intro a1
            obtain ⟨a1_left, a1_right⟩ := a1
            contradiction
          · intro a1
            simp only [Set.mem_empty_iff_false] at a1
    case epsilon =>
      apply Exists.intro {∅, {[]}}
      intro s
      cases s
      case nil =>
        rewrite [derivative_wrt_eps]
        apply Finset.mem_insert_of_mem
        simp only [Finset.mem_singleton]
      case cons hd tl =>
        rewrite [derivative_wrt_cons]
        simp only [derivative_of_eps_wrt_char]
        simp only [derivative_of_empty_wrt_str]
        apply Finset.mem_insert_self
    case zero =>
      apply Exists.intro {∅}
      intro s
      rewrite [derivative_of_empty_wrt_str]
      simp only [Finset.mem_singleton]
    case union L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2

      apply Exists.intro (T1.biUnion (fun a => T2.biUnion (fun b => {a ∪ b})))
      simp only [derivative_of_union_wrt_str]
      simp only [Finset.mem_biUnion, Finset.mem_singleton]
      intro s
      apply Exists.intro (derivative L1 s)
      constructor
      · exact a1 s
      · apply Exists.intro (derivative L2 s)
        constructor
        · exact a2 s
        · apply Eq.refl
    case concat L1 L2 L1_ih1 L2_ih1 L1_ih2 L2_ih2 =>
      obtain ⟨T1, a1⟩ := L1_ih2
      obtain ⟨T2, a2⟩ := L2_ih2

      simp only [derivative_of_concat_wrt_str]

      let A : Finset (Language α) := T1.biUnion (fun (M1 : Language α) => ({L2} : Finset (Language α)).biUnion (fun (M2 : Language α) => {concat M1 M2}))

      let B : Finset (Language α) := T1.biUnion (fun (M1 : Language α) => T2.biUnion (fun (M2 : Language α) => {concat M1.nullify M2}))

      have s1 : ∀ (s : Str α), {M : Language α | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ ¬ v = [] ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} ⊆ B :=
      by
        intro s
        unfold B
        simp only [Set.subset_def]
        simp only [Set.mem_setOf_eq, Finset.coe_biUnion, SetLike.mem_coe, Finset.coe_singleton, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, forall_exists_index]
        intro M u v a3
        obtain ⟨a3_left, ⟨a3_right_left, a2_right_right⟩⟩ := a3
        apply Exists.intro (derivative L1 u)
        constructor
        · exact a1 u
        · apply Exists.intro (derivative L2 v)
          constructor
          · exact a2 v
          · exact a2_right_right

      have s2 : ∀ (s : Str α), Finite {M : Language α | ∃ (u : Str α) (v : Str α), u ++ v = s ∧ ¬ v = [] ∧ M = concat (derivative L1 u).nullify (derivative L2 v)} :=
      by
        intro s
        apply Finite.Set.subset B
        apply s1

      let C : Finset (Set (Str α)) := B.powerset.image (fun (S : Finset (Language α)) => (S : Set (Language α)).sUnion)

      let T : Finset (Language α) := A.biUnion (fun (M1 : Language α) => C.biUnion (fun (M2 : Language α) => {M1 ∪ M2}))

      simp only [← gt_iff_lt, ← List.length_pos_iff] at s1

      unfold B at s1
      simp only [Finset.coe_biUnion, SetLike.mem_coe, Finset.coe_singleton] at s1

      simp only [← gt_iff_lt, ← List.length_pos_iff] at s2

      apply Exists.intro T
      intro s

      have s3 : ∃ (D : Finset (Language α)), ∀ (L : Language α), L ∈ D ↔ L ∈ {M | ∃ u v, u ++ v = s ∧ List.length v > 0 ∧ M = (L1.derivative u).nullify.concat (L2.derivative v)} :=
      by
        apply Set.Finite.exists_finset
        apply s2

      obtain ⟨D, s3⟩ := s3
      simp only [Set.mem_setOf_eq] at s3

      unfold T
      unfold A
      unfold C
      unfold B
      simp only [Finset.singleton_biUnion, Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image, Finset.mem_powerset, exists_exists_and_eq_and]

      apply Exists.intro ((derivative L1 s).concat L2)
      constructor
      · apply Exists.intro (derivative L1 s)
        constructor
        · apply a1
        · apply Eq.refl
      · apply Exists.intro D
        constructor
        · simp only [Finset.subset_iff]
          simp only [Finset.mem_biUnion, Finset.mem_singleton]
          intro M a3

          have s4 : ∃ u v, u ++ v = s ∧ List.length v > 0 ∧ M = (L1.derivative u).nullify.concat (L2.derivative v) :=
          by
            rewrite [← s3]
            exact a3

          obtain ⟨u, ⟨v, mp_1, mp_2, mp_3⟩ ⟩ := s4

          apply Exists.intro (L1.derivative u)
          constructor
          · apply a1
          · apply Exists.intro (L2.derivative v)
            constructor
            · apply a2
            · exact mp_3
        · congr 1
          ext cs
          simp only [Set.mem_sUnion, Set.mem_setOf_eq, SetLike.mem_coe]
          constructor
          · intro a3
            obtain ⟨t, ⟨a3_left, a3_right⟩⟩ := a3
            apply Exists.intro t
            constructor
            · rewrite [s3]
              exact a3_left
            · exact a3_right
          · intro a3
            obtain ⟨t, ⟨a3_left, a3_right⟩⟩ := a3
            apply Exists.intro t
            constructor
            · rewrite [← s3]
              exact a3_left
            · exact a3_right
    case kleene_closure L1 L1_ih1 L1_ih2 =>
      obtain ⟨T, a1⟩ := L1_ih2

      have s1 : ∀ (s : Str α), {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} ⊆ (T : Set (Language α)) :=
      by
        intro s
        simp only [Set.subset_def]
        simp only [Set.mem_setOf_eq, SetLike.mem_coe, forall_exists_index]
        intro t a2 a3
        obtain ⟨a3_left, a3_right⟩ := a3
        rewrite [← a3_right]
        apply a1

      have s2 : ∀ (s : Str α), Finite {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} :=
      by
        intro s
        apply Set.Finite.subset (Finset.finite_toSet T)
        apply s1

      have s3 : ∀ (s : Str α), (⋃ t ∈ foo' L1 s, derivative L1 t) = ⋃₀ {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M} :=
      by
        intro s
        ext cs
        simp only [Set.mem_iUnion, exists_prop, Set.mem_sUnion, Set.mem_setOf_eq]
        constructor
        · intro a2
          obtain ⟨i, ⟨a2_left, a2_right⟩⟩ := a2
          apply Exists.intro (L1.derivative i)
          constructor
          · apply Exists.intro i
            exact ⟨a2_left, rfl⟩
          · exact a2_right
        · intro a2
          obtain ⟨t, ⟨⟨i, ⟨a2_left_left, a2_left_right⟩⟩, a2_right⟩⟩ := a2
          apply Exists.intro i
          constructor
          · exact a2_left_left
          · rewrite [a2_left_right]
            exact a2_right

      have s4 : ∃ (S : Finset (Language α)), ∀ (s : Str α), (⋃ t ∈ foo' L1 s, derivative L1 t) ∈ S :=
      by
        apply Exists.intro (T.powerset.image (fun (S : Finset (Language α)) => (S : Set (Language α)).sUnion))
        intro s
        simp only [Finset.mem_image, Finset.mem_powerset]
        apply Exists.intro {M : Language α | ∃ (t : List α), t ∈ foo' L1 s ∧ derivative L1 t = M}.toFinite.toFinset
        constructor
        · simp only [Set.Finite.toFinset_subset]
          apply s1
        · rewrite [s3]
          simp only [Set.Finite.coe_toFinset]

      obtain ⟨S, s4⟩ := s4

      let A := {kleene_closure α L1} ∪ S.biUnion (fun (M : Language α) => {concat M (kleene_closure α L1)})

      apply Exists.intro A
      intro s
      by_cases c1 : s = []
      · unfold A
        rewrite [c1]
        rewrite [derivative_wrt_eps]
        simp only [Finset.singleton_union, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
        left
        exact True.intro
      · obtain s1 := derivative_of_kleene_closure_wrt_str L1 s c1
        rewrite [s1]
        clear s1

        have s2 : ⋃ t ∈ foo' L1 s, concat (derivative L1 t) (kleene_closure α L1) = concat (⋃ t ∈ foo' L1 s, derivative L1 t) (kleene_closure α L1) :=
        by
          unfold concat
          ext cs
          simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
          constructor
          · intro a2
            obtain ⟨i, hi, s, hs, t, ht, eq⟩ := a2
            rewrite [← eq]
            exact ⟨s, ⟨i, hi, hs⟩, t, ht, rfl⟩
          · intro a2
            obtain ⟨s, ⟨i, hi, hs⟩, t, ht, eq⟩ := a2
            rewrite [← eq]
            exact ⟨i, hi, s, hs, t, ht, rfl⟩
        rewrite [s2]
        clear s2

        unfold A
        simp only [Finset.singleton_union, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_singleton]
        right
        apply Exists.intro (⋃ t ∈ foo' L1 s, derivative L1 t)
        constructor
        · apply s4
        · apply Eq.refl


end Language
