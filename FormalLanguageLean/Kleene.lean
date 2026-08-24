import FormalLanguageLean.Exp


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 13 (Kleene closure). Let L be a language. L∗ is defined by
1. ε ∈ L∗
2. For any s ∈ L∗ and t ∈ L, st ∈ L∗
3. Nothing else is in L∗
-/
inductive kleene_closure
  (α : Type) :
  Language α → Language α
  | eps
    (L : Language α) :
    kleene_closure α L []
  | succ
    (L : Language α)
    (s t : Str α) :
    s ∈ kleene_closure α L →
    t ∈ L →
    kleene_closure α L (s ++ t)


theorem kleene_closure_empty
  {α : Type} :
  kleene_closure α ∅ = {[]} :=
  by
    ext cs
    simp only [Set.mem_singleton_iff]
    constructor
    · intro a1
      induction a1
      case eps =>
        apply Eq.refl
      case succ s t ih_1 ih_2 ih_3 =>
        simp only [Set.mem_empty_iff_false] at ih_2
    · intro a1
      rewrite [a1]
      exact kleene_closure.eps ∅


theorem kleene_closure_eps
  {α : Type} :
  kleene_closure α {[]} = {[]} :=
  by
    ext cs
    simp only [Set.mem_singleton_iff]
    constructor
    · intro a1
      induction a1
      case eps =>
        apply Eq.refl
      case succ s t ih_1 ih_2 ih_3 =>
        simp only [Set.mem_singleton_iff] at ih_2
        rewrite [ih_2]
        rewrite [ih_3]
        exact List.nil_append []
    · intro a1
      rewrite [a1]
      exact kleene_closure.eps {[]}


-------------------------------------------------------------------------------


theorem eps_mem_kleene_closure
  {α : Type}
  (L : Language α) :
  [] ∈ kleene_closure α L :=
  by
    exact kleene_closure.eps L

theorem kleene_closure_nonempty
  {α : Type}
  (L : Language α) :
  (kleene_closure α L).Nonempty :=
  by
    unfold Set.Nonempty
    apply Exists.intro []
    exact eps_mem_kleene_closure L


-------------------------------------------------------------------------------


-- Theorem 4
theorem exp_subset_kleene_closure
  {α : Type}
  (L : Language α)
  (n : ℕ) :
  exp L n ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1

    induction n generalizing cs
    case zero =>
      unfold exp at a1
      simp only [Set.mem_singleton_iff] at a1

      rewrite [a1]
      exact kleene_closure.eps L
    case succ n ih =>
      unfold exp at a1
      unfold concat at a1
      simp only [Set.mem_setOf_eq] at a1

      obtain ⟨s, hs, t, ht, eq⟩ := a1
      rewrite [← eq]
      apply kleene_closure.succ L
      · apply ih
        exact hs
      · exact ht


-------------------------------------------------------------------------------


theorem language_subset_kleene_closure
  {α : Type}
  (L : Language α) :
  L ⊆ kleene_closure α L :=
  by
    conv => left; rewrite [← exp_one L]
    exact exp_subset_kleene_closure L 1


theorem mem_language_mem_kleene_closure
  {α : Type}
  (L : Language α)
  (s : Str α)
  (h1 : s ∈ L) :
  s ∈ kleene_closure α L :=
  by
    obtain s1 := language_subset_kleene_closure L
    exact Set.mem_of_subset_of_mem s1 h1


-------------------------------------------------------------------------------


theorem union_exp_subset_kleene_closure
  {α : Type}
  (L : Language α) :
  ⋃ (n : ℕ), exp L n ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp only [Set.mem_iUnion] at a1
    obtain ⟨n, a2⟩ := a1
    exact Set.mem_of_subset_of_mem (exp_subset_kleene_closure L n) a2


theorem kleene_closure_subset_union_exp
  {α : Type}
  (L : Language α) :
  kleene_closure α L ⊆ ⋃ (n : ℕ), exp L n :=
  by
    simp only [Set.subset_def]
    intro cs a1
    induction a1
    case eps =>
      simp only [Set.mem_iUnion]
      apply Exists.intro 0
      unfold exp
      apply Set.mem_singleton
    case succ s t ih_1 ih_2 ih_3 =>
      simp only [Set.mem_iUnion] at ih_3
      obtain ⟨i, hs⟩ := ih_3

      simp only [Set.mem_iUnion]
      apply Exists.intro (i + 1)
      unfold exp
      unfold concat
      simp only [Set.mem_setOf_eq]
      exact ⟨s, hs, t, ih_2, rfl⟩


-- Theorem 5
theorem kleene_closure_eq_union_exp
  {α : Type}
  (L : Language α) :
  kleene_closure α L = ⋃ (n : ℕ), exp L n :=
  by
    exact Set.eq_of_subset_of_subset (kleene_closure_subset_union_exp L) (union_exp_subset_kleene_closure L)


-------------------------------------------------------------------------------


theorem concat_kleene_closure_closed
  {α : Type}
  (L : Language α) :
  concat (kleene_closure α L) (kleene_closure α L) ⊆ kleene_closure α L :=
  by
    simp only [kleene_closure_eq_union_exp]
    simp only [Set.subset_def]
    intro cs a1
    unfold concat at a1
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at a1
    obtain ⟨s, ⟨i, hs⟩, t, ⟨j, ht⟩, eq⟩ := a1

    simp only [Set.mem_iUnion]
    apply Exists.intro (i + j)
    rewrite [← eq]
    apply append_exp_sum
    · exact hs
    · exact ht


theorem append_kleene_closure_closed
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (h1 : s ∈ kleene_closure α L)
  (h2 : t ∈ kleene_closure α L) :
  s ++ t ∈ kleene_closure α L :=
  by
    simp only [kleene_closure_eq_union_exp] at h1
    simp only [Set.mem_iUnion] at h1
    obtain ⟨m, hs⟩ := h1

    simp only [kleene_closure_eq_union_exp] at h2
    simp only [Set.mem_iUnion] at h2
    obtain ⟨n, ht⟩ := h2

    simp only [kleene_closure_eq_union_exp]
    simp only [Set.mem_iUnion]

    apply Exists.intro (m + n)
    apply append_exp_sum
    · exact hs
    · exact ht


-------------------------------------------------------------------------------


-- Each s is the concatenation of a list of strings, each of which is in L.
def kleene_closure_set
  (α : Type)
  (L : Language α) :=
  { s : Str α | ∃ M : List (Str α), (∀ (r : Str α), r ∈ M → r ∈ L) ∧ s = M.flatten }


theorem kleene_closure_set_subset_kleene_closure
  {α : Type}
  (L : Language α) :
  kleene_closure_set α L ⊆ kleene_closure α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    simp only [kleene_closure_set] at a1
    simp only [Set.mem_setOf_eq] at a1
    obtain ⟨M, a1_left, a1_right⟩ := a1
    rewrite [a1_right]
    clear a1_right

    simp only [kleene_closure_eq_union_exp]
    simp only [Set.mem_iUnion]

    induction M
    case nil =>
      apply Exists.intro 0
      unfold exp
      simp only [List.flatten_nil, Set.mem_singleton_iff]
    case cons hd tl ih =>
      simp only [List.mem_cons] at a1_left

      have s1 : ∀ r ∈ tl, r ∈ L :=
      by
        intro r a2
        apply a1_left
        right
        exact a2

      specialize ih s1
      obtain ⟨i, ih⟩ := ih
      apply Exists.intro (i + 1)
      simp only [List.flatten_cons]
      apply append_mem_exp_right
      · apply a1_left
        left
        apply Eq.refl
      · exact ih


theorem kleene_closure_subset_kleene_closure_set
  {α : Type}
  (L : Language α) :
  kleene_closure α L ⊆ kleene_closure_set α L :=
  by
    simp only [Set.subset_def]
    intro cs a1
    unfold kleene_closure_set
    simp only [Set.mem_setOf_eq]

    induction a1
    case eps =>
      apply Exists.intro []
      constructor
      · intro r a2
        simp only [List.not_mem_nil] at a2
      · simp only [List.flatten_nil]
    case succ s t ih_1 ih_2 ih_3 =>
      obtain ⟨M, ⟨ih_3_left, ih_3_right⟩⟩ := ih_3
      rewrite [ih_3_right]
      apply Exists.intro (M ++ [t])
      constructor
      · intro r a4
        simp only [List.mem_append, List.mem_cons] at a4
        cases a4
        case inl a4 =>
          apply ih_3_left
          exact a4
        case inr a4 =>
          cases a4
          case inl a4 =>
            rewrite [a4]
            exact ih_2
          case inr a4 =>
            simp only [List.not_mem_nil] at a4
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]


theorem kleene_closure_set_eq_kleene_closure
  (α : Type)
  (L : Language α) :
  kleene_closure_set α L = kleene_closure α L :=
  by
    exact Set.eq_of_subset_of_subset (kleene_closure_set_subset_kleene_closure L) (kleene_closure_subset_kleene_closure_set L)


-------------------------------------------------------------------------------


-- Theorem 6
theorem kleene_closure_eq_eps_union_concat_language_kleene_closure
  {α : Type}
  (L : Language α) :
  (kleene_closure α L) = {[]} ∪ (concat L (kleene_closure α L)) :=
  by
    ext cs
    constructor
    · intro a1
      simp only [kleene_closure_eq_union_exp] at a1
      simp only [Set.mem_iUnion] at a1
      obtain ⟨i, a2⟩ := a1

      simp only [Set.singleton_union, Set.mem_insert_iff]
      cases i
      case zero =>
        unfold exp at a2
        simp only [Set.mem_singleton_iff] at a2
        left
        exact a2
      case succ k =>
        rewrite [exp_succ_concat_left] at a2
        unfold concat at a2
        simp only [Set.mem_setOf_eq] at a2
        obtain ⟨s, hs, t, ht, eq⟩ := a2

        right
        rewrite [← eq]
        apply append_mem_concat
        · exact hs
        · exact Set.mem_of_mem_of_subset ht (exp_subset_kleene_closure L k)
    · intro a1
      simp only [Set.singleton_union, Set.mem_insert_iff] at a1
      cases a1
      case inl a1 =>
        rewrite [a1]
        exact kleene_closure.eps L
      case inr a1 =>
        rewrite [kleene_closure_eq_union_exp L] at a1
        unfold concat at a1
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at a1
        obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1
        rewrite [← eq]
        apply exp_subset_kleene_closure L (i + 1)
        apply append_mem_exp_right
        · exact hs
        · exact ht


-- Corollary 1
theorem eps_mem_imp_kleene_closure_eq_concat_kleene_closure_left
  {α : Type}
  (L : Language α)
  (h1 : [] ∈ L) :
  kleene_closure α L = concat L (kleene_closure α L) :=
  by
    have s1 : {[]} ∪ concat L (kleene_closure α L) =
      concat L (kleene_closure α L) :=
    by
      apply Set.union_eq_self_of_subset_left
      simp only [Set.singleton_subset_iff]
      unfold concat
      simp only [Set.mem_setOf_eq, List.append_eq_nil_iff, exists_eq_right_right]
      constructor
      · exact h1
      · exact kleene_closure.eps L

    obtain s2 := kleene_closure_eq_eps_union_concat_language_kleene_closure L
    rewrite [s1] at s2
    exact s2


-------------------------------------------------------------------------------


theorem concat_kleene_closure_succ_left
  {α : Type}
  (L : Language α) :
  concat L (⋃ (n : ℕ), exp L n) = ⋃ (n : ℕ), exp L (n + 1) :=
  by
    ext cs
    constructor
    · intro a1
      unfold concat at a1
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at a1
      obtain ⟨s, hs, t, ⟨i, ht⟩, eq⟩ := a1
      rewrite [← eq]
      unfold exp
      simp only [Set.mem_iUnion]
      apply Exists.intro i
      apply append_mem_exp_right
      · exact hs
      · exact ht
    · intro a1
      simp only [Set.mem_iUnion] at a1
      obtain ⟨i, a1⟩ := a1

      unfold exp at a1
      rewrite [concat_exp_comm] at a1
      unfold concat at a1
      simp only [Set.mem_setOf_eq] at a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1

      unfold concat
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨s, hs, t, ⟨i, ht⟩, eq⟩


theorem concat_kleene_closure_succ_right
  {α : Type}
  (L : Language α) :
  concat (⋃ (n : ℕ), exp L n) L = ⋃ (n : ℕ), exp L (n + 1) :=
  by
    ext cs
    constructor
    · intro a1
      unfold concat at a1
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at a1
      obtain ⟨s, ⟨i, hs⟩,  t, ht, eq⟩ := a1
      rewrite [← eq]

      simp only [Set.mem_iUnion]
      unfold exp
      apply Exists.intro i
      apply append_mem_exp_left
      · exact hs
      · exact ht
    · intro a1
      simp only [Set.mem_iUnion] at a1
      obtain ⟨i, a1⟩ := a1

      unfold exp at a1
      unfold concat at a1
      simp only [Set.mem_setOf_eq] at a1
      obtain ⟨s, hs, t, ht, eq⟩ := a1

      unfold concat
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨s, ⟨i, hs⟩, t, ht, eq⟩


-- Theorem 7
theorem concat_kleene_closure_comm
  {α : Type}
  (L : Language α) :
  concat L (kleene_closure α L) = concat (kleene_closure α L) L :=
  by
    rewrite [kleene_closure_eq_union_exp]
    rewrite [concat_kleene_closure_succ_left]
    rewrite [concat_kleene_closure_succ_right]
    apply Eq.refl


-------------------------------------------------------------------------------


-- Theorem 8
theorem kleene_closure_idempotent
  {α : Type}
  (L : Language α) :
  kleene_closure α L = kleene_closure α (kleene_closure α L) :=
  by
    apply Set.eq_of_subset_of_subset
    · exact language_subset_kleene_closure (kleene_closure α L)
    · simp only [Set.subset_def]
      intro cs a1
      induction a1
      case eps =>
        apply kleene_closure.eps L
      case succ s t ih_1 ih_2 ih_3 =>
        apply append_kleene_closure_closed
        · exact ih_3
        · exact ih_2


-- Corollary 2
theorem kleene_closure_eq_concat_kleene_closure_kleene_closure
  {α : Type}
  (L : Language α) :
  kleene_closure α L =
    concat (kleene_closure α L) (kleene_closure α L) :=
  by
    have s1 : {[]} ∪ concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) = concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) :=
      by
        apply Set.union_eq_self_of_subset_left
        simp only [Set.singleton_subset_iff]
        unfold concat
        simp only [Set.mem_setOf_eq, List.append_eq_nil_iff, exists_eq_right_right]
        constructor
        · exact kleene_closure.eps L
        · exact kleene_closure.eps (kleene_closure α L)

    calc
      kleene_closure α L = kleene_closure α (kleene_closure α L) := kleene_closure_idempotent L

      _ = {[]} ∪ (concat (kleene_closure α L) (kleene_closure α (kleene_closure α L))) := kleene_closure_eq_eps_union_concat_language_kleene_closure (kleene_closure α L)

      _ = concat (kleene_closure α L) (kleene_closure α (kleene_closure α L)) := s1

      _ = concat (kleene_closure α L) (kleene_closure α L) :=
        by
          rewrite [← kleene_closure_idempotent]
          apply Eq.refl


-------------------------------------------------------------------------------


-- Theorem 9
theorem Ardens_rule
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = concat (kleene_closure α L1) L2) :
  X = (concat L1 X) ∪ L2 :=
  by
    calc
      X = concat (kleene_closure α L1) L2 := h1

      _ = concat ({[]} ∪ concat L1 (kleene_closure α L1)) L2 :=
        by
          rewrite [← kleene_closure_eq_eps_union_concat_language_kleene_closure]
          apply Eq.refl

      _ = concat ((concat L1 (kleene_closure α L1)) ∪ {[]}) L2 :=
        by
          rewrite [Set.union_comm (concat L1 (kleene_closure α L1))]
          apply Eq.refl

      _ = concat L1 (concat (kleene_closure α L1) L2) ∪ L2 :=
        by
          rewrite [concat_distrib_union_right]
          rewrite [concat_eps_left]
          rewrite [concat_assoc]
          apply Eq.refl

      _ = (concat L1 X) ∪ L2 :=
        by
          rewrite [h1]
          apply Eq.refl


theorem Ardens_rule_unique_left_aux
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2) :
  ∀ (n : ℕ), concat (exp L1 n) L2 ⊆ X :=
  by
    intro n
    induction n
    case zero =>
      unfold exp
      rewrite [concat_eps_left]
      rewrite [h1]
      exact Set.subset_union_right
    case succ n ih =>
      have s1 : concat L1 (concat (exp L1 n) L2) ⊆ concat L1 X :=
      by
        apply concat_subset_left
        exact ih

      rewrite [concat_assoc] at s1
      rewrite [← exp_succ_concat_left] at s1

      have s2 : concat L1 X ⊆ X :=
      by
        conv => right; rewrite [h1]
        exact Set.subset_union_left

      trans (concat L1 X)
      · exact s1
      · exact s2


theorem Ardens_rule_unique_left
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2) :
  concat (kleene_closure α L1) L2 ⊆ X :=
  by
    rewrite [kleene_closure_eq_union_exp]
    simp only [Set.subset_def]
    intro cs a1
    unfold concat at a1
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at a1
    obtain ⟨s, ⟨i, hs⟩, t, ht, eq⟩ := a1
    rewrite [← eq]

    obtain s1 := Ardens_rule_unique_left_aux L1 L2 X h1 i
    apply Set.mem_of_subset_of_mem s1
    unfold concat
    simp only [Set.mem_setOf_eq]
    exact ⟨s, hs, t, ht, rfl⟩


theorem Ardens_rule_unique_right
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2)
  (h2 : [] ∉ L1) :
  X ⊆ concat (kleene_closure α L1) L2
  | x, a1 => by
    rewrite [h1] at a1
    unfold concat at a1
    simp only [Set.mem_union, Set.mem_setOf_eq] at a1
    obtain ⟨s, hs, t, ht, eq⟩ | hx := a1
    · rewrite [← eq]
      unfold concat
      simp only [Set.mem_setOf_eq]
      have ht' := ht
      rewrite [h1] at ht'
      simp only [Set.mem_union] at ht'
      obtain _ | ht1 := ht'
      · have : t.length < x.length :=
        by
          rewrite [← eq]
          apply String.str_append_length_left
          intro contra
          rewrite [contra] at hs
          contradiction
        have IH := Ardens_rule_unique_right L1 L2 X h1 h2 ht
        unfold concat at IH
        simp only [Set.mem_setOf_eq] at IH
        obtain ⟨s', hs', t', ht', eq'⟩ := IH
        apply Exists.intro (s ++ s')
        constructor
        · apply append_kleene_closure_closed
          · apply mem_language_mem_kleene_closure
            exact hs
          · exact hs'
        · apply Exists.intro t'
          constructor
          · exact ht'
          · simp only [List.append_assoc, List.append_cancel_left_eq]
            exact eq'
      · apply Exists.intro s
        constructor
        · apply mem_language_mem_kleene_closure L1 s hs
        · apply Exists.intro t
          exact ⟨ht1, rfl⟩
    · apply append_mem_concat_eps_left
      · apply eps_mem_kleene_closure
      · exact hx
termination_by x => x.length


theorem Ardens_rule_unique
  {α : Type}
  (L1 L2 X : Language α)
  (h1 : X = (concat L1 X) ∪ L2)
  (h2 : [] ∉ L1) :
  concat (kleene_closure α L1) L2 = X :=
  by
    exact Set.eq_of_subset_of_subset (Ardens_rule_unique_left L1 L2 X h1) (Ardens_rule_unique_right L1 L2 X h1 h2)


end Language
