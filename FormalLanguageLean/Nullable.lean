import FormalLanguageLean.Kleene


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 14 (Nullable). A language L is said to be nullable if ε ∈ L, and we define the nullify function ν by ν(L) =
{ε} if ε ∈ L
∅ if ε ∉ L
-/


def is_nullable
  {α : Type}
  (L : Language α) :
  Prop :=
  [] ∈ L


def nullify
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  Language α :=
  open Classical in
  if [] ∈ L
  then {[]}
  else ∅


def nullify_list
  {α : Type}
  [DecidableEq α]
  (L : List (Str α)) :
  List (Str α) :=
  open Classical in
  if [] ∈ L
  then [[]]
  else []

#eval Language.nullify_list [[0], []]
#eval Language.nullify_list [[0]]


theorem is_nullable_iff_nullify_eq_eps_singleton
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L.is_nullable ↔ L.nullify = {[]} :=
  by
    unfold Language.is_nullable
    unfold Language.nullify
    constructor
    · intro a1
      split
      case isTrue c1 =>
        apply Eq.refl
      case isFalse c1 =>
        contradiction
    · intro a1
      split at a1
      case isTrue c1 =>
        exact c1
      case isFalse c1 =>
        simp only [Set.empty_ne_singleton] at a1


theorem not_is_nullable_iff_nullify_eq_empty
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  ¬ L.is_nullable ↔ L.nullify = ∅ :=
  by
    unfold Language.is_nullable
    unfold Language.nullify
    constructor
    · intro a1
      split
      case isTrue c1 =>
        contradiction
      case isFalse c1 =>
        apply Eq.refl
    · intro a1
      split at a1
      case isTrue c1 =>
        simp only [Set.singleton_ne_empty] at a1
      case isFalse c1 =>
        exact c1


theorem nullify_char
  {α : Type}
  [DecidableEq α]
  (c : α) :
  ({[c]} : Language α).nullify = ∅ :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      simp only [Set.mem_singleton_iff, List.ne_cons_self] at c1
    case isFalse c1 =>
      apply Eq.refl


theorem nullify_eps
  {α : Type}
  [DecidableEq α] :
  ({[]} : Language α).nullify = {[]} :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      apply Eq.refl
    case isFalse c1 =>
      exfalso
      apply c1
      apply Set.mem_singleton


theorem nullify_empty
  {α : Type}
  [DecidableEq α] :
  (∅ : Language α).nullify = ∅ :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      simp only [Set.mem_empty_iff_false] at c1
    case isFalse c1 =>
      apply Eq.refl


theorem nullify_union
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (L1 ∪ L2).nullify = L1.nullify ∪ L2.nullify :=
  by
    unfold Language.nullify
    ext cs
    constructor
    · intro a1
      simp only [Set.mem_union, Set.mem_ite_empty_right, Set.mem_singleton_iff] at a1
      obtain ⟨a1_left, a1_right⟩ := a1

      simp only [Set.mem_union, Set.mem_ite_empty_right, Set.mem_singleton_iff]
      cases a1_left
      case inl a1_left =>
        left
        exact ⟨a1_left, a1_right⟩
      case inr a1_left =>
        right
        exact ⟨a1_left, a1_right⟩
    · intro a1
      simp only [Set.mem_union, Set.mem_ite_empty_right, Set.mem_singleton_iff] at a1

      simp only [Set.mem_union, Set.mem_ite_empty_right, Set.mem_singleton_iff]
      cases a1
      case inl a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · left
          exact a1_left
        · exact a1_right
      case inr a1 =>
        obtain ⟨a1_left, a1_right⟩ := a1
        constructor
        · right
          exact a1_left
        · exact a1_right


theorem nullify_intersection
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (L1 ∩ L2).nullify = L1.nullify ∩ L2.nullify :=
  by
    unfold Language.nullify
    ext cs
    constructor
    · intro a1
      simp only [Set.mem_inter_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff] at a1
      obtain ⟨⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1

      simp only [Set.mem_inter_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff]
      exact ⟨⟨a1_left_left, a1_right⟩, ⟨a1_left_right, a1_right⟩⟩
    · intro a1
      simp only [Set.mem_inter_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff] at a1
      obtain ⟨⟨a1_left_left, a1_left_right⟩, ⟨a1_right_left, a1_right_right⟩⟩ := a1

      simp only [Set.mem_inter_iff, Set.mem_ite_empty_right, Set.mem_singleton_iff]
      exact ⟨⟨a1_left_left, a1_right_left⟩, a1_right_right⟩


theorem nullify_concat
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1 L2).nullify = concat L1.nullify L2.nullify :=
  by
    unfold Language.nullify
    ext cs
    constructor
    · intro a1
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff] at a1
      rewrite [eps_mem_concat_iff] at a1
      obtain ⟨⟨a1_left_left, a1_left_right⟩, a1_right⟩ := a1

      split
      case isTrue c1 =>
        apply append_mem_concat_eps_right
        · rewrite [a1_right]
          apply Set.mem_singleton
        · apply Set.mem_singleton
      case isFalse c1 =>
        contradiction
    · intro a1
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff]

      split at a1
      case isTrue c1 =>
        simp only [concat_eps_left] at a1
        split at a1
        case isTrue c2 =>
          constructor
          · obtain s1 := eps_mem_concat_iff L1 L2
            rewrite [s1]
            exact ⟨c1, c2⟩
          · simp only [Set.mem_singleton_iff] at a1
            exact a1
        case isFalse c2 =>
          simp only [Set.mem_empty_iff_false] at a1
      case isFalse c1 =>
        rewrite [concat_empty_left] at a1
        simp only [Set.mem_empty_iff_false] at a1


theorem nullify_kleene_closure
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  (kleene_closure α L).nullify = {[]} :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      apply Eq.refl
    case isFalse c1 =>
      exfalso
      apply c1
      apply eps_mem_kleene_closure


theorem nullify_complement_empty
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1 : L.nullify = ∅) :
  (Lᶜ).nullify = {[]} :=
  by
    unfold Language.nullify at h1
    split at h1
    case isTrue c1 =>
      simp only [Set.singleton_ne_empty] at h1
    case isFalse c1 =>
      unfold Language.nullify
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        exfalso
        apply c2
        simp only [Set.mem_compl_iff]
        exact c1


theorem nullify_complement_eps
  {α : Type}
  [DecidableEq α]
  (L : Language α)
  (h1 : L.nullify = {[]}) :
  (Lᶜ).nullify = ∅ :=
  by
    unfold Language.nullify at h1

    unfold Language.nullify
    split at h1
    case isTrue c1 =>
      split
      case isTrue c2 =>
        simp only [Set.mem_compl_iff] at c2
        contradiction
      case isFalse c2 =>
        apply Eq.refl
    case isFalse c2 =>
      simp only [Set.empty_ne_singleton] at h1


theorem nullify_idempotent
  {α : Type}
  [DecidableEq α]
  (L : Language α) :
  L.nullify.nullify = L.nullify :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        exfalso
        apply c2
        apply Set.mem_singleton
    case isFalse c1 =>
      split
      case isTrue c2 =>
        simp only [Set.mem_empty_iff_false] at c2
      case isFalse c2 =>
        apply Eq.refl


theorem nullify_concat_nullify_left
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1.nullify L2).nullify = (concat L1 L2).nullify :=
  by
    simp only [nullify_concat]
    simp only [nullify_idempotent]


theorem nullify_concat_nullify_right
  {α : Type}
  [DecidableEq α]
  (L1 L2 : Language α) :
  (concat L1 L2.nullify).nullify = (concat L1 L2).nullify :=
  by
    simp only [nullify_concat]
    simp only [nullify_idempotent]


/-
  If [] ∈ L1 then let L0 be L1 \ {[]}. If [] ∉ L1 then let L0 be L1.
-/
theorem lang_as_union_of_nullify_and_not_nullable
  {α : Type}
  [DecidableEq α]
  (L1 : Language α) :
  ∃ (L0 : Language α), L0.nullify = ∅ ∧ L1 = L1.nullify ∪ L0 :=
  by
    unfold Language.nullify
    split
    case isTrue c1 =>
      apply Exists.intro (L1 \ {[]})
      split
      case isTrue c2 =>
        simp only [Set.mem_sdiff, Set.mem_singleton_iff] at c2
        obtain ⟨c2_left, c2_right⟩ := c2
        contradiction
      case isFalse c2 =>
        constructor
        · apply Eq.refl
        · simp only [Set.union_sdiff_self, Set.singleton_union]
          apply Eq.symm
          exact Set.insert_eq_of_mem c1
    case isFalse c1 =>
      apply Exists.intro L1
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        constructor
        · apply Eq.refl
        · simp only [Set.empty_union]


theorem mem_concat_nullify_left_iff
  {α : Type}
  [DecidableEq α]
  (L M : Language α)
  (cs : Str α) :
  cs ∈ concat L.nullify M ↔ [] ∈ L ∧ cs ∈ M :=
  by
    constructor
    · intro a1
      unfold concat at a1
      unfold Language.nullify at a1
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_setOf_eq] at a1
      obtain ⟨s, ⟨⟨hL, hs⟩, ⟨t, ⟨ht, eq⟩⟩⟩⟩ := a1

      rewrite [← eq]
      rewrite [hs]
      simp only [List.nil_append]
      exact ⟨hL, ht⟩
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1

      unfold concat
      unfold Language.nullify
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_setOf_eq]
      apply Exists.intro []
      constructor
      · exact ⟨a1_left, rfl⟩
      · apply Exists.intro cs
        constructor
        · exact a1_right
        · apply List.nil_append


theorem mem_concat_nullify_right_iff
  {α : Type}
  [DecidableEq α]
  (L M : Language α)
  (cs : Str α) :
  cs ∈ concat L M.nullify ↔ cs ∈ L ∧ [] ∈ M :=
  by
    constructor
    · intro a1
      unfold concat at a1
      unfold Language.nullify at a1
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_setOf_eq] at a1
      obtain ⟨s, ⟨hs, ⟨t, ⟨⟨hM, ht⟩, eq⟩⟩⟩⟩ := a1

      rewrite [← eq]
      rewrite [ht]
      simp only [List.append_nil]
      exact ⟨hs, hM⟩
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1

      unfold concat
      unfold Language.nullify
      simp only [Set.mem_ite_empty_right, Set.mem_singleton_iff, Set.mem_setOf_eq]
      apply Exists.intro cs
      constructor
      · exact a1_left
      · apply Exists.intro []
        constructor
        · exact ⟨a1_right, rfl⟩
        · apply List.append_nil


end Language
