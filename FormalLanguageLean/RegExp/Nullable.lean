import FormalLanguageLean.RegExp.RegExp


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA


namespace RegExp


def is_nullable
  {α : Type} :
  RegExp α → Prop
  | char _ => False
  | epsilon => True
  | zero => False
  | union R S => R.is_nullable ∨ S.is_nullable
  | concat R S => R.is_nullable ∧ S.is_nullable
  | kleene_closure _ => True


instance
  (α : Type)
  [DecidableEq α]
  (RE : RegExp α) :
  Decidable RE.is_nullable :=
  by
    induction RE
    all_goals
      unfold RegExp.is_nullable
      infer_instance


theorem regexp_is_nullable_iff_eps_mem_lang_of
  {α : Type}
  (RE : RegExp α) :
  RE.is_nullable ↔ [] ∈ RE.LanguageOf :=
  by
    induction RE
    all_goals
      unfold RegExp.is_nullable
      unfold RegExp.LanguageOf
    case char c =>
      simp only [Set.mem_singleton_iff, List.ne_cons_self]
    case epsilon =>
      simp only [Set.mem_singleton_iff]
    case zero =>
      simp only [Set.mem_empty_iff_false]
    case union R S R_ih S_ih =>
      simp only [Set.mem_union]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Iff.refl
    case concat R S R_ih S_ih =>
      rewrite [Language.eps_mem_concat_iff]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Iff.refl
    case kleene_closure R ih =>
      constructor
      · intro a1
        apply Language.eps_mem_kleene_closure
      · intro a1
        exact True.intro


theorem regexp_is_nullable_iff_regexp_lang_of_is_nullable
  {α : Type}
  (RE : RegExp α) :
  RE.is_nullable ↔ RE.LanguageOf.is_nullable :=
  by
    unfold Language.is_nullable
    apply regexp_is_nullable_iff_eps_mem_lang_of


def nullify
  {α : Type} :
  RegExp α → RegExp α
  | char _ => zero
  | epsilon => epsilon
  | zero => zero
  | union R S => union R.nullify S.nullify
  | concat R S => concat R.nullify S.nullify
  | kleene_closure _ => epsilon


theorem regexp_nullify_lang_eq_regexp_lang_nullify
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  RE.nullify.LanguageOf = (RE.LanguageOf).nullify :=
  by
    induction RE
    case char c =>
      unfold RegExp.nullify
      unfold Language.nullify
      unfold RegExp.LanguageOf
      split
      case isTrue c1 =>
        simp only [Set.mem_singleton_iff, List.ne_cons_self] at c1
      case isFalse c1 =>
        apply Eq.refl
    case epsilon =>
      unfold RegExp.nullify
      unfold RegExp.LanguageOf
      rewrite [Language.nullify_eps]
      apply Eq.refl
    case zero =>
      unfold RegExp.nullify
      unfold RegExp.LanguageOf
      rewrite [Language.nullify_empty]
      apply Eq.refl
    case union R S R_ih S_ih =>
      unfold RegExp.nullify
      unfold RegExp.LanguageOf
      rewrite [Language.nullify_union]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Eq.refl
    case concat R S R_ih S_ih =>
      unfold RegExp.nullify
      unfold RegExp.LanguageOf
      rewrite [Language.nullify_concat]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Eq.refl
    case kleene_closure R ih =>
      unfold RegExp.nullify
      unfold RegExp.LanguageOf
      rewrite [Language.nullify_kleene_closure]
      apply Eq.refl


example
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  if RE.is_nullable
  then RE.nullify.LanguageOf = {[]}
  else RE.nullify.LanguageOf = ∅ :=
  by
    rewrite [regexp_nullify_lang_eq_regexp_lang_nullify]
    split
    case isTrue c1 =>
      rewrite [regexp_is_nullable_iff_eps_mem_lang_of] at c1

      unfold Language.nullify
      split
      case isTrue c2 =>
        apply Eq.refl
      case isFalse c2 =>
        contradiction
    case isFalse c1 =>
      rewrite [regexp_is_nullable_iff_eps_mem_lang_of] at c1

      unfold Language.nullify
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        apply Eq.refl


end RegExp
