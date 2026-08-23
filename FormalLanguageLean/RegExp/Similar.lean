import FormalLanguageLean.RegExp.Derivative


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577
-- https://www.cambridge.org/core/journals/journal-of-functional-programming/article/regularexpression-derivatives-reexamined/E5734B86DEB96C61C69E5CF3C4FB0AFA

-- Coqlex: Generating Formally Verified Lexers
-- https://arxiv.org/pdf/2306.12411
-- https://gitlab.inria.fr/wouedrao/coqlex/-/blob/master/RegexpSimpl.v?ref_type=heads


namespace RegExp


inductive Similar {α : Type} : RegExp α → RegExp α → Prop
| union_1
  (R : RegExp α) :
  Similar (RegExp.union R R) R

| union_2
  (R S : RegExp α) :
  Similar (RegExp.union R S) (RegExp.union S R)

| union_3
  (R S T : RegExp α) :
  Similar (RegExp.union (RegExp.union R S) T) (RegExp.union R (RegExp.union S T))

| union_4
  (R : RegExp α) :
  Similar (RegExp.union RegExp.zero R) R

| concat_1
  (R S T : RegExp α) :
  Similar (RegExp.concat (RegExp.concat R S) T) (RegExp.concat R (RegExp.concat S T))

| concat_2
  (R : RegExp α) :
  Similar (RegExp.concat RegExp.zero R) RegExp.zero

| concat_3
  (R : RegExp α) :
  Similar (RegExp.concat R RegExp.zero) RegExp.zero

| concat_4
  (R : RegExp α) :
  Similar (RegExp.concat RegExp.epsilon R) R

| concat_5
  (R : RegExp α) :
  Similar (RegExp.concat R RegExp.epsilon) R

| kleene_closure_1
  (R : RegExp α) :
  Similar (RegExp.kleene_closure (RegExp.kleene_closure R)) (RegExp.kleene_closure R)

| kleene_closure_2 :
  Similar (RegExp.kleene_closure RegExp.epsilon) RegExp.epsilon

| kleene_closure_3 :
  Similar (RegExp.kleene_closure RegExp.zero) RegExp.epsilon


example
  {α : Type}
  (RE_1 RE_2 : RegExp α)
  (h1 : Similar RE_1 RE_2) :
  RE_1.LanguageOf = RE_2.LanguageOf :=
  by
    induction h1
    case union_1 R =>
      simp only [RegExp.LanguageOf]
      simp only [Set.union_self]
    case union_2 R S =>
      unfold RegExp.LanguageOf
      apply Set.union_comm
    case union_3 R S T =>
      unfold RegExp.LanguageOf
      apply Set.union_assoc
    case union_4 R =>
      simp only [RegExp.LanguageOf]
      apply Set.empty_union
    case concat_1 R S T =>
      unfold RegExp.LanguageOf
      apply Eq.symm
      apply Language.concat_assoc
    case concat_2 R =>
      unfold RegExp.LanguageOf
      apply Language.concat_empty_left
    case concat_3 R =>
      unfold RegExp.LanguageOf
      apply Language.concat_empty_right
    case concat_4 R =>
      simp only [RegExp.LanguageOf]
      apply Language.concat_eps_left
    case concat_5 R =>
      simp only [RegExp.LanguageOf]
      apply Language.concat_eps_right
    case kleene_closure_1 R =>
      unfold RegExp.LanguageOf
      apply Eq.symm
      apply Language.kleene_closure_idempotent
    case kleene_closure_2 =>
      unfold RegExp.LanguageOf
      apply Language.kleene_closure_eps
    case kleene_closure_3 =>
      unfold RegExp.LanguageOf
      apply Language.kleene_closure_empty


def simp_union
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  RegExp α :=
  match RE_1 with
  | RegExp.zero => RE_2
  | R =>
    match RE_2 with
    | RegExp.zero => R
    | S => RegExp.union R S


theorem simp_union_lang_eq_union_lang
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  (simp_union RE_1 RE_2).LanguageOf = (RegExp.union RE_1 RE_2).LanguageOf :=
  by
    induction RE_1 generalizing RE_2
    case zero =>
      simp only [simp_union]
      simp only [RegExp.LanguageOf]
      simp only [Set.empty_union]
    all_goals
      cases RE_2
      case zero =>
        simp only [simp_union]
        simp only [RegExp.LanguageOf]
        simp only [Set.union_empty]
      all_goals
        simp only [simp_union]


def simp_concat
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  RegExp α :=
  match RE_1 with
  | RegExp.epsilon => RE_2
  | RegExp.zero => RegExp.zero
  | R =>
    match RE_2 with
    | RegExp.epsilon => R
    | RegExp.zero => RegExp.zero
    | S => RegExp.concat R S


theorem simp_concat_lang_eq_concat_lang
  {α : Type}
  (RE_1 RE_2 : RegExp α) :
  (simp_concat RE_1 RE_2).LanguageOf = (RegExp.concat RE_1 RE_2).LanguageOf :=
  by
    induction RE_1 generalizing RE_2
    case epsilon =>
      simp only [simp_concat]
      simp only [RegExp.LanguageOf]
      rewrite [Language.concat_eps_left]
      apply Eq.refl
    case zero =>
      simp only [simp_concat]
      simp only [RegExp.LanguageOf]
      rewrite [Language.concat_empty_left]
      apply Eq.refl
    all_goals
      cases RE_2
      case epsilon =>
        simp only [simp_concat]
        simp only [RegExp.LanguageOf]
        rewrite [Language.concat_eps_right]
        apply Eq.refl
      case zero =>
        simp only [simp_concat]
        simp only [RegExp.LanguageOf]
        rewrite [Language.concat_empty_right]
        apply Eq.refl
      all_goals
        simp only [simp_concat]


def simp_kleene_closure
  {α : Type}
  (RE : RegExp α) :
  RegExp α :=
  match RE with
  | RegExp.epsilon => RegExp.epsilon
  | RegExp.zero => RegExp.epsilon
  | RegExp.kleene_closure R => simp_kleene_closure R
  | R => RegExp.kleene_closure R


theorem simp_kleene_closure_lang_eq_kleene_closure_lang
  {α : Type}
  (RE : RegExp α) :
  (simp_kleene_closure RE).LanguageOf = (RegExp.kleene_closure RE).LanguageOf :=
  by
    induction RE
    case epsilon =>
      unfold simp_kleene_closure
      simp only [RegExp.LanguageOf]
      rewrite [Language.kleene_closure_eps]
      apply Eq.refl
    case zero =>
      unfold simp_kleene_closure
      simp only [RegExp.LanguageOf]
      rewrite [Language.kleene_closure_empty]
      apply Eq.refl
    case kleene_closure R R_ih =>
      simp only [RegExp.LanguageOf] at R_ih

      unfold simp_kleene_closure
      simp only [RegExp.LanguageOf]
      rewrite [← Language.kleene_closure_idempotent]
      exact R_ih
    all_goals
      unfold simp_kleene_closure
      apply Eq.refl


def simp_derivative
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  RegExp α :=
  match RE with
  | char b => if a = b then epsilon else zero
  | epsilon => zero
  | zero => zero
  | union R S => simp_union (R.simp_derivative a) (S.simp_derivative a)
  | concat R S => simp_union (simp_concat (R.simp_derivative a) S) (simp_concat R.nullify (S.simp_derivative a))
  | kleene_closure R => simp_concat (R.simp_derivative a) (simp_kleene_closure R)


theorem simp_derivative_lang_eq_derivative_lang
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α)
  (a : α) :
  (RegExp.simp_derivative RE a).LanguageOf = (RegExp.derivative RE a).LanguageOf :=
  by
    induction RE
    case union R S R_ih S_ih =>
      unfold RegExp.simp_derivative
      unfold RegExp.derivative
      rewrite [simp_union_lang_eq_union_lang]
      unfold RegExp.LanguageOf
      rewrite [R_ih]
      rewrite [S_ih]
      apply Eq.refl
    case concat R S R_ih S_ih =>
      unfold RegExp.simp_derivative
      unfold RegExp.derivative
      rewrite [simp_union_lang_eq_union_lang]
      unfold RegExp.LanguageOf
      simp only [simp_concat_lang_eq_concat_lang]
      simp only [RegExp.LanguageOf]
      rewrite [R_ih]
      rewrite [S_ih]
      apply Eq.refl
    case kleene_closure R ih =>
      unfold RegExp.simp_derivative
      unfold RegExp.derivative
      rewrite [simp_concat_lang_eq_concat_lang]
      unfold RegExp.LanguageOf
      rewrite [simp_kleene_closure_lang_eq_kleene_closure_lang]
      simp only [RegExp.LanguageOf]
      rewrite [ih]
      apply Eq.refl
    all_goals
      unfold simp_derivative
      unfold derivative
      apply Eq.refl


theorem all_simp_derivative_mem_finset
  {α : Type}
  [DecidableEq α]
  (RE : RegExp α) :
  ∃ (T : Finset (RegExp α)), ∀ (a : α), simp_derivative RE a ∈ T :=
  by
    induction RE
    case char c =>
      unfold simp_derivative
      apply Exists.intro {epsilon, zero}
      intro a
      split
      case isTrue c1 =>
        simp only [Finset.mem_insert]
        left
        exact True.intro
      case isFalse c1 =>
        simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton]
        right
        exact True.intro
    case epsilon =>
      unfold simp_derivative
      apply Exists.intro {zero}
      intro a
      simp only [Finset.mem_singleton]
    case zero =>
      unfold simp_derivative
      apply Exists.intro {zero}
      intro a
      simp only [Finset.mem_singleton]
    case union R S R_ih S_ih =>
      obtain ⟨T_R, T_R_ih⟩ := R_ih
      obtain ⟨T_S, T_S_ih⟩ := S_ih

      apply Exists.intro (T_R.biUnion (fun a => T_S.biUnion (fun b => {simp_union a b})))
      intro a
      by_cases c1 : R.simp_derivative a = zero
      · simp only [simp_derivative]
        rewrite [c1]
        simp only [Finset.mem_biUnion, Finset.mem_singleton]
        apply Exists.intro (R.simp_derivative a)
        constructor
        · apply T_R_ih
        · apply Exists.intro (S.simp_derivative a)
          constructor
          · apply T_S_ih
          · rewrite [c1]
            apply Eq.refl
      · simp only [simp_derivative]
        simp only [Finset.mem_biUnion, Finset.mem_singleton]
        apply Exists.intro (R.simp_derivative a)
        constructor
        · apply T_R_ih
        · apply Exists.intro (S.simp_derivative a)
          constructor
          · apply T_S_ih
          · by_cases c2 : S.simp_derivative a = zero
            · simp only [c2]
            case neg =>
              apply Eq.refl
    all_goals
      sorry


end RegExp
