import FormalLanguageLean.Derivative


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


-- https://arxiv.org/pdf/1907.13577


namespace Language


/-
Definition 16 (Distinguishing extension). Let L ⊆ Σ∗ be a language, and
s, t ∈ Σ∗ strings. A distinguishing extension is a string u ∈ Σ∗ such that
either su ∈ L or tu ∈ L, but not both.
-/
def is_dist_ext
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (u : Str α) :
  Prop :=
  (s ++ u ∈ L ∧ t ++ u ∉ L) ∨ (s ++ u ∉ L ∧ t ++ u ∈ L)


/-
Definition 17. Define the relation ≡L, “L-equivalent”, or “equivalent with
respect to L”, on strings by the rule
s ≡L t ⇔ {u : su ∈ L} = {u : tu ∈ L} , (1.66)
i.e. s ≡L t if there is no distinguishing extension for s and t.
-/
def L_equiv
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  Prop :=
  {u | s ++ u ∈ L} = {u | t ++ u ∈ L}


theorem L_equiv_iff_deriv_eq
  {α : Type}
  (L : Language α)
  (s t : Str α) :
  L_equiv L s t ↔ derivative L s = derivative L t :=
  by
    apply Iff.refl


theorem L_equiv_refl
  {α : Type}
  (L : Language α)
  (s : Str α) :
  L_equiv L s s :=
  by
    unfold L_equiv
    apply Eq.refl


theorem L_equiv_symm
  {α : Type}
  (L : Language α)
  (s t : Str α)
  (h1 : L_equiv L s t) :
  L_equiv L t s :=
  by
    unfold L_equiv
    exact Eq.symm h1


theorem L_equiv_trans
  {α : Type}
  (L : Language α)
  (r s t : Str α)
  (h1 : L_equiv L r s)
  (h2 : L_equiv L s t) :
  L_equiv L r t :=
  by
    unfold L_equiv at h1

    unfold L_equiv at h2

    unfold L_equiv
    exact Eq.trans h1 h2


instance (α : Type) (L : Language α) : IsEquiv (Str α) (L_equiv L) :=
  {
    symm := L_equiv_symm L
    refl := L_equiv_refl L
    trans := L_equiv_trans L
  }


theorem L_equivalence
  {α : Type}
  (L : Language α) :
  Equivalence (L_equiv L) :=
  ⟨ L_equiv_refl L, L_equiv_symm L _ _, L_equiv_trans L _ _ _ ⟩


def Str.equiv_class
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Set (Str α) :=
  {t | L_equiv L s t}


example
  {α : Type}
  (L : Language α)
  (s : Str α) :
  Str.equiv_class L s = { t | derivative L s = derivative L t } :=
  by
    apply Eq.refl


example
  {α : Type}
  (L : Language α)
  (a : α) :
  Str.equiv_class L [a] ∩ {s : Str α | s.length = 1} =
    { b | derivative L [a] = derivative L b ∧ b.length = 1 } :=
  by
    apply Eq.refl


theorem L_equiv_union
  {α : Type}
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∪ L2) s t :=
  by
    rewrite [L_equiv_iff_deriv_eq] at h1

    rewrite [L_equiv_iff_deriv_eq] at h2

    rewrite [L_equiv_iff_deriv_eq]
    rewrite [derivative_of_union_wrt_str L1 L2 s]
    rewrite [derivative_of_union_wrt_str L1 L2 t]
    rewrite [h1]
    rewrite [h2]
    apply Eq.refl


theorem L_equiv_intersection
  {α : Type}
  (L1 L2 : Language α)
  (s t : Str α)
  (h1 : L_equiv L1 s t)
  (h2 : L_equiv L2 s t) :
  L_equiv (L1 ∩ L2) s t :=
  by
    rewrite [L_equiv_iff_deriv_eq] at h1

    rewrite [L_equiv_iff_deriv_eq] at h2

    rewrite [L_equiv_iff_deriv_eq]
    rewrite [derivative_of_intersection_wrt_str L1 L2 s]
    rewrite [derivative_of_intersection_wrt_str L1 L2 t]
    rewrite [h1]
    rewrite [h2]
    apply Eq.refl


end Language
