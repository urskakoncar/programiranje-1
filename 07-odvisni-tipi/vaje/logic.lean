-- Izomorfizmi

theorem eq1 {A B : Prop} : (A ∧ B) ↔ (B ∧ A) :=
  by
    -- apply Iff.intro -- nasprotje od tega Iff.extro oz neki tazga
    constructor -- podobno kot apply Iff.intro
    intro ab
    constructor
    -- apply And.intro
    exact ab.right --dostopamo do desnega v paru
    exact ab.left

    intro ba
    constructor
    exact ba.right
    exact ba.left


theorem eq2 {A B : Prop} : (A ∨ B) ↔ (B ∨ A) :=
  sorry

theorem eq3 {A B C : Prop} : (A ∧ (B ∧ C)) ↔ (B ∧ (A ∧ C)) :=
  sorry

theorem eq4 {A B C : Prop} : (A ∨ (B ∨ C)) ↔ (B ∨ (A ∨ C)) :=
 sorry

theorem eq5 {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
  sorry

theorem eq6 {A B C : Prop} : (B ∨ C) → A ↔ (B → A) ∧ (C → A) :=
  by
    constructor
    intro h
    constructor
    intro b
    apply h
    left
    exact b

    --intro c
    --apply h
    --right
    --exact c

    --drug nacin za drugi del leve strani:
    intro c
    have xx : B ∨ C := Or.inr c -- ali ∨  se napiše kot \ or (brez presledka)
    have yy := h (Or.inr c)
    exact yy

    --se implikacija it desne v levo:
    intro h BvC
    cases BvC
    case inl b =>
      exact h.left b
      -- have l := h.left
      -- apply h.left
      -- exact b
    case inr c =>
      exact h.right c



theorem eq7 {A B C : Prop} : C → (A ∧ B) ↔ (C → A) ∧ (C → B) :=
  sorry
