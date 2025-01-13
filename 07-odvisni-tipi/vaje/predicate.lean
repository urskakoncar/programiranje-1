
variable (α : Type) (p q : α → Prop) (r : Prop)
variable (r : Prop)

-- Izjave napišite na list papirja, nato pa jih dokažite v datoteki.

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  intro h
  intro x
  intro px
  exact h (⟨x, px⟩)

  intro h
  intro ⟨x, px⟩
  exact h x px


-- Dokaz izključnosti med negacijo eksistence in univerzalno negacijo
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro  -- To dokaže obratno smer (¬ ∃ x, p x) ↔ (∀ x, ¬ p x)

  -- Dokažimo prvo smer (¬ ∃ x, p x → ∀ x, ¬ p x)
  intro h  -- Predpostavimo, da ni nobenega x, za katerega velja p(x)
  intro x  -- Izberemo poljuben x
  intro px  -- Predpostavimo, da za ta x velja p(x)
  exact h (⟨x, px⟩)  -- To pripelje do protislovja (ker predpostavljamo, da ni nobenega x, za katerega velja p(x))

  -- Dokažimo drugo smer (∀ x, ¬ p x → ¬ ∃ x, p x)
  intro h  -- Predpostavimo, da za vse x velja, da p(x) ni resničen
  intro ⟨x, px⟩  -- Predpostavimo, da obstaja x, za katerega velja p(x)
  exact h x px  -- To pripelje do protislovja (ker smo predpostavili, da je p(x) neresničen za vse x)


example : (r → ∀ x, p x) ↔ (∀ x, r → p x) := by
  apply Iff.intro

  intro h
  intro x
  intro r
  apply h r

  intro h
  intro r
  intro x
  apply h
  apply r


example : r ∧ (∃ x, p x) ↔ (∃ x, r ∧ p x) := by
  apply Iff.intro
  intro h
  c


example : r ∨ (∀ x, p x) → (∀ x, r ∨ p x) :=
  sorry

-- Tu pa nam bo v pomoč klasična logika
-- namig: `Classical.byContradiction` in `Classical.em` sta lahko v pomoč
open Classical

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
 sorry

example : r ∨ (∀ x, p x) ↔ (∀ x, r ∨ p x) :=
  sorry
