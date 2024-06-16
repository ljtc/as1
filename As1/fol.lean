-- Lógica de primer orden

/-
Sólo daremos algunas equivalencias que nos permitan
manejar fórmulas con cuantificadores.
-/

import Mathlib.Tactic

section fol

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

--cuantificar x en algo donde no ocurre x lo deja igual
example : (∃ x : α, r) → r := by
  intro ⟨_, hr⟩
  assumption

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example (a : α) : (∀ x : α, r) ↔ r := by
  constructor
  . intro h
    exact h a
  . intro hr _
    assumption
--



-- ∀ con ∧
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro a
      exact (h a).1
    . intro a
      exact (h a).2
  . intro ⟨h, h'⟩ x
    exact ⟨h x, h' x⟩

--consecuencia de lo anterior
example (a : α) : (∀ x, p x ∧ r) ↔ (∀ x, p x) ∧ r := by
  constructor
  . intro h
    constructor
    . intro x
      exact (h x).1
    . exact (h a).2
  . intro h x
    exact ⟨(h.1) x, h.2⟩



-- ∀ con →
-- sólo se vale una implicación
example : (∀ x, p x → q x) → ((∀ x, p x) → (∀ x, q x)) := by
  intro h h' a
  exact (h a) (h' a)



-- ∀ con ∨
-- sólo se vale una implicación
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h a
  rcases h with hp | hq
  . left
    exact hp a
  . right
    exact hq a



-- ∃ con ∧ y una fórmula donde x no ocurre
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro ⟨a, h⟩
    constructor
    . use a
      exact h.1
    . exact h.2
  . intro ⟨⟨a, hp⟩, hr⟩
    exact ⟨a, ⟨hp, hr⟩⟩



-- ∃ con ∨
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro ⟨a, hpq⟩
    rcases hpq with hp | hq
    . left
      exact ⟨a, hp⟩
    . right
      exact ⟨a, hq⟩
  . intro h
    rcases h with ⟨a, hp⟩ | ⟨a, hq⟩
    . exact ⟨a, Or.inl hp⟩
    . use a
      right
      assumption

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h ⟨a, hnp⟩
    exact hnp (h a)
  . intro h a
    push_neg at h
    exact h a

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro ⟨a, hp⟩ h
    exact (h a) hp
  . intro h
    push_neg at h
    assumption

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro h a
    push_neg at h
    exact h a
  . intro h ⟨a, hp⟩
    exact (h a) hp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . intro h
    push_neg at h
    assumption
  . intro ⟨a, hnp⟩ h
    exact hnp (h a)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h ⟨a, hp⟩
    exact (h a) hp
  . intro h a hp
    exact h ⟨a, hp⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro ⟨b, hpr⟩ h
    exact hpr (h b)
  . intro h
    by_contra h'
    push_neg at h'
    have : ∀ (x : α), p x := by
      intro b
      exact (h' b).1
    exact (h' a).2 (h this)

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro ⟨b, hrp⟩ hr
    use b
    exact hrp hr
  . intro h
    by_contra h'
    push_neg at h'
    have : ∃ x, p x := h (h' a).1
    rcases this with ⟨b, hp⟩
    exact (h' b).2 hp


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    by_contra h'
    push_neg at h'
    rcases h'.1 with ⟨a, hnp⟩
    rcases (h a) with hp | hr
    . exact hnp hp
    . exact h'.2 hr
  . intro h a
    rcases h with hp | _
    . left
      exact hp a
    . right
      assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h hr a
    exact (h a) hr
  . intro h a hr
    exact (h hr) a

end fol
