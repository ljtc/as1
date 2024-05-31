-- Lógica de proposiciones

/-
El objetivo es formalizar la deducciones lógicas que hemos hecho en el
curso. Principalmente haremos una demostración de las tautologías.
-/

section LProp
variable (p q r : Prop)

--algo simple
example : p → p := by
  intro hp
  assumption

--conmutatividad de ∧ y ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  . intro ⟨hq, hp⟩
    exact ⟨hp, hq⟩

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro h
    rcases h with hp | hq
    . right; assumption
    . left; assumption
  . rintro (hq | hp)
    . right; assumption
    . left; assumption

--asociatividad de ∧ y ∨
example : p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := by
  constructor
  . intro ⟨hp, ⟨hq, hr⟩⟩
    exact ⟨⟨hp, hq⟩, hr⟩
  . intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩

example : p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := by
  constructor
  . rintro (hp | (hq | hr))
    . left; left; assumption
    . left; right; assumption
    . right; assumption
  . rintro ((hp | hq) | hr)
    . left; assumption
    . right; left; assumption
    . right; right; assumption

--∧ y ∨ son idempotentes
example : p ∧ p ↔ p := by
  constructor
  . intro h
    exact h.1
  . intro hp
    exact ⟨hp, hp⟩

example : p ∨ p ↔ p := by
  constructor
  . rintro (hp | hp) <;> assumption
  . intro hp
    left; assumption

--absorciones
example : p ∧ (p ∨ q) ↔ p := by
  constructor
  . rintro ⟨hp, (h | _)⟩ <;> assumption
  . intro hp
    constructor
    . assumption
    . left; assumption

example : p ∨ (p ∧ q) ↔ p := by
  constructor
  . rintro (hp | ⟨hp, _⟩) <;> assumption
  . intro hp
    left
    assumption

--distributividad
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . rintro ⟨hp, (hq | hr)⟩
    . left
      exact ⟨hp, hq⟩
    . right
      exact ⟨hp, hr⟩
  . rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    . constructor
      . assumption
      . left; assumption
    . constructor
      . assumption
      . right; assumption


end LProp
