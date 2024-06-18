-- Lógica de proposiciones

/-
Comportamiento estructural de la lógica de proposiciones
("Álgebra de Boole")
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

--distributividades
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

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . rintro (hp | ⟨hq, hr⟩)
    . constructor
      repeat' left; assumption
    . constructor
      repeat' right; assumption
  . rintro ⟨(hp | hq), (hp | hr)⟩
    . left; assumption
    . left; assumption
    . left; assumption
    . right; exact ⟨hq, hr⟩

-- complemento
example : p ∧ ¬p ↔ False := by
  constructor
  . intro ⟨hp, hnp⟩
    exact hnp hp
  . intro h
    exfalso
    assumption

--esta parte del complemento tiene implicaciones fuertes
--acerca del tipo de lógica que vamos a trabajar
example : p ∨ ¬p ↔ True := by
  constructor
  . intro _
    trivial
  . intro _
    by_cases h : p
    . left; assumption
    . right; assumption




/-
Métodos de demostración
-/

--contrapuesta
example : (p → q) ↔ (¬q → ¬p) := by
  constructor
  . intro h hnq hp
    exact hnq (h hp)
  . intro h hp
    by_cases hq : q
    . assumption
    . exfalso
      exact (h hq) hp

--contradicción
example : ((p → q) ∧ (p → ¬q)) → ¬p := by
  intro ⟨hpq, hpnq⟩ hp
  exact (hpnq hp) (hpq hp)


end LProp
