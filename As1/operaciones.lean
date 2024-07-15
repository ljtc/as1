import Mathlib.Data.Set.Lattice

section ConOp
open Set

variable (α : Type)
variable (A B C : Set α)

--Algunas definiciones, con la nomenclatura de L∃∀N
#check mem_setOf
#check subset_def
#check ext

#check inter_def
#check mem_inter_iff

#check union_def
#check mem_union

#check mem_diff
#check mem_compl_iff
---

-- ∩ es un ínfimo:
-- cota inferior
example : A ∩ B ⊆ A := by
  intro x ⟨xa, _⟩
  assumption

example : A ∩ B ⊆ B := by
  intro x ⟨_, xb⟩
  assumption

-- la cota inferior más grande
example (h1 : C ⊆ A) (h2 : C ⊆ B) : C ⊆ A ∩ B := by
  intro x xc
  rw [mem_inter_iff]
  constructor
  . apply h1; assumption
  . apply h2 xc

-- ∪ es un supremo
-- cota superior
example : A ⊆ A ∪ B := by
  intro x xa
  rw [mem_union]
  left
  assumption

example : B ⊆ A ∪ B := by
  intro x xb
  right
  assumption

-- la más chica de las cotas superiores
example (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  rintro x (xa | xb)
  . apply h1 xa
  . apply h2 xb
---

-- ∅ está contenido en todos
example : ∅ ⊆ A := by
  intro x xe
  contradiction

-- equivalencia de ⊆
example : A ⊆ B ↔ A ∩ B = A := by
  constructor
  . intro h
    ext x
    constructor
    . intro ⟨xa, _⟩
      assumption
    . intro xa
      constructor
      . assumption
      . apply h; assumption
  . intro h x xa
    rw [<-h] at xa
    obtain ⟨_, xb⟩ := xa
    assumption

-- otra equivalencia de ⊆
example : A ⊆ B ↔ A ∪ B = B := by
  constructor
  . intro h
    ext x
    constructor
    . rintro (xa | xb)
      . apply h xa
      . assumption
    . intro
      right; assumption
  . intro h x xa
    rw [<-h]
    left; assumption

#check mem_compl

-- Una tercera equivalencia de ⊆ (lógica clásica)
example : A ⊆ B ↔ A ∩ Bᶜ = ∅ := by
  constructor
  . intro h
    ext x
    constructor
    . intro ⟨xa, xbc⟩
      rw [mem_compl_iff] at xbc
      exact xbc (h xa)
    . intro
      contradiction
  . intro h x xa
    by_cases xb : x ∈ B
    . assumption
    . have xint : x ∈ A ∩ Bᶜ := by
        constructor <;> assumption
      rw [h] at xint
      contradiction


-- ∩ es idempotente
example : A ∩ A = A := by
  ext x
  constructor
  . intro ⟨_, _⟩
    assumption
  . intro xa
    exact ⟨xa, xa⟩

-- ∪ es idempotente
example : A ∪ A = A := by
  ext x
  constructor
  . rintro (xa | xa) <;> assumption
  . intro xa
    right; assumption


-- ∩ es conmutativa
example : A ∩ B = B ∩ A := by
  ext x
  rw [mem_inter_iff, mem_inter_iff]
  constructor
  . intro ⟨xa, xb⟩
    constructor <;> assumption
  . intro ⟨xb, xa⟩
    constructor
    assumption'

-- ∪ es conmutativa
example : A ∪ B = B ∪ A := by
  ext x
  simp only [mem_union]
  constructor
  . rintro (xa | xb)
    . right; assumption
    . left; assumption
  . rintro (xb | xa)
    . right; assumption
    . left; assumption

-- ∩ es asociativa
example : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp only [mem_inter_iff]
  constructor
  . intro ⟨⟨xa, xb⟩, xc⟩
    exact ⟨xa, ⟨xb, xc⟩⟩
  . intro ⟨xa, ⟨xb, xc⟩⟩
    exact ⟨⟨xa, xb⟩, xc⟩

-- ∪ es asociativa
example : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  simp only [mem_union]
  constructor
  . rintro ((xa | xb) | xc)
    . left; assumption
    . right; left; assumption
    . right; right; assumption
  . rintro (xa | (xb | xc))
    . left; left; assumption
    . left; right; assumption
    . right; assumption

-- ∪ distribuye a ∩
example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp only [mem_union,mem_inter_iff]
  constructor
  . rintro (xa | ⟨xb, xc⟩)
    . constructor
      repeat' left; assumption
    . constructor
      repeat' right; assumption
  . rintro ⟨(xa1 | xb), (xa2 | xc)⟩
    . left; assumption
    . left; assumption
    . left; assumption
    . right; exact ⟨xb, xc⟩

-- ∩ distribuye a ∪
example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp only [mem_inter_iff, mem_union]
  constructor
  . rintro ⟨xa, (xb | xc)⟩
    . left; exact ⟨xa, xb⟩
    . right; exact ⟨xa, xc⟩
  . rintro (⟨xa, xb⟩ | ⟨xa, xc⟩)
    . constructor
      . assumption
      . left; assumption
    . constructor
      . assumption
      . right; assumption

-- absorción 1
example : A ∩ (B ∪ A) = A := by
  ext x
  simp only [mem_inter_iff, mem_union]
  constructor
  . rintro ⟨xa1, (_ | xa2)⟩
    repeat' assumption
  . intro xa
    constructor
    . assumption
    . right; assumption

-- absorción 2
example : A ∪ (B ∩ A) = A := by
  ext x
  simp only [mem_union, mem_inter_iff]
  constructor
  . rintro (xa1 | ⟨_, xa2⟩)
    repeat' assumption
  . intro xa
    left; assumption

-- ley de De Morgan 1 (lógica clásica)
example : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  . simp only [mem_compl_iff, mem_union]
    intro h
    by_cases xa : x ∈ A
    . by_cases xb : x ∈ B
      . have xint : x ∈ A ∩ B := by
          constructor <;> assumption
        contradiction
      . right; assumption
    . left; assumption
  . simp only [mem_compl_iff, mem_union]
    rintro (xna | xnb)
    . intro h
      obtain ⟨xa, _⟩ := h
      contradiction
    . intro h
      obtain ⟨_, xb⟩ := h
      contradiction

-- ley de De Morgan 2
example : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp only [mem_compl_iff, mem_inter_iff]
  constructor
  . intro h
    constructor
    . intro xa
      have : x ∈ A ∪ B := by
        left; assumption
      contradiction
    . intro xb
      have : x ∈ A ∪ B := by
        right; assumption
      contradiction
  . intro ⟨xna, xnb⟩ h
    rcases h with xa | xb <;> contradiction




end ConOp
