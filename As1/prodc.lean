import Mathlib.Data.Set.Lattice

section prodcart
variable (α : Type)
variable (A B C D : Set α)
variable (a b : α)

open Set

/-
En L∀∃N, el producto cartesiano de conjuntos se denota con ×ˢ.
La notación sin el superíndice está reservada para el producto de tipos
-/

--la definición de cuando alguien es elemento de un producto
#check mem_prod

example : ((A ∩ B) ×ˢ (C ∩ D)) = (A ×ˢ C) ∩ (B ×ˢ D) := by
  ext x --x tiene dos coordenadas x.1 y x.2
  simp only [mem_prod, mem_inter_iff]
  constructor
  . intro ⟨⟨x1a, x1b⟩, ⟨x2c, x2d⟩⟩
    constructor <;> (try constructor)
    assumption'
  . intro ⟨⟨x1a, x2c⟩, ⟨x1b, x2d⟩⟩
    constructor <;> (try constructor)
    assumption'


--la misma proposición pero demostrada como en clase
example : ((A ∩ B) ×ˢ (C ∩ D)) = (A ×ˢ C) ∩ (B ×ˢ D) := by
  ext x
  calc x ∈ (A ∩ B) ×ˢ (C ∩ D)
    _ ↔ (x.1 ∈ A ∩ B) ∧ (x.2 ∈ C ∩ D)              := by simp only [mem_prod]
    _ ↔ (x.1 ∈ A ∧ x.1 ∈ B) ∧ (x.2 ∈ C ∧ x.2 ∈ D)  := by simp only [mem_inter_iff]
    _ ↔ x.1 ∈ A ∧  (x.1 ∈ B ∧ (x.2 ∈ C ∧ x.2 ∈ D)) := by rw [and_assoc]
    _ ↔ x.1 ∈ A ∧ ((x.1 ∈ B ∧ x.2 ∈ C) ∧ x.2 ∈ D)  := by rw [and_assoc]
    _ ↔ x.1 ∈ A ∧ ((x.2 ∈ C ∧ x.1 ∈ B) ∧ x.2 ∈ D)  := by simp only [and_comm]
    _ ↔ (x.1 ∈ A ∧ x.2 ∈ C) ∧ (x.1 ∈ B ∧ x.2 ∈ D)  := by simp only [and_assoc]
    _ ↔ (x ∈ A ×ˢ C) ∧ (x ∈ B ×ˢ D)                := by simp only [mem_prod]
    _ ↔ x ∈ (A ×ˢ C) ∩ (B ×ˢ D)                    := by rw [mem_inter_iff]


end prodcart
