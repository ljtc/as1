import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

section

variable {α β : Type*}
variable (f : α → β)
variable (s₁ s₂ : Set α)
variable (t₁ t₂ : Set β)

open Function
open Set


example (h : s₁ ⊆ s₂) : f '' s₁ ⊆ f '' s₂ := by
  intro y ⟨x, ⟨x1, h'⟩⟩
  use x; constructor
  . apply h x1
  . assumption


example : f '' (s₁ ∪ s₂) = f '' s₁ ∪ f '' s₂ := by
  ext y; constructor
  . rintro ⟨x, ⟨x1 | x2, h⟩⟩
    . left; use x
    . right; use x
  . rw [mem_union]
    rintro (⟨x, ⟨x1, h1⟩⟩ | ⟨x, ⟨x2, h2⟩⟩)
    . use x; constructor
      . left; assumption
      . assumption
    . use x; constructor
      . right; assumption
      . assumption


example : f '' (s₁ ∩ s₂) ⊆ f '' s₁ ∩ f '' s₂ := by
  intro y ⟨x, ⟨⟨x1, x2⟩, h⟩⟩
  constructor
  repeat' use x


example (h : t₁ ⊆ t₂) : f ⁻¹' t₁ ⊆ f ⁻¹' t₂ := by
  intro x
  simp only [mem_preimage]
  intro h'
  apply h
  assumption


example : f ⁻¹' (t₁ ∪ t₂) = f ⁻¹' t₁ ∪ f ⁻¹' t₂ := by
  ext x
  simp only [mem_preimage, mem_union]


example : f ⁻¹' (t₁ ∩ t₂) = f ⁻¹' t₁ ∩ f ⁻¹' t₂ := by
  ext x
  simp only [mem_preimage, mem_inter_iff]


example : f ⁻¹' ⊤ = ⊤ := by
  ext x;
  rw [mem_preimage]
  constructor
  repeat' intro _; trivial


example : f ⁻¹' (⊤ \ t₁) = ⊤ \ f ⁻¹' t₁ := by
  ext x
  simp only [mem_preimage, mem_diff]
  constructor
  . intro ⟨_, h⟩
    constructor
    . trivial
    . assumption
  . intro ⟨_, h⟩
    constructor
    . trivial
    . assumption

example : f ⁻¹' (t₁ᶜ) = (f ⁻¹' t₁)ᶜ := by
  ext x
  rw [mem_preimage, mem_compl_iff, mem_compl_iff]
  constructor
  . intro h h'
    rw [mem_preimage] at h'
    contradiction
  . intro h h'
    rw [<-mem_preimage] at h'
    contradiction

example : f ⁻¹' (t₁ᶜ) = (f ⁻¹' t₁)ᶜ := by
  ext x
  simp only [mem_preimage, mem_compl_iff]


example : f '' (f ⁻¹' t₁) ⊆ t₁ := by
  intro y ⟨x, ⟨h, h'⟩⟩
  rw [mem_preimage] at h
  rw [h'] at h
  assumption


example : s₁ ⊆ f ⁻¹' (f '' s₁) := by
  intro x xs
  rw [mem_preimage, mem_image]
  use x



end
