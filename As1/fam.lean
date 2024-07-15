import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Use
import Mathlib.Tactic.PushNeg

variable (I α : Type*)
variable (B C : Set α)
variable (A : I → Set α)

section Fam
open Set

--Definiciones con los nombres de L∃∀N
#check mem_iUnion
#check mem_iInter


-- ∪ distribuye a ⋂ (lógica clásica)
example : B ∪ ⋂ i : I, A i = ⋂ i, B ∪ A i := by
  ext x
  simp only [mem_iInter, mem_union]
  constructor
  . rintro (xb | h)
    . intro i
      left; assumption
    . intro i
      right; apply h
  . intro h
    by_cases xb : x ∈ B
    . left; assumption
    . right
      intro i
      rcases h i with xb1 | xai
      . contradiction
      . assumption

-- ∩ distribuye a ⋃
example : B ∩ ⋃ i : I, A i = ⋃ i, B ∩ A i := by
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  constructor
  . intro ⟨xb, ⟨i, xai⟩⟩
    use i
  . intro ⟨i, ⟨xb, xai⟩⟩
    constructor
    . assumption
    . use i

-- ley de De Morgan generalizada 1
example : (⋃ i : I, A i)ᶜ = ⋂ i, (A i)ᶜ := by
  ext x
  simp only [mem_compl_iff, mem_iInter]
  constructor
  . intro h i xai
    have : x ∈ ⋃ i, A i := by
      rw [mem_iUnion]
      use i
    contradiction
  . intro h xu
    rw [mem_iUnion] at xu
    obtain ⟨i, xai⟩ := xu
    apply h i
    assumption

-- ley de De Morgan generalizada 2 (lógica clásica)
example : (⋂ i : I, A i)ᶜ = ⋃ i, (A i)ᶜ := by
  ext x
  simp only [mem_compl_iff, mem_iUnion, mem_iInter]
  constructor
  . intro h
    push_neg at h
    assumption
  . intro h1 h2
    obtain ⟨i, xnai⟩ := h1
    apply xnai
    apply h2


end Fam
