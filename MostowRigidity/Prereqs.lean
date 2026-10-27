import Mathlib.Data.Set.Basic

namespace MostowRigidity

theorem inter_subset_union {α : Type*} (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  intro x hx          -- hx : x ∈ A ∩ B
  left                -- the goal x ∈ A ∪ B means x ∈ A ∨ x ∈ B; pick x ∈ A
  exact hx.1          -- hx.1 is the "x ∈ A" half of hx

end MostowRigidity