import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : Profinite.{u}} 
    (X : α → Profinite.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b 
    ] := by
  tfae_have 1 → 2 
  · intro ; infer_instance 
  tfae_have 2 → 3
  · sorry 
  tfae_have 3 → 1
  · sorry
  tfae_finish
