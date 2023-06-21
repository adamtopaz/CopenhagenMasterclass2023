import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

open CategoryTheory

namespace ExtrDisc

universe u

lemma epi_iff_surjective {X Y : ExtrDisc.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := 
  sorry

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc.{u}} 
    (X : α → ExtrDisc.{u})
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

end ExtrDisc