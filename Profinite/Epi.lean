import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

open CategoryTheory Limits

namespace Profinite

universe u

variable {X Y B : Profinite.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/--
The pullback of two morphisms `f,g` in `Profinite`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def pullback : Profinite.{u} :=
  let set := { xy : X × Y | f xy.fst = g xy.snd }
  have : CompactSpace set := by
    rw [← isCompact_iff_compactSpace]
    apply IsClosed.isCompact
    exact isClosed_eq (f.continuous.comp continuous_fst) (g.continuous.comp continuous_snd)
  Profinite.of set

/--
The projection from the pullback to the first component.
-/
def pullback.fst : pullback f g ⟶ X where
  toFun := fun ⟨⟨x,_⟩,_⟩ => x
  continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val

/--
The projection from the pullback to the second component.
-/
def pullback.snd : pullback f g ⟶ Y where
  toFun := fun ⟨⟨_,y⟩,_⟩ => y
  continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : Profinite.{u}}
    (X : α → Profinite.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b
    ] := by
  sorry
  -- WIP Jon & Sina

end Profinite
