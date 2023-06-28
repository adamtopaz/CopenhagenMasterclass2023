import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Limits.Shapes.Types

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

variable {C : Type u₁} [Category.{v₁} C]

variable {X : C} (R : Presieve X)

def isPullbackPresieve : Prop :=
  ∀ Y Z (f : Y ⟶ X) (_ : R f) (g : Z ⟶ X) (_ : R g),
  -- ∀ fg : (ΣY, { f : Y ⟶ X // R f }) × ΣZ, { g : Z ⟶ X // R g },
  HasPullback f g 


end CategoryTheory