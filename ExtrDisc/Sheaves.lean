import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Limits.Shapes.Types

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]

variable {X : C} (R : Presieve X)

def isPullbackPresieve : Prop :=
  ∀ fg : (ΣY, { f : Y ⟶ X // R f }) × ΣZ, { g : Z ⟶ X // R g },
  HasPullback fg.1.2.1 fg.2.2.1

end Presieve

end CategoryTheory