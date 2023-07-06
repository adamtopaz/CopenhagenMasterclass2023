import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts
set_option autoImplicit false
/-!
We prove that biproducts (direct sums) are preserved by any preadditive functor.

This result is not in mathlib, so full marks for the exercise are only
achievable if you contribute to a pull request! :-)
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe u v
-- porting note: was Preadditive but stupid structure below breaks it!
variable {C : Type u} [Category C] [CategoryTheory.Preadditive C]
variable {D : Type v} [Category D] [CategoryTheory.Preadditive D]

/-!
In fact, no one has gotten around to defining preadditive functors,
so I'll help you out by doing that first.
-/

structure Functor.Preadditive (F : C ⥤ D) : Prop :=
(map_zero : ∀ X Y, F.map (0 : X ⟶ Y) = 0)
(map_add : ∀ {X Y} (f g : X ⟶ Y), F.map (f + g) = F.map f + F.map g)

variable [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def Functor.Preadditive.preserves_biproducts (F : C ⥤ D) (P : F.Preadditive) (X Y : C) :
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y where
    hom := (F.map biprod.fst) ≫ biprod.inl + F.map biprod.snd ≫ biprod.inr
    inv := biprod.fst ≫ F.map biprod.inl + biprod.snd ≫ F.map biprod.inr
    hom_inv_id := by
      simp
      sorry
      done
    inv_hom_id := by
      simp
      sorry
      done

/-!
There are some further hints in
`hints/category_theory/exercise5/`
-/

-- Challenge problem:
-- In fact one could prove a better result,
-- not requiring chosen biproducts in D,
-- asserting that `F.obj (X ⊞ Y)` is a biproduct of `F.obj X` and `F.obj Y`.


end CategoryTheory

end section