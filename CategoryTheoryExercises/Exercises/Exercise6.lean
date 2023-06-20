import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
set_option autoImplicit false in

/-!
Thanks to Markus Himmel for suggesting this question.
-/

open CategoryTheory
open Limits

/-!
Let C be a category, X and Y be objects and f : X ⟶ Y be a morphism. Show that f is an epimorphism
if and only if the diagram

X --f--→ Y
|        |
f        𝟙
|        |
↓        ↓
Y --𝟙--→ Y

is a pushout.
-/

universe u

variables {C : Type u} [Category C]

def pushout_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
  IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
-- Hint: you can start a proof with `fapply pushout_cocone.is_colimit.mk`
-- to save a little bit of work over just building a `is_colimit` structure directly.
sorry

theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : IsColimit (PushoutCocone.mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
-- Hint: You can use `pushout_cocone.mk` to conveniently construct a cocone over a cospan.
-- Hint: use `is_colim.desc` to construct the map from a colimit cocone to any other cocone.
-- Hint: use `is_colim.fac` to show that this map gives a factorisation of the cocone maps through the colimit cocone.
-- Hint: if `simp` won't correctly simplify `𝟙 X ≫ f`, try `dsimp, simp`.
sorry

/-!
There are some further hints in
`hints/category_theory/exercise6/`
-/

