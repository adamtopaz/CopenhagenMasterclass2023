import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Yoneda
set_option autoImplicit false

open CategoryTheory
open Opposite

universe u

variable {C : Type u} [Category C]

/-! Hint 1:
`yoneda` is set up so that `(yoneda.obj X).obj (op Y) = (Y ⟶ X)`
(we need to write `op Y` to explicitly move `Y` to the opposite category).
-/

/-! Hint 2:
If you have a natural isomorphism `α : F ≅ G`, you can access
* the forward natural transformation as `α.hom`
* the backwards natural transformation as `α.inv`
* the component at `Z`, as an isomorphism `F.obj Z ≅ G.obj X` as `α.app X`.
-/

def iso_of_hom_iso (X Y : C) (h : yoneda.obj X ≅ yoneda.obj Y) : X ≅ Y :=
sorry

/-!
There are some further hints in
`hints/category_theory/exercise1/`
-/



