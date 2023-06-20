import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Polynomial.Eval

/-!
Let's show that taking polynomials over a ring is functor `RingCat ⥤ RingCat`.
-/

noncomputable section -- the default implementation of polynomials is noncomputable

/-!
Hints:
* use `polynomial.map_ring_hom`
-/

def RingCat.polynomial : RingCat ⥤ RingCat :=
sorry

def CommRingCat.polynomial : CommRingCat ⥤ CommRingCat :=
sorry

open CategoryTheory

def commutes :
  (forget₂ CommRingCat RingCat) ⋙ RingCat.polynomial ≅ 
  CommRingCat.polynomial ⋙ (forget₂ CommRingCat RingCat) :=
-- Hint: You can do this in two lines, ≤ 33 columns!
sorry


/-!
There are some further hints in
`hints/category_theory/exercise2/`
-/

end section
