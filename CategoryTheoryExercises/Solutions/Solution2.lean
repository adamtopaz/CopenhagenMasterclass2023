import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.Polynomial.Eval

/-!
Let's show that taking polynomials over a ring is a functor `RingCat ⥤ RingCat`.
-/

noncomputable section -- the default implementation of polynomials is noncomputable

/-!
Hints:
* use `Polynomial.mapRingHom`
-/

def RingCat.polynomial : RingCat ⥤ RingCat where
  obj := fun R ↦ RingCat.of (Polynomial R)
  map := Polynomial.mapRingHom
  -- porting note: both proofs below were `by intros; ext; simp`
  map_id := fun _ ↦ RingHom.ext $ fun _ ↦ Polynomial.map_id
  map_comp := fun φ ψ ↦ RingHom.ext $ fun f ↦ (Polynomial.map_map φ ψ f).symm

def CommRingCat.polynomial : CommRingCat ⥤ CommRingCat where
  obj := fun R ↦ CommRingCat.of (Polynomial R)
  map := Polynomial.mapRingHom
  map_id := fun _ ↦ RingHom.ext $ fun _ ↦ Polynomial.map_id
  map_comp := fun φ ψ ↦ RingHom.ext $ fun f ↦ (Polynomial.map_map φ ψ f).symm

open CategoryTheory

def commutes :
  (forget₂ CommRingCat RingCat) ⋙ RingCat.polynomial ≅ 
  CommRingCat.polynomial ⋙ (forget₂ CommRingCat RingCat) where
    hom := eqToHom rfl
    inv := eqToHom rfl

/-!
There are some further hints in
`hints/category_theory/exercise2/`
-/

end section
