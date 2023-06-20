import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Polynomial.AlgebraMap

open CategoryTheory
open Opposite
open Polynomial

noncomputable section

/-!
We show that the forgetful functor `CommRing ⥤ Type` is (co)representable.

There are a sequence of hints available in
`hints/category_theory/hintX.lean`, for `X = 1,2,3,4`.
-/

/-!
One bonus hint before we start, showing you how to obtain the
ring homomorphism from `ℤ` into any commutative ring.
-/
example (R : CommRingCat) : ℤ →+* R :=
by exact Int.castRingHom ↑R

/-!
Also useful may be the functions
-/
#check Polynomial.eval₂
#check Polynomial.eval₂RingHom

/-!
The actual exercise!
-/
def CommRing_forget_representable : Σ (R : CommRingCat), (forget CommRingCat) ≅ coyoneda.obj (op R) :=
⟨CommRingCat.of ℤ[X], {
  hom := 
  { app := fun R r ↦ Polynomial.eval₂RingHom (Int.castRingHom R) r, 
    naturality := by
      intros A B φ
      ext a
      apply Polynomial.ringHom_ext
      · aesop
      · simp
        apply congr_arg φ
        simp
      done
  }, 
  inv :=
  { app := fun R (r : ℤ[X] →+* R) ↦ r Polynomial.X,
    naturality := by
      intros A B φ
      ext α
      exact rfl 
  }, 
  hom_inv_id := by
    aesop_cat
  inv_hom_id := by
    ext A (φ : ℤ[X] →+* A)
    apply Polynomial.ringHom_ext
    · aesop
    · aesop
}⟩

/-!
There are some further hints in
`hints/category_theory/exercise4/`
-/

/-
If you get an error message
```
synthesized type class instance is not definitionally equal to expression inferred by typing rules
```
while solving this exercise, see hint4.lean.
-/

end section
