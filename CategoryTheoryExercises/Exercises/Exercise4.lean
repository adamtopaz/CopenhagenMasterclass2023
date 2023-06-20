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

-- Because we'll be working with `polynomial ℤ`, which is in `Type 0`,
-- we just restrict to that universe for this exercise.
set_option quotPrecheck false in
notation "CommRingCat" => CommRingCat.{0}

/-!
One bonus hint before we start, showing you how to obtain the
ring homomorphism from `ℤ` into any commutative ring.
-/
example (R : CommRingCat) : ℤ →+* R :=
by exact?

/-!
Also useful may be the functions
-/
#print Polynomial.eval₂
#print Polynomial.eval₂RingHom

/-!
The actual exercise!
-/
def CommRing_forget_representable : Σ (R : CommRingCat), (forget CommRingCat) ≅ coyoneda.obj (op R) :=
sorry

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
