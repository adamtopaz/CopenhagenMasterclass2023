import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Condensed.CartesianClosed

/-
The category of condensed Abelian groups admits a closed symmetric monoidal structure inherited from the closed symmetric monoidal structure on the category of Abelian groups.

We shall use Day's reflection principle:
https://ncatlab.org/nlab/show/Day%27s+reflection+theorem
-/

universe u

open CategoryTheory

section Day

variable {C D : Type u} [Category C] [Category D] [MonoidalCategory D]

open List in
/--
(Day) Let R:C→D be a fully faithful functor with left adjoint L:D→C, and suppose given a symmetric monoidal closed structure on D with tensor ⊗ and internal hom [−,−]. Then for objects c of C and d,d′ of D, the following are equivalent:

    u[d,Rc]:[d,Rc]→RL[d,Rc] is an isomorphism;

    [u,1]:[RLd,Rc]→[d,Rc] is an isomorphism;

    L(u⊗1):L(d⊗d′)→L(RLd⊗d′) is an isomorphism;

    L(u⊗u):L(d⊗d′)→L(RLd⊗RLd′) is an isomorphism.
-/
theorem day_reflection (R : C ⥤ D) [Full R] [Faithful R] [IsRightAdjoint R] :
    TFAE [
      True,
      True
    ] := by sorry

end Day




#check Condensed.{u} Ab.{u}

namespace CondensedAb

namespace MonoidalCategory

-- /-- (implementation) tensor product of R-modules -/
-- def tensorObj (M N : Condensed Ab) : Condensed Ab :=
--   ModuleCat.of R (M ⊗[R] N)
-- #align Module.monoidal_category.tensor_obj ModuleCat.MonoidalCategory.tensorObj


end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (Condensed.{u} Ab.{u}) where
  tensorObj F G := _
  tensorHom f g := _
  tensor_id X Y := _
  tensor_comp := _
  tensorUnit' := _
  associator := _
  associator_naturality := _
  leftUnitor := _
  leftUnitor_naturality := _
  rightUnitor := _
  rightUnitor_naturality := _
  pentagon := _
  triangle := _

end CondensedAb

/-
We don't have the closed symmetric monoidal structure on the category of Abelian groups, but only on R-modules for any ring R.
-/

