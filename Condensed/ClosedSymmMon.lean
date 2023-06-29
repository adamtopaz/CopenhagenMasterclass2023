import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Condensed.CartesianClosed
import Mathlib.Condensed.Abelian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib

-- import Mathlib.Tactic.Widget.CommDiag
-- import ProofWidgets.Component.GoalTypePanel
-- -- with_panel_widgets [ProofWidgets.GoalTypePanel]

-- TODO
set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory

/-
The category of condensed Abelian groups admits a closed symmetric monoidal structure inherited from the closed symmetric monoidal structure on the category of Abelian groups.

We shall use Day's reflection principle:
https://ncatlab.org/nlab/show/Day%27s+reflection+theorem
-/

/-! TODO: This section, in particular the section `MonoidalClosed` herein,
should go at the bottom of
`Mathlib/CategoryTheory/Monoidal/FunctorCategory.lean` -/
namespace CategoryTheory.Monoidal

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

section MonoidalClosed

open CategoryTheory.MonoidalClosed

variable [MonoidalClosed.{v₂} D]

/-- When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functorCategoryMonoidalClosed : MonoidalClosed (C ⥤ D) where
  closed F := by
    sorry

end MonoidalClosed
end CategoryTheory.Monoidal


section Ab.Monoidal

open MonoidalCategory

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D]  (e : C ≌ D)

/-- Transport a braided monoidal structure along an equivalence of (plain) categories -/
@[simps!]
def Braided.transport [BraidedCategory C] (e : C ≌ D) :
    letI : MonoidalCategory D := Monoidal.transport e
    BraidedCategory D :=
  letI : MonoidalCategory D := Monoidal.transport e
  { -- The braiding on `D` is simply `e` applied to the braiding iso on `C`
    braiding := fun X Y =>  e.functor.mapIso <| β_ (e.inverse.obj X) (e.inverse.obj Y)
    braiding_naturality := fun f g => by
      dsimp only [Monoidal.transport_tensorObj, Monoidal.transport_tensorHom, Functor.mapIso_hom]
      rw [← Functor.map_comp e.functor, ← Functor.map_comp e.functor]
      rw [BraidedCategory.braiding_naturality (e.inverse.map f) (e.inverse.map g)]
    hexagon_forward := sorry
    hexagon_reverse := sorry }

/-- Transport a symmetric monoidal structure along an equivalence of (plain) categories. -/
@[simps!]
def Symmetric.transport [SymmetricCategory C] (e : C ≌ D) :
    letI : MonoidalCategory D := Monoidal.transport e
    SymmetricCategory.{v₂} D :=
  letI : MonoidalCategory D := Monoidal.transport e
  letI : BraidedCategory D := Braided.transport e
  { symmetry := fun X Y => by
      dsimp
      rw [← Functor.map_comp e.functor]
      rw [SymmetricCategory.symmetry (e.inverse.obj X) (e.inverse.obj Y)]
      simp
  }

/-- Transport a symmetric monoidal structure along an equivalence of (plain) categories. -/
@[simps!]
def MonoidalClosed.transport [MonoidalClosed C] (e : C ≌ D) :
    letI : MonoidalCategory D := Monoidal.transport e
    MonoidalClosed.{v₂} D :=
  letI : MonoidalCategory D := Monoidal.transport e
  { closed := sorry
  }

lemma moduleCat_int_equiv_ab : ModuleCat.{u} (ULift.{u} ℤ) ≌ Ab.{u} := sorry

/-- Transport relevant instances from `ℤ`-Modules to `Ab`. -/

instance : MonoidalCategory Ab.{u} := Monoidal.transport moduleCat_int_equiv_ab
instance : SymmetricCategory Ab.{u} := Symmetric.transport moduleCat_int_equiv_ab
instance : MonoidalClosed Ab.{u} := MonoidalClosed.transport moduleCat_int_equiv_ab

/-
The category of presheaves underlying condensed abelian groups
is symmetric monoidal.
-/
example : SymmetricCategory (Cᵒᵖ ⥤ Ab.{u}) := inferInstance

#synth MonoidalCategory (Cᵒᵖ ⥤ Ab.{u})
#synth MonoidalClosed (Cᵒᵖ ⥤ Ab.{u})


end Ab.Monoidal


-- #check Condensed.{u, u, u}

-- section Day

-- variable {C D : Type u} [Category C] [Category D] [MonoidalCategory D]

-- #check MonoidalCategory

-- open List in
-- /--
-- (Day) Let R:C→D be a fully faithful functor with left adjoint L:D→C, and suppose given a symmetric monoidal closed structure on D with tensor ⊗ and internal hom [−,−]. Then for objects c of C and d,d′ of D, the following are equivalent:

--     u[d,Rc]:[d,Rc]→RL[d,Rc] is an isomorphism;

--     [u,1]:[RLd,Rc]→[d,Rc] is an isomorphism;

--     L(u⊗1):L(d⊗d′)→L(RLd⊗d′) is an isomorphism;

--     L(u⊗u):L(d⊗d′)→L(RLd⊗RLd′) is an isomorphism.
-- -/
-- theorem day_reflection (R : C ⥤ D) [Full R] [Faithful R] [IsRightAdjoint R] :
--     TFAE [
--       R.leftAdjoint.obj (u ⊗ 𝟙_)
--     ] := by sorry

-- end Day

-- #check Condensed.{u} Ab.{u}

namespace CondensedAb


-- namespace MonoidalCategory

-- /-- (implementation) tensor product of R-modules -/
-- def tensorObj (M N : Condensed Ab) : Condensed Ab :=
--   ModuleCat.of R (M ⊗[R] N)
-- #align Module.monoidal_category.tensor_obj ModuleCat.MonoidalCategory.tensorObj


-- end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (CondensedAb.{u}) := sorry
-- where
  -- tensorObj F G := _
  -- tensorHom f g := _
  -- tensor_id X Y := _
  -- tensor_comp := _
  -- tensorUnit' := _
  -- associator := _
  -- associator_naturality := _
  -- leftUnitor := _
  -- leftUnitor_naturality := _
  -- rightUnitor := _
  -- rightUnitor_naturality := _
  -- pentagon := _
  -- triangle := _

instance symmetricCategory : SymmetricCategory CondensedAb.{u} := sorry

instance monodialClosed : MonoidalClosed CondensedAb.{u} := sorry

end CondensedAb

/-
We don't have the closed symmetric monoidal structure on the category of Abelian groups, but only on R-modules for any ring R.
-/

