import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Condensed.CartesianClosed
import Mathlib.Condensed.Abelian
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib

-- These imports let you display commutative diagrams.
import Mathlib.Tactic.Widget.CommDiag
import ProofWidgets.Component.GoalTypePanel

-- Just put the following inside any proof
-- by
--   with_panel_widgets [ProofWidgets.GoalTypePanel]
--   · tactic block goes here


noncomputable section

universe u v

open CategoryTheory

/-
The category of condensed Abelian groups admits a closed symmetric monoidal structure inherited from the closed symmetric monoidal structure on the category of Abelian groups.

We shall use Day's reflection principle:
https://ncatlab.org/nlab/show/Day%27s+reflection+theorem
-/

namespace CategoryTheory.Monoidal

/-! Apparently we dont have the result in the library that the Functor category
is closed monoidal if the target is. So we prove it in this section.

TODO: This section, in particular the section `MonoidalClosed` herein,
should go at the bottom of
`Mathlib/CategoryTheory/Monoidal/FunctorCategory.lean` -/
section MonoidalClosed

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open CategoryTheory.MonoidalClosed

variable [MonoidalClosed.{v₂} D]

/-- When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
instance functorCategoryMonoidalClosed : MonoidalClosed (C ⥤ D) where
  closed F := by
    sorry -- TODO: Data in form of a left-adjoint to (· ⊗ ·)

end MonoidalClosed



/-! In this section we transport all variations of monoidal structures along an
isomorphism. The library only knows `Monoidal.transport` so far , which transports
the monoidal structure itself. -/
section transport

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
    hexagon_forward:= fun X Y Z => by
      dsimp
      with_panel_widgets [ProofWidgets.GoalTypePanel]
        sorry
    hexagon_reverse := fun X Y Z => by
      dsimp
      with_panel_widgets [ProofWidgets.GoalTypePanel]
        sorry
  }

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
  { closed := sorry -- TODO: data in form of a left adjoint to `(· ⊗ ·)`
  }

end transport



/-! In this section we proof that `Ab` is isomorphic to the cateogry of `ℤ`-modules
and transport the closed symmetric monoidal structure over from there. -/
section Ab

open MonoidalCategory

lemma moduleCat_int_equiv_ab : ModuleCat.{u} (ULift.{u} ℤ) ≌ Ab.{u} := sorry -- TODO: data

/-- The monoidal structure on `Ab` is induced by the one on `ℤ`-modules. -/
instance : MonoidalCategory Ab := Monoidal.transport moduleCat_int_equiv_ab

/-- The symmetric monoidal structure on `Ab` is induced by the one on `ℤ`-modules. -/
instance : SymmetricCategory Ab := Symmetric.transport moduleCat_int_equiv_ab

/-- The closed monoidal structure on `Ab` is induced by the one on `ℤ`-modules. -/
instance : MonoidalClosed Ab := MonoidalClosed.transport moduleCat_int_equiv_ab


/- We get the closed symmetric monoidal structure for presheaves `(Cᵒᵖ ⥤ Ab.{u})` for free -/

variable {C : Type _} [Category C] [MonoidalCategory C]

/-
The category of presheaves underlying condensed abelian groups
is symmetric monoidal.
-/
example : SymmetricCategory (Cᵒᵖ ⥤ Ab) := inferInstance

#synth MonoidalCategory (Cᵒᵖ ⥤ Ab)
#synth MonoidalClosed (Cᵒᵖ ⥤ Ab)

end Ab



/-! In this section we construct the closed symmetric monoidal structure on
sheaves `(Cᵒᵖ ⥤ Ab)`, which are exactly condensed abelian groups.

We work with sheaves here because we hope to generalise the results to a more generic
target than `Ab`. -/
section Condensed

open MonoidalCategory GrothendieckTopology Limits

-- TODO: Add this instance!
variable [PreservesLimits (forget Ab.{u+1})]

/-
Comment: we want `Category.{u, u+1} C` and `Ab.{u+1}`.
The objects of `C`, the objects of `Ab`, and the hom-sets of `Ab` are all
proper classes while the hom-set of `C` should be a set.
TODO: @Sina Is this correct?
-/
variable {C : Type (u+1)} [c : Category.{u} C] (J : GrothendieckTopology C)

variable (G H : Sheaf J Ab.{u+1})

def helper_1 (F G : Cᵒᵖ ⥤ Ab.{u+1}) :
    (presheafToSheaf J Ab).obj (tensorObj (sheafify J F) G) ≅
    (presheafToSheaf J Ab).obj (tensorObj F G) :=
  sorry -- TODO: data


def helper_2 (F G : Cᵒᵖ ⥤ Ab.{u+1}) :
    (presheafToSheaf J Ab).obj (tensorObj F (sheafify J G)) ≅
    (presheafToSheaf J Ab).obj (tensorObj F G) :=
  sorry -- TODO: data

-- NOTE: Before proving any  sorrys in here one probably needs to fill the sorries in
-- `helper_1` and `helper_2`
/-- Sheaves admit a monoidal structure given by `X ⊗ Y := S(X ⊗ Y)` where `S` is the
"sheafification" and the tensor product is taken of underlying presheaves. -/
instance Sheaf.monodialCategory :
    MonoidalCategory <| Sheaf J Ab.{u+1} where
  /- The monoidal structure is given by sheafification to the one gor presheaves. -/
  tensorObj F G := (presheafToSheaf J Ab.{u+1}).obj <| tensorObj F.val G.val
  tensorHom f g := (presheafToSheaf J Ab.{u+1}).map <| tensorHom f.val g.val
  tensor_id := sorry -- by aesop_cat
  tensor_comp := sorry -- by aesop_cat
  tensorUnit' := (presheafToSheaf J Ab.{u+1}).obj tensorUnit'
  associator F G H :=
    helper_1 J (tensorObj F.val G.val) H.val ≪≫
    (presheafToSheaf J Ab.{u+1}).mapIso (α_ F.val G.val H.val) ≪≫
    (helper_2 J F.val (tensorObj G.val H.val)).symm
  associator_naturality f g h := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  leftUnitor F :=
    helper_1 J tensorUnit' F.val ≪≫ (presheafToSheaf J Ab.{u+1}).mapIso (leftUnitor F.val) ≪≫
    (sheafificationIso F).symm
  leftUnitor_naturality f := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  rightUnitor F :=
    helper_2 J F.val tensorUnit' ≪≫ (presheafToSheaf J Ab.{u+1}).mapIso (rightUnitor F.val) ≪≫
    (sheafificationIso F).symm
  rightUnitor_naturality F := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  pentagon := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  triangle := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry

open BraidedCategory

/-- The braiding on sheaves is the sheafification of the braiding of presheaves -/
instance : BraidedCategory <| Sheaf J Ab.{u+1} where
  braiding F G := (presheafToSheaf J Ab.{u+1}).mapIso (braiding F.val G.val)
  braiding_naturality f g := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  hexagon_forward F G H := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry
  hexagon_reverse F G H := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry

instance : SymmetricCategory <| Sheaf J Ab.{u+1} where
  symmetry F G := by
    dsimp
    with_panel_widgets [ProofWidgets.GoalTypePanel]
      sorry

instance : MonoidalClosed <| Sheaf J Ab.{u+1} where
  closed F := sorry -- TODO: contains data in form of a left-adjoint to `(· ⊗ ·)`

/-!
Now for the closed symmetric monoidal structure on `Condensed Ab` it
seems that lean wants us to unfold the definition of `Condensed`
-/

instance : MonoidalCategory <| Condensed.{u} Ab.{u+1} := by
  dsimp [Condensed]
  infer_instance

instance : BraidedCategory <| Condensed.{u} Ab.{u+1} := by
  dsimp [Condensed]
  infer_instance

instance : SymmetricCategory <| Condensed.{u} Ab.{u+1} := by
  dsimp [Condensed]
  infer_instance

instance : MonoidalClosed <| Condensed.{u} Ab.{u+1} := by
  dsimp [Condensed]
  infer_instance

/-! Checks that we have the closed symmetric monoidal structure on `CondensedAb` -/

#synth MonoidalCategory (CondensedAb.{u})
#synth BraidedCategory (CondensedAb.{u})
#synth SymmetricCategory (CondensedAb.{u})
#synth MonoidalClosed (CondensedAb.{u})

end Condensed

end CategoryTheory.Monoidal



/-! The following is a start on Day's reflection, but not sure if we need it now… -/

-- section Day
--
-- variable {C D : Type u} [Category C] [Category D] [MonoidalCategory D]
--
-- #check MonoidalCategory
--
-- open List in
-- /--
-- (Day) Let R:C→D be a fully faithful functor with left adjoint L:D→C, and suppose given a symmetric monoidal closed structure on D with tensor ⊗ and internal hom [−,−]. Then for objects c of C and d,d′ of D, the following are equivalent:
--
--     u[d,Rc]:[d,Rc]→RL[d,Rc] is an isomorphism;
--
--     [u,1]:[RLd,Rc]→[d,Rc] is an isomorphism;
--
--     L(u⊗1):L(d⊗d′)→L(RLd⊗d′) is an isomorphism;
--
--     L(u⊗u):L(d⊗d′)→L(RLd⊗RLd′) is an isomorphism.
-- -/
-- theorem day_reflection (R : C ⥤ D) [Full R] [Faithful R] [IsRightAdjoint R] :
--     TFAE [
--       R.leftAdjoint.obj (u ⊗ 𝟙_)
--     ] := by sorry
--
-- end Day

