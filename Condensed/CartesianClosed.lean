/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Closed.Ideal
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheafification


/-!

Condensed sets form a cartesian closed category

-/

universe u

open CategoryTheory Limits





/--
The category of condensed abelian groups, defined as sheaves of types over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedSet := Condensed.{u} (Type (u + 1))
-- notation "Presheaf " C " , " D => Cᵒᵖ ⥤ D


section A
#check CategoryTheory.instCartesianClosedFunctorTypeTypesCategoryInstHasFiniteProductsFunctorTypeTypesCategory
end A

open GrothendieckTopology
-- def Hom_pre (X Y : CompHaus.{u}ᵒᵖ ⥤ (Type (u + 1))) :
--   CompHaus.{u}ᵒᵖ ⥤ (Type (u + 1)) where
--     obj := fun Z => X.obj Z ⟶ Y.obj Z
--     map := _
--     map_id := _
--     map_comp := _
-- def Hom (X Y : CondensedSet.{u}) : CondensedSet.{u} := sheafify (coherentTopology CompHaus.{u}) (Hom_pre _)


instance : HasFiniteProducts (CompHaus.{u}ᵒᵖ ⥤ Type (u + 1)) := by infer_instance
instance : Category.{u} (CompHaus.{u}ᵒᵖ) := by infer_instance

def AsSmall_Functor_equiv : (CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) ≌ (AsSmall.{u+1} CompHaus.{u}ᵒᵖ ⥤ Type (u+1)) :=
Equivalence.congrLeft.{u, u + 1, u + 1, u + 1, u + 1, u + 2}
  AsSmall.equiv.{u, u + 1, u + 1}

noncomputable
instance : CartesianClosed (AsSmall.{u+1} CompHaus.{u}ᵒᵖ ⥤ Type (u + 1)) :=
CategoryTheory.instCartesianClosedFunctorTypeTypesCategoryInstHasFiniteProductsFunctorTypeTypesCategory

universe v₁ v₂
instance {C D : Type v₁} [Category C] [Category D] (e : C ⥤ D) [IsEquivalence e] :
  Reflective e := ⟨⟩
--huh fails second time
-- instance {C D : Type v₁} [Category C] [Category D] (e : C ⥤ D) [IsEquivalence e] :
--   Reflective e := ⟨⟩
instance {C D : Type v₁} [Category C] [Category D] (e : C ⥤ D) [IsEquivalence e] :
  EssSurj e := Equivalence.essSurj_of_equivalence _
-- TODO maybe reflective should just have an inst
-- instance {C D : Type v₁} [Category C] [Category D] (e : C ≌ D) :
--   Reflective e.inverse := ⟨⟩
noncomputable
instance {C D : Type v₁} [Category C] [Category D] (e : C ≌ D) :
  Reflective e.inverse := ⟨⟩

/-- Any essentially surjective, viewed as a subcategory is an exponential ideal. -/
instance {C D : Type _} [Category C] [Category D] [HasFiniteProducts D] [CartesianClosed D]
  (e : C ⥤ D) [EssSurj e] : ExponentialIdeal e :=
  ExponentialIdeal.mk' _ fun _ _ => EssSurj.mem_essImage _
-- This generalizes the following mathlib lemma
instance {C : Type _} [Category C] [HasFiniteProducts C] [CartesianClosed C] :
  ExponentialIdeal (𝟭 C) := inferInstance
  -- ExponentialIdeal.mk' _ fun _ _ => ⟨_, ⟨Iso.refl _⟩⟩
-- TODO no duplicate TC argument linter?
-- instance {C : Type _} [Category C] [Category C] [HasFiniteProducts C] [CartesianClosed C] :
-- #lint

-- this works now too
instance {C D : Type _} [Category C] [Category D] [HasFiniteProducts D] [CartesianClosed D]
  (e : C ≌ D) :
ExponentialIdeal e.functor :=
  inferInstance

noncomputable
instance : CartesianClosed (CompHaus.{u}ᵒᵖ ⥤ Type (u + 1)) :=
  cartesianClosedOfReflective AsSmall_Functor_equiv.functor



universe w v

variable {C : Type u} [Category.{v} C]

variable {D : Type w} [Category.{max v u} D] [Limits.HasFiniteProducts D]

variable {J : GrothendieckTopology C}
instance : Full (sheafToPresheaf J D) := inferInstance
instance : Faithful (sheafToPresheaf J D) := inferInstance
-- Generalize this in mathlib?
instance Condensed.hasFiniteProductsSheaf : HasFiniteProducts (Sheaf J D) where
  out j := { has_limit := fun F => by infer_instance }
variable [ConcreteCategory D] [PreservesLimits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : Cover J X), HasMultiequalizer (Cover.index S P)]
  [∀ (X : C), HasColimitsOfShape (Cover J X)ᵒᵖ D]
  [(X : C) → PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget D)]
  [ReflectsIsomorphisms (forget D)]
-- noncomputable
-- instance : IsRightAdjoint (sheafToPresheaf J D) := sheafToPresheafIsRightAdjoint
-- _ _
noncomputable
instance : Reflective (sheafToPresheaf J D) where
-- noncomputable
-- instance : IsRightAdjoint (sheafToPresheaf J (Type _)) := sheafToPresheafIsRightAdjoint
-- _ _

namespace CondensedSet

noncomputable instance HasFiniteProducts :
    HasFiniteProducts CondensedSet.{u} :=
Condensed.hasFiniteProductsSheaf -- TODO generalize


lemma foo :autoParam a s = a:=by rfl
-- noncomputable instance :
-- PreservesLimitsOfShape (Discrete WalkingPair)
--     (leftAdjoint (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))) :=
-- by
--   constructor -- TODO output weird
noncomputable instance :
PreservesLimitsOfShape (Discrete WalkingPair)
    (leftAdjoint (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))) :=
⟨by
  intros K
  show PreservesLimit K (presheafToSheaf _ _)
  exact PreservesLimitsOfShape.preservesLimit⟩
  -- convert_to {K : _} → PreservesLimit K (leftAdjoint (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))))


-- noncomputable instance :
--   ExponentialIdeal (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))) := inferInstance
noncomputable instance CartesianClosed :
    CategoryTheory.CartesianClosed CondensedSet.{u} :=
cartesianClosedOfReflective (sheafToPresheaf _ (Type (u + 1)))

#print axioms CartesianClosed
