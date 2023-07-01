import Mathlib.Condensed.Abelian

/-

## Functors from topological spaces to condensed sets.

This file constructs condensed sets from compact hausdorff, and also from arbitrary,
topological spaces. Initially we make terms of type `Condensed.{u} (Type u)`, but this is
a small category (the type of all objects and the type of each hom set is `Type (u+1)`). 
Dagur would rather have a large category, so we either need a functor
`Condensed.{u} (Type u) ⥤ Condensed.{u} (Type max u v)`
(and then we set `v = u + 1`) or a functor
`Condensed.{max u v} (Type w) ⥤ Condensed.{u} (Type w)`.
We supply these too.

## TODO

Lots of proofs that the sheaf axiom is satisfied!

-/
open CategoryTheory

/-

## Small category version (no ulifts) 

#synth LargeCategory.{u} CompHaus.{u}
#synth LargeCategory.{u} TopCat.{u}
#synth SmallCategory.{u+1} (Condensed.{u} (Type u)) 

-/
universe v u


-- This is the simplest thing, but typically not what people want
/-- The natural functor (Yoneda) from compact hausdorff spaces to a small category of condensed sets. -/
def CompHaus.toCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) where
  obj X := {
    val := yoneda.obj X 
    cond := sorry -- sheaf condition
  }
  map f := ⟨yoneda.map f⟩

-- This is the second simplest thing
/-- The natural functor (Yoneda) from topological spaces to a small category of condensed sets. -/
def TopCat.toCondensed' : TopCat.{u} ⥤ Condensed.{u} (Type u) where
  obj X := {
    val := (compHausToTop : CompHaus.{u} ⥤ TopCat.{u}).op ⋙ 
      (yoneda.obj X : TopCat.{u}ᵒᵖ ⥤ Type u)
    cond := sorry -- sheaf condition
  }
  map (f) := { val := whiskerLeft _ <| yoneda.map f }

/-

I just spent 20 minutes trying to prove
example : CompHaus.toCondensed' ≅ CompHausToTop ⋙ TopCat.toCondensed'
I hate `autoImplicit`.

-/

example : CompHaus.toCondensed' = compHausToTop ⋙ TopCat.toCondensed' := rfl

/-

## Universe changing shenannigans

-/

universe x

example : Condensed.{x} (Type u) ⥤ Condensed.{x} (Type max u v) where
  obj X := {
    val := X.val ⋙ uliftFunctor.{v,u}
    cond := by
      sorry -- uliftFunctor preserves sheafiness
  }
  map f := {
    val := {
      app := fun S ↦ uliftFunctor.map (f.val.app S)
      naturality := by
        intros S T φ
        dsimp only [Functor.comp_obj, Functor.comp_map]
        rw [← Functor.map_comp, f.val.naturality φ, Functor.map_comp]
    }
  }


def ULift.homeomorph (X : Type u) [TopologicalSpace X] : X ≃ₜ ULift.{v} X where
  toFun := ULift.up
  invFun := ULift.down
  left_inv := ULift.down_up.{u, v}
  right_inv := ULift.up_down
  continuous_toFun := continuous_uLift_up
  continuous_invFun := continuous_uLift_down

instance ULift.compactSpace (X : Type u) [TopologicalSpace X] [CompactSpace X] : CompactSpace (ULift.{v} X) :=
  Homeomorph.compactSpace (ULift.homeomorph X)

instance ULift.t2Space (X : Type u) [TopologicalSpace X] [T2Space X] : T2Space (ULift.{v} X) := 
  Homeomorph.t2Space (ULift.homeomorph X)

def CompHaus.ulift' : CompHaus.{u} ⥤ CompHaus.{max u v} where
  obj X := {
    toTop := TopCat.of $ ULift.{v} (X.toTop)
    is_compact := ULift.compactSpace X
    is_hausdorff := ULift.t2Space X
  }
  map f := by
    cases' f with f hf
    exact ⟨fun ⟨x⟩ ↦ ⟨f x⟩, by continuity⟩

universe v₁ u₁ 

def Condensed.uDesc {A : Type u₁} [Category.{v₁} A] : Condensed.{max u v} A ⥤ Condensed.{u} A where
  obj X := {
    val := CompHaus.ulift'.op.{v} ⋙ X.val
    cond := sorry -- sheaf condition
  }
  map f := ⟨whiskerLeft _ f.val⟩

def TopCat.toCondensed : TopCat.{u+1} ⥤ Condensed.{u} (Type (u+1)) :=
  TopCat.toCondensed' ⋙ Condensed.uDesc.{u+1,u}

def CompHaus.toCondensed : CompHaus.{u+1} ⥤ Condensed.{u} (Type (u+1)) :=
  CompHaus.toCondensed' ⋙ Condensed.uDesc.{u+1,u}

example : CompHaus.toCondensed = compHausToTop ⋙ TopCat.toCondensed := rfl
