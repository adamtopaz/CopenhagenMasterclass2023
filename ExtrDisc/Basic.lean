/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.ExtremallyDisconnected
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected sets.

## Overview

This file defines the type `ExtrDisc` of all extremally (note: not "extremely"!) 
disconnected spaces, and gives it the structure of a large category.

The Lean implementation: a term of type `ExtrDisc` is a pair, considering of 
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`, 
in the sense of category theory (i.e., such that morphisms out of the object 
can be lifted along epimorphisms).

This file defines the type of all extremally disconnected spaces, gives it the
structure of a large category, and proves some basic observations about this
category and various functors from it.

## Main definitions

* `ExtrDisc` : the category of extremally disconnected spaces.
* `ExtrDisc.toCompHaus` : the forgetful functor `ExtrDisc ⥤ CompHaus` from extremally disconnected
  spaces to compact Hausdorff spaces
* `ExtrDisc.toProfinite` : the functor from extremally disconnected spaces to profinite spaces.

## TODO

The following proofs need to be filled in: 

* Gleason's theorem: a compact Hausdorff space is extrDisc if and 
  only if it is projective (one direction is in `mathlib4`).
* If `X` is extremally disconnected then it is totally disconnected.
* The forgetful functor `toCompHaus : ExtrDisc ⥤ CompHaus` is full and faithful.
* The functor `toProfinite : ExtrDisc ⥤ Profinite` is full and faithful.
* The category of extremally disconnected spaces has arbitrary coproducts.

-/
universe u

open CategoryTheory

/-- `ExtrDisc` is the category of extremally disconnected spaces. -/
structure ExtrDisc where
  compHaus : CompHaus.{u}
  [extrDisc : ExtremallyDisconnected compHaus]

-- the fields of the structure don't need docstrings
attribute [nolint docBlame] ExtrDisc.compHaus ExtrDisc.extrDisc

namespace ExtrDisc

/-- Extremally disconnected spaces form a large category. -/
instance : LargeCategory ExtrDisc.{u} :=  
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from extremally disconnected spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is full. -/
instance : Full toCompHaus where
  preimage := @fun _ _ h => h
  witness := @fun _ _ f => refl f

/-- The forgetful functor `ExtrDisc ⥤ CompHaus` is faithful. -/
instance : Faithful toCompHaus where
  map_injective := by
    intro X Y a b h
    simp only [inducedFunctor_obj, inducedFunctor_map] at h
    exact h

/-- Extremally disconnected spaces are a concrete category. -/
instance : ConcreteCategory ExtrDisc where
  forget := toCompHaus ⋙ forget _

instance : CoeSort ExtrDisc.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : ExtrDisc.{u}} : FunLike (X ⟶ Y) X (fun _ => Y) := ConcreteCategory.funLike

/-- Extremally disconnected spaces are topological spaces. -/
instance (X : ExtrDisc.{u}) : TopologicalSpace X := 
  show TopologicalSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are compact. -/
instance (X : ExtrDisc.{u}) : CompactSpace X := 
  show CompactSpace X.compHaus from inferInstance

/-- Extremally disconnected spaces are Hausdorff. -/
instance (X : ExtrDisc.{u}) : T2Space X := 
  show T2Space X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : ExtremallyDisconnected X := 
  X.2

/-- Extremally disconnected spaces are totally disconnected. -/
instance (X : ExtrDisc.{u}) : TotallySeparatedSpace X := 
{ isTotallySeparated_univ := by 
    intro x _ y _ hxy 
    obtain ⟨U, V, hUV⟩ := T2Space.t2 x y hxy
    use closure U 
    use (closure U)ᶜ 
    refine ⟨ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_, 
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩ 
    simp only [Set.mem_compl_iff]
    rw [mem_closure_iff] 
    push_neg 
    use V 
    refine' ⟨hUV.2.1,hUV.2.2.2.1,_⟩
    rw [Set.nonempty_iff_ne_empty]
    simp only [not_not]
    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]
    exact hUV.2.2.2.2 }

instance (X : ExtrDisc.{u}) : TotallyDisconnectedSpace X := inferInstance

/-- The functor from extremally disconnected spaces to profinite spaces. -/
@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := { 
    toCompHaus := X.compHaus, 
    IsTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from extremally disconnected spaces to profinite spaces is full. -/
instance : Full toProfinite := sorry
instance : Faithful toProfinite := sorry

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus := 
  rfl

-- TODO: Gleason's theorem.
instance (X : ExtrDisc) : Projective X.compHaus := sorry

end ExtrDisc

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is an extremally disconnected space
  equipped with an epimorphism down to `X`. It is a "constructive" witness to the
  fact that `CompHaus` has enough projectives.  -/
noncomputable
def presentation (X : CompHaus) : ExtrDisc where
  compHaus := (projectivePresentation X).p
  extrDisc := sorry 

/-- The morphism from `presentation X` to `X`. -/
noncomputable
def presentationπ (X : CompHaus) : X.presentation.compHaus ⟶ X :=   
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
instance epiPresentπ (X : CompHaus) : Epi X.presentationπ :=   
  (projectivePresentation X).epi

/-- 

               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
              
If `Z` is extremally disconnected, X, Y are compact Hausdorff, if `f : X ⟶ Y` is an epi and `e : Z ⟶ Y` is
arbitrary, then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`. 
-/
noncomputable
def lift {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] : Z.compHaus ⟶ X :=
  Projective.factorThru e f 

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

/-- The category of extremally disconnected spaces has arbitrary coproducts. -/
instance : Limits.HasCoproducts ExtrDisc.{u} := sorry

/-- The category of extremally disconnected spaces has finite coproducts. -/
instance : Limits.HasFiniteCoproducts ExtrDisc.{u} := 
  Limits.hasFiniteCoproducts_of_hasCoproducts.{u} ExtrDisc.{u}

end CompHaus
