/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Topology.Category.CompHaus.Projective
import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected sets.

## Overview

This file defines the type `ExtrDisc` of all extremally (note: not "extremely"!) 
disconnected types, and gives it the structure of a large category.

The Lean implementation: a term of type `ExtrDisc` is a pair, considering of 
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the term is projective in `CompHaus`, in the sense of category theory.

This file defines the type of all extremally disconnected sets, gives it the
structure of a large category

## Main definitions

* `ExtrDisc` : the category of extremally disconnected spaces.

## TODO

Fill in the proof that if `X` is extremally disconnected then it
is totally disconnected.

-/
universe u

open CategoryTheory

/-- `ExtrDisc` is the category of extremally disconnected spaces. -/
structure ExtrDisc where
  compHaus : CompHaus.{u}
  [projective : Projective compHaus]

-- the fields of the structure don't need docstrings
attribute [nolint docBlame] ExtrDisc.compHaus ExtrDisc.projective

namespace ExtrDisc

instance : LargeCategory ExtrDisc.{u} :=  
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

/-- The (forgetful) functor from extremally disconnected spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

instance : Full toCompHaus := sorry
instance : Faithful toCompHaus := sorry

instance : ConcreteCategory ExtrDisc where
  forget := toCompHaus ⋙ forget _

instance : CoeSort ExtrDisc.{u} (Type u) := ConcreteCategory.hasCoeToSort _
instance {X Y : ExtrDisc.{u}} : FunLike (X ⟶ Y) X (fun _ => Y) := ConcreteCategory.funLike

instance (X : ExtrDisc.{u}) : TopologicalSpace X := 
  show TopologicalSpace X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : CompactSpace X := 
  show CompactSpace X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : T2Space X := 
  show T2Space X.compHaus from inferInstance

instance (X : ExtrDisc.{u}) : TotallyDisconnectedSpace X := 
  sorry

/-- The functor from extremally disconnected spaces to profinite spaces. -/
@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := { 
    toCompHaus := X.compHaus, 
    IsTotallyDisconnected := show TotallyDisconnectedSpace X from inferInstance }
  map f := f

/-- The functor from extremally disconnecred spaces to profinite spaces is full. -/
instance : Full toProfinite := sorry
instance : Faithful toProfinite := sorry

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus := 
  rfl

instance (X : ExtrDisc) : Projective X.compHaus := X.projective

end ExtrDisc

namespace CompHaus

noncomputable
def presentation (X : CompHaus) : ExtrDisc where
  compHaus := (projectivePresentation X).p

noncomputable
def presentationπ (X : CompHaus) : X.presentation.compHaus ⟶ X :=   
  (projectivePresentation X).f

noncomputable
instance epiPresentπ (X : CompHaus) : Epi X.presentationπ :=   
  (projectivePresentation X).epi

noncomputable
def lift {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] : Z.compHaus ⟶ X :=
  Projective.factorThru e f 

@[simp, reassoc]
lemma lift_lifts {X Y : CompHaus} {Z : ExtrDisc} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

instance : Limits.HasCoproducts ExtrDisc.{u} := sorry

instance : Limits.HasFiniteCoproducts ExtrDisc.{u} := 
  Limits.hasFiniteCoproducts_of_hasCoproducts.{u} ExtrDisc.{u}

end CompHaus
