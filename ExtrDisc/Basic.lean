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
  projective : Projective compHaus

-- the fields of the structure don't need docstrings
attribute [nolint docBlame] ExtrDisc.compHaus ExtrDisc.projective

namespace ExtrDisc

instance : LargeCategory ExtrDisc.{u} :=  
  show Category (InducedCategory CompHaus (·.compHaus)) from inferInstance

instance : CoeSort ExtrDisc.{u} (Type u) where
  coe X := X.compHaus

example (X : ExtrDisc.{u}) : TopologicalSpace X := inferInstance
example (X : ExtrDisc.{u}) : CompactSpace X := inferInstance
example (X : ExtrDisc.{u}) : T2Space X := inferInstance

instance (X : ExtrDisc.{u}) : TotallyDisconnectedSpace X := sorry

/-- The functor from extremally disconnected spaces to profinite spaces. -/
@[simps]
def toProfinite : ExtrDisc.{u} ⥤ Profinite.{u} where
  obj X := { toCompHaus := X.compHaus }
  map f := f

/-- The (forgetful) functor from extremally disconnected spaces to compact Hausdorff spaces. -/
@[simps!]
def toCompHaus : ExtrDisc.{u} ⥤ CompHaus.{u} :=
  inducedFunctor _

example : toProfinite ⋙ profiniteToCompHaus = toCompHaus := 
  rfl

end ExtrDisc
