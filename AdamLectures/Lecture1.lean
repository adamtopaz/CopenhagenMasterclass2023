import Mathlib.Condensed.Basic
import Mathlib.Topology.ExtremallyDisconnected

import FindWithGpt
import ExtrDisc.Basic

/-!

Goals for this talk:
- Recall the definition of a condensed object in a category `C`: three definitions.
- Explain how `Condensed.{u} C` is defined in `mathlib4`.

-/

section section1 -- Some topological categories

/-!
# Three categories

- `CompHaus` = compact Hausdorff spaces.
- `Profinite` = compact Hausdorff totally disconnected spaces.
- `ExtrDisc` =  compact Hausdorff extremally disconnected spaces 
  (the closure of any open is open).

Theorem (Gleason): 
A compact Hausdorff space is extremally disconnected 
if and only if 
it is projective in the category of compact Hausdorff spaces.
-/

#check CompHaus
#check Profinite
#check ExtrDisc

example (X : CompHaus) : TopologicalSpace X := inferInstance
example (X : CompHaus) : CompactSpace X := inferInstance
example (X : CompHaus) : T2Space X := inferInstance

example (X : Profinite) : TopologicalSpace X := inferInstance
example (X : Profinite) : CompactSpace X := inferInstance
example (X : Profinite) : TotallyDisconnectedSpace X := inferInstance

example (X : ExtrDisc) : TopologicalSpace X := inferInstance
example (X : ExtrDisc) : CompactSpace X := inferInstance
example (X : ExtrDisc) : ExtremallyDisconnected X := inferInstance

end section1 

section section2 -- Their category structure

open CategoryTheory

/-!

The category structure on all three of these categories is obtained by 
viewing them as full subcategories of `TopCat`.

Morphisms are *by definition* continuous maps

-/

instance : LargeCategory CompHaus := inferInstance
instance : LargeCategory Profinite := inferInstance
instance : LargeCategory ExtrDisc := inferInstance

example : Profinite ⥤ CompHaus := profiniteToCompHaus
example : ExtrDisc ⥤ CompHaus := ExtrDisc.toCompHaus 
example : ExtrDisc ⥤ Profinite := ExtrDisc.toProfinite -- uses a `sorry`.

example : 
    ExtrDisc.toProfinite ⋙ profiniteToCompHaus = ExtrDisc.toCompHaus := 
  rfl

example (X Y : CompHaus) : (X ⟶ Y) = C(X,Y) := rfl
example (X Y : Profinite) : (X ⟶ Y) = C(X,Y) := rfl
example (X Y : ExtrDisc) : (X ⟶ Y) = C(X,Y) := rfl

end section2

section section3

open CategoryTheory

/-!

# Effective Epimorphisms and the coherent topology

TODO: 
- Recall the definitions.
- `Precoherent`
- In `CompHaus`, `EffectiveEpiFamily` iff jointly surjective.

-/

#check EffectiveEpi

end section3

section section4

/-!

# Condensed Objects

-/

end section4