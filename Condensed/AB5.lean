import Condensed.Equivalence
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Category.GroupCat.Abelian
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Condensed.Abelian
import Mathlib.CategoryTheory.Limits.Filtered

/-!

# `Condensed Ab` has AB5

- Recall AB3, AB4, AB5:
[https://stacks.math.columbia.edu/tag/079A](Stacks 079A)

- How should we formulate this in lean?

- Review proof that `Condensed Ab` has AB5 (on the board) 

- Start the skeleton for this assertion in Lean.

-/

universe v u

open CategoryTheory Limits

#check CondensedAb.{u}

variable (A B : Type u) 
  [Category.{v} A] [Abelian A]
  [Category.{v} B] [Abelian B]
  (F : A ⥤ B) [F.Additive]

-- AB3

example [HasColimits A] : HasCoproducts A := inferInstance

example [HasCoproducts A] : HasColimits A := 
  by exact has_colimits_of_hasCoequalizers_and_coproducts

noncomputable
example [PreservesFiniteLimits F] (X Y : A) 
    (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F := 
  inferInstance

noncomputable
example [∀ {X Y : A} (f : X ⟶ Y), 
    PreservesLimit (parallelPair f 0) F] : PreservesFiniteLimits F :=
  by exact Functor.preservesFiniteLimitsOfPreservesKernels F

noncomputable
example [∀ {X Y : A} (f : X ⟶ Y), 
    PreservesColimit (parallelPair f 0) F] : PreservesFiniteColimits F :=
  by exact Functor.preservesFiniteColimitsOfPreservesCokernels F

abbrev AB4 (A : Type u) [Category.{v} A] 
    [HasCoproducts A] := 
    ∀ (α : Type v), PreservesFiniteLimits 
      (colim : (Discrete α ⥤ A) ⥤ A)

example [HasCoproducts A] 
  [∀ α : Type v, PreservesFiniteLimits 
    (colim (J := Discrete α) (C := A))] : AB4 A := inferInstance

abbrev AB5 (A : Type u) [Category.{v} A] 
    [HasFilteredColimitsOfSize.{v} A] :=
    ∀ (J : Type v) [SmallCategory J] [IsFiltered J],
      PreservesFiniteLimits (colim (J := J) (C := A))

noncomputable
example (A : Type u) [Category.{v} A] 
    (J : Type v) [SmallCategory J] [HasColimitsOfShape J A] :
    PreservesColimits (colim (J := J) (C := A)) := 
  colimConstAdj.leftAdjointPreservesColimits



-- Condensed Mathematics

#check CondensedAb

noncomputable section

example : Abelian CondensedAb := inferInstance

example : Sheaf (coherentTopology ExtrDisc.{u}) AddCommGroupCat.{u+1} ≌ CondensedAb := 
  Condensed.ExtrDiscCompHaus.equivalence _

set_option pp.universes true
example : Abelian (Sheaf (coherentTopology ExtrDisc.{u}) AddCommGroupCat.{u+1}) := 
  letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  CategoryTheory.sheafIsAbelian

example : 
  Functor.Additive 
    (Condensed.ExtrDiscCompHaus.equivalence AddCommGroupCat).inverse := by
  constructor
  aesop_cat



























/-


open CategoryTheory Limits

universe v u

example : HasColimits (CondensedAb.{u}) := 
  letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
    AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  show HasColimits (Sheaf _ _) from inferInstance
  --CategoryTheory.Sheaf.instHasColimitsSheafInstCategorySheaf 

example : HasLimits (CondensedAb.{u}) := 
  --letI : PreservesLimits (forget AddCommGroupCat.{u+1}) :=
  --  AddCommGroupCat.forgetPreservesLimits.{u+1, u+1}
  show HasLimits (Sheaf _ _) from inferInstance

noncomputable
example : Sheaf (coherentTopology ExtrDisc.{u}) AddCommGroupCat.{u+1} ≌ CondensedAb.{u} := 
  Condensed.ExtrDiscCompHaus.equivalence AddCommGroupCat.{u+1}

example (A : Type u) [Category.{v} A] [Abelian A] 
    [HasCoproducts A] : HasColimits A := 
  has_colimits_of_hasCoequalizers_and_coproducts

noncomputable
example (J : Type v) [SmallCategory J] (C D : Type u) 
    [Category.{v} C] [Category.{v} D] (e : C ≌ D)
    [HasColimits C] [HasColimits D]
    [PreservesLimits (colim : (J ⥤ C) ⥤ C)] :
    PreservesLimits (colim : (J ⥤ D) ⥤ D) := 
  let e₁ : (J ⥤ D) ≌ (J ⥤ C) := sorry 
  let e₂ : e₁.functor ⋙ colim ⋙ e.functor ≅ colim := sorry
  preservesLimitsOfNatIso e₂

noncomputable
example (J : Type v) [SmallCategory J] 
    (C : Type u) [Category.{v} C]
    [HasColimitsOfShape J C] :
    PreservesColimits (colim : (J ⥤ C) ⥤ C) := 
  Adjunction.leftAdjointPreservesColimits colimConstAdj   

noncomputable
example {A B : Type u} [Category.{v} A] [Category.{v} B] 
    (F : A ⥤ B) [Abelian A] [Abelian B] [F.Additive] 
    [∀ {X Y : A} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F] : 
    PreservesFiniteLimits F := 
  Functor.preservesFiniteLimitsOfPreservesKernels F

noncomputable
example {A B : Type u} [Category.{v} A] [Category.{v} B] 
    (F : A ⥤ B) [Abelian A] [Abelian B] [F.Additive] 
    [∀ {X Y : A} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F] : 
    PreservesFiniteColimits F := 
  Functor.preservesFiniteColimitsOfPreservesCokernels F

-/