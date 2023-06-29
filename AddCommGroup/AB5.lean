import Condensed.AB5
import Mathlib.CategoryTheory.Limits.ConcreteCategory

instance : CategoryTheory.Limits.HasColimits AddCommGroupCat :=
inferInstance

open CategoryTheory Limits

universe u v

instance (C : Type u) [Category.{v} C] [HasColimits C] :
    HasFilteredColimitsOfSize.{v, v, v} C where
  HasColimitsOfShape := inferInstance

theorem AddCommGroupCat.AB5 : AB5 (AddCommGroupCat.{u}) := by
  intro J _ _
  suffices {X Y : J ⥤ AddCommGroupCat} → (f : X ⟶ Y) → PreservesLimit (parallelPair f 0) colim by
    apply Functor.preservesFiniteLimitsOfPreservesKernels
  intros X Y f
  -- strat: first prove that limits in functor categories can be computed pointwise
  -- then hopefully a direct calculation
