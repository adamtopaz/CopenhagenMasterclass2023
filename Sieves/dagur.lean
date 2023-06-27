import Mathlib.CategoryTheory.Sites.Coverage

namespace CategoryTheory

variable (C : Type _) [Category C]

open Sieve

@[ext]
structure dCoverage where
  covering : ∀ (X : C), Set (Sieve X)
  pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Presieve X) (_ : S ∈ (arrows)'' (covering X)),
    ∃ (T : Presieve Y), T ∈ (arrows)'' (covering Y) ∧ T.FactorsThruAlong S f

variable {C}

def dCoverage.toCoverage (F : dCoverage C) : Coverage C where
  covering := fun X => (arrows)'' (F.covering X)
  pullback := fun _ _ f S hS => F.pullback f S hS
    

end CategoryTheory