import Mathlib.CategoryTheory.Sites.Coverage

namespace CategoryTheory

variable (C : Type _) [Category C]

open Sieve

@[ext]
structure DCoverage where
  covering : ∀ (X : C), Set (Sieve X)
  pullback : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Presieve X) (_ : S ∈ (arrows)'' (covering X)),
    ∃ (T : Presieve Y), T ∈ (arrows)'' (covering Y) ∧ T.FactorsThruAlong S f

variable {C}

def DCoverage.toCoverage (F : DCoverage C) : Coverage C where
  covering := fun X => (arrows)'' (F.covering X)
  pullback := F.pullback
    

def Coverage.toDCoverage (F : Coverage C) : DCoverage C where
  covering := fun X ↦ generate '' (F.covering X)
  pullback := fun X Y f S hS ↦ by
    obtain ⟨T, ⟨W, hW⟩, hT⟩ := hS 
    obtain ⟨R,hR⟩ := F.pullback f W hW.1
    refine' ⟨(Sieve.generate R).arrows, ⟨⟨Sieve.generate R, ⟨⟨R, ⟨hR.1, rfl⟩⟩, rfl⟩⟩, _⟩⟩    
    dsimp [Presieve.FactorsThruAlong] at *  
    simp only [forall_exists_index, and_imp]
    intro Z φ K ψ τ hτ hh
    obtain ⟨W_1, i, e, h⟩ := hR.2 hτ 
    refine' ⟨W_1, ψ ≫ i, e, ⟨_, by rw [← hh, Category.assoc, Category.assoc, h.2]⟩⟩
    rw [← hT, ← hW.2]
    exact ⟨W_1, 𝟙 _, e, ⟨h.1, by simp⟩⟩ 

end CategoryTheory