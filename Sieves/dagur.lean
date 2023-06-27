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
  pullback := F.pullback
    

def Coverage.to_dCoverage (F : Coverage C) : dCoverage C where
  covering := fun X ↦ generate '' (F.covering X)
  pullback := fun X Y f S hS ↦ by
    obtain ⟨T, ⟨W, hW⟩, hT⟩ := hS 
    obtain ⟨R,hR⟩ := F.pullback f W hW.1
    use (Sieve.generate R).arrows 
    refine' ⟨⟨Sieve.generate R, ⟨_, _⟩⟩, _⟩ 
    · use R 
      exact ⟨hR.1,rfl⟩  
    · rfl
    · dsimp [Presieve.FactorsThruAlong] at *  
      simp only [forall_exists_index, and_imp]
      intro Z φ K ψ τ hτ  
      -- simp only [forall_exists_index, and_imp]
      have hR' := hR.2 hτ 
      obtain ⟨W_1, i, e, h⟩ := hR' 
      intro hh 
      use W_1
      use ψ ≫ i
      use e 
      constructor
      · sorry
      · rw [← hh] 
        simp only [Category.assoc]  
        rw [h.2]

end CategoryTheory