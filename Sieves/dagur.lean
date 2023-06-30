import ExtrDisc.Basic
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sieves.isSheafForPullbackSieve

universe u v
section HasPullbackOfRightMono

open CategoryTheory Opposite CategoryTheory.Limits Functor

variable (C : Type u) [Category.{v, u} C] 

class HasPullbackOfRightMono : Prop where
    HasPullback_of_mono : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbackOfRightMono C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C} 
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :  
    HasPullback f (i a) := HasPullbackOfRightMono.HasPullback_of_mono f i a

instance [HasPullbacks C] : HasPullbackOfRightMono C := ⟨fun _ _ _ => inferInstance⟩

end HasPullbackOfRightMono

section Coverage
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] 

open Sieve CategoryTheory.Limits

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

def DagurSieveIso [HasFiniteCoproducts C] (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C)
  (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def DagurSieveSingle (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }

variable [HasFiniteCoproducts C] (C)


lemma Extensivity {α : Type} {Y : C} [Fintype α] [HasPullbackOfRightMono C]
  {Z : α → C}  {π : (a : α) → Z a ⟶ X} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)) 
  [∀ a : α, HasPullback f (π a)] :
  IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _)) := sorry

@[reducible]
def EverythingIsProjective (C : Type _) [Category C] : Prop :=
  ∀ X : C, Projective X

@[reducible]
def IsMono_ι (C : Type (u+1)) [Category C] [HasFiniteCoproducts C] : Prop :=
  ∀ (α : Type u) [Fintype α] (Z : α → C) (a : α), Mono (Sigma.ι Z a)


def dagurCoverage (C : Type _) [Category C] [HasFiniteCoproducts C] [HasPullbackOfRightMono C]
    (h_proj : EverythingIsProjective C) (h_mono_ι : IsMono_ι C) : Coverage C where
  covering B :=   (DagurSieveIso B) ∪ (DagurSieveSingle B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · have : ∀ a : α, Mono (π a)
      -- infer_instance
      · intro a
        have : π a = Sigma.ι Z a ≫ (Sigma.desc π)
        · simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
        rw [this]
        -- have ciccio := @mono_comp C
        sorry
        -- apply Mo
        
      --   -- have : Mono (Sigma.desc π)
      --   sorry
        -- refine SplitMono.mono (?_ (id (Eq.symm hS)))
      set Z' : α → C := fun a ↦ pullback f (π a) with hZ'
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [DagurSieveIso]
        -- simp only [Set.mem_setOf_eq]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          apply Extensivity
          exact h_iso
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
        rw [hS]
        refine Presieve.ofArrows.mk a
    · set S' := Presieve.singleton (𝟙 Y) with hS'
      use S'
      constructor
      · apply Or.intro_right
        rw [DagurSieveSingle]
        simp only [Set.mem_setOf_eq]--comment
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        rcases hg with ⟨a⟩
        simp only [Category.id_comp]
        sorry
        -- have proj : Projective (toCompHaus.obj X) := inferInstanceAs (Projective X.compHaus)
      -- have : Epi (toCompHaus.map f) := by
      --   rw [CompHaus.epi_iff_surjective]
      --   change Function.Surjective f
      --   rwa [← ExtrDisc.epi_iff_surjective]
      -- set g := toCompHaus.preimage <| Projective.factorThru (𝟙 _) (toCompHaus.map f) with hg
      -- have hfg : g ≫ f = 𝟙 _ := by
      --   refine' toCompHaus.map_injective _
      --   rw [map_comp, hg, image_preimage, Projective.factorThru_comp, CategoryTheory.Functor.map_id]


variable [HasPullbackOfRightMono C] {C}

lemma isPullbackSieve_DagurSieveIso {X : C} {S : Presieve X}
  (hS : S ∈ DagurSieveIso X) : isPullbackPresieve S := sorry

lemma isSheafForDagurSieveIso {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X)
    {F : Cᵒᵖ ⥤ Type max u v} (hF : PreservesFiniteProducts F) : Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_DagurSieveIso hS).2 _
  sorry

lemma two (F : DCoverage C) : F.toCoverage.toDCoverage = F := sorry

lemma three (F : Coverage C) : F.toGrothendieck = F.toDCoverage.toCoverage.toGrothendieck := sorry

end CategoryTheory

end Coverage