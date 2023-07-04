import ExtrDisc.Basic
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sieves.isSheafForPullbackSieve

universe u v
section HasPullbackOfRightMono

open CategoryTheory Opposite CategoryTheory.Limits Functor

variable (C : Type u) [Category.{v, u} C] 

class HasPullbackOfIsIsodesc : Prop where
    HasPullback : ∀ {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbackOfIsIsodesc C] {X Z : C} {α : Type _} (f : X ⟶ Z) {Y : (a : α) → C} 
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :  
    HasPullback f (i a) := HasPullbackOfIsIsodesc.HasPullback f i a

instance [HasPullbacks C] : HasPullbackOfIsIsodesc C := ⟨fun _ _ _ => inferInstance⟩

end HasPullbackOfRightMono

section Coverage
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] 

open Sieve CategoryTheory.Limits Opposite

variable {C}

def DagurSieveIso [HasFiniteCoproducts C] (B : C) := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C)
  (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }

def DagurSieveSingle (B : C) := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
      (fun (_ : Unit) ↦ f) ∧ Epi f }

variable [HasFiniteCoproducts C] (C)

def Extensivity [HasPullbackOfIsIsodesc C] : Prop :=
  ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
  {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
     IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

def EverythingIsProjective : Prop :=
  ∀ X : C, Projective X

def dagurCoverage [HasFiniteCoproducts C] [HasPullbackOfIsIsodesc C]
    (h_proj : EverythingIsProjective C) (h_ext : Extensivity C) : Coverage C where
  covering B :=   (DagurSieveIso B) ∪ (DagurSieveSingle B)
  pullback := by
    rintro X Y f S (⟨α, hα, Z, π, hS, h_iso⟩ | ⟨Z, π, hπ, h_epi⟩)
    · let Z' : α → C := fun a ↦ pullback f (π a)
      set π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst with hπ'
      set S' := @Presieve.ofArrows C _ _ α Z' π' with hS'
      use S'
      constructor
      · rw [Set.mem_union]
        apply Or.intro_left
        rw [DagurSieveIso]
        constructor
        refine ⟨hα, Z', π', ⟨by simp only, ?_⟩⟩
        · rw [hπ']
          exact h_ext (fun x => π x) f h_iso
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
        refine ⟨Y, 𝟙 _, by {rw [Presieve.ofArrows_pUnit (𝟙 Y)]}, instEpiIdToCategoryStruct Y⟩
      · rw [hS', Presieve.FactorsThruAlong]
        intro W g hg
        cases hg
        simp only [Category.id_comp]
        use Z
        use @Projective.factorThru C _ Y X Z ?_ f π h_epi
        exact h_proj Y
        use π
        constructor
        · cases hπ
          rw [Presieve.ofArrows_pUnit]
          exact Presieve.singleton.mk
        · have : Projective Y
          exact h_proj Y
          exact @Projective.factorThru_comp C _ Y X Z this f π h_epi

variable [HasPullbackOfIsIsodesc C] {C}

lemma isPullbackSieve_DagurSieveIso {X : C} {S : Presieve X}
    (hS : S ∈ DagurSieveIso X) : isPullbackPresieve S := by
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩ 
  intro Y₁ Y₂ f hf g hg
  rw [hS] at hf hg
  cases' hg with b
  apply HasPullbackOfIsIsodesc.HasPullback f

lemma DagurSieveIsoFinite {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X) :
    Finite (ΣY, { f : Y ⟶ X // S f }) := by
  rcases hS with ⟨α, _, Z, π, hS, _⟩
  classical
  refine' Fintype.finite (Fintype.ofSurjective (fun a => ⟨Z a, π a, hS ▸ Presieve.ofArrows.mk a⟩)
    (fun ⟨Y, ⟨f, hf⟩⟩ => _))
  cases' (hS ▸ hf) with a h
  exact ⟨a, rfl⟩

lemma isSheafForDagurSieveIso {X : C} {S : Presieve X} (hS : S ∈ DagurSieveIso X)
    {F : Cᵒᵖ ⥤ Type max u v}
    (hF : PreservesFiniteProducts F) :
    Presieve.IsSheafFor F S := by    
  have hFinite := DagurSieveIsoFinite hS
  obtain ⟨n, ⟨e⟩⟩ := finite_iff_exists_equiv_fin.1 hFinite
  let E := (Discrete.equivalence e).symm
  refine' (Equalizer.Presieve.sheaf_condition' F <| isPullbackSieve_DagurSieveIso hS).2 _
  rcases hS with ⟨α, _, Z, π, hS, HIso⟩
  rw [Limits.Types.type_equalizer_iff_unique]
  intro y hy
  have hpreserves : PreservesLimitsOfShape (Discrete (ΣY, { f : Y ⟶ X // S f })) F := by
    suffices PreservesLimitsOfShape (Discrete (Fin n)) F by
      · exact Limits.preservesLimitsOfShapeOfEquiv E F
    have := (hF.preserves (Fin n))
    infer_instance
  let φ : F.obj (∏ fun f : ΣY, { f : Y ⟶ X // S f } => (op f.1)) ≅
      ∏ fun f : ΣY, { f : Y ⟶ X // S f } => F.obj (op f.1) :=
    Limits.PreservesProduct.iso F (fun f : ΣY, { f : Y ⟶ X // S f } => (op f.1))

  sorry

end CategoryTheory

end Coverage