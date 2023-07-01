import Mathlib.Condensed.Basic
import FindWithGpt

namespace Condensed

open CategoryTheory Limits Opposite


universe u v w

-- TODO: Move
lemma isSheafFor_ofArrows 
  {α : Type} {C : Type _} [Category C] (P : Cᵒᵖ ⥤ Type w)
  (B : C) (X : α → C) (π : (a : α)  → (X a ⟶ B)) :
  Presieve.IsSheafFor P (Presieve.ofArrows X π) ↔ 
  (∀ (x : (a : α) → P.obj (op (X a)))
    (hx : ∀ (R : C) (i j : α) (ri : R ⟶ X i) (rj : R ⟶ X j),
      P.map ri.op (x i) = P.map rj.op (x j)), 
    ∃! b : P.obj (op B), ∀ i, P.map (π i).op b = x i) := sorry

variable {C : Type w} [Category.{v} C]

noncomputable
def productFan (P : CompHaus.{u}ᵒᵖ ⥤ C) 
    {α : Type} [Fintype α] 
    (X : α → CompHaus.{u}) :
    Fan fun a => P.obj (X a |> op) := 
  Fan.mk (P.obj (∐ X |> op)) fun a => P.map (Sigma.ι _ a).op

def ProductCondition (P : CompHaus.{u}ᵒᵖ ⥤ C) : Prop := 
  ∀ {α : Type} [Fintype α] (X : α → CompHaus.{u}),  
  Nonempty (IsLimit <| productFan P X)

noncomputable
def equalizerFork (P : CompHaus.{u}ᵒᵖ ⥤ C) 
    {X B : CompHaus.{u}} (f : X ⟶ B) :
    Fork 
      (P.map <| pullback.fst (f := f) (g := f) |>.op) 
      (P.map <| pullback.snd (f := f) (g := f) |>.op) := 
  Fork.ofι (P.map f.op) <| by 
    simp only [← P.map_comp, ← op_comp, pullback.condition]

def EqualizerCondition (P : CompHaus.{u}ᵒᵖ ⥤ C) : Prop :=
  ∀ {X Y : CompHaus.{u}} (f : X ⟶ Y) [Epi f],
  Nonempty (IsLimit <| equalizerFork P f) 

/-- NOTE: A different approach in terms of coverages is underway (DON't SE). -/
theorem isSheaf_iff_conditions (P : CompHaus.{u}ᵒᵖ ⥤ C) :
    Presheaf.IsSheaf (coherentTopology CompHaus) P ↔ 
    ProductCondition P ∧ EqualizerCondition P := by
  constructor
  · intro H
    constructor
    · intro α _ X
      let B := ∐ X
      let π : (a : α) → (X a ⟶ B) := 
        Sigma.ι X
      have : EffectiveEpiFamily X π := sorry
      specialize H (P.obj <| op B)
      erw [Presieve.isSheaf_coverage] at H
      specialize H (Presieve.ofArrows X π) ?_
      · sorry
      sorry
    · sorry 
  · intro ⟨H1,H2⟩ 
    intro T
    erw [Presieve.isSheaf_coverage] 
    rintro B R ⟨α, _, X, π, rfl, H⟩
    specialize H2 (Sigma.desc π)
    rw [isSheafFor_ofArrows]
    intro x hx 
    dsimp at x
    sorry

end Condensed


