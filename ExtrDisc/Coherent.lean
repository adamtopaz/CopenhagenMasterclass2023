/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import ExtrDisc.Basic
import ExtrDisc.Epi

/-!
# The category of extremally disconnected spaces is precoherent

This file contains a proof that the category of extremally disconnected
spaces is precoherent. Precoherence is the claim that "effective epis pull back"
and is the condition we'll use to define a *coverage* on `ExtrDisc`, which
is a collection of covering presieves satisfying a pullback condition.

## TODO

Supply the proof!

-/
universe u

open CategoryTheory

namespace ExtrDisc

def Family.toCompHaus {α : Type} (X : α → ExtrDisc.{u}) : α → CompHaus :=
  fun a => toCompHaus.obj (X a) 

def Family.toCompHaus' {α : Type} {B : ExtrDisc.{u}} 
    {X : α → ExtrDisc.{u}}
    (π : (a : α) → (X a ⟶ B)) : (a : α) → (Family.toCompHaus X) a ⟶ ExtrDisc.toCompHaus.obj B :=
  fun a => ExtrDisc.toCompHaus.map (π a)

theorem effectiveEpiFamily.toCompHaus {α : Type} [Fintype α] {B : ExtrDisc.{u}} {X : α → ExtrDisc.{u}}
    {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (Family.toCompHaus X) (Family.toCompHaus' π) := by 
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  exact (((ExtrDisc.effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _


instance : Precoherent ExtrDisc.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine' ⟨α, inferInstance, fun a => (CompHaus.pullback f (π₁ a)).presentation, fun a => 
    ExtrDisc.toCompHaus.preimage (CompHaus.presentationπ (CompHaus.pullback f (π₁ a)) ≫ (CompHaus.pullback.fst _ _) :
      toCompHaus.obj (CompHaus.presentation (CompHaus.pullback f (π₁ a))) ⟶ toCompHaus.obj B₂), _, _⟩
  · refine' ((effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
    have h₁' := effectiveEpiFamily.toCompHaus h₁
    have := (CompHaus.effectiveEpiFamily_tfae _ (Family.toCompHaus' π₁)).out 0 2 ; rw [this] at h₁' ; clear this
    obtain ⟨a,x,h⟩ := h₁' (f b)
    set foo : CompHaus.pullback f (π₁ a) := ⟨⟨b, x⟩, h.symm⟩ with foodef
    obtain ⟨bar, hbar⟩ := (CompHaus.epi_iff_surjective _).1 (CompHaus.epiPresentπ (CompHaus.pullback f (π₁ a))) foo
    refine' ⟨a, bar, _⟩

    change ExtrDisc.toCompHaus.map (Full.preimage (_ : ExtrDisc.toCompHaus.obj _ ⟶ ExtrDisc.toCompHaus.obj _)) _ = _
    

    







end ExtrDisc