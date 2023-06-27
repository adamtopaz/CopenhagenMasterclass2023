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

open CategoryTheory CompHaus Functor

namespace ExtrDisc

theorem _root_.CategoryTheory.EffectiveEpiFamily.toCompHaus {α : Type} [Fintype α] {B : ExtrDisc.{u}} {X : α → ExtrDisc.{u}}
    {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (fun a => toCompHaus.obj (X a) ) (fun a => toCompHaus.map (π a)) := by 
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  exact (((effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _


instance : Precoherent ExtrDisc.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine' ⟨α, inferInstance, fun a => (pullback f (π₁ a)).presentation, fun a => 
    toCompHaus.preimage (presentationπ _ ≫ (pullback.fst _ _)), _, id, fun a =>
    toCompHaus.preimage (presentationπ _ ≫ (pullback.snd _ _ )), fun a => _⟩
  · refine' ((effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
    have h₁' := ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).1 h₁.toCompHaus
    obtain ⟨a, x, h⟩ := h₁' (f b)
    obtain ⟨c, hc⟩ := (CompHaus.epi_iff_surjective _).1 (epiPresentπ (pullback f (π₁ a))) ⟨⟨b, x⟩, h.symm⟩
    refine' ⟨a, c, _⟩
    change toCompHaus.map (toCompHaus.preimage _) _ = _
    simp only [image_preimage, toCompHaus_obj, comp_apply, hc]
    rfl
  · apply map_injective toCompHaus
    simp only [map_comp, image_preimage, Category.assoc]
    congr 1
    ext ⟨⟨_, _⟩, h⟩
    exact h.symm

end ExtrDisc