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

theorem effectiveEpiFamily.toCompHaus {α : Type} [Fintype α] {B : ExtrDisc.{u}} {X : α → ExtrDisc.{u}}
    {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (fun a => toCompHaus.obj (X a) ) (fun a => ExtrDisc.toCompHaus.map (π a)) := by 
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  exact (((ExtrDisc.effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _


instance : Precoherent ExtrDisc.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine' ⟨α, inferInstance, fun a => (CompHaus.pullback f (π₁ a)).presentation, fun a => 
    ExtrDisc.toCompHaus.preimage (CompHaus.presentationπ (CompHaus.pullback f (π₁ a)) ≫ (CompHaus.pullback.fst _ _) :
      toCompHaus.obj (CompHaus.presentation (CompHaus.pullback f (π₁ a))) ⟶ toCompHaus.obj B₂), _, id, fun a =>
      ExtrDisc.toCompHaus.preimage (CompHaus.presentationπ (CompHaus.pullback f (π₁ a)) ≫ (CompHaus.pullback.snd _ _ )),
      fun a => _⟩
  · refine' ((effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
    have h₁' := effectiveEpiFamily.toCompHaus h₁
    have := (CompHaus.effectiveEpiFamily_tfae _ (fun a => ExtrDisc.toCompHaus.map (π₁ a))).out 0 2 ; rw [this] at h₁' ; clear this
    obtain ⟨a,x,h⟩ := h₁' (f b)
    obtain ⟨bar, hbar⟩ := (CompHaus.epi_iff_surjective _).1 (CompHaus.epiPresentπ (CompHaus.pullback f (π₁ a)))
      (⟨⟨b, x⟩, h.symm⟩ : CompHaus.pullback f (π₁ a))
    refine' ⟨a, bar, _⟩
    change ExtrDisc.toCompHaus.map (ExtrDisc.toCompHaus.preimage (_ : ExtrDisc.toCompHaus.obj _ ⟶ ExtrDisc.toCompHaus.obj _)) _ = _
    simp only [CategoryTheory.Functor.image_preimage, toCompHaus_obj, comp_apply, hbar, Set.mem_setOf_eq]
    rfl
  · apply CategoryTheory.Functor.map_injective ExtrDisc.toCompHaus
    change toCompHaus.map (toCompHaus.preimage ((_ : ExtrDisc.toCompHaus.obj _ ⟶ ExtrDisc.toCompHaus.obj _)) ≫
      _) = toCompHaus.map (toCompHaus.preimage ((_ : ExtrDisc.toCompHaus.obj _ ⟶ ExtrDisc.toCompHaus.obj _)) ≫ _)
    rw [Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.image_preimage,
      CategoryTheory.Functor.image_preimage, Category.assoc, Category.assoc]
    congr 1
    dsimp
    ext ⟨⟨_, _⟩, h⟩
    exact h.symm

end ExtrDisc