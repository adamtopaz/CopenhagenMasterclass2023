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
    (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) : (a : α) → (Family.toCompHaus X) a ⟶ ExtrDisc.toCompHaus.obj B :=
  fun a => ExtrDisc.toCompHaus.map (π a)

theorem effectiveEpiFamily.toCompHaus {α : Type} [Fintype α] {B : ExtrDisc.{u}} (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (Family.toCompHaus X) (Family.toCompHaus' X π) := by 
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  replace := ((ExtrDisc.effectiveEpiFamily_tfae _ _).out 0 2).1 H
  
  sorry

-- instance : Precoherent ExtrDisc.{u} := by
--   constructor
--   intro B₁ B₂ f α _ X₁ π₁ h₁
--   refine' ⟨α, inferInstance, fun a => _, _, _⟩
--   · 
  -- refine ⟨α, inferInstance, fun a => pullback f (π₁ a), fun a => pullback.fst _ _, ?_,
  --   id, fun a => pullback.snd _ _, ?_⟩
  -- · have := (effectiveEpiFamily_tfae _ π₁).out 0 2 ; rw [this] at h₁ ; clear this
  --   have := (effectiveEpiFamily_tfae _ (fun a => pullback.fst f (π₁ a))).out 0 2
  --   rw [this] ; clear this
  --   intro b₂
  --   obtain ⟨a,x,h⟩ := h₁ (f b₂)
  --   refine ⟨a, ⟨⟨b₂, x⟩, h.symm⟩, rfl⟩
  -- · intro a
  --   dsimp
  --   ext ⟨⟨_,_⟩,h⟩
  --   exact h.symm

end ExtrDisc